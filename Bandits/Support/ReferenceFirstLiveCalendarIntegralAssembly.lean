/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstLiveSourcePhasePartition

import Mathlib.Tactic.FinCases

/-!
# Original-source first-live calendar integral assembly

The source law throughout is the original finite source law, retaining the
complete public rows, all private arrays, and the original coordinator index.
All cell measures are inherited unnormalized restrictions, including zero
mass cells. These are internal integration identities and do not state a
conditional sampler law or a manuscript filtration claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveCalendarIntegralAssembly

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (t : Fin p.T) (control0 : TimeControl p)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
/-- Continuing first-live sources are exactly the original branch images over
the original selected row and elapsed launch time. -/
theorem sourcePhase_nonempty_iUnion :
    Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 =
      ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
        Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0 := by
  classical
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · intro hp
    have hstart :
        ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val :=
      hp.2.1.le
    refine ⟨BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega,
      ⟨_, Nat.lt_succ_of_le hstart⟩, ?_⟩
    rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalBranchEvent_physical_iff]
    refine ⟨Bandits.Support.ReferenceFirstLiveSourcePhasePartition.source_actual_stratum
      rate rewards C_star C_h t omega hp.1 hstart,
      Nat.sub_pos_of_lt hp.2.1, ?_⟩
    obtain ⟨hn, htest⟩ := hp.2.2
    refine ⟨hn, ?_⟩
    cases hc : (ReferenceActivePhysicalStep.prepare
        ((Bandits.Support.ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simp_all only
    | _ => simp_all only
  · rintro ⟨q, ⟨v, hv⟩, hmem⟩
    rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalBranchEvent_physical_iff] at hmem
    obtain ⟨hE, hpos, hn, htest⟩ := hmem
    have he : ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = v :=
      hE.2.2
    subst v
    refine ⟨hE.2.1, ?_, hn, ?_⟩
    · change 0 < t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at hpos
      change ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h < t.val
      omega
    · cases hc : (ReferenceActivePhysicalStep.prepare
        ((Bandits.Support.ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h]'hn).input).coordinator with
      | live r owned base outcome => cases outcome <;> simp_all only
      | _ => simp_all only

/-- Empty-pending first-live sources are exactly the original empty-cell
images over the original selected row and elapsed launch time. -/
theorem sourcePhase_empty_iUnion :
    Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4 =
      ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
        Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0 := by
  classical
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · intro hp
    have hstart :
        ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val :=
      hp.2.1.le
    refine ⟨BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega,
      ⟨_, Nat.lt_succ_of_le hstart⟩, ?_⟩
    rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalEmptyEvent_physical_iff]
    refine ⟨Bandits.Support.ReferenceFirstLiveSourcePhasePartition.source_actual_stratum
      rate rewards C_star C_h t omega hp.1 hstart,
      Nat.sub_pos_of_lt hp.2.1, ?_⟩
    obtain ⟨hn, htest⟩ := hp.2.2
    refine ⟨hn, ?_⟩
    cases hc : (ReferenceActivePhysicalStep.prepare
        ((Bandits.Support.ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simp_all only
    | _ => simp_all only
  · rintro ⟨q, ⟨v, hv⟩, hmem⟩
    rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalEmptyEvent_physical_iff] at hmem
    obtain ⟨hE, hpos, hn, htest⟩ := hmem
    have he : ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = v :=
      hE.2.2
    subst v
    refine ⟨hE.2.1, ?_, hn, ?_⟩
    · change 0 < t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at hpos
      change ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h < t.val
      omega
    · cases hc : (ReferenceActivePhysicalStep.prepare
        ((Bandits.Support.ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simp_all only
    | _ => simp_all only

/-- The birth phase uses the actual source stratum at the exact first
launch-time index. -/
theorem sourcePhase_birth_iUnion :
    Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 =
      ⋃ q : Fin (ConstructorDimensions.M p),
        Bandits.Support.ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
  classical
  ext omega
  simp only [Set.mem_iUnion]
  change ((ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
      t.val = ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h) ↔
    (∃ q : Fin (ConstructorDimensions.M p),
      omega ∈ Bandits.Support.ReferenceTotalSourcePairCoupling.sourceStratumEvent
        rate rewards C_star C_h t
          (Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
  constructor
  · intro h
    refine ⟨BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega, ?_⟩
    change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega = _ ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).completed = t.val
    refine ⟨rfl, h.1, ?_⟩
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using h.2.symm
  · rintro ⟨q, hq⟩
    change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega = q ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).completed = t.val at hq
    refine ⟨hq.2.1, ?_⟩
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hq.2.2.symm

private theorem branch_events_pairwise :
    Pairwise (fun a b : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) =>
      Disjoint
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h b.1 t b.2.val (Nat.lt_succ_iff.mp b.2.isLt) control0)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro omega ha hb
  rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalBranchEvent_physical_iff] at ha hb
  obtain ⟨hEa, _, _, _⟩ := ha
  obtain ⟨hEb, _, _, _⟩ := hb
  let ia := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
    a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt)
  let ib := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
    b.1 t b.2.val (Nat.lt_succ_iff.mp b.2.isLt)
  by_cases hindex : ia = ib
  · have hq : a.1 = b.1 := congrArg Prod.fst hindex
    have hs : a.2.val = b.2.val := congrArg (fun i :
      ReferenceTotalSourceDisintegration.StratumIndex t => i.2.val) hindex
    have hv : a.2 = b.2 := Fin.ext hs
    exact hab (Prod.ext hq hv)
  · exact Set.disjoint_left.mp
      (ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
        rate rewards C_star C_h t ia ib hindex) hEa hEb

private theorem empty_events_pairwise :
    Pairwise (fun a b : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) =>
      Disjoint
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h b.1 t b.2.val (Nat.lt_succ_iff.mp b.2.isLt) control0)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro omega ha hb
  rw [Bandits.Support.ReferenceFirstLiveSourcePhasePartition.mem_originalEmptyEvent_physical_iff] at ha hb
  obtain ⟨hEa, _, _, _⟩ := ha
  obtain ⟨hEb, _, _, _⟩ := hb
  let ia := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
    a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt)
  let ib := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
    b.1 t b.2.val (Nat.lt_succ_iff.mp b.2.isLt)
  by_cases hindex : ia = ib
  · have hq : a.1 = b.1 := congrArg Prod.fst hindex
    have hs : a.2.val = b.2.val := congrArg (fun i :
      ReferenceTotalSourceDisintegration.StratumIndex t => i.2.val) hindex
    have hv : a.2 = b.2 := Fin.ext hs
    exact hab (Prod.ext hq hv)
  · exact Set.disjoint_left.mp
      (ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
        rate rewards C_star C_h t ia ib hindex) hEa hEb

/-- The continuing branch images are pairwise disjoint across both cell kinds,
selected rows, and elapsed calendar times. -/
theorem source_images_pairwise :
    Pairwise (fun a b : Fin 2 ×
      (Fin (ConstructorDimensions.M p) × Fin (t.val + 1)) =>
      Disjoint
        (if a.1.val = 0 then
          Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h a.2.1 t a.2.2.val
            (Nat.lt_succ_iff.mp a.2.2.isLt) control0
        else Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h a.2.1 t a.2.2.val
          (Nat.lt_succ_iff.mp a.2.2.isLt) control0)
        (if b.1.val = 0 then
          Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h b.2.1 t b.2.2.val
            (Nat.lt_succ_iff.mp b.2.2.isLt) control0
        else Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h b.2.1 t b.2.2.val
          (Nat.lt_succ_iff.mp b.2.2.isLt) control0)) := by
  classical
  intro a b hab
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases a with ⟨qa, va⟩
  rcases b with ⟨qb, vb⟩
  fin_cases i <;> fin_cases j <;> norm_num
  · have hne : (qa, va) ≠ (qb, vb) := by
      intro he
      apply hab
      cases he
      rfl
    have hdisj : Disjoint
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h qa t va.val (Nat.lt_succ_iff.mp va.isLt) control0)
        (Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h qb t vb.val (Nat.lt_succ_iff.mp vb.isLt) control0) :=
      branch_events_pairwise rate rewards C_star C_h t control0 hne
    exact hdisj
  · apply Set.disjoint_left.mpr
    intro omega ha hb
    have h3 : omega ∈ Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 3 := by
      have hmem : omega ∈ ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 :=
        Set.mem_iUnion.mpr ⟨qa, Set.mem_iUnion.mpr ⟨va, ha⟩⟩
      rw [sourcePhase_nonempty_iUnion]
      exact hmem
    have h4 : omega ∈ Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 4 := by
      have hmem : omega ∈ ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 :=
        Set.mem_iUnion.mpr ⟨qb, Set.mem_iUnion.mpr ⟨vb, hb⟩⟩
      rw [sourcePhase_empty_iUnion]
      exact hmem
    have hdisj : Disjoint
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 3)
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 4) :=
      Bandits.Support.ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint
        rate rewards C_star C_h t (by decide : (3 : Fin 6) ≠ 4)
    exact Set.disjoint_left.mp hdisj h3 h4
  · apply Set.disjoint_left.mpr
    intro omega ha hb
    have h3 : omega ∈ Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 3 := by
      have hmem : omega ∈ ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          Bandits.Support.ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 :=
        Set.mem_iUnion.mpr ⟨qb, Set.mem_iUnion.mpr ⟨vb, hb⟩⟩
      rw [sourcePhase_nonempty_iUnion]
      exact hmem
    have h4 : omega ∈ Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 4 := by
      have hmem : omega ∈ ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 :=
        Set.mem_iUnion.mpr ⟨qa, Set.mem_iUnion.mpr ⟨va, ha⟩⟩
      rw [sourcePhase_empty_iUnion]
      exact hmem
    have hdisj : Disjoint
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 3)
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 4) :=
      Bandits.Support.ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint
        rate rewards C_star C_h t (by decide : (3 : Fin 6) ≠ 4)
    exact Set.disjoint_left.mp hdisj h3 h4
  · have hne : (qa, va) ≠ (qb, vb) := by
      intro he
      apply hab
      cases he
      rfl
    have hdisj : Disjoint
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h qa t va.val (Nat.lt_succ_iff.mp va.isLt) control0)
        (Bandits.Support.ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h qb t vb.val (Nat.lt_succ_iff.mp vb.isLt) control0) :=
      empty_events_pairwise rate rewards C_star C_h t control0 hne
    exact hdisj

private theorem birth_events_pairwise :
    Pairwise (fun q q' : Fin (ConstructorDimensions.M p) =>
      Disjoint
        (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
        (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q' t))) := by
  intro q q' hne
  apply ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
  intro h
  apply hne
  exact congrArg Prod.fst h

private theorem sourcePhase_cover :
    (⋃ i : Fin 6, ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t i) = Set.univ := by
  ext omega
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ReferenceFirstLiveSourcePhasePartition.source_phases_exhaustive
    rate rewards C_star C_h t omega

private theorem sourcePhase_measure_sum (control0 : TimeControl p) :
    mu = ∑ i : Fin 6, Measure.restrict mu
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i) := by
  calc
    mu = Measure.restrict mu Set.univ := Measure.restrict_univ.symm
    _ = Measure.restrict mu (⋃ i : Fin 6,
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i) := by
      rw [sourcePhase_cover]
    _ = Measure.sum fun i : Fin 6 => Measure.restrict mu
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i) :=
      Measure.restrict_iUnion
        (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t)
        (fun i => ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
          rate rewards C_star C_h t control0 i)
    _ = _ := Measure.sum_fintype _

private theorem birth_phase_restrict (control0 : TimeControl p) :
    Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2) =
      ∑ q : Fin (ConstructorDimensions.M p), Measure.restrict mu
        (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) := by
  rw [sourcePhase_birth_iUnion]
  rw [Measure.restrict_iUnion (birth_events_pairwise rate rewards C_star C_h t)
    (fun q => ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))]
  exact Measure.sum_fintype _

private theorem branch_phase_restrict :
    Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 3) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1), Measure.restrict mu
        (ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) := by
  rw [sourcePhase_nonempty_iUnion,
    ← Set.iUnion_prod' (fun a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) =>
      ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
        rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)]
  rw [Measure.restrict_iUnion (branch_events_pairwise rate rewards C_star C_h t control0)
    (fun a => ReferenceFirstLiveBranchIntegralTransport.measurableSet_originalBranchEvent
      rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)]
  rw [Measure.sum_fintype, Fintype.sum_prod_type]

private theorem empty_phase_restrict :
    Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 4) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1), Measure.restrict mu
        (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) := by
  rw [sourcePhase_empty_iUnion,
    ← Set.iUnion_prod' (fun a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) =>
      ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
        rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)]
  rw [Measure.restrict_iUnion (empty_events_pairwise rate rewards C_star C_h t control0)
    (fun a => ReferenceFirstLiveSourcePhasePartition.measurableSet_originalEmptyEvent
      rate rewards C_star C_h a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0)]
  rw [Measure.sum_fintype, Fintype.sum_prod_type]

/-- The original source law is the finite disjoint sum of its no-crossing,
future-start, terminal, birth, nonempty, and empty restrictions. All induced
cell measures retain their original unnormalized mass. -/
theorem original_source_measure_decomposition :
    mu =
      Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0) +
      Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 1) +
      Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 5) +
      (∑ q : Fin (ConstructorDimensions.M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).map
          (Subtype.val : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) → S)) +
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
          (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
          (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := by
  have h := sourcePhase_measure_sum rate rewards C_star C_h t control0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  norm_num at h
  rw [birth_phase_restrict rate rewards C_star C_h t control0,
    branch_phase_restrict rate rewards C_star C_h t control0,
    empty_phase_restrict rate rewards C_star C_h t control0] at h
  simp_rw [← ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h t control0,
    ← ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_map_original
      rate rewards C_star C_h,
    ← ReferenceFirstLiveSourcePhasePartition.muEmpty_map_original
      rate rewards C_star C_h] at h
  have hcombine :
      (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) +
      (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext q
    rw [← Finset.sum_add_distrib]
  rw [← hcombine]
  calc
    mu =
      Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0) +
      (Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 1) +
      ((∑ q : Fin (ConstructorDimensions.M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).map
          (Subtype.val : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) → S)) +
      ((∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) +
       ((∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).map
            (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) +
        Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 5))))) := h
    _ = _ := by abel

private theorem birth_cell_real (control0 : TimeControl p)
    (q : Fin (ConstructorDimensions.M p)) :
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ =
      Measure.real mu (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) := by
  let f := (Subtype.val :
    ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) → S)
  have hmap := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
    rate rewards C_star C_h t control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  calc
    _ = Measure.real ((ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).map f) Set.univ := by
        symm
        simpa [f] using map_measureReal_apply
          (measurable_subtype_coe : Measurable f) MeasurableSet.univ
    _ = (Measure.restrict mu (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))).real Set.univ := by
        exact congrArg (fun η : Measure S => η.real Set.univ) (by simpa [f] using hmap)
    _ = _ := by simp

private theorem branch_cell_real (q : Fin (ConstructorDimensions.M p))
    (v : Fin (t.val + 1)) :
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ =
      Measure.real mu (ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0) := by
  let f := ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
    v.val (Nat.lt_succ_iff.mp v.isLt) control0
  have hmap := ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_map_original
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  calc
    _ = Measure.real ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0).map f) Set.univ := by
        symm
        simpa [f] using map_measureReal_apply
          (ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).measurable
          MeasurableSet.univ
    _ = (Measure.restrict mu (ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0)).real Set.univ := by
        exact congrArg (fun η : Measure S => η.real Set.univ) (by simpa [f] using hmap)
    _ = _ := by simp

private theorem empty_cell_real (q : Fin (ConstructorDimensions.M p))
    (v : Fin (t.val + 1)) :
    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0) := by
  let f := ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
    v.val (Nat.lt_succ_iff.mp v.isLt) control0
  have hmap := ReferenceFirstLiveSourcePhasePartition.muEmpty_map_original
    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  calc
    _ = Measure.real ((ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0).map f) Set.univ := by
        symm
        simpa [f] using map_measureReal_apply
          (ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).measurable
          MeasurableSet.univ
    _ = (Measure.restrict mu (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0)).real Set.univ := by
        exact congrArg (fun η : Measure S => η.real Set.univ) (by simpa [f] using hmap)
    _ = _ := by simp

private theorem birth_cells_real_sum (control0 : TimeControl p) :
    (∑ q : Fin (ConstructorDimensions.M p),
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2) := by
  classical
  symm
  rw [sourcePhase_birth_iUnion]
  rw [measureReal_iUnion_fintype
    (birth_events_pairwise rate rewards C_star C_h t)
    (fun q => ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))]
  simp_rw [birth_cell_real rate rewards C_star C_h t control0]

private theorem branch_cells_real_sum :
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ) =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3) := by
  classical
  let f : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) → Set S := fun a =>
    ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h a.1 t
      a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  have hf : Pairwise (fun a b => Disjoint (f a) (f b)) :=
    branch_events_pairwise rate rewards C_star C_h t control0
  have hm : ∀ a, MeasurableSet (f a) := fun a =>
    ReferenceFirstLiveBranchIntegralTransport.measurableSet_originalBranchEvent rate rewards C_star C_h
      a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  symm
  rw [sourcePhase_nonempty_iUnion, ← Set.iUnion_prod' f]
  rw [measureReal_iUnion_fintype hf hm, Fintype.sum_prod_type]
  simp_rw [f]
  simp_rw [branch_cell_real rate rewards C_star C_h t control0]

private theorem empty_cells_real_sum :
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ) =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) := by
  classical
  let f : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) → Set S := fun a =>
    ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h a.1 t
      a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  have hf : Pairwise (fun a b => Disjoint (f a) (f b)) :=
    empty_events_pairwise rate rewards C_star C_h t control0
  have hm : ∀ a, MeasurableSet (f a) := fun a =>
    ReferenceFirstLiveSourcePhasePartition.measurableSet_originalEmptyEvent rate rewards C_star C_h
      a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  symm
  rw [sourcePhase_empty_iUnion, ← Set.iUnion_prod' f]
  rw [measureReal_iUnion_fintype hf hm, Fintype.sum_prod_type]
  simp_rw [f]
  simp_rw [empty_cell_real rate rewards C_star C_h t control0]

private theorem phase234_real_union (control0 : TimeControl p) :
    Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2) +
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3) +
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) := by
  let P2 := ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2
  let P3 := ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3
  let P4 := ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4
  have h23 : Disjoint P2 P3 := by
    exact ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t
      (by decide : (2 : Fin 6) ≠ 3)
  have h24 : Disjoint P2 P4 := by
    exact ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t
      (by decide : (2 : Fin 6) ≠ 4)
  have h34 : Disjoint P3 P4 := by
    exact ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t
      (by decide : (3 : Fin 6) ≠ 4)
  have hUnion : Disjoint (P2 ∪ P3) P4 := Set.disjoint_union_left.mpr ⟨h24, h34⟩
  have hm3 := ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
    rate rewards C_star C_h t control0 (3 : Fin 6)
  have hm4 := ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
    rate rewards C_star C_h t control0 (4 : Fin 6)
  calc
    Measure.real mu (P2 ∪ P3 ∪ P4) = Measure.real mu (P2 ∪ P3) + Measure.real mu P4 :=
      measureReal_union hUnion hm4
    _ = Measure.real mu P2 + Measure.real mu P3 + Measure.real mu P4 := by
      rw [measureReal_union h23 hm3]

/-- The original source mass of the combined birth, continuing, and empty
phases equals the sum of all unnormalized cell masses. -/
theorem source_cell_mass_eq :
    (∑ q : Fin (ConstructorDimensions.M p),
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
       (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) := by
  calc
    _ =
      (∑ q : Fin (ConstructorDimensions.M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
      ((∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ) +
       (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) := by
      congr 1
      calc
        (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
          ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
            (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ))
            = ∑ q : Fin (ConstructorDimensions.M p),
                ((∑ v : Fin (t.val + 1),
                    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
                      v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ) +
                 (∑ v : Fin (t.val + 1),
                    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
                      v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact Finset.sum_add_distrib
        _ = _ := Finset.sum_add_distrib
    _ =
      Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2) +
      (Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3) +
       Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) := by
      rw [birth_cells_real_sum rate rewards C_star C_h t control0,
        branch_cells_real_sum rate rewards C_star C_h t control0,
        empty_cells_real_sum rate rewards C_star C_h t control0]
    _ = _ := by
      rw [phase234_real_union rate rewards C_star C_h t control0]
      abel

/-- The original source phase masses are bounded by the original probability
law; no cell is conditioned or renormalized. -/
theorem source_cell_mass_le_one :
    (∑ q : Fin (ConstructorDimensions.M p),
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
       (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) ≤ 1 := by
  have hprob : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hmass : mu Set.univ = 1 := hprob.measure_univ
  rw [source_cell_mass_eq rate rewards C_star C_h t control0]
  calc
    Measure.real mu (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4) ≤
        Measure.real mu Set.univ := by
          exact measureReal_mono (Set.subset_univ _) (by rw [hmass]; simp)
    _ = 1 := by simp [Measure.real_def, hmass]

private def calendarPotentialStep : S → ℝ := fun omega =>
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
      (t.val + 1) omega -
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
      t.val omega

private def calendarBacklogStep (j : Fin p.K) : S → ℝ := fun omega =>
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
      (t.val + 1) omega -
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
      t.val omega

private def calendarExpStep (j : Fin p.K) : S → ℝ := fun omega =>
  Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
        (t.val + 1) omega) -
    Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
        t.val omega)

private theorem firstWindow_prefix_stable_on_exception (omega : S)
    (hω : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h) =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h) := by
  classical
  rcases hω with h0 | h1 | h5
  · change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing = none at h0
    have hnil := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega h0).2.1
    rw [hnil]
    simp
  · change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
      t.val < ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at h1
    have hbefore : t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = 0 := by
      omega
    have hafter : t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = 0 := by
      omega
    rw [hafter, hbefore]
  · change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
      ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h < t.val ∧
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length ≤
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at h5
    have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
      rate rewards C_star C_h omega
    have hbefore :
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ≤
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h := by
      rw [hlen]
      exact h5.2.2
    have hafter :
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ≤
          t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h := by
      omega
    rw [List.take_of_length_le hafter, List.take_of_length_le hbefore]

private theorem calendarPotentialStep_zero_on_exception (omega : S)
    (hω : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5) :
    calendarPotentialStep rate rewards C_star C_h t omega = 0 := by
  unfold calendarPotentialStep
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
  rw [firstWindow_prefix_stable_on_exception rate rewards C_star C_h t omega hω]
  simp

private theorem calendarBacklogStep_zero_on_exception (j : Fin p.K) (omega : S)
    (hω : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5) :
    calendarBacklogStep rate rewards C_star C_h t j omega = 0 := by
  unfold calendarBacklogStep
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
  rw [firstWindow_prefix_stable_on_exception rate rewards C_star C_h t omega hω]
  simp

private theorem calendarExpStep_zero_on_exception (j : Fin p.K) (omega : S)
    (hω : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5) :
    calendarExpStep rate rewards C_star C_h t j omega = 0 := by
  unfold calendarExpStep
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
  rw [firstWindow_prefix_stable_on_exception rate rewards C_star C_h t omega hω]
  simp

private theorem integrable_calendarPotentialStep :
    Integrable (calendarPotentialStep rate rewards C_star C_h t) mu := by
  exact (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
    rate rewards C_star C_h (t.val + 1)).sub
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
      rate rewards C_star C_h t.val)

private theorem integrable_calendarBacklogStep (j : Fin p.K) :
    Integrable (calendarBacklogStep rate rewards C_star C_h t j) mu := by
  exact (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowBacklogAt
    rate rewards C_star C_h j (t.val + 1)).sub
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowBacklogAt
      rate rewards C_star C_h j t.val)

private theorem integrable_calendarExpStep (j : Fin p.K) :
    Integrable (calendarExpStep rate rewards C_star C_h t j) mu := by
  exact (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
    rate rewards C_star C_h j (t.val + 1)).sub
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h j t.val)

private theorem integral_sourcePhase_sum (control0 : TimeControl p)
    {f : S → ℝ} (hf : Integrable f mu) :
    (∫ omega, f omega ∂mu) =
      ∑ i : Fin 6, ∫ omega in
        ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i,
          f omega ∂mu := by
  classical
  have h := integral_iUnion_fintype
    (fun i => ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 i)
    (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t)
    (fun i => hf.integrableOn)
  rw [sourcePhase_cover] at h
  simpa using h

private theorem integral_birth_phase (control0 : TimeControl p)
    {f : S → ℝ} (hf : Integrable f mu) :
    (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 2, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
          f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
  classical
  rw [sourcePhase_birth_iUnion]
  calc
    (∫ omega in ⋃ q : Fin (ConstructorDimensions.M p),
        ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
        f omega ∂mu) =
        ∑ q : Fin (ConstructorDimensions.M p),
          ∫ omega in ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
            f omega ∂mu :=
      integral_iUnion_fintype
        (fun q => ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
          rate rewards C_star C_h t control0
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
        (birth_events_pairwise rate rewards C_star C_h t)
        (fun q => hf.integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (integral_subtype_comap
        (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
          rate rewards C_star C_h t control0
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) f).symm

private theorem integral_branch_phase {f : S → ℝ} (hf : Integrable f mu) :
    (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 3, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          f z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
  classical
  let E : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) → Set S := fun a =>
    ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h a.1 t
      a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  have hd : Pairwise (fun a b => Disjoint (E a) (E b)) :=
    branch_events_pairwise rate rewards C_star C_h t control0
  have hm : ∀ a, MeasurableSet (E a) := fun a =>
    ReferenceFirstLiveBranchIntegralTransport.measurableSet_originalBranchEvent rate rewards C_star C_h
      a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  rw [sourcePhase_nonempty_iUnion, ← Set.iUnion_prod' E]
  calc
    (∫ omega in ⋃ a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1), E a,
        f omega ∂mu) = ∑ a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1),
          ∫ omega in E a, f omega ∂mu :=
      integral_iUnion_fintype hm hd (fun a => hf.integrableOn)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro v hv
      exact (ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 f).symm

private theorem integral_empty_phase {f : S → ℝ} (hf : Integrable f mu) :
    (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 4, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          f z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
  classical
  let E : Fin (ConstructorDimensions.M p) × Fin (t.val + 1) → Set S := fun a =>
    ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h a.1 t
      a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  have hd : Pairwise (fun a b => Disjoint (E a) (E b)) :=
    empty_events_pairwise rate rewards C_star C_h t control0
  have hm : ∀ a, MeasurableSet (E a) := fun a =>
    ReferenceFirstLiveSourcePhasePartition.measurableSet_originalEmptyEvent rate rewards C_star C_h
      a.1 t a.2.val (Nat.lt_succ_iff.mp a.2.isLt) control0
  rw [sourcePhase_empty_iUnion, ← Set.iUnion_prod' E]
  calc
    (∫ omega in ⋃ a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1), E a,
        f omega ∂mu) = ∑ a : Fin (ConstructorDimensions.M p) × Fin (t.val + 1),
          ∫ omega in E a, f omega ∂mu :=
      integral_iUnion_fintype hm hd (fun a => hf.integrableOn)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro v hv
      exact (ReferenceFirstLiveSourcePhasePartition.integral_originalEmpty
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 f).symm

private theorem integral_calendar_step_assemble {f : S → ℝ} (hf : Integrable f mu)
    {A : ℝ}
    (h0 : (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 0, f omega ∂mu) = 0)
    (h1 : (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 1, f omega ∂mu) = 0)
    (h5 : (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 5, f omega ∂mu) = 0)
    (hbirth : (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2, f omega ∂mu) = A) :
    (∫ omega, f omega ∂mu) = A +
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
            f z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
         (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
            f z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := by
  classical
  have hb := integral_branch_phase rate rewards C_star C_h t control0 hf
  have he := integral_empty_phase rate rewards C_star C_h t control0 hf
  have hs := integral_sourcePhase_sum rate rewards C_star C_h t control0 hf
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hs
  norm_num at hs
  rw [h0, h1, hbirth, hb, he, h5] at hs
  let B := ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
    ∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0,
      f z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let E := ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
    ∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0,
      f z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0
  have hcombine : B + E = ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          f z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
       (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          f z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
            v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := by
    dsimp [B, E]
    rw [← Finset.sum_add_distrib]
    congr 1
    funext q
    rw [← Finset.sum_add_distrib]
  calc
    _ = A + (B + E) := by
      calc
        _ = 0 + (0 + (A + (B + (E + 0)))) := by simpa [B, E] using hs
        _ = _ := by abel
    _ = _ := by rw [hcombine]

private theorem integral_exception_phase_zero (control0 : TimeControl p)
    {f : S → ℝ} (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5)
    (hz : ∀ omega, omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 0 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
      omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5 →
      f omega = 0) :
    (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i,
      f omega ∂mu) = 0 := by
  calc
    _ = ∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t i,
        (0 : ℝ) ∂mu :=
      setIntegral_congr_fun
        (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
          rate rewards C_star C_h t control0 i)
        (fun omega hω => by
          rcases hi with h0 | h1 | h5
          · subst i
            exact hz omega (Or.inl hω)
          · subst i
            exact hz omega (Or.inr (Or.inl hω))
          · subst i
            exact hz omega (Or.inr (Or.inr hω)))
    _ = 0 := by simp

/-- The potential change over one actual calendar step, assembled on the
original source law from the birth update and the continuing physical cells. -/
theorem integral_potential_calendar_step :
    (∫ omega : S,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
        (t.val + 1) omega -
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
        t.val omega ∂mu) =
    (∑ q : Fin (ConstructorDimensions.M p),
      ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
        RecordedWeightedDrift.weightedSquarePotential p.m
          (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
          (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z)
          ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
            (t.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
            t.val z.val.val
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
       (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
            (t.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
            t.val z.val.val
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  let f := calendarPotentialStep rate rewards C_star C_h t
  have hf : Integrable f mu := integrable_calendarPotentialStep rate rewards C_star C_h t
  have hz : ∀ omega, omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 0 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5 →
      f omega = 0 := fun omega hω =>
    calendarPotentialStep_zero_on_exception rate rewards C_star C_h t omega hω
  have h0 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (0 : Fin 6) (by decide) hz
  have h1 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (1 : Fin 6) (by decide) hz
  have h5 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (5 : Fin 6) (by decide) hz
  have hbirth := integral_birth_phase rate rewards C_star C_h t control0 hf
  have hbirthActual :
      (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 2, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
          RecordedWeightedDrift.weightedSquarePotential p.m
            (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
            (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z)
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
    rw [hbirth]
    apply Finset.sum_congr rfl
    intro q hq
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f, calendarPotentialStep]
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_birth_after
          rate rewards C_star C_h q t control0 z,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_birth_before
          rate rewards C_star C_h q t z]
    simp
  exact integral_calendar_step_assemble rate rewards C_star C_h t control0 hf
    h0 h1 h5 hbirthActual

/-- The actual per-arm normalized backlog change over one calendar step. -/
theorem integral_backlog_calendar_step (j : Fin p.K) :
    (∫ omega : S,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
        (t.val + 1) omega -
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
        t.val omega ∂mu) =
    (∑ q : Fin (ConstructorDimensions.M p),
      ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
        StoppedQueueBound.normalizedBacklog
          (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
          (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) j
          ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
            (t.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
            t.val z.val.val
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
       (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
            (t.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
            t.val z.val.val
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  let f := calendarBacklogStep rate rewards C_star C_h t j
  have hf : Integrable f mu := integrable_calendarBacklogStep rate rewards C_star C_h t j
  have hz : ∀ omega, omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 0 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5 →
      f omega = 0 := fun omega hω =>
    calendarBacklogStep_zero_on_exception rate rewards C_star C_h t j omega hω
  have h0 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (0 : Fin 6) (by decide) hz
  have h1 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (1 : Fin 6) (by decide) hz
  have h5 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (5 : Fin 6) (by decide) hz
  have hbirth := integral_birth_phase rate rewards C_star C_h t control0 hf
  have hbirthActual :
      (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 2, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
          StoppedQueueBound.normalizedBacklog
            (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
            (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) j
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
    rw [hbirth]
    apply Finset.sum_congr rfl
    intro q hq
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f, calendarBacklogStep]
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_after
          rate rewards C_star C_h q t control0 z j,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_before
          rate rewards C_star C_h q t z j]
    simp
  exact integral_calendar_step_assemble rate rewards C_star C_h t control0 hf
    h0 h1 h5 hbirthActual

/-- The actual exponential backlog increment over one calendar step. -/
theorem integral_exp_calendar_step (j : Fin p.K) :
    (∫ omega : S,
      Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          (t.val + 1) omega) -
      Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          t.val omega) ∂mu) =
    (∑ q : Fin (ConstructorDimensions.M p),
      ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
        (Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
          StoppedQueueBound.normalizedBacklog
            (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
            (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) j) - 1)
          ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) +
    (∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
              (t.val + 1) z.val.val) -
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
              t.val z.val.val)
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
       (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
              (t.val + 1) z.val.val) -
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
              t.val z.val.val)
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  let f := calendarExpStep rate rewards C_star C_h t j
  have hf : Integrable f mu := integrable_calendarExpStep rate rewards C_star C_h t j
  have hz : ∀ omega, omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 0 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 1 ∨
    omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 5 →
      f omega = 0 := fun omega hω =>
    calendarExpStep_zero_on_exception rate rewards C_star C_h t j omega hω
  have h0 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (0 : Fin 6) (by decide) hz
  have h1 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (1 : Fin 6) (by decide) hz
  have h5 := integral_exception_phase_zero rate rewards C_star C_h t control0
    (5 : Fin 6) (by decide) hz
  have hbirth := integral_birth_phase rate rewards C_star C_h t control0 hf
  have hbirthActual :
      (∫ omega in ReferenceFirstLiveSourcePhasePartition.sourcePhase
        rate rewards C_star C_h t 2, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t),
          (Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            StoppedQueueBound.normalizedBacklog
              (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
              (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z) j) - 1)
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := by
    rw [hbirth]
    apply Finset.sum_congr rfl
    intro q hq
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f, calendarExpStep]
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_after
          rate rewards C_star C_h q t control0 z j,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_before
          rate rewards C_star C_h q t z j]
    simp
  exact integral_calendar_step_assemble rate rewards C_star C_h t control0 hf
    h0 h1 h5 hbirthActual

private theorem fin_sum_succ_sub (n : ℕ) : ∀ f : ℕ → ℝ,
    (∑ t : Fin n, (f (t.val + 1) - f t.val)) = f n - f 0 := by
  induction n with
  | zero => intro f; simp
  | succ n ih =>
      intro f
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      have htail :
          (∑ t : Fin n, (f (t.val + 2) - f (t.val + 1))) = f (n + 1) - f 1 := by
        simpa [Nat.add_assoc] using ih (fun k => f (k + 1))
      rw [htail]
      ring

private theorem integral_calendar_telescope {g : ℕ → S → ℝ}
    (hg : ∀ n, Integrable (g n) mu) :
    (∑ t : Fin p.T,
      ∫ omega, g (t.val + 1) omega - g t.val omega ∂mu) =
      (∫ omega, g p.T omega ∂mu) - (∫ omega, g 0 omega ∂mu) := by
  calc
    _ = ∑ t : Fin p.T,
        ((∫ omega, g (t.val + 1) omega ∂mu) - (∫ omega, g t.val omega ∂mu)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact integral_sub (hg (t.val + 1)) (hg t.val)
    _ = _ := fin_sum_succ_sub p.T (fun n => ∫ omega, g n omega ∂mu)

private theorem firstWindowPotentialAt_zero (omega : S) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h 0 omega = 0 := by
  simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt,
    ReferenceFirstLiveCalendarPrefixReadout.queueParameters, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState,
    RecordedWeightedDrift.weightedSquarePotential, StoppedQueueBound.normalizedBacklog]

private theorem firstWindowBacklogAt_zero (j : Fin p.K) (omega : S) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j 0 omega = 0 := by
  simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt,
    ReferenceFirstLiveCalendarPrefixReadout.queueParameters, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

private theorem integral_potential_step_sum :
    (∑ t : Fin p.T, ∫ omega : S,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
          (t.val + 1) omega -
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
          t.val omega ∂mu) =
      ∫ omega : S, ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
        p.T omega ∂mu := by
  let g := fun n omega => ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
    rate rewards C_star C_h n omega
  have hg : ∀ n, Integrable (g n) mu := fun n =>
    ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt rate rewards C_star C_h n
  have h := integral_calendar_telescope hg
  have hzero : (∫ omega, g 0 omega ∂mu) = 0 := by
    calc
      _ = ∫ omega, (0 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact firstWindowPotentialAt_zero rate rewards C_star C_h omega
      _ = 0 := by simp
  rw [hzero] at h
  simpa [g] using h

private theorem integral_backlog_step_sum (j : Fin p.K) :
    (∑ t : Fin p.T, ∫ omega : S,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          (t.val + 1) omega -
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          t.val omega ∂mu) =
      ∫ omega : S, ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
        p.T omega ∂mu := by
  let g := fun n omega => ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rate rewards C_star C_h j n omega
  have hg : ∀ n, Integrable (g n) mu := fun n =>
    ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowBacklogAt rate rewards C_star C_h j n
  have h := integral_calendar_telescope hg
  have hzero : (∫ omega, g 0 omega ∂mu) = 0 := by
    calc
      _ = ∫ omega, (0 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact firstWindowBacklogAt_zero rate rewards C_star C_h j omega
      _ = 0 := by simp
  rw [hzero] at h
  simpa [g] using h

private theorem integral_exp_step_sum (j : Fin p.K) :
    (∑ t : Fin p.T, ∫ omega : S,
      Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          (t.val + 1) omega) -
      Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          t.val omega) ∂mu) =
      (∫ omega : S, Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j
          p.T omega) ∂mu) - 1 := by
  let g := fun n omega => Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j n omega)
  have hg : ∀ n, Integrable (g n) mu := fun n =>
    ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt rate rewards C_star C_h j n
  have h := integral_calendar_telescope hg
  have hzero : (∫ omega, g 0 omega ∂mu) = 1 := by
    calc
      _ = ∫ omega, (1 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        simp [g, firstWindowBacklogAt_zero rate rewards C_star C_h j omega]
      _ = 1 := by simp
  rw [hzero] at h
  simpa [g] using h

theorem integral_potential_calendar_telescope :
    (∫ omega : S, ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h p.T omega ∂mu) =
    ∑ u : Fin p.T,
      ((∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h u
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u),
          RecordedWeightedDrift.weightedSquarePotential p.m
            (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
            (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q u control0 z)
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h u
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u)) +
       ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (u.val + 1),
        ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h (u.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h u.val z.val.val
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
         (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h (u.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h u.val z.val.val
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  calc
    _ = ∑ u : Fin p.T, ∫ omega : S,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h (u.val + 1) omega -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h u.val omega ∂mu :=
      (integral_potential_step_sum rate rewards C_star C_h).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_potential_calendar_step rate rewards C_star C_h u control0

theorem integral_backlog_calendar_telescope (j : Fin p.K) :
    (∫ omega : S, ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega ∂mu) =
    ∑ u : Fin p.T,
      ((∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h u
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u),
          StoppedQueueBound.normalizedBacklog (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
            (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q u control0 z) j
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h u
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u)) +
       ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (u.val + 1),
        ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val z.val.val
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
         (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) z.val.val -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val z.val.val
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  calc
    _ = ∑ u : Fin p.T, ∫ omega : S,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) omega -
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val omega ∂mu :=
      (integral_backlog_step_sum rate rewards C_star C_h j).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_backlog_calendar_step rate rewards C_star C_h u control0 j

theorem integral_exp_calendar_telescope (j : Fin p.K) :
    ((∫ omega : S, Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j p.T omega) ∂mu) - 1) =
    ∑ u : Fin p.T,
      ((∑ q : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h u
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u),
          (Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            StoppedQueueBound.normalizedBacklog (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
              (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q u control0 z) j) - 1)
            ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h u
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q u)) +
       ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (u.val + 1),
        ((∫ z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) z.val.val) -
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val z.val.val)
            ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
         (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q u
            v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) z.val.val) -
          Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
            ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val z.val.val)
            ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q u
              v.val (Nat.lt_succ_iff.mp v.isLt) control0))) := by
  calc
    _ = ∑ u : Fin p.T, ∫ omega : S,
        Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (u.val + 1) omega) -
        Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j u.val omega) ∂mu :=
      (integral_exp_step_sum rate rewards C_star C_h j).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_exp_calendar_step rate rewards C_star C_h u control0 j

end Bandits.Support.ReferenceFirstLiveCalendarIntegralAssembly

end
