/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseWaiting
public import Bandits.Support.ReferenceFirstLiveInspectedFastCollision

import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic.Positivity

/-!
# The stopped first-release pending-masked sentinel charge

This module combines the existing guarded fast-collision conditional bounds
over a finite least-pending partition on the same source-prefix field.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveStoppedReleaseSentinelBound

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

abbrev Source (p₀ : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p₀

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "P" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h
local notation "ω" =>
  ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
    rate rewards C_star C_h control0
local notation "Z" =>
  ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
    rate rewards C_star C_h
local notation "Hfield" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The actual source fast-collision charge masked by the nonempty stopped
pending set at the same physical round. -/
def pendingMaskedSentinel (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) : ℝ :=
  (if (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z).Nonempty then (1 : ℝ) else 0) *
    ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
      rate rewards C_star C_h t z

private theorem pending_nonempty_measurable (t : Fin p.T) :
    MeasurableSet[Hfield (t.val + 1)]
      {z : Source p | (P t.val z).Nonempty} := by
  change MeasurableSet[Hfield (t.val + 1)]
    {z : Source p | ∃ i : Fin (p.m - 1), i ∈ P t.val z}
  have hset : {z : Source p | ∃ i : Fin (p.m - 1), i ∈ P t.val z} =
      {z : Source p | ∃ i : Fin (p.m - 1), i ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rate rewards C_star C_h z t} := by
    ext z
    simp only [Set.mem_ofPred_eq,
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin]
  rw [hset]
  rw [show {z : Source p | ∃ i : Fin (p.m - 1), i ∈
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
        rate rewards C_star C_h z t} =
      ⋃ i : Fin (p.m - 1), {z : Source p | i ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rate rewards C_star C_h z t} by
      ext z
      simp]
  exact MeasurableSet.iUnion fun i =>
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_pending_adapted
      rate rewards C_star C_h control0 t i

private theorem source_prefix_le_borel (t : Fin p.T) :
    Hfield (t.val + 1) ≤ (inferInstance : MeasurableSpace (Source p)) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  exact (ReferenceSourceCurrentControlFreshness.measurable_c_t (p := p) control0 t).comap_le

theorem pendingMaskedSentinel_measurable (t : Fin p.T) :
    Measurable (pendingMaskedSentinel rate rewards C_star C_h control0 t) := by
  have hmask : Measurable (fun z : Source p =>
      if (P t.val z).Nonempty then (1 : ℝ) else 0) := by
    have hset := pending_nonempty_measurable rate rewards C_star C_h control0 t
    have hind : Measurable[Hfield (t.val + 1)]
        ({z : Source p | (P t.val z).Nonempty}.indicator
          (fun _ : Source p => (1 : ℝ))) := measurable_const.indicator hset
    convert hind.mono (source_prefix_le_borel control0 t) le_rfl using 1
    funext z
    simp [Set.indicator]
  exact hmask.mul
    (ReferenceFirstLiveInspectedFastCollision.sourceFastCollisionCharge_measurable
      rate rewards C_star C_h t)

theorem pendingMaskedSentinel_bounds (t : Fin p.T) (z : Source p) :
    0 ≤ pendingMaskedSentinel rate rewards C_star C_h control0 t z ∧
      pendingMaskedSentinel rate rewards C_star C_h control0 t z ≤ 1 := by
  by_cases hpending : (P t.val z).Nonempty
  · simpa [pendingMaskedSentinel, hpending] using
      (ReferenceFirstLiveInspectedFastCollision.sourceFastCollisionCharge_bounds
        rate rewards C_star C_h t z)
  · simp [pendingMaskedSentinel, hpending]

theorem pendingMaskedSentinel_integrable (t : Fin p.T) :
    Integrable (pendingMaskedSentinel rate rewards C_star C_h control0 t) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply (integrable_const (1 : ℝ)).mono'
    (pendingMaskedSentinel_measurable rate rewards C_star C_h control0 t).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pendingMaskedSentinel_bounds rate rewards C_star C_h control0 t z).1]
  exact (pendingMaskedSentinel_bounds rate rewards C_star C_h control0 t z).2

theorem pendingMaskedAuxiliaryWeight_measurable (t : Fin p.T) :
    Measurable[Hfield (t.val + 1)] (fun z : Source p =>
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z) := by
  have hmask : Measurable[Hfield (t.val + 1)] (fun z : Source p =>
      if (P t.val z).Nonempty then (1 : ℝ) else 0) := by
    have hset := pending_nonempty_measurable rate rewards C_star C_h control0 t
    have hind : Measurable[Hfield (t.val + 1)]
        ({z : Source p | (P t.val z).Nonempty}.indicator
          (fun _ : Source p => (1 : ℝ))) := measurable_const.indicator hset
    convert hind using 1
    funext z
    simp [Set.indicator]
  have hweight :=
    (ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_predictable
      rate rewards C_star C_h control0 t.val t.isLt).measurable
  exact hmask.mul hweight

theorem pendingMaskedAuxiliaryWeight_bounds (t : Fin p.T) (z : Source p) :
    0 ≤ (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z ∧
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z ≤ 1 := by
  by_cases hpending : (P t.val z).Nonempty
  · simpa [hpending] using
      (ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_bounds
        rate rewards C_star C_h control0 t.val z)
  · simp [hpending]

theorem pendingMaskedAuxiliaryWeight_integrable (t : Fin p.T) :
    Integrable (fun z : Source p =>
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply (integrable_const (1 : ℝ)).mono'
    ((pendingMaskedAuxiliaryWeight_measurable rate rewards C_star C_h control0 t).mono
      (source_prefix_le_borel control0 t) le_rfl).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pendingMaskedAuxiliaryWeight_bounds rate rewards C_star C_h control0 t z).1]
  exact (pendingMaskedAuxiliaryWeight_bounds rate rewards C_star C_h control0 t z).2

private abbrev GuardIndex (t : Fin p.T) :=
  Fin (p.m - 1) × (Fin (M p) ×
    Fin (t.val + 1))

private def leastPendingSet (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1)) : Set (Source p) :=
  {z | i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z ∧
    ∀ j : Fin (p.m - 1), j < i →
      j ∉ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z}

private def leastPendingGuardSet
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (q : Fin (M p))
    (v : Fin (t.val + 1)) : Set (Source p) :=
  leastPendingSet rate rewards C_star C_h t i ∩
    ReferenceFirstLiveSourceStoppedReleaseService.g
      rate rewards C_star C_h control0 i t q v

private def guardedChargeTerm
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : GuardIndex t) (z : Source p) : ℝ :=
  (leastPendingSet rate rewards C_star C_h t a.1).indicator
    (fun z =>
      ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator
        rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
        (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val z *
      ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
        rate rewards C_star C_h t z) z

private def guardedWeightTerm
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : GuardIndex t) (z : Source p) : ℝ :=
  (leastPendingSet rate rewards C_star C_h t a.1).indicator
    (fun z =>
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
        (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val z) z

private theorem pendingMember_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1)]
      {z : Source p | i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z} := by
  rw [show {z : Source p | i ∈
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z} =
      {z : Source p | i ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rate rewards C_star C_h z t} by
      ext z
      simp only [Set.mem_ofPred_eq,
        ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin]]
  exact ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_pending_adapted
    rate rewards C_star C_h control0 t i

private theorem leastPendingSet_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1)] (leastPendingSet rate rewards C_star C_h t i) := by
  classical
  have hprevSet :
      {z : Source p | ∀ j : Fin (p.m - 1), j < i →
        j ∉ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
          rate rewards C_star C_h t.val z} =
      ⋂ j : Fin (p.m - 1),
        if j < i then
          {z : Source p | j ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
            rate rewards C_star C_h t.val z}ᶜ
        else Set.univ := by
    ext z
    simp [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
  rw [leastPendingSet, show {z : Source p | _ ∧ _} =
      {z : Source p | i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z} ∩
      {z : Source p | ∀ j : Fin (p.m - 1), j < i →
        j ∉ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
          rate rewards C_star C_h t.val z} by
      ext z
      simp]
  exact (pendingMember_measurable rate rewards C_star C_h control0 t i).inter (by
    rw [hprevSet]
    exact MeasurableSet.iInter fun j => by
      by_cases hji : j < i
      · simpa [hji] using
          (pendingMember_measurable rate rewards C_star C_h control0 t j).compl
      · simp [hji])

private theorem leastPendingSet_unique
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p)
    (i j : Fin (p.m - 1))
    (hi : z ∈ leastPendingSet rate rewards C_star C_h t i)
    (hj : z ∈ leastPendingSet rate rewards C_star C_h t j) : i = j := by
  change i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z ∧
    (∀ k : Fin (p.m - 1), k < i → k ∉
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z) at hi
  change j ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z ∧
    (∀ k : Fin (p.m - 1), k < j → k ∉
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z) at hj
  have hij : i ≤ j := by
    by_contra hnot
    exact hi.2 j (lt_of_not_ge hnot) hj.1
  have hji : j ≤ i := by
    by_contra hnot
    exact hj.2 i (lt_of_not_ge hnot) hi.1
  exact le_antisymm hij hji

private theorem existsUnique_leastPending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p)
    (hpending : (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z).Nonempty) :
    ∃! i : Fin (p.m - 1), z ∈ leastPendingSet rate rewards C_star C_h t i := by
  classical
  let i := (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h t.val z).min' hpending
  have himem : i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z := Finset.min'_mem _ hpending
  have hleast : ∀ j : Fin (p.m - 1), j < i → j ∉
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z := by
    intro j hji hjmem
    have hmin := Finset.min'_le
      (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z) j hjmem
    exact (not_le_of_gt hji) hmin
  refine ⟨i, ?_, ?_⟩
  · exact ⟨himem, hleast⟩
  · intro j hj
    change j ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z ∧
      (∀ k : Fin (p.m - 1), k < j → k ∉
        ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
          rate rewards C_star C_h t.val z) at hj
    have hij : i ≤ j := by
      by_contra hnot
      exact hleast j (lt_of_not_ge hnot) hj.1
    have hji : j ≤ i := by
      by_contra hnot
      exact hj.2 i (lt_of_not_ge hnot) himem
    exact le_antisymm hji hij

private theorem leastPendingGuard_coverage_unique
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p)
    (hpending : (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z).Nonempty) :
    ∃! a : GuardIndex t,
      z ∈ leastPendingGuardSet rate rewards C_star C_h control0 t a.1 a.2.1 a.2.2 := by
  classical
  obtain ⟨i, hi, huni⟩ := existsUnique_leastPending
    rate rewards C_star C_h t z hpending
  rcases hi with ⟨hipending, hleast⟩
  obtain ⟨⟨q, v⟩, hguard, _hguardUnique⟩ :=
    ReferenceFirstLiveSourceStoppedReleaseService.pending_guard_coverage
      rate rewards C_star C_h control0 i t z hipending
  refine ⟨(i, (q, v)), ?_, ?_⟩
  · change z ∈ leastPendingSet rate rewards C_star C_h t i ∧
      z ∈ ReferenceFirstLiveSourceStoppedReleaseService.g
        rate rewards C_star C_h control0 i t q v
    exact ⟨⟨hipending, hleast⟩, hguard⟩
  · intro a ha
    rcases a with ⟨j, q', v'⟩
    change z ∈ leastPendingSet rate rewards C_star C_h t j ∧
      z ∈ ReferenceFirstLiveSourceStoppedReleaseService.g
        rate rewards C_star C_h control0 j t q' v' at ha
    rcases ha with ⟨hj, hg'⟩
    have hji : j = i := huni j hj
    subst j
    have hqv := ReferenceFirstLiveSourceStoppedReleaseService.guard_strata_exclusive
      rate rewards C_star C_h control0 i i t q q' v v' z hguard hg'
    rcases hqv with ⟨hq, hv⟩
    subst q'
    subst v'
    rfl

private theorem leastPendingGuard_absent_of_empty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p)
    (hpending : ¬ (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z).Nonempty)
    (a : GuardIndex t) :
    z ∉ leastPendingGuardSet rate rewards C_star C_h control0 t a.1 a.2.1 a.2.2 := by
  intro ha
  change z ∈ leastPendingSet rate rewards C_star C_h t a.1 ∧
    z ∈ ReferenceFirstLiveSourceStoppedReleaseService.g
      rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2 at ha
  have hleast := ha.1
  change a.1 ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z ∧ _ at hleast
  exact hpending ⟨a.1, hleast.1⟩

private theorem guardedChargeTerm_eq_coveredIndicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : GuardIndex t) (z : Source p) :
    guardedChargeTerm rate rewards C_star C_h control0 t a z =
      (leastPendingGuardSet rate rewards C_star C_h control0 t
        a.1 a.2.1 a.2.2).indicator
        (fun _ : Source p =>
          ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
            rate rewards C_star C_h t z) z := by
  classical
  let L := leastPendingSet rate rewards C_star C_h t a.1
  let G := ReferenceFirstLiveSourceStoppedReleaseService.g
    rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2
  by_cases hL : z ∈ L
  · by_cases hG : z ∈ G
    · have hG' : z ∈
          ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
            rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
            (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val := by
        change z ∈
          ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
            rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
            (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val at hG
        exact hG
      simp [guardedChargeTerm, leastPendingGuardSet, L, hL, hG',
        ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        ReferenceFirstLiveSourceStoppedReleaseService.g,
        ReferenceFirstLiveInspectedCoefficients.guardedEvent]
    · have hG' : z ∉
          ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
            rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
            (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val := by
        intro hz
        apply hG
        exact hz
      simp [guardedChargeTerm, leastPendingGuardSet, L, hL, hG',
        ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        ReferenceFirstLiveSourceStoppedReleaseService.g,
        ReferenceFirstLiveInspectedCoefficients.guardedEvent]
  · simp [guardedChargeTerm, leastPendingGuardSet, L, hL,
      ReferenceFirstLiveSourceStoppedReleaseService.g,
      ReferenceFirstLiveInspectedCoefficients.guardedEvent]

private theorem guardedTerm_condExp_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : GuardIndex t) :
    μ[guardedChargeTerm rate rewards C_star C_h control0 t a |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] ≤ᵐ[μ]
      guardedWeightTerm rate rewards C_star C_h control0 t a := by
  let L := leastPendingSet rate rewards C_star C_h t a.1
  let guardCharge := fun z : Source p =>
    ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator
      rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
      (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val z *
      ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
        rate rewards C_star C_h t z
  let guardWeight := fun z : Source p =>
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
      rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
      (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val z
  have hL := leastPendingSet_measurable rate rewards C_star C_h control0 t a.1
  have hint : Integrable guardCharge μ := by
    exact ReferenceFirstLiveInspectedFastCollision.guardedFastCollisionCharge_integrable
      rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
      (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val
  have hpull := condExp_indicator hint hL
  have hguard := ReferenceFirstLiveInspectedFastCollision.guardedFastCollisionCharge_prefix_condExp_le
    rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
    (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val
  change μ[L.indicator guardCharge |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] ≤ᵐ[μ]
    L.indicator guardWeight
  filter_upwards [hpull, hguard] with z hpull hguard
  rw [hpull]
  by_cases hz : z ∈ L
  · have hz' : z ∈ leastPendingSet rate rewards C_star C_h t a.1 := by
      simpa [L] using hz
    simp only [Set.indicator_of_mem hz']
    simp only [Set.indicator_of_mem hz]
    simpa [guardCharge, guardWeight] using hguard
  · have hz' : z ∉ leastPendingSet rate rewards C_star C_h t a.1 := by
      simpa [L] using hz
    simp only [Set.indicator_of_notMem hz']
    simp [Set.indicator_of_notMem hz]

private theorem guardedChargeTerm_sum_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) :
    (∑ a : GuardIndex t, guardedChargeTerm rate rewards C_star C_h control0 t a z) =
      pendingMaskedSentinel rate rewards C_star C_h control0 t z := by
  classical
  let pending := ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h t.val z
  by_cases hpending : pending.Nonempty
  · obtain ⟨a, ha, huniq⟩ := leastPendingGuard_coverage_unique
      rate rewards C_star C_h control0 t z (by simpa [pending] using hpending)
    have hmain : guardedChargeTerm rate rewards C_star C_h control0 t a z =
        ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
          rate rewards C_star C_h t z := by
      rw [guardedChargeTerm_eq_coveredIndicator]
      simp only [Set.indicator_of_mem ha]
    have hzero : ∀ b ∈ (Finset.univ : Finset (GuardIndex t)), b ≠ a →
        guardedChargeTerm rate rewards C_star C_h control0 t b z = 0 := by
      intro b _ hba
      have hnot : z ∉ leastPendingGuardSet rate rewards C_star C_h control0 t
          b.1 b.2.1 b.2.2 := by
        intro hb
        exact hba (huniq b hb)
      rw [guardedChargeTerm_eq_coveredIndicator]
      exact Set.indicator_of_notMem hnot _
    calc
      (∑ b : GuardIndex t, guardedChargeTerm rate rewards C_star C_h control0 t b z) =
          guardedChargeTerm rate rewards C_star C_h control0 t a z :=
        Finset.sum_eq_single_of_mem a (Finset.mem_univ _) hzero
      _ = ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
          rate rewards C_star C_h t z := hmain
      _ = pendingMaskedSentinel rate rewards C_star C_h control0 t z := by
          simp [pendingMaskedSentinel, pending, hpending]
  · have hzero : ∀ a : GuardIndex t,
        guardedChargeTerm rate rewards C_star C_h control0 t a z = 0 := by
      intro a
      have hnot := leastPendingGuard_absent_of_empty
        rate rewards C_star C_h control0 t z (by simpa [pending] using hpending) a
      rw [guardedChargeTerm_eq_coveredIndicator]
      exact Set.indicator_of_notMem hnot _
    have hpendingEmpty : pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpending
    rw [Finset.sum_eq_zero fun a _ => hzero a]
    simp [pendingMaskedSentinel, pending, hpendingEmpty]

private theorem guardedWeightTerm_sum_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) :
    (∑ a : GuardIndex t, guardedWeightTerm rate rewards C_star C_h control0 t a z) =
      (if (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h t.val z).Nonempty then (1 : ℝ) else 0) *
        ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
          rate rewards C_star C_h control0 t.val z := by
  classical
  let pending := ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h t.val z
  have hinner (i : Fin (p.m - 1)) :
      (∑ q : Fin (M p), ∑ v : Fin (t.val + 1),
        guardedWeightTerm rate rewards C_star C_h control0 t (i, (q, v)) z) =
        if z ∈ leastPendingSet rate rewards C_star C_h t i then
          ReferenceFirstLiveSourceStoppedReleaseService.u
            rate rewards C_star C_h control0 i t z else 0 := by
    by_cases hi : z ∈ leastPendingSet rate rewards C_star C_h t i
    · simp [hi, guardedWeightTerm,
        ReferenceFirstLiveSourceStoppedReleaseService.u]
    · simp [guardedWeightTerm, hi]
  calc
    (∑ a : GuardIndex t, guardedWeightTerm rate rewards C_star C_h control0 t a z) =
        ∑ i : Fin (p.m - 1), ∑ q : Fin (M p), ∑ v : Fin (t.val + 1),
          guardedWeightTerm rate rewards C_star C_h control0 t (i, (q, v)) z := by
            simp only [Fintype.sum_prod_type]
    _ = ∑ i : Fin (p.m - 1),
          if z ∈ leastPendingSet rate rewards C_star C_h t i then
            ReferenceFirstLiveSourceStoppedReleaseService.u
              rate rewards C_star C_h control0 i t z else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            exact hinner i
    _ = (if pending.Nonempty then (1 : ℝ) else 0) *
          ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
            rate rewards C_star C_h control0 t.val z := by
            by_cases hpending : pending.Nonempty
            · obtain ⟨i, hi, huniq⟩ := existsUnique_leastPending
                rate rewards C_star C_h t z (by simpa [pending] using hpending)
              have hi' : i ∈ pending := by
                change i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
                  rate rewards C_star C_h t.val z ∧ _ at hi
                exact hi.1
              have haux := ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_eq_at_pending
                rate rewards C_star C_h control0 i t z hi'
              rcases haux with ⟨q, v, hguard, h_o, h_branch⟩
              have hfin := ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_fin
                rate rewards C_star C_h control0 t z
              have hbranchSum :
                  (∑ q' : Fin (M p), ∑ v' : Fin (t.val + 1),
                    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
                      rate rewards C_star C_h control0 i t q' v'.val
                      (Nat.le_of_lt_succ v'.isLt) v'.val z) =
                    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
                      rate rewards C_star C_h control0 i t q v.val
                      (Nat.le_of_lt_succ v.isLt) v.val z := by
                change ReferenceFirstLiveSourceStoppedReleaseService.u
                  rate rewards C_star C_h control0 i t z = _
                exact h_branch
              have hbranchOmega :
                  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
                    rate rewards C_star C_h control0 i t q v.val
                    (Nat.le_of_lt_succ v.isLt) v.val z =
                  ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
                    rate rewards C_star C_h control0 t.val z := by
                calc
                  _ = ReferenceFirstLiveSourceStoppedReleaseService.u
                      rate rewards C_star C_h control0 i t z := h_branch.symm
                  _ = ReferenceFirstLiveSourceStoppedReleaseService.o
                      rate rewards C_star C_h control0 t z := h_o.symm
                  _ = ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
                      rate rewards C_star C_h control0 t.val z := hfin.symm
              have h_u_omega :
                  ReferenceFirstLiveSourceStoppedReleaseService.u
                    rate rewards C_star C_h control0 i t z =
                    ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
                      rate rewards C_star C_h control0 t.val z :=
                h_branch.trans hbranchOmega
              have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (p.m - 1))), j ≠ i →
                  (if z ∈ leastPendingSet rate rewards C_star C_h t j then
                    ReferenceFirstLiveSourceStoppedReleaseService.u
                      rate rewards C_star C_h control0 j t z else 0) = 0 := by
                intro j _ hji
                by_cases hj : z ∈ leastPendingSet rate rewards C_star C_h t j
                · have hEq : j = i := huniq j hj
                  exact (hji hEq).elim
                · simp [hj]
              rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) hzero]
              simpa [hi, hpending] using h_u_omega
            · have hzero : ∀ i : Fin (p.m - 1),
                  z ∉ leastPendingSet rate rewards C_star C_h t i := by
                intro i hi
                have hmem : i ∈ pending := by
                  change i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
                    rate rewards C_star C_h t.val z ∧ _ at hi
                  exact hi.1
                exact hpending ⟨i, hmem⟩
              have hpendingEmpty : pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpending
              rw [Finset.sum_eq_zero fun i _ => by
                by_cases hi : z ∈ leastPendingSet rate rewards C_star C_h t i
                · exact (hzero i hi).elim
                · simp [hi]]
              simp [hpendingEmpty]

/-- The stopped pending mask can be pulled through conditional expectation on
the same source-prefix field, by summing the guarded estimates over the
finite least-pending partition. -/
theorem stoppedPendingMaskedSentinel_condExp_le (t : Fin p.T) :
    μ[pendingMaskedSentinel rate rewards C_star C_h control0 t |
        Hfield (t.val + 1)] ≤ᵐ[μ]
      (fun z : Source p =>
        (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z) := by
  classical
  let f : GuardIndex t → Source p → ℝ := fun a z =>
    guardedChargeTerm rate rewards C_star C_h control0 t a z
  let g : GuardIndex t → Source p → ℝ := fun a z =>
    guardedWeightTerm rate rewards C_star C_h control0 t a z
  have hf : ∀ a : GuardIndex t, Integrable (f a) μ := by
    intro a
    have hLmeas := leastPendingSet_measurable
      rate rewards C_star C_h control0 t a.1
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hLmeas
    rcases hLmeas with ⟨S, hS, hpre⟩
    have hLambient : MeasurableSet (leastPendingSet rate rewards C_star C_h t a.1) := by
      rw [← hpre]
      exact hS.preimage
        (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val)
    have hguard :=
      ReferenceFirstLiveInspectedFastCollision.guardedFastCollisionCharge_integrable
        rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
        (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val
    change Integrable
      ((leastPendingSet rate rewards C_star C_h t a.1).indicator
        (fun z : Source p =>
          ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator
            rate rewards C_star C_h control0 a.1 t a.2.1 a.2.2.val
            (Nat.le_of_lt_succ a.2.2.isLt) a.2.2.val z *
          ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
            rate rewards C_star C_h t z)) μ
    exact (integrable_indicator_iff hLambient).2 hguard.integrableOn
  have hterm : ∀ a : GuardIndex t,
      μ[f a | Hfield (t.val + 1)] ≤ᵐ[μ] fun z => g a z := by
    intro a
    exact guardedTerm_condExp_le rate rewards C_star C_h control0 t a
  have hcondSum :
      μ[(∑ a : GuardIndex t, f a) | Hfield (t.val + 1)] =ᵐ[μ]
        (fun z : Source p => ∑ a : GuardIndex t,
          μ[f a | Hfield (t.val + 1)] z) := by
    have hraw := condExp_finsetSum
      (s := (Finset.univ : Finset (GuardIndex t))) (f := f)
      (fun a _ => hf a) (Hfield (t.val + 1))
    filter_upwards [hraw] with z hz
    simpa only [Finset.sum_apply] using hz
  have hsumLe :
      (fun z : Source p => ∑ a : GuardIndex t,
        μ[f a | Hfield (t.val + 1)] z) ≤ᵐ[μ]
      (fun z : Source p => ∑ a : GuardIndex t, g a z) := by
    have hall := (Finset.univ : Finset (GuardIndex t)).eventually_all.mpr
      (fun a _ => hterm a)
    filter_upwards [hall] with z hz
    exact Finset.sum_le_sum (fun a ha => hz a ha)
  have hchargeFunction :
      (∑ a : GuardIndex t, f a) =
        pendingMaskedSentinel rate rewards C_star C_h control0 t := by
    funext z
    simpa only [Finset.sum_apply] using
      (guardedChargeTerm_sum_eq rate rewards C_star C_h control0 t z)
  have hweightFunction :
      (∑ a : GuardIndex t, g a) =
        (fun z : Source p =>
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z) := by
    funext z
    simpa only [Finset.sum_apply] using
      (guardedWeightTerm_sum_eq rate rewards C_star C_h control0 t z)
  have hceStart :
      μ[pendingMaskedSentinel rate rewards C_star C_h control0 t |
          Hfield (t.val + 1)] =ᵐ[μ]
        μ[(∑ a : GuardIndex t, f a) | Hfield (t.val + 1)] :=
    condExp_congr_ae (m := Hfield (t.val + 1))
      (ae_of_all μ fun z => congrFun hchargeFunction.symm z)
  filter_upwards [hceStart, hcondSum, hsumLe,
    ae_of_all μ fun z => congrFun hweightFunction z] with z hstart hcond hle hweight
  calc
    μ[pendingMaskedSentinel rate rewards C_star C_h control0 t |
        Hfield (t.val + 1)] z =
      ∑ a : GuardIndex t, μ[f a | Hfield (t.val + 1)] z := by
        rw [hstart]
        exact hcond
    _ ≤ ∑ a : GuardIndex t, g a z := hle
    _ = (if (P t.val z).Nonempty then (1 : ℝ) else 0) * ω t.val z := by
      simpa only [Finset.sum_apply] using hweight

end Bandits.Support.ReferenceFirstLiveStoppedReleaseSentinelBound

end
