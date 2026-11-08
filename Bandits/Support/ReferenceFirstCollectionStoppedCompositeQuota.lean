/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpCountOrAwaitedFailure
public import Bandits.Support.ReferenceFirstCollectionUpDetectedQueueMask
public import Bandits.Support.ReferenceFirstCollectionStoppedOldDownQuota

import Lean.Elab.Tactic.Omega

/-!
# Inclusive stopped composite quota for first-collection service

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-109,139-157`.

The two stage counts use the same actual UP-detected pending mask and the same
original physical calendar. Both retain the detecting round. Their disjoint
union is the stopped service count, which also bounds every prefix of the
range-based service counter.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionStoppedCompositeQuota

variable {p : ConstructorDimensions.Parameters}

/-- Literal FORMED-stage positive readouts stopped by the actual UP-detected
mask, on the whole original physical calendar. -/
def stoppedFormedUpTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z ∧
    z ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Literal OLD-stage positive readouts stopped by the same actual
UP-detected mask, on the whole original physical calendar. -/
def stoppedOldDownTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z ∧
    z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Literal stopped service dates on the original physical calendar. -/
def stoppedServiceTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val z = true

/-- Every actual stopped FORMED-UP count, including its detecting round, is
at most twice the decoder quota. -/
theorem actual_first_collection_stopped_formed_up_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    (stoppedFormedUpTests (p := p) rate rewards C_star C_h i z).card ≤
      2 * AffineBatchDecoder.quota p := by
  classical
  let tests := stoppedFormedUpTests (p := p) rate rewards C_star C_h i z
  by_cases hne : tests.Nonempty
  · let latest := tests.max' hne
    have hlatest : latest ∈ tests := Finset.max'_mem tests hne
    rcases Finset.mem_filter.mp hlatest with ⟨_, hlatestParts⟩
    rcases hlatestParts with ⟨hPup, hFormed, hx⟩
    have hdetect :
        i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) latest.val z :=
      ReferenceFirstCollectionUpDetectedQueueMask.Pup_subset_Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        latest.val z hPup
    have hlatestOriginal : latest ∈
        ReferenceFirstCollectionFormedUpTestInjection.formedUpTests
          rate rewards C_star C_h i z := by
      change latest ∈ (Finset.univ : Finset (Fin p.T)).filter _
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hdetect, hFormed, hx⟩
    have hdichotomy :=
      ReferenceFirstCollectionFormedUpCountOrAwaitedFailure.actual_first_collection_formed_up_count_or_awaited_failure
        rate rewards C_star C_h z i latest hlatestOriginal
    rcases hdichotomy with hquota | ⟨a, ha, hfailure⟩
    · have hsubset : tests ⊆
          (ReferenceFirstCollectionFormedUpTestInjection.formedUpTests
            rate rewards C_star C_h i z).filter (fun t => t.val ≤ latest.val) := by
        intro t ht
        rcases Finset.mem_filter.mp ht with ⟨_, hparts⟩
        rcases hparts with ⟨hPt, hFt, hxt⟩
        have hdetT :
            i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
              (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) t.val z :=
          ReferenceFirstCollectionUpDetectedQueueMask.Pup_subset_Pdetect
            (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) t.val z hPt
        have horiginal : t ∈
            ReferenceFirstCollectionFormedUpTestInjection.formedUpTests
              rate rewards C_star C_h i z := by
          change t ∈ (Finset.univ : Finset (Fin p.T)).filter _
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hdetT, hFt, hxt⟩
        have hle : t.val ≤ latest.val := Finset.le_max' tests t ht
        exact Finset.mem_filter.mpr ⟨horiginal, hle⟩
      exact (Finset.card_le_card hsubset).trans hquota
    · have hmask :=
        (ReferenceFirstCollectionUpDetectedQueueMask.mem_Pup_iff
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          i latest.val z).mp hPup
      have hnoEarlier :=
        (ReferenceFirstCollectionUpDetectedQueueMask.pastUpFailureFlag_false_iff_no_earlier_failure
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          latest.val z).mp hmask.1
      exact False.elim (hnoEarlier a ha hfailure)
  · have hzero : tests = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [tests, hzero]

/-- The stopped OLD dates are a literal subset of the existing OLD quota set,
so they inherit its inclusive two-quota bound. -/
theorem actual_first_collection_stopped_old_down_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    (stoppedOldDownTests (p := p) rate rewards C_star C_h i z).card ≤
      2 * AffineBatchDecoder.quota p := by
  classical
  have hsubset :
      stoppedOldDownTests (p := p) rate rewards C_star C_h i z ⊆
        ReferenceFirstCollectionStoppedOldDownQuota.stoppedOldDownTests
          (p := p) rate rewards C_star C_h i z := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨_, hparts⟩
    rcases hparts with ⟨hPup, hOld, hx⟩
    have hdet :=
      ReferenceFirstCollectionUpDetectedQueueMask.Pup_subset_Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        t.val z hPup
    change t ∈ (Finset.univ : Finset (Fin p.T)).filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdet, hOld, hx⟩
  exact (Finset.card_le_card hsubset).trans
    (ReferenceFirstCollectionStoppedOldDownQuota.actual_first_collection_stopped_old_down_quota
      (p := p) rate rewards C_star C_h control0 z i)

/-- A positive joined staged observation lies in at least one of its two
actual stage supports. This follows directly from the exposed literal
definition of `X`. -/
private theorem source_stage_support_of_positive_X
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hX : ReferenceFirstCollectionStagedConditionalService.X
      (p := p) (rate := rate) rewards C_star C_h i t z = 1) :
    z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
        (p := p) (rate := rate) rewards C_star C_h i t ∨
      z ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
        (p := p) (rate := rate) rewards C_star C_h i t := by
  by_cases hOld : z ∈ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t
  · exact Or.inl hOld
  · by_cases hFormed : z ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
        (p := p) (rate := rate) rewards C_star C_h i t
    · exact Or.inr hFormed
    · simp [ReferenceFirstCollectionStagedConditionalService.X, hOld, hFormed] at hX

/-- The stopped service dates are exactly the disjoint union of the stopped
OLD and FORMED dates on the same `Pup` and original calendar. -/
theorem stoppedServiceTests_eq_union
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    stoppedServiceTests (p := p) rate rewards C_star C_h i z =
      stoppedOldDownTests (p := p) rate rewards C_star C_h i z ∪
        stoppedFormedUpTests (p := p) rate rewards C_star C_h i z := by
  classical
  ext t
  simp only [stoppedServiceTests, stoppedOldDownTests, stoppedFormedUpTests,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨hPup, hx⟩
    have hX : ReferenceFirstCollectionStagedConditionalService.X
        (p := p) (rate := rate) rewards C_star C_h i t z = 1 := by
      have hdecide : ReferenceFirstCollectionStagedConditionalService.X
          (p := p) (rate := rate) rewards C_star C_h i t z = 1 :=
        of_decide_eq_true (by
          simpa [ReferenceFirstCollectionRoundEndObservation.x] using hx)
      exact hdecide
    rcases source_stage_support_of_positive_X
        (p := p) rate rewards C_star C_h i t z hX with hOld | hFormed
    · exact Or.inl ⟨hPup, hOld, hx⟩
    · exact Or.inr ⟨hPup, hFormed, hx⟩
  · rintro (⟨hPup, _hOld, hx⟩ | ⟨hPup, _hFormed, hx⟩)
    · exact ⟨hPup, hx⟩
    · exact ⟨hPup, hx⟩

/-- The two stage-restricted stopped date sets are disjoint by the actual
OLD/FORMED disjointness theorem. -/
theorem stoppedOldDownTests_disjoint_stoppedFormedUpTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    Disjoint (stoppedOldDownTests (p := p) rate rewards C_star C_h i z)
      (stoppedFormedUpTests (p := p) rate rewards C_star C_h i z) := by
  classical
  rw [Finset.disjoint_left]
  intro t hOldTest hFormedTest
  rcases Finset.mem_filter.mp hOldTest with ⟨_, hOldParts⟩
  rcases hOldParts with ⟨_, hOld, _⟩
  rcases Finset.mem_filter.mp hFormedTest with ⟨_, hFormedParts⟩
  rcases hFormedParts with ⟨_, hFormed, _⟩
  exact (Set.disjoint_left.mp
    (ReferenceFirstCollectionStagedConditionalService.disjoint_OLD_FORMED
      (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed

/-- The total stopped service count is at most four decoder quotas. -/
theorem actual_first_collection_stopped_service_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card ≤
      4 * AffineBatchDecoder.quota p := by
  calc
    (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card =
        (stoppedOldDownTests (p := p) rate rewards C_star C_h i z ∪
          stoppedFormedUpTests (p := p) rate rewards C_star C_h i z).card :=
      congrArg Finset.card (stoppedServiceTests_eq_union
        (p := p) rate rewards C_star C_h z i)
    _ = (stoppedOldDownTests (p := p) rate rewards C_star C_h i z).card +
          (stoppedFormedUpTests (p := p) rate rewards C_star C_h i z).card :=
      Finset.card_union_of_disjoint
        (stoppedOldDownTests_disjoint_stoppedFormedUpTests
          (p := p) rate rewards C_star C_h z i)
    _ ≤ 2 * AffineBatchDecoder.quota p + 2 * AffineBatchDecoder.quota p :=
      Nat.add_le_add
        (actual_first_collection_stopped_old_down_quota
          (p := p) rate rewards C_star C_h control0 z i)
        (actual_first_collection_stopped_formed_up_quota
          (p := p) rate rewards C_star C_h z i)
    _ = 4 * AffineBatchDecoder.quota p := by omega

private theorem stoppedServiceTests_card_eq_waiting_count_at_horizon
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N
        (fun n z => ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) n z)
        (fun i n z => ReferenceFirstCollectionRoundEndObservation.x
          (rate := rate) rewards C_star C_h i n z)
        i p.T z =
      (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card := by
  classical
  change (∑ n ∈ Finset.range p.T,
      if i ∈ ReferenceFirstCollectionUpDetectedQueueMask.Pup
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) n z ∧
          ReferenceFirstCollectionRoundEndObservation.x
            (rate := rate) rewards C_star C_h i n z then 1 else 0) = _
  rw [← Fin.sum_univ_eq_sum_range]
  simp [stoppedServiceTests, Finset.sum_boole]

/-- The actual range-based service counter through every prefix, including
zero, the horizon, and dates beyond the empty observation extension, is
bounded by the inclusive stopped composite quota. -/
theorem actual_first_collection_stopped_service_waiting_count_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) :
    PhaseServiceWaiting.N
        (fun v z => ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) v z)
        (fun j v z => ReferenceFirstCollectionRoundEndObservation.x
          (rate := rate) rewards C_star C_h j v z)
        i n z ≤ 4 * AffineBatchDecoder.quota p := by
  classical
  let P := fun v (source : BootstrapPrivateRoundStreams.SourceInput p) =>
    ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) v source
  let X := fun j v (source : BootstrapPrivateRoundStreams.SourceInput p) =>
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h j v source
  have hcount : PhaseServiceWaiting.N P X i p.T z =
      (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card := by
    exact stoppedServiceTests_card_eq_waiting_count_at_horizon
      (p := p) rate rewards C_star C_h z i
  have hquota := actual_first_collection_stopped_service_quota
    (p := p) rate rewards C_star C_h control0 z i
  have hstable : ∀ v, p.T ≤ v →
      PhaseServiceWaiting.N P X i v z = PhaseServiceWaiting.N P X i p.T z := by
    intro v hv
    unfold PhaseServiceWaiting.N
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr hv)
    intro t ht hnot
    have hnotT : ¬ t < p.T := by
      intro htT
      exact hnot (Finset.mem_range.mpr htT)
    have htT : p.T ≤ t := Nat.le_of_not_gt hnotT
    have hx := ReferenceFirstCollectionRoundEndObservation.x_eq_false_of_horizon_le
      (rate := rate) rewards C_star C_h i t htT z
    simp [P, X, hx]
  have hmono : ∀ v, v ≤ p.T →
      PhaseServiceWaiting.N P X i v z ≤ PhaseServiceWaiting.N P X i p.T z := by
    intro v hv
    unfold PhaseServiceWaiting.N
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hv)
    intro t ht hnot
    exact Nat.zero_le _
  change PhaseServiceWaiting.N P X i n z ≤ 4 * AffineBatchDecoder.quota p
  rcases le_total n p.T with hnT | hTn
  · calc
      PhaseServiceWaiting.N P X i n z ≤ PhaseServiceWaiting.N P X i p.T z :=
        hmono n hnT
      _ = (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card := hcount
      _ ≤ 4 * AffineBatchDecoder.quota p := hquota
  · calc
      PhaseServiceWaiting.N P X i n z = PhaseServiceWaiting.N P X i p.T z :=
        hstable n hTn
      _ = (stoppedServiceTests (p := p) rate rewards C_star C_h i z).card := hcount
      _ ≤ 4 * AffineBatchDecoder.quota p := hquota

end Bandits.Support.ReferenceFirstCollectionStoppedCompositeQuota

end
