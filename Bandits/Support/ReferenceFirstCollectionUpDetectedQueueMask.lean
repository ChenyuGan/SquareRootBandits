/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionUpFailureReadoutV2
public import Bandits.Support.ReferenceFirstCollectionQueuePrefixChronology
public import Bandits.Support.ReferenceFirstCollectionDetectedQueueMask

/-!
# Strict-past UP-failure mask for first-collection tasks

This module adds the fixed-awaited-UP failure detector to the existing
first-collection task mask. It is an analytical mask on the original source
input and leaves the physical protocol unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionUpDetectedQueueMask

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}

/-- The actual finite task mask, further erased after a strict-past fixed-UP
ambiguity failure has been observed. -/
def Pup (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Finset (Fin (p.m - 1)) :=
  if ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rate rewards C_star C_h n z = false then
    ReferenceFirstCollectionDetectedQueueMask.Pdetect
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) n z
  else ∅

/-- Membership in the UP-detected mask is old detected membership together
with the literal strict-past UP-failure flag being false. -/
theorem mem_Pup_iff (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    i ∈ Pup (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z ↔
      ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h n z = false ∧
        i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z := by
  constructor
  · intro hi
    by_cases hflag : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h n z = false
    · exact ⟨hflag, by simpa [Pup, hflag] using hi⟩
    · simp [Pup, hflag] at hi
  · rintro ⟨hflag, hi⟩
    simpa [Pup, hflag] using hi

/-- The UP-detected mask is pointwise a subset of the existing detector. -/
theorem Pup_subset_Pdetect (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      n z ⊆
      ReferenceFirstCollectionDetectedQueueMask.Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) n z := by
  intro i hi
  exact (mem_Pup_iff (rate := rate) (rewards := rewards) (C_star := C_star)
    (C_h := C_h) i n z).mp hi |>.2

/-- The UP-detected mask remains a subset of the original pending tasks. -/
theorem Pup_subset_Praw (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      n z ⊆
      ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z := by
  intro i hi
  exact ReferenceFirstCollectionDetectedQueueMask.Pdetect_subset_Praw
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    n z ((Pup_subset_Pdetect (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) n z) hi)

/-- Membership is measurable in the original source filtration at exactly
the requested pre-round field, including the empty extension at and beyond
the horizon. -/
theorem Pup_mem_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        i ∈ Pup (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z} := by
  have hflag := ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag_adapted
    rate rewards C_star C_h control0 n
  have hflagFalse :
      MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (n + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
            rate rewards C_star C_h n z = false} := by
    have hpre := hflag (MeasurableSet.singleton false)
    simpa only [Set.preimage, Set.mem_singleton_iff] using hpre
  have hdet := ReferenceFirstCollectionDetectedQueueMask.Pdetect_mem_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    control0 i n
  have heq :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        i ∈ Pup (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z} =
      {z | ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
          rate rewards C_star C_h n z = false} ∩
        {z | i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z} := by
    ext z
    exact mem_Pup_iff (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) i n z
  rw [heq]
  exact hflagFalse.inter hdet

/-- The flag is false at scan `n` exactly when no fixed-awaited-UP failure
occurred at a physical round strictly smaller than `n`. -/
theorem pastUpFailureFlag_false_iff_no_earlier_failure
    (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h n z = false ↔
      ∀ r : Fin p.T, r.val < n →
        ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
          rate rewards C_star C_h z r := by
  constructor
  · intro hflag r hr hfail
    have htrue : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h n z = true := by
      unfold ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rw [decide_eq_true_eq]
      exact ⟨r, hr, hfail⟩
    rw [hflag] at htrue
    cases htrue
  · intro hnone
    unfold ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
    apply decide_eq_false_iff_not.mpr
    rintro ⟨r, hr, hfail⟩
    exact hnone r hr hfail

/-- Exact scan semantics for the combined mask. The gate scans physical
rounds `r` with `r.val < n`, and otherwise leaves the old mask unchanged. -/
theorem Pup_scan_semantics
    (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        n z =
      if ∀ r : Fin p.T, r.val < n →
          ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
            rate rewards C_star C_h z r then
        ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z
      else ∅ := by
  by_cases hnone : ∀ r : Fin p.T, r.val < n →
      ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z r
  · have hflag := (pastUpFailureFlag_false_iff_no_earlier_failure
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      n z).2 hnone
    change (if ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
          rate rewards C_star C_h n z = false then
          ReferenceFirstCollectionDetectedQueueMask.Pdetect
            (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) n z else ∅) =
      if (∀ r : Fin p.T, r.val < n →
          ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
            rate rewards C_star C_h z r) then
        ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z else ∅
    rw [ite_eq_left hflag, ite_eq_left hnone]
  · have hflag : ¬ ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h n z = false := by
      intro hfalse
      exact hnone ((pastUpFailureFlag_false_iff_no_earlier_failure
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        n z).mp hfalse)
    change (if ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
          rate rewards C_star C_h n z = false then
          ReferenceFirstCollectionDetectedQueueMask.Pdetect
            (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) n z else ∅) =
      if (∀ r : Fin p.T, r.val < n →
          ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
            rate rewards C_star C_h z r) then
        ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z else ∅
    rw [ite_eq_right hflag, ite_eq_right hnone]

/-- A physical fixed-awaited-UP failure at round `t` is absent from scan
`t.val` itself, and the old detecting mask is retained there whenever no
strictly earlier physical round failed. -/
theorem Pup_retains_detecting_scan
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcurrent : ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t)
    (hprior : ∀ r : Fin p.T, r.val < t.val →
      ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z r) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z =
        ReferenceFirstCollectionDetectedQueueMask.Pdetect
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) t.val z ∧
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t := by
  have hflag : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rate rewards C_star C_h t.val z = false := by
    exact (pastUpFailureFlag_false_iff_no_earlier_failure
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z).2 hprior
  constructor
  · simp [Pup, hflag]
  · exact hcurrent

/-- Once a physical UP failure is in the strict past, the mask is empty at
every later scan, including the terminal scan `n = p.T`. -/
theorem Pup_empty_after_fixed_failure
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hfail : ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t) :
    ∀ n : ℕ, t.val < n →
      Pup (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) n z = ∅ := by
  intro n htn
  have hsuccessor : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rate rewards C_star C_h (t.val + 1) z = true := by
    unfold ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
    simp only [decide_eq_true_eq]
    exact ⟨t, by omega, hfail⟩
  have hflag := ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag_mono
    rate rewards C_star C_h z (t.val + 1) n (by omega) hsuccessor
  simp [Pup, hflag]

/-- At an actual boundary, the combined mask is its original pending set
exactly when both the strict-past UP gate and the existing boundary detector
pass. -/
theorem Pup_at_boundary
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s u : ℕ) (hs : s ≤ u) (hu : u ≤ t.val)
    (hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u t) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z =
        if ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
              rate rewards C_star C_h t.val z = false ∧
            (t.val + 1 <
                ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
                  rate rewards C_star C_h z ∧
              z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
                (rate := rate) (rewards := rewards) (C_star := C_star)
                (C_h := C_h) s u t) then
          ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
            t.val z
        else ∅ := by
  rw [Pup,
    ReferenceFirstCollectionDetectedQueueMask.Pdetect_at_boundary
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t z s u hs hu hC]
  by_cases hflag : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rate rewards C_star C_h t.val z = false
  · rw [ite_eq_left hflag]
    by_cases hboundary : t.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
            rate rewards C_star C_h z ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) s u t
    · simp [hflag, hboundary]
    · simp [hflag, hboundary]
  · simp [hflag]

/-- Within one actual first collection, the combined mask nests backwards.
The later actual boundary is a scoped premise, so this does not assert any
global nesting across absent or distinct phases. -/
theorem Pup_backward_on_actual_collection
    {s u : ℕ} {t0 t1 : Fin p.T}
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hs : s ≤ u) (hu : u ≤ t0.val) (ht : t0.val ≤ t1.val)
    (hC1 : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u t1) :
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t1.val z ⊆
    Pup (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t0.val z := by
  intro i hi
  have hmem := (mem_Pup_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) i t1.val z).mp hi
  have hflag1 := hmem.1
  have hdet1 := hmem.2
  have hflag0 : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
      rate rewards C_star C_h t0.val z = false := by
    cases h0 : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h t0.val z with
    | false => rfl
    | true =>
        have h1 := ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag_mono
          rate rewards C_star C_h z t0.val t1.val (by omega) h0
        rw [hflag1] at h1
        cases h1
  have hboundary1 := ReferenceFirstCollectionDetectedQueueMask.Pdetect_at_boundary
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t1 z s u hs (by omega) hC1
  have hcondition1 : t1.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z ∧
      z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) s u t1 := by
    by_cases hc : t1.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
            rate rewards C_star C_h z ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) s u t1
    · exact hc
    · rw [hboundary1, ite_eq_right hc] at hdet1
      simp at hdet1
  have hP1 : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t1.val z := by
    rw [hboundary1] at hdet1
    simpa only [ite_eq_left hcondition1] using hdet1
  have hback := ReferenceFirstCollectionQueuePrefixChronology.active_boundary_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (u := u) (t0 := t0) (t1 := t1) z hs hu ht hC1
  have hC0 := hback.1
  have hP0 := hback.2 hP1
  have hq0 := ReferenceFirstCollectionQueuePrefixChronology.active_queue_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (u := u) (t0 := t0) (t1 := t1) hs hu ht hC1 hcondition1.2
  have hcut0 : t0.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z := by
    omega
  have hboundary0 := ReferenceFirstCollectionDetectedQueueMask.Pdetect_at_boundary
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t0 z s u hs hu hC0
  have hdet0 : i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t0.val z := by
    rw [hboundary0]
    rw [ite_eq_left ⟨hcut0, hq0⟩]
    exact hP0
  exact (mem_Pup_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) i t0.val z).mpr ⟨hflag0, hdet0⟩

/-- Same-field service for UP-detected tasks under the original source law.
The observation, reward statistic, filtration, and conditional expectation
are exactly those of the established detected-task service theorem. -/
theorem Pup_service
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (i : Fin (p.m - 1)) (n : ℕ), n < p.T →
        i ∈ Pup (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          PhaseServiceWaiting.observation
            (ReferenceFirstCollectionRoundEndObservation.x
              (rate := rate) rewards C_star C_h) i n |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (n + 1)] z =
          ReferenceFirstCollectionRoundEndObservation.g rewards n z /
            (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
  filter_upwards [ReferenceFirstCollectionDetectedQueueMask.Pdetect_service
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    control0] with z hz
  intro i n hn hi
  exact hz i n hn ((Pup_subset_Pdetect (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) n z) hi)

end Bandits.Support.ReferenceFirstCollectionUpDetectedQueueMask

end
