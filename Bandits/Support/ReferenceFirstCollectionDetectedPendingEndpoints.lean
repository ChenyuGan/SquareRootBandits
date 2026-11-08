/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDetectedQueueMask
public import Bandits.Support.ReferenceFirstCollectionQueuePrefixChronology

/-!
# Endpoints of detected first-collection pending support

The analytical support indices are exactly the interval on which the actual
detector is nonempty. Their endpoints are stopping times for the original
source-prefix filtration.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionDetectedQueueMask
open ReferenceFirstCollectionQueuePrefixChronology
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionDetectedPendingEndpoints

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}

/-- Calendar dates on which the actual detector has nonempty support. -/
def supportIndices (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Finset ℕ :=
  (Finset.range p.T).filter fun n =>
    (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty

/-- The first supported date, with the literal empty-support sentinel. -/
def sigma (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).min' h + 1
  else p.T + 1

/-- One plus the last supported date, with the literal empty-support sentinel. -/
def theta (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).max' h + 2
  else p.T + 1

private theorem localCutoff_le_of_detected_nonempty
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hn : n < p.T)
    (hP : (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length ≤ n := by
  have hraw := Pdetect_subset_Praw (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) n z
  have hraw' : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h n z).Nonempty := by
    rcases hP with ⟨i, hi⟩
    exact ⟨i, hraw hi⟩
  let t : Fin p.T := ⟨n, hn⟩
  obtain ⟨pair, hpair, _⟩ := actual_pending_boundary_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t z hraw'
  rcases hpair with ⟨_, htn, _, _, hcut, _⟩
  simpa only [hcut] using htn

/-- After the actual cutoff, every later detected task is still present at
each earlier date. The physical boundary, decoder test, and numerical queue
test all refer to the same original source and the same actual boundary. -/
theorem Pdetect_backward_after_actual_cutoff
    (a b : ℕ) (hab : a ≤ b) (hb : b < p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hcut : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length ≤ a) :
    Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) b z ⊆
    Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) a z := by
  intro i hi
  have hrawB := Pdetect_subset_Praw (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) b z hi
  have hrawNonempty : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h b z).Nonempty := ⟨i, hrawB⟩
  let tB : Fin p.T := ⟨b, hb⟩
  obtain ⟨pair, hpair, _⟩ := actual_pending_boundary_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    tB z hrawNonempty
  rcases pair with ⟨s, u⟩
  rcases hpair with ⟨hsu0, hub0, hCB0, hs0, hu0, _⟩
  have hsu : s ≤ u := by simpa using hsu0
  have hub : u ≤ b := by simpa [tB] using hub0
  have hCB : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u tB := by simpa using hCB0
  have hu : u = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length := by simpa using hu0
  have huA : u ≤ a := by
    simpa only [hu] using hcut
  let tA : Fin p.T := ⟨a, lt_of_le_of_lt hab hb⟩
  have hCAq := active_boundary_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (u := u) (t0 := tA) (t1 := tB) z hsu huA hab hCB
  have hCA := hCAq.1
  have hrawSubset : ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h b z ⊆
      ReferenceFirstCollectionPendingObservation.Praw
        rate rewards C_star C_h a z := by
    simpa [tA, tB] using hCAq.2
  have hsafeB : z ∈ safePendingEvent (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) tB := by
    by_cases hsaf : z ∈ safePendingEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) tB
    · exact hsaf
    · simp [Pdetect, tB, hb, hsaf] at hi
  have hboundaryB := safePendingEvent_at_boundary
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    tB z s u hsu hub hCB
  obtain ⟨hdecoderB, hqueueB⟩ := hboundaryB.mp hsafeB
  have hdecoderB' : b + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z := by simpa [tB] using hdecoderB
  have hqueueA := active_queue_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (u := u) (t0 := tA) (t1 := tB) (z := z)
    hsu huA hab hCB hqueueB
  have hdecoderA : a + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z := by
    exact lt_of_le_of_lt (Nat.add_le_add_right hab 1) hdecoderB'
  have hboundaryA := Pdetect_at_boundary
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    tA z s u hsu huA hCA
  have hdetA : Pdetect (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) a z =
      ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h a z := by
    simpa [tA, hdecoderA, hqueueA] using hboundaryA
  rw [hdetA]
  exact hrawSubset hrawB

/-- Exact interval support: no absent date is added and every intermediate
detected date is included. -/
theorem supportIndices_eq_Ico
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z =
      Finset.Ico
        (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z - 1)
        (theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z - 1) := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hminT : S.min' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmin).1
    have hmaxT : S.max' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le_max' S hS
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hminT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' < p.T := by
      simpa [S] using hminT
    have hmaxT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).max' hS' < p.T := by
      simpa [S] using hmaxT
    have hminmax' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' ≤
        (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
      simpa [S] using hminlemax
    have hcutMin := localCutoff_le_of_detected_nonempty
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      z (S.min' hS) hminT (Finset.mem_filter.mp hmin).2
    have hcutMin' : ReferenceCompletePhysicalHistory.physicalStart rate z rewards
        C_star C_h +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)).length ≤
        (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).min' hS' := by
      simpa [S] using hcutMin
    ext n
    constructor
    · intro hn
      have hlemin : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).min' hS' ≤ n := by
        simpa [S] using Finset.min'_le S _ hn
      have hmaxle : n ≤ (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
        simpa [S] using Finset.le_max' S _ hn
      simp only [Finset.mem_Ico]
      simp only [sigma, theta, dite_eq_left hS']
      omega
    · intro hn
      simp only [Finset.mem_Ico] at hn
      simp only [sigma, theta, dite_eq_left hS'] at hn
      have hmaxMember : S.max' hS ∈ S := hmax
      have hmaxNonempty0 :
          (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) (S.max' hS) z).Nonempty :=
        (Finset.mem_filter.mp hmaxMember).2
      have hmaxNonempty :
          (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h)
            ((supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z).max' hS') z).Nonempty := by
        simpa [S] using hmaxNonempty0
      have hnT : n < p.T := by omega
      have hcutN : ReferenceCompletePhysicalHistory.physicalStart rate z rewards
          C_star C_h +
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)).length ≤ n :=
        le_trans hcutMin' (by omega)
      have hback := Pdetect_backward_after_actual_cutoff
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        n ((supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS') (by omega) hmaxT' z hcutN
      have hmember : n ∈ S := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr hnT
        · rcases hmaxNonempty with ⟨j, hj⟩
          exact ⟨j, hback hj⟩
      exact hmember
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hEmpty : supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS'
    change supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z = _
    simp only [sigma, theta, dite_eq_right hS']
    rw [hEmpty]
    simp

/-- The first and one-past-last detected dates are ordered and bounded by the
literal empty-support sentinel. -/
theorem sigma_theta_range
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ∧
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z ∧
      theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ p.T + 1 := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hminT : S.min' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmin).1
    have hmaxT : S.max' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
    have hminmax := Finset.min'_le_max' S hS
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hminT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' < p.T := by
      simpa [S] using hminT
    have hmaxT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).max' hS' < p.T := by
      simpa [S] using hmaxT
    have hminmax' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' ≤
        (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
      simpa [S] using hminmax
    simp only [sigma, theta, dite_eq_left hS']
    omega
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    simp [sigma, theta, hS']

/-- Full nonemptiness characterization, including dates beyond the physical
horizon and the empty-support sentinel. -/
theorem Pdetect_nonempty_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n + 1 ∧
      n + 1 < theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z := by
  have hsupport : (Pdetect (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) n z).Nonempty ↔
      n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
    by_cases hn : n < p.T
    · simp only [supportIndices, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        exact ⟨hn, h⟩
      · rintro ⟨_, h⟩
        exact h
    · simp only [supportIndices, Finset.mem_filter, Finset.mem_range]
      simp [Pdetect, hn]
  rw [hsupport]
  have hIco := supportIndices_eq_Ico (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have hmemIco : n ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1 ≤ n ∧
      n < theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1 := by
    have h := congrArg (fun S : Finset ℕ => n ∈ S) hIco
    exact Iff.of_eq (by simpa only [Finset.mem_Ico] using h)
  rw [hmemIco]
  have hrange := sigma_theta_range (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  omega

/-- Every nonempty detector date lies between the literal first and last
endpoints. This supplies the phase-membership hypothesis for the waiting theorem. -/
theorem Pdetect_endpoint_phase :
    ∀ t, t < p.T → ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) t z).Nonempty →
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ t + 1 ∧
      t + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
  intro t ht z hdet
  have hmember : t ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hdet⟩
  rw [supportIndices_eq_Ico (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z] at hmember
  simp only [Finset.mem_Ico] at hmember
  have hrange := sigma_theta_range (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  omega

/-- The first-collection support is characterized on every natural date by
the two literal endpoints. -/
theorem Pdetect_endpoint_characterization
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n + 1 ∧
      n + 1 < theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z :=
  Pdetect_nonempty_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z n

/-- Exact interval nesting for the original concrete detected task set. -/
theorem Pdetect_endpoint_nested
    (a b : ℕ) (hab : a ≤ b) (hb : b < p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ a + 1 →
      b + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z →
      Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) b z ⊆
      Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) a z := by
  intro ha hbt i hi
  have hrange := sigma_theta_range (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have haSupport : a ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z := by
    rw [supportIndices_eq_Ico (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z]
    simp only [Finset.mem_Ico]
    omega
  have haT : a < p.T := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp haSupport).1
  have haNonempty : (Pdetect (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) a z).Nonempty :=
    (Finset.mem_filter.mp haSupport).2
  have hu := localCutoff_le_of_detected_nonempty
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z a haT haNonempty
  exact Pdetect_backward_after_actual_cutoff
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    a b hab hb z hu hi

private theorem Pdetect_nonempty_measurable_at
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    MeasurableSet[sourcePrefixFiltration control0 (n + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z).Nonempty} := by
  have hEq :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z).Nonempty} =
        ⋃ i : Fin (p.m - 1), {z | i ∈
          Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) n z} := by
    ext z
    simp [Finset.Nonempty]
  rw [hEq]
  exact MeasurableSet.iUnion fun i => Pdetect_mem_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    control0 i n

/-- The exact empty-last-cell identity used to make the last endpoint
pre-round measurable. -/
theorem theta_le_iff
    (n : ℕ) (hn : 0 < n) (hnT : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z < n ∧
      ¬ (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (n - 1) z).Nonempty := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have hmem : (Pdetect (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (n - 1) z).Nonempty ↔ n - 1 ∈ S := by
    have hn' : n - 1 < p.T := by omega
    simp [S, supportIndices, hn']
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hminmax : S.min' hS ≤ S.max' hS := Finset.min'_le_max' S hS
    have hInterval := supportIndices_eq_Ico
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hInterval' : S = Finset.Ico (S.min' hS) (S.max' hS + 1) := by
      simpa [S, sigma, theta, hS'] using hInterval
    have hintervalMem : n - 1 ∈ S ↔
        S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
      have h := congrArg (fun U : Finset ℕ => n - 1 ∈ U) hInterval'
      simp only [Finset.mem_Ico] at h
      constructor
      · intro hx
        have hx' := h.mp hx
        exact ⟨hx'.1, by omega⟩
      · rintro ⟨hx₁, hx₂⟩
        apply h.mpr
        exact ⟨hx₁, by omega⟩
    have hdet : (Pdetect (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (n - 1) z).Nonempty ↔
        S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
      exact hmem.trans hintervalMem
    have hσ : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have hθ : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hσ, hθ]
    rw [hdet]
    omega
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hdet : ¬ (Pdetect (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (n - 1) z).Nonempty := by
      intro h
      exact hS' ⟨n - 1, hmem.mp h⟩
    simp only [sigma, theta, dite_eq_right hS', hdet]
    omega

/-- The first detected date is a stopping time for the unchanged source-prefix
filtration, including zero and terminal observation indices. -/
theorem sigma_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (sourcePrefixFiltration control0)
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hnT : p.T + 1 ≤ n
  · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hr := sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
      exact hr.2.1.trans (hr.2.2.trans hnT)
    rw [hwhole]
    exact MeasurableSet.univ
  · have hnle : n ≤ p.T := by omega
    have hEq :
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          sigma (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} =
        ⋃ k : Fin p.T,
          {z | k.val + 1 ≤ n ∧
            (Pdetect (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) k.val z).Nonempty} := by
      ext z
      by_cases hS : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).Nonempty
      · have hmin : (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z).min' hS ∈
          supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z := Finset.min'_mem _ hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_left hS]
        constructor
        · intro h
          refine ⟨⟨_, Finset.mem_range.mp
            (Finset.mem_filter.mp hmin).1⟩, ?_, ?_⟩
          · omega
          · exact (Finset.mem_filter.mp hmin).2
        · rintro ⟨k, hk, hdet⟩
          have hmem : k.val ∈ supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, hdet⟩
          have hminle := Finset.min'_le
            (supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z) k.val hmem
          omega
      · have hSempty : supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_right hS]
        constructor
        · intro h
          omega
        · rintro ⟨k, _, hdet⟩
          have hmem : k.val ∈ supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, hdet⟩
          rw [hSempty] at hmem
          simp at hmem
    rw [hEq]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k.val + 1 ≤ n
    · have hdet := Pdetect_nonempty_measurable_at
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) control0 k.val
      have hdet' := (sourcePrefixFiltration control0).mono
        (by omega : k.val + 1 ≤ n) _ hdet
      simpa [hk] using hdet'
    · simp [hk]

/-- The last detected endpoint is a stopping time. For intermediate source
dates, its event is expressed by the earlier first-endpoint event and the
empty test at date `n - 1`; no future maximum is exposed to the filtration. -/
theorem theta_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (sourcePrefixFiltration control0)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hempty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ 0} = ∅ := by
      ext z
      have hpos := (sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).1
      have hst := (sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).2.1
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [hempty]
    exact (sourcePrefixFiltration control0 0).measurableSet_empty
  · by_cases hnT : p.T + 1 ≤ n
    · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (sigma_theta_range (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).2.2.trans (by omega)
      rw [hwhole]
      exact MeasurableSet.univ
    · have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
      have hnT' : n ≤ p.T := by omega
      have hEq :
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            theta (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) z ≤ n} =
          {z | sigma (rate := rate) (rewards := rewards)
                (C_star := C_star) (C_h := C_h) z < n} ∩
            {z | ¬ (Pdetect (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact theta_le_iff (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) n hn0' hnT' z
      rw [hEq]
      apply (MeasurableSet.inter ?_ ?_)
      · have hsig := sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 (n - 1)
        have hsig' := (sourcePrefixFiltration control0).mono
          (by omega : n - 1 ≤ n) _ hsig
        apply hsig'.congr
        ext z
        simp only [Set.mem_ofPred_eq]
        omega
      · have hdet := Pdetect_nonempty_measurable_at
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 (n - 1)
        have hdet' : MeasurableSet[sourcePrefixFiltration control0 n]
            {z | (Pdetect (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) (n - 1) z).Nonempty} := by
          have hnsub : (n - 1) + 1 = n := by omega
          rw [hnsub] at hdet
          exact hdet
        exact hdet'.compl

end Bandits.Support.ReferenceFirstCollectionDetectedPendingEndpoints

end
