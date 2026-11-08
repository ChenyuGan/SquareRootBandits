/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport
public import Bandits.Support.PhaseServiceWaiting

/-!
# Calendar support and endpoints for the actual post-collection H phase

The phase starts at the first actual later installation after the literal raw
replacement collection. Its pending sets are the actual choice-time sets on
the original calendar, with the finite horizon sentinel used only for the
analysis endpoints.

Sources: `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix
open Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseEndpoints

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual H task at zero-based source index `k`, retaining its original
calendar date `k + 1`. Out-of-horizon indices are empty. -/
def rawHPendingNat (k : ℕ) (z : SourceInput p) : Finset (Fin (p.m - 1)) :=
  if hk : k < p.T then
    Finset.univ.filter fun i =>
      rawHTaskSupport rate rewards C_star C_h ⟨k, hk⟩ i z
  else ∅

/-- The actual one-based source dates at which at least one H confirmation is
pending at arm choice. -/
def rawHSupportDates (z : SourceInput p) : Finset ℕ :=
  ((Finset.range p.T).filter fun k =>
    (rawHPendingNat rate rewards C_star C_h k z).Nonempty).image fun k => k + 1

/-- First active one-based H source date, with `T + 1` when this raw H phase
does not occur. -/
def rawHSigma (z : SourceInput p) : ℕ :=
  (rawHSupportDates rate rewards C_star C_h z ∪ {p.T + 1}).min'
    ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩

/-- First excluded one-based H endpoint: one beyond the last actual pending
date, or `T + 1` on an empty support. -/
def rawHTheta (z : SourceInput p) : ℕ :=
  if h : (rawHSupportDates rate rewards C_star C_h z).Nonempty then
    (rawHSupportDates rate rewards C_star C_h z).max' h + 1
  else p.T + 1

theorem rawHPendingNat_mem (z : SourceInput p) (k : ℕ)
    (i : Fin (p.m - 1)) :
    i ∈ rawHPendingNat rate rewards C_star C_h k z ↔
      ∃ hk : k < p.T, rawHTaskSupport rate rewards C_star C_h ⟨k, hk⟩ i z := by
  by_cases hk : k < p.T
  · simp [rawHPendingNat, hk]
  · simp [rawHPendingNat, hk]

theorem rawHPendingNat_nonempty_iff (z : SourceInput p) (k : ℕ) :
    (rawHPendingNat rate rewards C_star C_h k z).Nonempty ↔
      ∃ hk : k < p.T, ∃ i : Fin (p.m - 1),
        rawHTaskSupport rate rewards C_star C_h ⟨k, hk⟩ i z := by
  simp only [Finset.Nonempty, rawHPendingNat_mem]
  constructor
  · rintro ⟨i, hk, hsupport⟩
    exact ⟨hk, i, hsupport⟩
  · rintro ⟨hk, i, hsupport⟩
    exact ⟨i, hk, hsupport⟩

theorem rawHPendingNat_empty_of_ge_horizon (z : SourceInput p) (k : ℕ)
    (hk : p.T ≤ k) :
    rawHPendingNat rate rewards C_star C_h k z = ∅ := by
  simp [rawHPendingNat, Nat.not_lt.mpr hk]

theorem rawHSupportDates_mem_iff (z : SourceInput p) (d : ℕ) :
    d ∈ rawHSupportDates rate rewards C_star C_h z ↔
      ∃ k, k < p.T ∧ d = k + 1 ∧
        (rawHPendingNat rate rewards C_star C_h k z).Nonempty := by
  simp only [rawHSupportDates, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hpending⟩, rfl⟩
    exact ⟨k, hk, rfl, hpending⟩
  · rintro ⟨k, hk, rfl, hpending⟩
    exact ⟨k, ⟨hk, hpending⟩, rfl⟩

theorem rawHSupportDates_bounds (z : SourceInput p) (d : ℕ)
    (hd : d ∈ rawHSupportDates rate rewards C_star C_h z) :
    1 ≤ d ∧ d ≤ p.T := by
  rcases (rawHSupportDates_mem_iff rate rewards C_star C_h z d).mp hd with
    ⟨k, hk, rfl, _⟩
  omega

theorem rawHSigma_bounds (z : SourceInput p) :
    1 ≤ rawHSigma rate rewards C_star C_h z ∧
      rawHSigma rate rewards C_star C_h z ≤ p.T + 1 := by
  have hmem := Finset.min'_mem
    (rawHSupportDates rate rewards C_star C_h z ∪ {p.T + 1})
    (show (rawHSupportDates rate rewards C_star C_h z ∪ {p.T + 1}).Nonempty from
      ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩)
  have hbound : ∀ d ∈ rawHSupportDates rate rewards C_star C_h z ∪ {p.T + 1},
      1 ≤ d ∧ d ≤ p.T + 1 := by
    intro d hd
    rcases Finset.mem_union.mp hd with hsupport | hsentinel
    · exact ⟨(rawHSupportDates_bounds rate rewards C_star C_h z d hsupport).1,
        Nat.le_succ_of_le (rawHSupportDates_bounds rate rewards C_star C_h z d hsupport).2⟩
    · simp only [Finset.mem_singleton] at hsentinel
      subst d
      omega
  unfold rawHSigma
  exact ⟨hbound _ hmem |>.1, hbound _ hmem |>.2⟩

theorem rawHTheta_bounds (z : SourceInput p) :
    1 ≤ rawHTheta rate rewards C_star C_h z ∧
      rawHTheta rate rewards C_star C_h z ≤ p.T + 1 := by
  unfold rawHTheta
  split
  · rename_i h
    have hmax := Finset.max'_mem (rawHSupportDates rate rewards C_star C_h z) h
    have hb := rawHSupportDates_bounds rate rewards C_star C_h z _ hmax
    omega
  · omega

/-- The birth is the same rawK endpoint record and is retained as the first
record of the actual H scan. -/
theorem rawH_birth_actual_pending_univ (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    birth ∈ rawHRecords rate rewards C_star C_h z ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection birth.input,
        birth.output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice = Finset.univ := by
  have hrecords := rawHRecords_eq_actualH_of_endpoint
    rate rewards C_star C_h z hK birth hbirth
  obtain ⟨selected, hselected, hpending⟩ := rawKEndpoint_birthPending_univ
    rate rewards C_star C_h z hK birth hbirth
  have hmissing : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      birth = true := by
    simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
      hselected, hpending, decide_eq_true_eq]
    have hm := p.two_le_m
    have hcount : 0 < p.m - 1 := by omega
    exact ⟨⟨0, hcount⟩, Finset.mem_univ _⟩
  refine ⟨?_, ⟨selected, hselected, hpending⟩⟩
  rw [hrecords]
  simp only [List.takeWhile_cons, hmissing, ↓reduceIte,
    List.mem_cons_self]

private theorem actualRecord_at_complete_index (z : SourceInput p) (t : Fin p.T)
    (j : ℕ)
    (hj : j < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (htime : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j]).input.time = t) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j] := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hrowTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨j, hj⟩
  change (R[j]).input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j at hrowTime
  have ht : (R[j]).input.time.val = t.val := congrArg Fin.val htime
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ t.val := by omega
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = j := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact List.getElem?_eq_getElem hj

/-- A supported record is the actual record at that same one-based physical
source date; its pending set is the exact choice-time pending set. -/
theorem rawHTaskSupport_same_actual_record (z : SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    ∃ r ∈ rawHRecords rate rewards C_star C_h z,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        t z = some r ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧ r.input.time = t := by
  rcases hsupport with ⟨r, hr, htime, selected, hs, hi⟩
  have hrRaw : r ∈ rawHRecords rate rewards C_star C_h z := hr
  by_cases hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z = []
  · have hnil := rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z hK
    rw [hnil] at hr
    cases hr
  · cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
    | none =>
        have hnil := rawHRecords_eq_nil_of_endpoint_none
          rate rewards C_star C_h z hK hb
        rw [hnil] at hr
        cases hr
    | some birth =>
        have hraw := rawHRecords_eq_actualH_of_endpoint
          rate rewards C_star C_h z hK birth hb
        rw [hraw] at hr
        have hmem : r ∈ birth ::
            ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z
              (rawKEndpointIndex rate rewards C_star C_h z +
                (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
                  rate rewards C_star C_h z).length + 1) :=
          (List.takeWhile_prefix
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).sublist.subset hr
        rcases List.mem_cons.mp hmem with heq | htail
        · subst r
          let a := rawKEndpointIndex rate rewards C_star C_h z +
            (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
              rate rewards C_star C_h z).length
          have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[a]? = some birth := by
            simpa only [rawKEndpointRecord?, a] using hb
          have hlookup' := List.getElem?_eq_some_iff.mp hlookup
          rcases hlookup' with ⟨hj, hrecord⟩
          have htime' :
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[a]).input.time = t := by
            simpa only [hrecord, a] using htime
          have hactual := actualRecord_at_complete_index rate rewards C_star C_h z t
            a hj htime'
          rw [hrecord] at hactual
          exact ⟨birth, hrRaw, hactual, selected, hs, hi, htime⟩
        · obtain ⟨j, hj, hrow⟩ := List.mem_iff_getElem.mp htail
          let start := rawKEndpointIndex rate rewards C_star C_h z +
            (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
              rate rewards C_star C_h z).length + 1
          let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z start
          have hjW : j < W.length := by
            simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hj
          have hlen : W.length ≤ R.length - start := by
            have hlen' := (List.takeWhile_prefix
              (l := R.drop start)
              ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
            simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
              R, List.length_drop] using hlen'
          have hstartLt : start < R.length := by omega
          let b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h).length := ⟨start, hstartLt⟩
          have hprefixLen := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
            rewards C_star C_h z b
          have hindex : start + j < R.length := by omega
          have hrowPrefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
            rewards C_star C_h z b j hjW
          let ix := start + j
          have hrow' : W[j] =
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[ix]'hindex := by
            simpa only [W, ix, b,
              ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hrowPrefix
          have heq : r = (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[ix]'hindex := hrow.symm.trans hrow'
          have htime' :
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[ix]).input.time = t := by
            rw [← heq]
            exact htime
          have hactual := actualRecord_at_complete_index rate rewards C_star C_h z t
            ix hindex htime'
          rw [← heq] at hactual
          exact ⟨r, hrRaw, hactual, selected, hs, hi, htime⟩

/-- Calendar pending factors through the accepted original-source strict
prefix, without changing its date or the continuous source payloads. -/
theorem rawHPendingNat_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (hk : k < p.T) (z : SourceInput p) :
    rawHPendingNat rate rewards C_star C_h k z =
      rawHPendingNat rate rewards C_star C_h k
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 k z) := by
  apply Finset.ext
  intro i
  simp only [rawHPendingNat, dite_eq_left hk, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [rawHTaskSupport_factor rate rewards C_star C_h control0 z ⟨k, hk⟩ i]

theorem rawHPendingNat_factor_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p)
    (k n : ℕ) (hkn : k ≤ n) (hk : k < p.T) (z : SourceInput p) :
    rawHPendingNat rate rewards C_star C_h k z =
      rawHPendingNat rate rewards C_star C_h k
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  calc
    rawHPendingNat rate rewards C_star C_h k z =
        rawHPendingNat rate rewards C_star C_h k
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 k z) :=
      rawHPendingNat_factor rate rewards C_star C_h control0 k hk z
    _ = rawHPendingNat rate rewards C_star C_h k
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 k
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
      rw [← ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 k n hkn z]
    _ = rawHPendingNat rate rewards C_star C_h k
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) :=
      (rawHPendingNat_factor rate rewards C_star C_h control0 k hk
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).symm

theorem rawHPendingNat_measurableSet
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (hk : k < p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (k + 1)]
      {z : SourceInput p | i ∈ rawHPendingNat rate rewards C_star C_h k z} := by
  simpa only [rawHPendingNat, dite_eq_left hk, Finset.mem_filter,
    Finset.mem_univ, true_and] using
      rawHTaskSupport_measurableSet rate rewards C_star C_h control0
        ⟨k, hk⟩ i

theorem rawHPendingNat_nonempty_measurableSet
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (hk : k < p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (k + 1)]
      {z : SourceInput p |
        (rawHPendingNat rate rewards C_star C_h k z).Nonempty} := by
  have heq : {z : SourceInput p |
        (rawHPendingNat rate rewards C_star C_h k z).Nonempty} =
      ⋃ i : Fin (p.m - 1),
        {z : SourceInput p | i ∈ rawHPendingNat rate rewards C_star C_h k z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.Nonempty]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    rawHPendingNat_measurableSet rate rewards C_star C_h control0 k hk i

theorem rawHSigma_le_iff (z : SourceInput p) (n : ℕ) :
    rawHSigma rate rewards C_star C_h z ≤ n ↔
      p.T + 1 ≤ n ∨ ∃ k, k < p.T ∧ k + 1 ≤ n ∧
        (rawHPendingNat rate rewards C_star C_h k z).Nonempty := by
  let D := rawHSupportDates rate rewards C_star C_h z
  let A := D ∪ {p.T + 1}
  have hA : A.Nonempty := ⟨p.T + 1, Finset.mem_union_right _
    (Finset.mem_singleton_self _)⟩
  change A.min' hA ≤ n ↔ _
  constructor
  · intro hle
    change A.min' hA ≤ n at hle
    have hminmem : A.min' hA ∈ A := Finset.min'_mem A hA
    rcases Finset.mem_union.mp hminmem with hd | hterminal
    · rcases (rawHSupportDates_mem_iff rate rewards C_star C_h z _).mp hd with
        ⟨k, hk, hdate, hpending⟩
      right
      refine ⟨k, hk, ?_, hpending⟩
      rw [← hdate]
      exact hle
    · left
      simp only [Finset.mem_singleton] at hterminal
      rw [← hterminal]
      exact hle
  · rintro (hterminal | ⟨k, hk, hleDate, hpending⟩)
    · exact (Finset.min'_le A _
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))).trans hterminal
    · have hdate : k + 1 ∈ rawHSupportDates rate rewards C_star C_h z :=
        (rawHSupportDates_mem_iff rate rewards C_star C_h z (k + 1)).mpr
          ⟨k, hk, rfl, hpending⟩
      exact (Finset.min'_le A _ (Finset.mem_union_left _ hdate)).trans hleDate

theorem rawHSigma_le_sourcePrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (_hn : n ≤ p.T) (z : SourceInput p) :
    (rawHSigma rate rewards C_star C_h z ≤ n) =
      (rawHSigma rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ≤ n) := by
  apply propext
  rw [rawHSigma_le_iff rate rewards C_star C_h z n,
    rawHSigma_le_iff rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) n]
  constructor
  · rintro (hterminal | ⟨k, hk, hdate, hpending⟩)
    · exact Or.inl hterminal
    · right
      refine ⟨k, hk, hdate, ?_⟩
      have hfactor := rawHPendingNat_factor_of_prefix rate rewards C_star C_h
        control0 k n (by omega) hk z
      rw [← hfactor]
      exact hpending
  · rintro (hterminal | ⟨k, hk, hdate, hpending⟩)
    · exact Or.inl hterminal
    · right
      refine ⟨k, hk, hdate, ?_⟩
      have hfactor := rawHPendingNat_factor_of_prefix rate rewards C_star C_h
        control0 k n (by omega) hk z
      rw [hfactor]
      exact hpending

theorem rawHSigma_preRoundStoppingTime
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (rawHSigma rate rewards C_star C_h) := by
  intro n
  by_cases hterminal : p.T + 1 ≤ n
  · have heq : {z : SourceInput p | rawHSigma rate rewards C_star C_h z ≤ n} =
        Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (rawHSigma_le_iff rate rewards C_star C_h z n).2 (Or.inl hterminal)
    rw [heq]
    exact MeasurableSet.univ
  · have hn : n ≤ p.T := by omega
    have heq : {z : SourceInput p | rawHSigma rate rewards C_star C_h z ≤ n} =
        ⋃ k : Fin n,
          {z : SourceInput p | (rawHPendingNat rate rewards C_star C_h k.val z).Nonempty} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      rw [rawHSigma_le_iff]
      constructor
      · rintro (hterminal | ⟨k, hk, hdate, hpending⟩)
        · omega
        · exact ⟨⟨k, by omega⟩, hpending⟩
      · rintro ⟨k, hpending⟩
        exact Or.inr ⟨k.val, by omega, by omega, hpending⟩
    rw [heq]
    exact MeasurableSet.iUnion fun k => by
      have hkT : k.val < p.T := lt_of_lt_of_le k.isLt hn
      have hbase := rawHPendingNat_nonempty_measurableSet
        rate rewards C_star C_h control0 k.val hkT
      have hmono := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0).mono (show k.val + 1 ≤ n by omega)
      exact hmono _ hbase

theorem rawHRecord_pending_nonempty (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ rawHRecords rate rewards C_star C_h z) :
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice.Nonempty := by
  by_cases hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z = []
  · have hnil := rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z hK
    rw [hnil] at hr
    cases hr
  · cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
    | none =>
        have hnil := rawHRecords_eq_nil_of_endpoint_none
          rate rewards C_star C_h z hK hb
        rw [hnil] at hr
        cases hr
    | some birth =>
        rw [rawHRecords_eq_actualH_of_endpoint
          rate rewards C_star C_h z hK birth hb] at hr
        have hmissing := List.mem_takeWhile_imp hr
        unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice at hmissing
        cases hs : r.output.preparation.coordinator.selection with
        | none => simp [hs] at hmissing
        | some selected =>
            simp only [hs, decide_eq_true_eq] at hmissing
            exact ⟨selected, rfl, hmissing⟩

/-- `rawHSupportDates` is precisely the one-based time projection of actual
H records. Each such record's choice-time set is nonempty by the literal
`takeWhile missingAtChoice` construction. -/
theorem rawHSupportDates_mem_actualRecord (z : SourceInput p) (d : ℕ) :
    d ∈ rawHSupportDates rate rewards C_star C_h z ↔
      ∃ r ∈ rawHRecords rate rewards C_star C_h z,
        d = r.input.time.val + 1 := by
  constructor
  · intro hd
    rcases (rawHSupportDates_mem_iff rate rewards C_star C_h z d).mp hd with
      ⟨k, hk, hdate, hpending⟩
    rcases (rawHPendingNat_nonempty_iff rate rewards C_star C_h z k).mp hpending with
      ⟨hk', i, hsupport⟩
    have hkEq : hk' = hk := Subsingleton.elim _ _
    subst hk'
    rcases hsupport with ⟨r, hr, htime, _selected, _hselection, _hi⟩
    refine ⟨r, hr, ?_⟩
    have ht := congrArg Fin.val htime
    change r.input.time.val = k at ht
    rw [hdate]
    omega
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨selected, hs, hne⟩ := rawHRecord_pending_nonempty rate rewards C_star C_h z r hr
    obtain ⟨i, hi⟩ := hne
    let t := r.input.time
    have hsupport : rawHTaskSupport rate rewards C_star C_h t i z :=
      ⟨r, hr, rfl, selected, hs, hi⟩
    have hpending := (rawHPendingNat_nonempty_iff rate rewards C_star C_h z t.val).mpr
      ⟨t.isLt, i, hsupport⟩
    exact (rawHSupportDates_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
      ⟨t.val, t.isLt, rfl, hpending⟩

private theorem rawH_record_ge_birth_date (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ rawHRecords rate rewards C_star C_h z) :
    birth.input.time.val ≤ r.input.time.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := rawKEndpointIndex rate rewards C_star C_h z +
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
  let start := a + 1
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z start
  have hrecords := rawHRecords_eq_actualH_of_endpoint
    rate rewards C_star C_h z hK birth hbirth
  rw [hrecords] at hr
  have hmem : r ∈ birth :: W :=
    (List.takeWhile_prefix
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).sublist.subset hr
  rcases List.mem_cons.mp hmem with heq | htail
  · rw [heq]
  · obtain ⟨j, hj, hrow⟩ := List.mem_iff_getElem.mp htail
    have hjW : j < W.length := by
      simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hj
    have hlen : W.length ≤ R.length - start := by
      have hlen' := (List.takeWhile_prefix
        (l := R.drop start)
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
      simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
        R, List.length_drop] using hlen'
    have hstartLt : start < R.length := by omega
    let b : Fin R.length := ⟨start, hstartLt⟩
    have hindex : start + j < R.length := by omega
    have hrowPrefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
      rewards C_star C_h z b j hjW
    have hrow' : W[j] = R[start + j]'hindex := by
      simpa only [W, b, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hrowPrefix
    have hrecord : r = R[start + j]'hindex := hrow.symm.trans hrow'
    have hbirthLookup : R[a]? = some birth := by
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[rawKEndpointIndex rate rewards C_star C_h z +
          (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
            rate rewards C_star C_h z).length]? = some birth at hbirth
      simpa only [R, a] using hbirth
    obtain ⟨ha, hbirthEq⟩ := List.getElem?_eq_some_iff.mp hbirthLookup
    have hbirthTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z ⟨a, ha⟩
    have hrowTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z ⟨start + j, hindex⟩
    have hrowRecordTime : r.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          (start + j) := by
      have htimeEq := congrArg (fun rr : ReferenceActivePhysicalHorizon.RoundRecord =>
        rr.input.time.val) hrecord
      rw [htimeEq]
      exact hrowTime
    have hbirthRecordTime : birth.input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a := by
      have htimeEq := congrArg (fun rr : ReferenceActivePhysicalHorizon.RoundRecord =>
        rr.input.time.val) hbirthEq
      rw [← htimeEq]
      exact hbirthTime
    omega

/-- On a reached actual H segment, the first supported source date is the
same rawK endpoint record's original calendar date. -/
theorem rawHSigma_eq_birth_time_succ (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    rawHSigma rate rewards C_star C_h z = birth.input.time.val + 1 := by
  let i : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
  have hbirthTask := rawH_birthTaskSupport rate rewards C_star C_h z i birth hK hbirth
  have hbirthPending := (rawHPendingNat_nonempty_iff rate rewards C_star C_h z
    birth.input.time.val).mpr ⟨birth.input.time.isLt, i, hbirthTask⟩
  have hbirthDate : birth.input.time.val + 1 ∈
      rawHSupportDates rate rewards C_star C_h z :=
    (rawHSupportDates_mem_iff rate rewards C_star C_h z _).mpr
      ⟨birth.input.time.val, birth.input.time.isLt, rfl, hbirthPending⟩
  let A := rawHSupportDates rate rewards C_star C_h z ∪ {p.T + 1}
  have hA : A.Nonempty := ⟨p.T + 1, Finset.mem_union_right _
    (Finset.mem_singleton_self _)⟩
  have hminmem : A.min' hA ∈ A := Finset.min'_mem A hA
  have hminle : A.min' hA ≤ birth.input.time.val + 1 :=
    Finset.min'_le A _ (Finset.mem_union_left _ hbirthDate)
  have hbirthLower : birth.input.time.val + 1 ≤ A.min' hA := by
    rcases Finset.mem_union.mp hminmem with hd | hsentinel
    · have hd' := (rawHSupportDates_mem_actualRecord rate rewards C_star C_h z
          (A.min' hA)).mp hd
      rcases hd' with ⟨record, hrecord, hdate⟩
      have htime := rawH_record_ge_birth_date rate rewards C_star C_h z
        hK birth hbirth record hrecord
      rw [hdate]
      omega
    · simp only [Finset.mem_singleton] at hsentinel
      rw [hsentinel]
      have hbt := birth.input.time.isLt
      omega
  unfold rawHSigma
  change A.min' hA = birth.input.time.val + 1
  omega

private theorem rawH_recordAt_index_date (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (j : ℕ) (hj : j < (rawHRecords rate rewards C_star C_h z).length) :
    (rawHRecords rate rewards C_star C_h z)[j].input.time.val =
      birth.input.time.val + j := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := rawKEndpointIndex rate rewards C_star C_h z +
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
  let start := a + 1
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z start
  let V := birth :: W
  have hrecords := rawHRecords_eq_actualH_of_endpoint
    rate rewards C_star C_h z hK birth hbirth
  have hlen : (rawHRecords rate rewards C_star C_h z).length ≤ V.length := by
    rw [hrecords]
    exact (List.takeWhile_prefix
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le
  have hjV : j < V.length := by omega
  have hjTake : j < (V.takeWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length := by
    simpa only [V, hrecords] using hj
  have hrow : (rawHRecords rate rewards C_star C_h z)[j] = V[j]'hjV := by
    have h := (List.takeWhile_prefix
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).getElem hjTake
    simpa only [V, hrecords] using h
  cases j with
  | zero =>
      have htime := congrArg
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.time.val) hrow
      simpa only [V, List.getElem_cons_zero, Nat.add_zero] using htime
  | succ j =>
      have hjW : j < W.length := by
        have hj' : j + 1 < ((birth :: W).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length := by
          simpa [hrecords, W, start] using hj
        have hlength : ((birth :: W).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length ≤
              W.length + 1 := by
          calc
            _ ≤ (birth :: W).length := (List.takeWhile_prefix
              ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le
            _ = W.length + 1 := by simp
        omega
      have hrowW : (rawHRecords rate rewards C_star C_h z)[j + 1] = W[j] := by
        have h := hrow
        simpa only [V, List.getElem_cons_succ] using h
      have hlenW : W.length ≤ R.length - start := by
        have hlen' := (List.takeWhile_prefix
          (l := R.drop start)
          ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
        simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
          R, List.length_drop] using hlen'
      have hstartLt : start < R.length := by omega
      let b : Fin R.length := ⟨start, hstartLt⟩
      have hindex : start + j < R.length := by omega
      have hprefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
        rewards C_star C_h z b j hjW
      have hrowR : W[j] = R[start + j]'hindex := by
        simpa only [W, b, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hprefix
      have hbirthLookup : R[a]? = some birth := by
        simpa only [R, a, rawKEndpointRecord?] using hbirth
      obtain ⟨ha, hbirthEq⟩ := List.getElem?_eq_some_iff.mp hbirthLookup
      have hbirthTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z ⟨a, ha⟩
      have hrowTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z ⟨start + j, hindex⟩
      have htimeEq := congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord =>
        r.input.time.val) (hrowW.trans hrowR)
      have htime : (rawHRecords rate rewards C_star C_h z)[j + 1].input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
            (start + j) := by
        rw [htimeEq]
        exact hrowTime
      have hbirthTime' : birth.input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a := by
        have htimeEq' := congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord =>
          r.input.time.val) hbirthEq
        rw [← htimeEq']
        exact hbirthTime
      rw [htime, hbirthTime']
      dsimp [start, a]
      omega

private theorem rawHRecord_eq_of_time (z : SourceInput p)
    (r s : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ rawHRecords rate rewards C_star C_h z)
    (hs : s ∈ rawHRecords rate rewards C_star C_h z)
    (ht : r.input.time = s.input.time) : r = s := by
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro h
    rw [rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z h] at hr
    cases hr
  cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
  | none =>
      rw [rawHRecords_eq_nil_of_endpoint_none rate rewards C_star C_h z hK hb] at hr
      cases hr
  | some birth =>
      obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hr
      obtain ⟨k, hk, hks⟩ := List.mem_iff_getElem.mp hs
      have hjt := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb j hj
      have hkt := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb k hk
      rw [hjr] at hjt
      rw [hks] at hkt
      have ht' := congrArg Fin.val ht
      have heq : j = k := by omega
      subst k
      exact hjr.symm.trans hks

/-- The whole finite pending set is the same actual selected set, at the
record's global source index, rather than just a membership containment. -/
theorem rawHPendingNat_eq_selected (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ rawHRecords rate rewards C_star C_h z)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    rawHPendingNat rate rewards C_star C_h r.input.time.val z =
      selected.view.pendingAtChoice := by
  ext i
  rw [rawHPendingNat_mem]
  constructor
  · rintro ⟨hk, other, ho, ht, choice, hc, hi⟩
    have htime : other.input.time = r.input.time := by
      apply Fin.ext
      exact congrArg Fin.val ht
    have heq := rawHRecord_eq_of_time rate rewards C_star C_h z other r ho hr htime
    subst other
    have hchoice := Option.some.inj (hc.symm.trans hs)
    subst choice
    exact hi
  · intro hi
    exact ⟨r.input.time.isLt, r, hr, rfl, selected, hs, hi⟩

private theorem rawH_index_complete (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (j : ℕ) (hj : j < (rawHRecords rate rewards C_star C_h z).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let a := rawKEndpointIndex rate rewards C_star C_h z +
      (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
    ∃ h : a + j < R.length, (rawHRecords rate rewards C_star C_h z)[j] = R[a + j] := by
  intro R a
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (a + 1)
  have hH : rawHRecords rate rewards C_star C_h z =
      (birth :: W).takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice :=
    rawHRecords_eq_actualH_of_endpoint rate rewards C_star C_h z hK birth hb
  have hjV : j < (birth :: W).length := by
    have hlen := (List.takeWhile_prefix (l := birth :: W)
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le
    rw [← hH] at hlen
    omega
  have hrow : (rawHRecords rate rewards C_star C_h z)[j] = (birth :: W)[j] := by
    have h := (List.takeWhile_prefix (l := birth :: W)
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).getElem (hH ▸ hj)
    simpa only [← hH] using h
  obtain ⟨ha, hbirth⟩ := List.getElem?_eq_some_iff.mp
    (show R[a]? = some birth from hb)
  cases j with
  | zero =>
      refine ⟨by omega, ?_⟩
      simpa only [Nat.add_zero, List.getElem_cons_zero, hbirth] using hrow
  | succ j =>
      have hjW : j < W.length := by
        simp only [List.length_cons] at hjV
        omega
      have hlen : W.length ≤ R.length - (a + 1) := by
        simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
          R, List.length_drop] using (List.takeWhile_prefix (l := R.drop (a + 1))
            ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest).length_le
      have hstart : a + 1 < R.length := by omega
      have hindex : a + 1 + j < R.length := by omega
      have hprefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
        rewards C_star C_h z ⟨a + 1, hstart⟩ j hjW
      have hprefix' : W[j] = R[a + 1 + j]'hindex := hprefix
      refine ⟨by omega, ?_⟩
      simpa only [List.getElem_cons_succ, hprefix', Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hrow

/-- Actual outgoing pending update, and the actual incoming pending registers
on every continuing row. The birth alternative is kept explicit. -/
theorem rawHRecord_pending_frames (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : record ∈ rawHRecords rate rewards C_star C_h z)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected) :
    ∃ (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
      (beta : Fin (p.m - 1) → ℕ),
      record.output.next.coordinator = .live next owned beta ∧
      next.pendingAtChoice =
        (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent record selected then
          selected.view.pendingAtChoice.erase (PublicDiscreteDraws.selectedFollowerDraw
            p.two_le_m p.m_lt_K (record.input.row.2 record.input.time).1)
        else selected.view.pendingAtChoice) ∧
      (record = birth ∨ ∃ (incoming : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (queues : CoordinatorLiveServiceFinish.OwnedRegisters incoming),
        record.input.state.coordinator = .live incoming queues beta ∧
        selected.view.pendingAtChoice = incoming.pendingAtChoice) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := rawKEndpointIndex rate rewards C_star C_h z +
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
  obtain ⟨ha, hbirth⟩ := List.getElem?_eq_some_iff.mp
    (show R[a]? = some birth from hb)
  let b : Fin R.length := ⟨a, ha⟩
  have hlater := rawKEndpoint_laterChosen rate rewards C_star C_h z hK birth hb
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  have hlater' : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
    simpa only [b, hbirth] using hlater
  rw [ite_eq_left hlater'] at hh
  rw [show R[b.val] = birth from hbirth] at hh
  obtain ⟨rb, qb, beta, bs, hout, _hinstall, _hlater, hbs, _hpayload,
    hfull, hafter, hno, _hfollowers, _htail, _hnorelease, hframes⟩ := hh
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (a + 1)
  have hmem : record ∈ birth :: W := by
    rw [rawHRecords_eq_actualH_of_endpoint rate rewards C_star C_h z hK birth hb] at hr
    exact (List.takeWhile_prefix
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).sublist.subset hr
  rcases List.mem_cons.mp hmem with heq | htail
  · subst record
    have hbs' : birth.output.preparation.coordinator.selection = some bs := by
      simpa only [b, hbirth] using hbs
    have heq := Option.some.inj (hbs'.symm.trans hs)
    subst selected
    refine ⟨rb, qb, beta, ?_, ?_, Or.inl rfl⟩
    · simpa only [b, hbirth] using hout
    · have hno' : ¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent birth bs := by
        simpa only [b, hbirth] using hno
      rw [ite_eq_right hno', hafter]
      simpa only [b, hbirth] using hfull.symm
  · obtain ⟨j, hj, hrow⟩ := List.mem_iff_getElem.mp htail
    have hjW : j < W.length := hj
    obtain ⟨r, q, choice, next, owned, _states, _memories, hin, _hpay, hc,
      _hcpay, hpending, hout, _hnpay, hupdate, _⟩ := hframes ⟨j, hjW⟩
    change W[j].input.state.coordinator = .live r q beta at hin
    change W[j].output.preparation.coordinator.selection = some choice at hc
    change W[j].output.next.coordinator = .live next owned beta at hout
    change next.pendingAtChoice = (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      W[j] choice then _ else _) at hupdate
    have hrow' : W[j] = record := hrow
    subst record
    have heq := Option.some.inj (hc.symm.trans hs)
    subst selected
    exact ⟨next, owned, beta, hout, hupdate, Or.inr ⟨r, q, hin, hpending⟩⟩

/-- One physical row erases exactly its selected confirmed follower, and
otherwise preserves pending. Both dates are inside the same actual H scan. -/
theorem rawHPendingNat_step (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (j : ℕ) (hj : j + 1 < (rawHRecords rate rewards C_star C_h z).length)
    (selected : ReferenceActivePhysicalStep.Selection
      (rawHRecords rate rewards C_star C_h z)[j].input)
    (hs : (rawHRecords rate rewards C_star C_h z)[j].output.preparation.coordinator.selection =
      some selected) :
    rawHPendingNat rate rewards C_star C_h (birth.input.time.val + j + 1) z =
      if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          (rawHRecords rate rewards C_star C_h z)[j] selected then
        (rawHPendingNat rate rewards C_star C_h (birth.input.time.val + j) z).erase
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((rawHRecords rate rewards C_star C_h z)[j].input.row.2
              (rawHRecords rate rewards C_star C_h z)[j].input.time).1)
      else rawHPendingNat rate rewards C_star C_h (birth.input.time.val + j) z := by
  let H := rawHRecords rate rewards C_star C_h z
  change j + 1 < H.length at hj
  have hj0 : j < H.length := by omega
  have hm0 : H[j] ∈ H := List.getElem_mem hj0
  have hm1 : H[j + 1] ∈ H := List.getElem_mem hj
  obtain ⟨next, owned, beta, hout, hupdate, _⟩ :=
    rawHRecord_pending_frames rate rewards C_star C_h z hK birth hb H[j] hm0 selected hs
  obtain ⟨choice, hc, _hne⟩ := rawHRecord_pending_nonempty
    rate rewards C_star C_h z H[j + 1] hm1
  obtain ⟨_next1, _owned1, beta1, _hout1, _hupdate1, hinput⟩ :=
    rawHRecord_pending_frames rate rewards C_star C_h z hK birth hb H[j + 1] hm1 choice hc
  have ht0 := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb j hj0
  have ht1 := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb (j + 1) hj
  rcases hinput with hbirth | ⟨incoming, queues, hin, hpending⟩
  · change H[j + 1] = birth at hbirth
    change H[j + 1].input.time.val = birth.input.time.val + (j + 1) at ht1
    rw [hbirth] at ht1
    omega
  · obtain ⟨hi0, hr0⟩ := rawH_index_complete rate rewards C_star C_h z hK birth hb j hj0
    obtain ⟨hi1, hr1⟩ := rawH_index_complete rate rewards C_star C_h z hK birth hb (j + 1) hj
    have hadj : H[j + 1].input.state = H[j].output.next := by
      rw [hr1, hr0]
      have h := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z
        (rawKEndpointIndex rate rewards C_star C_h z +
          (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length + j)
        (by simpa only [Nat.add_assoc] using hi1)
      simpa only [Nat.add_assoc] using h
    have hregs := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
      (hin.symm.trans ((congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
        state.coordinator) hadj).trans hout))).1
    have hp0 := rawHPendingNat_eq_selected rate rewards C_star C_h z H[j] hm0 selected hs
    have hp1 := rawHPendingNat_eq_selected rate rewards C_star C_h z H[j + 1] hm1 choice hc
    change rawHPendingNat rate rewards C_star C_h H[j].input.time.val z = _ at hp0
    change rawHPendingNat rate rewards C_star C_h H[j + 1].input.time.val z = _ at hp1
    change H[j].input.time.val = _ at ht0
    change H[j + 1].input.time.val = _ at ht1
    rw [ht0] at hp0
    rw [ht1, ← Nat.add_assoc] at hp1
    rw [hp0, hp1, hpending, hregs, hupdate]
    rfl

/-- Pending sets shrink forward along the original dates within one H phase.
There is no nesting claim across a later assignment's fresh initialization. -/
theorem rawHPendingNat_subset_of_active_indices (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (j k : ℕ) (hjk : j ≤ k)
    (hk : k < (rawHRecords rate rewards C_star C_h z).length) :
    rawHPendingNat rate rewards C_star C_h (birth.input.time.val + k) z ⊆
      rawHPendingNat rate rewards C_star C_h (birth.input.time.val + j) z := by
  induction k, hjk using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hjk ih =>
      have hk0 : k < (rawHRecords rate rewards C_star C_h z).length := by omega
      obtain ⟨selected, hs, _⟩ := rawHRecord_pending_nonempty rate rewards C_star C_h z
        (rawHRecords rate rewards C_star C_h z)[k] (List.getElem_mem hk0)
      have hstep := rawHPendingNat_step rate rewards C_star C_h z hK birth hb k hk selected hs
      have hsub : rawHPendingNat rate rewards C_star C_h (birth.input.time.val + (k + 1)) z ⊆
          rawHPendingNat rate rewards C_star C_h (birth.input.time.val + k) z := by
        rw [← Nat.add_assoc, hstep]
        split
        · exact Finset.erase_subset _ _
        · exact Finset.Subset.refl _
      exact hsub.trans (ih hk0)

/-- A confirmation clearing pending is the last included H row. The clearing
row itself remains included; the next physical row has no H task. -/
theorem rawH_clearing_confirmation_last (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (j : ℕ) (hj : j < (rawHRecords rate rewards C_star C_h z).length)
    (selected : ReferenceActivePhysicalStep.Selection
      (rawHRecords rate rewards C_star C_h z)[j].input)
    (hs : (rawHRecords rate rewards C_star C_h z)[j].output.preparation.coordinator.selection = some selected)
    (hconfirm : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      (rawHRecords rate rewards C_star C_h z)[j] selected)
    (hclear : selected.view.pendingAtChoice.erase
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((rawHRecords rate rewards C_star C_h z)[j].input.row.2
          (rawHRecords rate rewards C_star C_h z)[j].input.time).1) = ∅) :
    j + 1 = (rawHRecords rate rewards C_star C_h z).length := by
  by_contra hnot
  have hj1 : j + 1 < (rawHRecords rate rewards C_star C_h z).length := by omega
  have hstep := rawHPendingNat_step rate rewards C_star C_h z hK birth hb j hj1 selected hs
  have hp := rawHPendingNat_eq_selected rate rewards C_star C_h z
    (rawHRecords rate rewards C_star C_h z)[j] (List.getElem_mem hj) selected hs
  rw [rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb j hj] at hp
  rw [ite_eq_left hconfirm, hp] at hstep
  have hempty := hstep.trans hclear
  obtain ⟨choice, hc, hne⟩ := rawHRecord_pending_nonempty rate rewards C_star C_h z
    (rawHRecords rate rewards C_star C_h z)[j + 1] (List.getElem_mem hj1)
  have hp1 := rawHPendingNat_eq_selected rate rewards C_star C_h z
    (rawHRecords rate rewards C_star C_h z)[j + 1] (List.getElem_mem hj1) choice hc
  rw [rawH_recordAt_index_date rate rewards C_star C_h z hK birth hb (j + 1) hj1,
    ← Nat.add_assoc, hempty] at hp1
  rw [← hp1] at hne
  exact Finset.not_nonempty_empty hne

/-- The support dates on a reached H phase are exactly its original
consecutive calendar rows, ending before the first excluded row. -/
private theorem rawHSupportDates_mem_iff_actual_index (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (d : ℕ) :
    d ∈ rawHSupportDates rate rewards C_star C_h z ↔
      ∃ j, j < (rawHRecords rate rewards C_star C_h z).length ∧
        d = birth.input.time.val + j + 1 := by
  constructor
  · intro hd
    rcases (rawHSupportDates_mem_actualRecord rate rewards C_star C_h z d).mp hd with
      ⟨r, hr, hdate⟩
    obtain ⟨j, hj, hrow⟩ := List.mem_iff_getElem.mp hr
    refine ⟨j, hj, ?_⟩
    have htime := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hbirth j hj
    have hrowtime : r.input.time.val =
        (rawHRecords rate rewards C_star C_h z)[j].input.time.val :=
      congrArg (fun x : ReferenceActivePhysicalHorizon.RoundRecord => x.input.time.val) hrow.symm
    rw [hdate, hrowtime, htime]
  · rintro ⟨j, hj, rfl⟩
    let r := (rawHRecords rate rewards C_star C_h z)[j]
    have hr : r ∈ rawHRecords rate rewards C_star C_h z := by
      exact List.getElem_mem hj
    obtain ⟨selected, hs, hne⟩ := rawHRecord_pending_nonempty rate rewards C_star C_h z r hr
    obtain ⟨i, hi⟩ := hne
    have hsupport : rawHTaskSupport rate rewards C_star C_h r.input.time i z :=
      ⟨r, hr, rfl, selected, hs, hi⟩
    have hpending := (rawHPendingNat_nonempty_iff rate rewards C_star C_h z
      r.input.time.val).mpr ⟨r.input.time.isLt, i, hsupport⟩
    have hdate := rawH_recordAt_index_date rate rewards C_star C_h z hK birth hbirth j hj
    change r.input.time.val = birth.input.time.val + j at hdate
    exact (rawHSupportDates_mem_iff rate rewards C_star C_h z _).mpr
      ⟨r.input.time.val, r.input.time.isLt, by omega, hpending⟩

private theorem rawHTheta_eq_birthDate_add_length (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    rawHTheta rate rewards C_star C_h z =
      birth.input.time.val + 1 + (rawHRecords rate rewards C_star C_h z).length := by
  let D := rawHSupportDates rate rewards C_star C_h z
  let L := (rawHRecords rate rewards C_star C_h z).length
  have hstart : birth.input.time.val + 1 ∈ D := by
    have hbirthmem := rawH_birth_actual_pending_univ
      rate rewards C_star C_h z hK birth hbirth
    exact (rawHSupportDates_mem_actualRecord rate rewards C_star C_h z _).mpr
      ⟨birth, hbirthmem.1, rfl⟩
  have hD : D.Nonempty := ⟨birth.input.time.val + 1, hstart⟩
  have hL : 0 < L := by
    have hbmem := rawH_birth_actual_pending_univ rate rewards C_star C_h z hK birth hbirth
    have hrecords := hbmem.1
    have : (rawHRecords rate rewards C_star C_h z).length ≠ 0 := by
      intro he
      have hnil : rawHRecords rate rewards C_star C_h z = [] :=
        List.eq_nil_of_length_eq_zero he
      rw [hnil] at hrecords
      simp at hrecords
    omega
  let dLast := birth.input.time.val + L
  have hlast : dLast ∈ D := by
    apply (rawHSupportDates_mem_iff_actual_index rate rewards C_star C_h z hK birth hbirth dLast).2
    refine ⟨L - 1, by omega, ?_⟩
    dsimp [dLast]
    omega
  have hmaxle : D.max' hD ≤ dLast :=
    Finset.max'_le D hD dLast (by
      intro d hd
      rcases (rawHSupportDates_mem_iff_actual_index rate rewards C_star C_h z
        hK birth hbirth d).mp hd with ⟨j, hj, rfl⟩
      dsimp [dLast]
      omega)
  have hlastle : dLast ≤ D.max' hD := Finset.le_max' D dLast hlast
  have hmax : D.max' hD = dLast := by omega
  have hD' : (rawHSupportDates rate rewards C_star C_h z).Nonempty := by
    simpa only [D] using hD
  unfold rawHTheta
  rw [dite_eq_left hD']
  have hmax' : (rawHSupportDates rate rewards C_star C_h z).max' hD' = dLast := by
    simpa only [D] using hmax
  rw [hmax']
  dsimp [dLast, L]
  omega

/-- On the reached H branch, the actual selected pending sets occupy exactly
the consecutive original source dates from the birth through the last
takeWhile-retained choice. -/
theorem rawHPendingNat_nonempty_iff_phase_interval (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (k : ℕ) (hk : k < p.T) :
    (rawHPendingNat rate rewards C_star C_h k z).Nonempty ↔
      rawHSigma rate rewards C_star C_h z ≤ k + 1 ∧
        k + 1 < rawHTheta rate rewards C_star C_h z := by
  have hdateInterval (d : ℕ) :
      d ∈ rawHSupportDates rate rewards C_star C_h z ↔
        rawHSigma rate rewards C_star C_h z ≤ d ∧
          d < rawHTheta rate rewards C_star C_h z := by
    rw [rawHSupportDates_mem_iff_actual_index rate rewards C_star C_h z
      hK birth hbirth d,
      rawHSigma_eq_birth_time_succ rate rewards C_star C_h z hK birth hbirth,
      rawHTheta_eq_birthDate_add_length rate rewards C_star C_h z hK birth hbirth]
    let start := birth.input.time.val + 1
    let L := (rawHRecords rate rewards C_star C_h z).length
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨hstart, hend⟩
      refine ⟨d - start, ?_, ?_⟩
      · omega
      · omega
  rw [rawHPendingNat_nonempty_iff rate rewards C_star C_h z k]
  constructor
  · rintro ⟨hk', i, htask⟩
    have hkEq : hk' = hk := Subsingleton.elim _ _
    subst hk'
    have hdate : k + 1 ∈ rawHSupportDates rate rewards C_star C_h z :=
      (rawHSupportDates_mem_iff rate rewards C_star C_h z (k + 1)).mpr
        ⟨k, hk, rfl, (rawHPendingNat_nonempty_iff rate rewards C_star C_h z k).2
          ⟨hk, i, htask⟩⟩
    exact hdateInterval (k + 1) |>.mp hdate
  · rintro hinterval
    have hdate : k + 1 ∈ rawHSupportDates rate rewards C_star C_h z :=
      hdateInterval (k + 1) |>.mpr hinterval
    rcases (rawHSupportDates_mem_iff rate rewards C_star C_h z (k + 1)).mp hdate with
      ⟨j, hj, hdateEq, hpending⟩
    have hEq : j = k := by omega
    subst j
    exact (rawHPendingNat_nonempty_iff rate rewards C_star C_h z k).1 hpending

/-- Global active-date characterization. Empty, missing-endpoint, and
horizon-stop branches have both sentinels at `T + 1`; a reached H branch uses
the actual post-collection birth and takeWhile interval. -/
theorem rawHPendingNat_nonempty_iff_interval (z : SourceInput p)
    (k : ℕ) (hk : k < p.T) :
    (rawHPendingNat rate rewards C_star C_h k z).Nonempty ↔
      rawHSigma rate rewards C_star C_h z ≤ k + 1 ∧
        k + 1 < rawHTheta rate rewards C_star C_h z := by
  by_cases hD : (rawHSupportDates rate rewards C_star C_h z).Nonempty
  · obtain ⟨d, hd⟩ := hD
    obtain ⟨r, hr, _⟩ :=
      (rawHSupportDates_mem_actualRecord rate rewards C_star C_h z d).mp hd
    have hH : rawHRecords rate rewards C_star C_h z ≠ [] := by
      intro hnil
      rw [hnil] at hr
      simp at hr
    have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z ≠ [] := by
      intro hKempty
      exact hH (rawHRecords_eq_nil_of_rawK_eq_nil
        rate rewards C_star C_h z hKempty)
    cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
    | none =>
        exact (hH (rawHRecords_eq_nil_of_endpoint_none
          rate rewards C_star C_h z hK hb)).elim
    | some birth =>
        exact rawHPendingNat_nonempty_iff_phase_interval
          rate rewards C_star C_h z hK birth hb k hk
  · have hempty : rawHSupportDates rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hD
    have hsigma : rawHSigma rate rewards C_star C_h z = p.T + 1 := by
      unfold rawHSigma
      simp [hempty]
    have htheta : rawHTheta rate rewards C_star C_h z = p.T + 1 := by
      unfold rawHTheta
      simp [hempty]
    rw [hsigma, htheta]
    have hnot : ¬ (rawHPendingNat rate rewards C_star C_h k z).Nonempty := by
      intro hp
      have hd : k + 1 ∈ rawHSupportDates rate rewards C_star C_h z :=
        (rawHSupportDates_mem_iff rate rewards C_star C_h z (k + 1)).mpr
          ⟨k, hk, rfl, hp⟩
      rw [hempty] at hd
      simp at hd
    have hsentinel : ¬ (p.T + 1 ≤ k + 1 ∧ k + 1 < p.T + 1) := by omega
    exact ⟨fun hp => (hnot hp).elim, fun h => (hsentinel h).elim⟩

/-- The active interval identity also holds outside the horizon: no natural
index at or beyond `T` carries a task. -/
theorem rawHPendingNat_nonempty_iff_interval_all (z : SourceInput p) (k : ℕ) :
    (rawHPendingNat rate rewards C_star C_h k z).Nonempty ↔
      rawHSigma rate rewards C_star C_h z ≤ k + 1 ∧
        k + 1 < rawHTheta rate rewards C_star C_h z := by
  by_cases hk : k < p.T
  · exact rawHPendingNat_nonempty_iff_interval rate rewards C_star C_h z k hk
  · rw [rawHPendingNat_empty_of_ge_horizon rate rewards C_star C_h z k (by omega)]
    have hbound := (rawHTheta_bounds rate rewards C_star C_h z).2
    constructor
    · exact fun h => (Finset.not_nonempty_empty h).elim
    · intro h
      omega

private theorem rawHSigma_eq_sentinel_of_support_empty (z : SourceInput p)
    (hempty : rawHSupportDates rate rewards C_star C_h z = ∅) :
    rawHSigma rate rewards C_star C_h z = p.T + 1 := by
  unfold rawHSigma
  simp [hempty]

private theorem rawHTheta_eq_sentinel_of_support_empty (z : SourceInput p)
    (hempty : rawHSupportDates rate rewards C_star C_h z = ∅) :
    rawHTheta rate rewards C_star C_h z = p.T + 1 := by
  unfold rawHTheta
  simp [hempty]

theorem rawHSigma_le_rawHTheta (z : SourceInput p) :
    rawHSigma rate rewards C_star C_h z ≤ rawHTheta rate rewards C_star C_h z := by
  by_cases hD : (rawHSupportDates rate rewards C_star C_h z).Nonempty
  · let D := rawHSupportDates rate rewards C_star C_h z
    let A := D ∪ {p.T + 1}
    have hA : A.Nonempty := ⟨p.T + 1, Finset.mem_union_right _
      (Finset.mem_singleton_self _)⟩
    have hmin : A.min' hA ≤ D.max' hD :=
      Finset.min'_le A _ (Finset.mem_union_left _ (Finset.max'_mem D hD))
    unfold rawHSigma rawHTheta
    rw [dite_eq_left hD]
    exact Nat.le_succ_of_le hmin
  · have hempty : rawHSupportDates rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hD
    rw [rawHSigma_eq_sentinel_of_support_empty rate rewards C_star C_h z hempty,
      rawHTheta_eq_sentinel_of_support_empty rate rewards C_star C_h z hempty]

theorem rawHTheta_le_iff_current_empty (z : SourceInput p) (n : ℕ)
    (hn : 1 ≤ n) (hnT : n ≤ p.T) :
    rawHTheta rate rewards C_star C_h z ≤ n ↔
      rawHSigma rate rewards C_star C_h z ≤ n ∧
        ¬ (rawHPendingNat rate rewards C_star C_h (n - 1) z).Nonempty := by
  by_cases hD : (rawHSupportDates rate rewards C_star C_h z).Nonempty
  · obtain ⟨d, hd⟩ := hD
    obtain ⟨r, hr, _⟩ :=
      (rawHSupportDates_mem_actualRecord rate rewards C_star C_h z d).mp hd
    have hH : rawHRecords rate rewards C_star C_h z ≠ [] := by
      intro hnil
      rw [hnil] at hr
      simp at hr
    have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z ≠ [] := by
      intro hKempty
      have hnil := rawHRecords_eq_nil_of_rawK_eq_nil
        rate rewards C_star C_h z hKempty
      exact hH hnil
    cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
    | none =>
        have hnil := rawHRecords_eq_nil_of_endpoint_none
          rate rewards C_star C_h z hK hb
        exact (hH hnil).elim
    | some birth =>
        have hsigma := rawHSigma_eq_birth_time_succ
          rate rewards C_star C_h z hK birth hb
        have htheta := rawHTheta_eq_birthDate_add_length
          rate rewards C_star C_h z hK birth hb
        have hinterval := rawHPendingNat_nonempty_iff_phase_interval
          rate rewards C_star C_h z hK birth hb (n - 1) (by omega)
        constructor
        · intro hthetaLe
          have hsigmaLe : rawHSigma rate rewards C_star C_h z ≤ n :=
            (rawHSigma_le_rawHTheta rate rewards C_star C_h z).trans hthetaLe
          refine ⟨hsigmaLe, ?_⟩
          intro hpending
          have hactive := hinterval.mp hpending
          have hdate : n - 1 + 1 = n := by omega
          rw [hdate] at hactive
          omega
        · rintro ⟨hsigmaLe, hpendingEmpty⟩
          by_contra hnot
          have hpending : (rawHPendingNat rate rewards C_star C_h (n - 1) z).Nonempty :=
            hinterval.mpr ⟨by omega, by omega⟩
          exact hpendingEmpty hpending
  · have hempty : rawHSupportDates rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hD
    rw [rawHTheta_eq_sentinel_of_support_empty rate rewards C_star C_h z hempty,
      rawHSigma_eq_sentinel_of_support_empty rate rewards C_star C_h z hempty]
    omega

/-- Complete endpoint event identity for every natural date, including zero,
the horizon sentinel, and dates beyond the physical horizon. -/
theorem rawHTheta_le_event_iff (z : SourceInput p) (n : ℕ) :
    rawHTheta rate rewards C_star C_h z ≤ n ↔
      p.T + 1 ≤ n ∨
        (1 ≤ n ∧ n ≤ p.T ∧ rawHSigma rate rewards C_star C_h z ≤ n ∧
          ¬ (rawHPendingNat rate rewards C_star C_h (n - 1) z).Nonempty) := by
  by_cases hterminal : p.T + 1 ≤ n
  · constructor
    · intro _
      exact Or.inl hterminal
    · intro _
      exact (rawHTheta_bounds rate rewards C_star C_h z).2.trans hterminal
  · have hnT : n ≤ p.T := by omega
    by_cases hzero : n = 0
    · have hfalse : ¬ rawHTheta rate rewards C_star C_h z ≤ n := by
        have hpos := (rawHTheta_bounds rate rewards C_star C_h z).1
        omega
      constructor
      · exact fun h => (hfalse h).elim
      · rintro (hterm | ⟨hpos, _, _, _⟩)
        · exact (hterminal hterm).elim
        · omega
    · have hn : 1 ≤ n := by omega
      rw [rawHTheta_le_iff_current_empty rate rewards C_star C_h z n hn hnT]
      constructor
      · intro h
        exact Or.inr ⟨hn, hnT, h.1, h.2⟩
      · rintro (hterm | ⟨_, _, hsigma, hpending⟩)
        · exact (hterminal hterm).elim
        · exact ⟨hsigma, hpending⟩

/-- Endpoint events at a deterministic date factor through the original
strict-past source prefix. -/
theorem rawHTheta_le_sourcePrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    (rawHTheta rate rewards C_star C_h z ≤ n) =
      (rawHTheta rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ≤ n) := by
  apply propext
  rw [rawHTheta_le_event_iff rate rewards C_star C_h z n,
    rawHTheta_le_event_iff rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) n]
  have hterm : ¬ p.T + 1 ≤ n := by omega
  simp only [hterm, false_or]
  constructor
  · rintro ⟨hnpos, hnT, hsigma, hpending⟩
    have hfactor := rawHPendingNat_factor_of_prefix rate rewards C_star C_h
      control0 (n - 1) n (by omega) (by omega) z
    refine ⟨hnpos, hnT, ?_, ?_⟩
    · rw [← rawHSigma_le_sourcePrefix_factor rate rewards C_star C_h control0 n hn z]
      exact hsigma
    · rw [← hfactor]
      exact hpending
  · rintro ⟨hnpos, hnT, hsigma, hpending⟩
    have hfactor := rawHPendingNat_factor_of_prefix rate rewards C_star C_h
      control0 (n - 1) n (by omega) (by omega) z
    refine ⟨hnpos, hnT, ?_, ?_⟩
    · rw [rawHSigma_le_sourcePrefix_factor rate rewards C_star C_h control0 n hn z]
      exact hsigma
    · rw [hfactor]
      exact hpending

/-- Exact first-occurrence event at every physical source date. -/
theorem rawHSigma_eq_iff_first_pending (z : SourceInput p) (k : ℕ) (hk : k < p.T) :
    rawHSigma rate rewards C_star C_h z = k + 1 ↔
      (rawHPendingNat rate rewards C_star C_h k z).Nonempty ∧
        ∀ j < k, rawHPendingNat rate rewards C_star C_h j z = ∅ := by
  constructor
  · intro hs
    obtain hterm | ⟨l, hlT, hl, hp⟩ :=
      (rawHSigma_le_iff rate rewards C_star C_h z (k + 1)).mp (by omega)
    · omega
    · have hsle := (rawHSigma_le_iff rate rewards C_star C_h z (l + 1)).mpr
        (Or.inr ⟨l, hlT, le_rfl, hp⟩)
      have hlk : l = k := by omega
      subst l
      refine ⟨hp, ?_⟩
      intro j hj
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hpj
      have hsle := (rawHSigma_le_iff rate rewards C_star C_h z (j + 1)).mpr
        (Or.inr ⟨j, by omega, le_rfl, hpj⟩)
      omega
  · rintro ⟨hp, hbefore⟩
    have hsle := (rawHSigma_le_iff rate rewards C_star C_h z (k + 1)).mpr
      (Or.inr ⟨k, hk, le_rfl, hp⟩)
    by_contra hne
    have hsmall : rawHSigma rate rewards C_star C_h z ≤ k := by omega
    obtain hterm | ⟨j, _hjT, hj, hpj⟩ :=
      (rawHSigma_le_iff rate rewards C_star C_h z k).mp hsmall
    · omega
    · rw [hbefore j (by omega)] at hpj
      exact Finset.not_nonempty_empty hpj

/-- Localization at a deterministic start date factors through the same
original source prefix, including the zero-date event. -/
theorem rawHSigma_eq_sourcePrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    (rawHSigma rate rewards C_star C_h z = n) =
      (rawHSigma rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) = n) := by
  have hpos := (rawHSigma_bounds rate rewards C_star C_h z).1
  have hpos' := (rawHSigma_bounds rate rewards C_star C_h
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).1
  have hnow := rawHSigma_le_sourcePrefix_factor rate rewards C_star C_h control0 n hn z
  have hpast := rawHSigma_le_sourcePrefix_factor rate rewards C_star C_h control0
    (n - 1) (by omega) z
  have hprefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 (n - 1) n (by omega) z
  have hpast' := rawHSigma_le_sourcePrefix_factor rate rewards C_star C_h control0
    (n - 1) (by omega)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)
  rw [hprefix] at hpast'
  apply propext
  have hle := Eq.to_iff hnow
  have hlt := (Eq.to_iff hpast).trans (Eq.to_iff hpast').symm
  omega

/-- After this actual H start, pending can only shrink at later global source
indices. Empty endpoint, cutoff and out-of-horizon branches are included. -/
theorem rawHPendingNat_subset_after_start (z : SourceInput p)
    (j k : ℕ) (hjk : j ≤ k)
    (hstart : rawHSigma rate rewards C_star C_h z ≤ j + 1) :
    rawHPendingNat rate rewards C_star C_h k z ⊆
      rawHPendingNat rate rewards C_star C_h j z := by
  by_cases hempty : rawHPendingNat rate rewards C_star C_h k z = ∅
  · rw [hempty]
    exact Finset.empty_subset _
  have hp := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hk, i, hi⟩ := (rawHPendingNat_nonempty_iff rate rewards C_star C_h z k).mp hp
  obtain ⟨r, hr, _ht, _⟩ := hi
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro h
    rw [rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z h] at hr
    cases hr
  cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
  | none =>
      rw [rawHRecords_eq_nil_of_endpoint_none rate rewards C_star C_h z hK hb] at hr
      cases hr
  | some birth =>
      have hs := rawHSigma_eq_birth_time_succ rate rewards C_star C_h z hK birth hb
      have he := rawHTheta_eq_birthDate_add_length rate rewards C_star C_h z hK birth hb
      have hactive := (rawHPendingNat_nonempty_iff_interval rate rewards C_star C_h z k hk).mp hp
      have hbj : birth.input.time.val ≤ j := by omega
      have hbk : birth.input.time.val ≤ k := by omega
      have hindex : k - birth.input.time.val < (rawHRecords rate rewards C_star C_h z).length := by omega
      have hsub := rawHPendingNat_subset_of_active_indices rate rewards C_star C_h z hK birth hb
        (j - birth.input.time.val) (k - birth.input.time.val) (Nat.sub_le_sub_right hjk _) hindex
      simpa only [Nat.add_sub_of_le hbj, Nat.add_sub_of_le hbk] using hsub

/-- The first excluded H endpoint is adapted to the original strict source
prefix. The event at date `n` is determined by the current choice-time pending
set; the future H scan length is not used as data. -/
theorem rawHTheta_preRoundStoppingTime
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (rawHTheta rate rewards C_star C_h) := by
  intro n
  by_cases hterminal : p.T + 1 ≤ n
  · have heq : {z : SourceInput p | rawHTheta rate rewards C_star C_h z ≤ n} =
        Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (rawHTheta_bounds rate rewards C_star C_h z).2.trans hterminal
    rw [heq]
    exact MeasurableSet.univ
  · by_cases hzero : n = 0
    · have heq : {z : SourceInput p | rawHTheta rate rewards C_star C_h z ≤ n} =
          ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hle
        have hpos := (rawHTheta_bounds rate rewards C_star C_h z).1
        omega
      rw [heq]
      rw [hzero]
      exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 0).measurableSet_empty
    · have hn : 1 ≤ n := by omega
      have hnT : n ≤ p.T := by omega
      have heq : {z : SourceInput p | rawHTheta rate rewards C_star C_h z ≤ n} =
          {z : SourceInput p | rawHSigma rate rewards C_star C_h z ≤ n} ∩
            {z : SourceInput p | ¬ (rawHPendingNat rate rewards C_star C_h (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact rawHTheta_le_iff_current_empty rate rewards C_star C_h z n hn hnT
      rw [heq]
      apply MeasurableSet.inter
      · exact rawHSigma_preRoundStoppingTime rate rewards C_star C_h control0 n
      · have hpending := rawHPendingNat_nonempty_measurableSet
          rate rewards C_star C_h control0 (n - 1) (by omega)
        have hmono := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0).mono (show (n - 1) + 1 ≤ n by omega)
        exact hmono _ hpending |>.compl

end Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseEndpoints

end
