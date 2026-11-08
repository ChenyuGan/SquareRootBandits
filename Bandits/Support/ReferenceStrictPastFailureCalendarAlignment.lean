/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAwaitedDownDecoderErrorProbability
import Lean.Elab.Tactic.Omega

/-!
# Strict-past failure calendar alignment

The actual source lookup and the physical postlaunch suffix use different
coordinates. This module aligns them through literal suffix timestamps, then
applies the alignment to the existing failure readouts and UP-only diagnostic
tail.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open MeasureTheory

namespace Bandits.Support.ReferenceStrictPastFailureCalendarAlignment

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The original source carrier used by the physical calendar. -/
abbrev Z := BootstrapPrivateRoundStreams.SourceInput p

/-- A record in the same complete physical suffix as the source lookup. -/
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem completeSuffixRecord_get_time (z : Z (p := p)) (k : ℕ)
    (hk : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
        ⟨k, hk⟩).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[k]?) htimes
  have hk' : k < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
  have hrange := List.getElem?_range'
    (s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (step := 1) hk'
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem hk, hrange] using hget

/-- Exact strict-past alignment for every literal predicate on physical
records. The suffix index is natural subtraction, and its timestamp is
recovered from completeSuffixRecords_time_values, not from membership alone.
-/
theorem actualRecord_calendarPrefix_exists_iff
    (z : Z (p := p)) (n : ℕ) (P : Record (p := p) (rate := rate) → Prop) :
    (∃ t : Fin p.T, ∃ r : Record (p := p) (rate := rate),
      t.val < n ∧
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t z = some r ∧ P r) ↔
      ∃ r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h),
        P r := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let L := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hsT : s ≤ p.T := by
    dsimp [s]
    exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hlen : L.length = p.T - s := by
    dsimp [L, s]
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  constructor
  · rintro ⟨t, r, htn, hactual, hP⟩
    by_cases hs : s ≤ t.val
    · let k := t.val - s
      have hlookup : L[k]? = some r := by
        change (if s ≤ t.val then L[t.val - s]? else none) = some r at hactual
        rw [ite_eq_left hs] at hactual
        simpa [k] using hactual
      obtain ⟨hk, hget⟩ := (List.getElem?_eq_some_iff.mp hlookup)
      have hstamp := completeSuffixRecord_get_time rate rewards C_star C_h z k
        (by simpa only [L] using hk)
      have hdate : t.val = s + k := by
        dsimp [k]
        omega
      have hrtime : r.input.time.val = s + k := by
        rw [← hget]
        exact hstamp
      have hrbefore : r.input.time.val < n := by
        rw [hrtime, ← hdate]
        exact htn
      have hkPast : k < n - s := by
        dsimp only [s] at hdate hrtime hrbefore ⊢
        omega
      have htake : k < (L.take (n - s)).length := by
        rw [List.length_take]
        exact Nat.lt_min.mpr ⟨hkPast, hk⟩
      have hmem : r ∈ L.take (n - s) := by
        apply List.mem_iff_getElem.mpr
        refine ⟨k, htake, ?_⟩
        exact (List.getElem_take' hk hkPast).symm.trans hget
      exact ⟨r, hmem, hP⟩
    · change (if s ≤ t.val then L[t.val - s]? else none) = some r at hactual
      rw [ite_eq_right hs] at hactual
      cases hactual
  · rintro ⟨r, hmem, hP⟩
    obtain ⟨k, hkTake, hgetTake⟩ := List.mem_iff_getElem.mp hmem
    have hbounds : k < n - s ∧ k < L.length := by
      rw [List.length_take] at hkTake
      exact Nat.lt_min.mp hkTake
    have hget : L[k] = r := by
      simpa only [List.getElem_take] using hgetTake
    have hkT : k < p.T - s := by
      simpa only [hlen] using hbounds.2
    have hkL : k < L.length := by
      simpa only [hlen] using hkT
    have htimeLt : s + k < p.T := by omega
    have htn : s + k < n := by
      dsimp only [s] at hbounds ⊢
      omega
    have hlookup :
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord rate rewards C_star C_h
            ⟨s + k, htimeLt⟩ z = some r := by
      change (if s ≤ (⟨s + k, htimeLt⟩ : Fin p.T).val then
        L[(⟨s + k, htimeLt⟩ : Fin p.T).val - s]? else none) = some r
      have hle : s ≤ (⟨s + k, htimeLt⟩ : Fin p.T).val := by
        change s ≤ s + k
        omega
      rw [ite_eq_left hle]
      rw [show (⟨s + k, htimeLt⟩ : Fin p.T).val - s = k by simp]
      rw [List.getElem?_eq_getElem hkL, hget]
    exact ⟨⟨s + k, htimeLt⟩, r, htn, hlookup, hP⟩

/-- At zero, below the physical start, or exactly at the physical start, the
strict-past lookup is empty. This uses n - s = 0, including no-launch and
terminal-start branches where the complete suffix is empty.
-/
theorem actualRecord_calendarPrefix_empty_of_le_start
    (z : Z (p := p)) (n : ℕ)
    (P : Record (p := p) (rate := rate) → Prop)
    (hn : n ≤ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    ¬ ∃ t : Fin p.T, ∃ r : Record (p := p) (rate := rate),
      t.val < n ∧
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t z = some r ∧ P r := by
  intro h
  have halign := (actualRecord_calendarPrefix_exists_iff
    rate rewards C_star C_h z n P).1 h
  obtain ⟨r, hr, _⟩ := halign
  have htake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) = [] := by
    simp [Nat.sub_eq_zero_of_le hn]
  rw [htake] at hr
  simp at hr

/-- Once the strict-past boundary reaches the horizon, taking the suffix
prefix saturates at the actual suffix length, which may be zero.
-/
theorem completeSuffixRecords_take_eq_of_horizon_le
    (z : Z (p := p)) (n : ℕ)
    (hn : p.T ≤ n) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
  apply (List.take_eq_self_iff _).2
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  omega

/-- No corrected launch means that the actual complete physical suffix is
empty, so no fictitious record at T enters the finite calendar.
-/
theorem completeSuffixRecords_eq_nil_of_no_launch
    (z : Z (p := p))
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h = [] := by
  have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate z rewards C_star C_h hno
  have hlen :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length = 0 := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hs]
    exact Nat.sub_self _
  exact List.length_eq_zero_iff.mp hlen

/-- A physical start at the terminal boundary likewise has an empty suffix,
including a launch whose start is T.
-/
theorem completeSuffixRecords_eq_nil_of_terminal_start
    (z : Z (p := p))
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h = [] := by
  have hlen :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length = 0 := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
    exact Nat.sub_self _
  exact List.length_eq_zero_iff.mp hlen

/-- Expand the existing saved-wrong record predicate into its literal UP and
DOWN diagnostics inside the already defined saved-wrong suffix event.
-/
theorem savedWrongSuffixPrefixEvent_expanded
    (z : Z (p := p)) (prefixCount : ℕ) :
    z ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        rate rewards C_star C_h prefixCount ↔
      (∃ r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take prefixCount,
        ∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true) ∨
      (∃ r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take prefixCount,
        ∃ i cut, (r.output.followers i).down = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut) := by
  rw [ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent_true_iff]
  constructor
  · rintro ⟨r, hr, hwrong⟩
    change (∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true) ∨
      (∃ i cut, (r.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) at hwrong
    rcases hwrong with hup | hdown
    · exact Or.inl ⟨r, hr, hup⟩
    · exact Or.inr ⟨r, hr, hdown⟩
  · rintro (⟨r, hr, hup⟩ | ⟨r, hr, hdown⟩)
    · exact ⟨r, hr, Or.inl hup⟩
    · exact ⟨r, hr, Or.inr hdown⟩

private theorem savedWrongCalendarPrefix_iff
    (z : Z (p := p)) (n : ℕ) :
    (∃ t : Fin p.T, ∃ r : Record (p := p) (rate := rate),
      t.val < n ∧
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t z = some r ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r) ↔
      z ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        rate rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
  rw [actualRecord_calendarPrefix_exists_iff rate rewards C_star C_h z n
    (fun r => ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r)]
  rw [savedWrongSuffixPrefixEvent_expanded rate rewards C_star C_h z
    (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)]
  constructor
  · rintro ⟨r, hr, hwrong⟩
    change (∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true) ∨
      (∃ i cut, (r.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) at hwrong
    rcases hwrong with hup | hdown
    · exact Or.inl ⟨r, hr, hup⟩
    · exact Or.inr ⟨r, hr, hdown⟩
  · rintro (⟨r, hr, hup⟩ | ⟨r, hr, hdown⟩)
    · exact ⟨r, hr, Or.inl hup⟩
    · exact ⟨r, hr, Or.inr hdown⟩

/-- Exact identity for the actual strict-past flag: saved wrong, fixed-awaited
DOWN, and the existing fixed-awaited UP event retain their separate meanings.
-/
theorem pastFailureFlag_true_iff
    (z : Z (p := p)) (n : ℕ) :
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n z = true ↔
      z ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        rate rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∨
      (∃ t : Fin p.T, t.val < n ∧
        ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
          rate rewards C_star C_h z t) ∨
      (∃ t : Fin p.T, t.val < n ∧
        ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
          rate rewards C_star C_h z t) := by
  classical
  change (decide (∃ t : Fin p.T, t.val < n ∧
    ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
      rate rewards C_star C_h z t) = true) ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, hfailure⟩
    rcases hfailure with ⟨r, hactual, hwrong⟩ | hdown | hup
    · exact Or.inl (savedWrongCalendarPrefix_iff
        rate rewards C_star C_h z n |>.mp ⟨t, r, ht, hactual, hwrong⟩)
    · exact Or.inr (Or.inl ⟨t, ht, hdown⟩)
    · exact Or.inr (Or.inr ⟨t, ht, hup⟩)
  · rintro (hsaved | hdown | hup)
    · obtain ⟨t, r, ht, hactual, hwrong⟩ :=
        (savedWrongCalendarPrefix_iff rate rewards C_star C_h z n).mpr hsaved
      exact ⟨t, ht, Or.inl ⟨r, hactual, hwrong⟩⟩
    · obtain ⟨t, ht, hfailure⟩ := hdown
      exact ⟨t, ht, Or.inr (Or.inl hfailure)⟩
    · obtain ⟨t, ht, hfailure⟩ := hup
      exact ⟨t, ht, Or.inr (Or.inr hfailure)⟩

/-- Inclusive detecting-round specialization: the strict-past readout at
t.val + 1 includes the update on round t itself.
-/
theorem pastFailureFlag_inclusive_round_iff
    (z : Z (p := p)) (t : Fin p.T) :
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h (t.val + 1) z = true ↔
      z ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        rate rewards C_star C_h
        (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∨
      (∃ u : Fin p.T, u.val < t.val + 1 ∧
        ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
          rate rewards C_star C_h z u) ∨
      (∃ u : Fin p.T, u.val < t.val + 1 ∧
        ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
          rate rewards C_star C_h z u) := by
  exact pastFailureFlag_true_iff rate rewards C_star C_h z (t.val + 1)

/-- The literal UP-only saved diagnostic on an actual strict-past calendar
round. Absent diagnostics, including no-selection rounds, produce no witness.
-/
def upWrongCalendarEvent (n : ℕ) : Set (Z (p := p)) :=
  {z | ∃ t : Fin p.T, ∃ r : Record (p := p) (rate := rate),
    t.val < n ∧
      ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
          rate rewards C_star C_h t z = some r ∧
        ∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true}

/-- Calendar existence of the literal UP diagnostic is exactly the existing
generated-UP wrong suffix-prefix event at the shifted count n - s.
-/
theorem upWrongCalendarEvent_iff_generatedUpWrongSuffixPrefixEvent
    (n : ℕ) (z : Z (p := p)) :
    z ∈ upWrongCalendarEvent rate rewards C_star C_h n ↔
      z ∈ ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        rate rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
  calc
    z ∈ upWrongCalendarEvent rate rewards C_star C_h n ↔
        ∃ r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).take
          (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h),
          ∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true :=
      actualRecord_calendarPrefix_exists_iff rate rewards C_star C_h z n
        (fun r => ∃ d, r.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true)
    _ ↔ z ∈ ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
          rate rewards C_star C_h
          (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
      (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) z).symm

/-- The strict-past UP calendar event is contained in the existing full
count-T generated-UP event. Prefixes before T are monotone; past T, the take
saturates at the actual suffix length.
-/
theorem upWrongCalendarEvent_subset_generatedUpWrongSuffixPrefixEvent_horizon
    (n : ℕ) :
    upWrongCalendarEvent rate rewards C_star C_h n ⊆
      ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        rate rewards C_star C_h p.T := by
  intro z hz
  have hprefix :=
    (upWrongCalendarEvent_iff_generatedUpWrongSuffixPrefixEvent
      rate rewards C_star C_h n z).mp hz
  obtain ⟨r, hr, hup⟩ :=
    (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
      (rate := rate) rewards C_star C_h
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) z).mp hprefix
  let L := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hlen : L.length = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    dsimp [L]
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  have hfull : L.take p.T = L := by
    apply (List.take_eq_self_iff _).2
    rw [hlen]
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  by_cases hn : p.T ≤ n
  · have hsaturated := completeSuffixRecords_take_eq_of_horizon_le
      rate rewards C_star C_h z n hn
    change r ∈ L.take
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) at hr
    rw [hsaturated] at hr
    have hrL : r ∈ L := by simpa only [L] using hr
    have hrT : r ∈ L.take p.T := by
      rw [hfull]
      exact hrL
    have hrOut : r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take p.T := by
      simpa only [L] using hrT
    exact (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
      (rate := rate) rewards C_star C_h p.T z).2 ⟨r, hrOut, hup⟩
  · change r ∈ L.take
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) at hr
    obtain ⟨k, hkTake, hgetTake⟩ := List.mem_iff_getElem.mp hr
    have hbounds : k < n -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
        k < L.length := by
      rw [List.length_take] at hkTake
      exact Nat.lt_min.mp hkTake
    have hget : L[k] = r := by
      simpa only [List.getElem_take] using hgetTake
    have hmem : r ∈ L := List.mem_iff_getElem.mpr ⟨k, hbounds.2, hget⟩
    have hmemT : r ∈ L.take p.T := by
      rw [hfull]
      exact hmem
    have hmemOut : r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take p.T := by
      simpa only [L] using hmemT
    exact (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
      (rate := rate) rewards C_star C_h p.T z).2 ⟨r, hmemOut, hup⟩

/-- The literal UP-only calendar event inherits the accepted 1/(4 N^2) bound
from the existing count-T generated-UP wrong event under the same source law.
-/
theorem upWrongCalendarEvent_measureReal_le
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (upWrongCalendarEvent rate rewards C_star C_h n) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  apply le_trans
    (measureReal_mono
      (upWrongCalendarEvent_subset_generatedUpWrongSuffixPrefixEvent_horizon
        rate rewards C_star C_h n))
  exact ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_measureReal_le
    (rate := rate) rewards C_star C_h control0 p.T

end Bandits.Support.ReferenceStrictPastFailureCalendarAlignment

end
