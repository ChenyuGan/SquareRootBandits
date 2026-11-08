/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals
public import Bandits.Support.ReferenceOriginalStoppedTransferSignedReindex
public import Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

import Mathlib.Tactic

/-!
# Original ranked release dates and the source-local assignment gate

This module localizes the release dates of one original ranked stopped
transfer to the existing timestamp-indexed gate on the same complete source.
It makes no waiting-time, law, stopping-time, or conditional-expectation claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthReleaseGateAlignment

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

/-- The original ranked stopped-transfer window, restricted to actual release
dates on this same complete original source. -/
public def kthReleaseDates (k : Fin (p.T + 1)) : Finset (Fin p.T) :=
  ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k ∩
    ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
      rate rewards C_star C_h z

/-- The literal global source-prefix entry gate for one zero-based absolute
assignment timestamp, retained through the inclusive first-bad date. -/
public def fixedLabelReleaseDates (ell : ℕ) : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z).map
        Prod.fst = some true ∧
      t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z

/-- Complete membership characterization of the literal ranked release
projection. -/
public theorem mem_kthReleaseDates_iff (k : Fin (p.T + 1)) (t : Fin p.T) :
    t ∈ kthReleaseDates rate rewards C_star C_h z k ↔
      t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
          rate rewards C_star C_h z k ∧
        t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
          rate rewards C_star C_h z := by
  simp only [kthReleaseDates, Finset.mem_inter]

/-- Complete membership characterization of the literal timestamp-indexed
global source entry projection. -/
public theorem mem_fixedLabelReleaseDates_iff (ell : ℕ) (t : Fin p.T) :
    t ∈ fixedLabelReleaseDates rate rewards C_star C_h z ell ↔
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z).map
          Prod.fst = some true ∧
        t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z := by
  simp only [fixedLabelReleaseDates, Finset.mem_filter, Finset.mem_univ, true_and]

/-- On a physical source record with a true local gate, the entry keeps that
gate and its follower pending observer as separate coordinates. -/
private theorem entry_and_pending_of_actual_gate
    (ell : ℕ) (t : Fin p.T) (r : Record rate) (ht : r.input.time = t)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell t
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true) :
    ∃ M : ReferenceActivePhysicalStep.Payload rate,
      M.sigma.val = ell ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z).map
          Prod.fst = some true ∧
      ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h ell t z =
        ReferencePhysicalReleaseQuota.pendingSet M r ∧
      ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z =
        some (true, some (ReferencePhysicalReleaseQuota.pendingSet M r)) := by
  obtain ⟨payload, hassignment⟩ :=
    ReferenceRetainedReleasePhaseObservation.localReleaseGate_reselects_actualAssignment
      rate ell t (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) hgate
  have hpair :
      ReferenceRetainedReleasePhaseObservation.localStoredPayload
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
        some payload ∧ payload.sigma.val = ell := by
    have h := hassignment
    simp only [ReferenceRetainedReleasePhaseObservation.localStoredAssignment,
      Option.map_eq_some_iff] at h
    rcases h with ⟨actual, hactual, hfields⟩
    rcases Prod.mk.inj hfields with ⟨hstamp, hsame⟩
    subst actual
    exact ⟨hactual, hstamp⟩
  have hstored :
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
        some payload := by
    have h := ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
    simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using
      (hpair.1.symm.trans h).symm
  have hgate' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell
      r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    rw [ht]
    exact hgate
  have hlocalPending :=
    ReferenceLocalReleasePendingHistory.source_localReleasePending_eq_pendingSet
      rate ell payload r hgate'
  rw [ht] at hlocalPending
  have hentry :
      ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z =
        some (true, some (ReferencePhysicalReleaseQuota.pendingSet payload r)) := by
    unfold ReferenceSourcePrefixHistoryFiltration.entry
      ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hrecord]
    simp only [Option.map_some]
    unfold ReferenceRetainedReleasePhaseObservation.localReleaseEntry
    rw [hpair.1]
    simp only [hgate, ↓reduceIte,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
    rw [hlocalPending]
  refine ⟨payload, hpair.2, hstored, ?_, ?_, hentry⟩
  · rw [hentry]
    rfl
  · rw [ReferenceSourcePrefixHistoryFiltration.pending, hentry]
    rfl

/-- The entry and follower-pending readouts can be transported to the
already-proved source-calendar APIs on the computed crossing and elapsed
event. The original source and its selected private row are retained. -/
private theorem entry_pending_source_calendar
    (ell : ℕ) (t : Fin p.T)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let hspan : s + (p.T - s) ≤ p.T := by
      have hT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      dsimp only [s]
      omega
    let hsT : s ≤ p.T := by
      have hT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      dsimp only [s]
      exact hT
    let event : ReferenceSourceReleaseWaitingReadouts.SourceEvent
        rate rewards C_star C_h s := ⟨z, hcross, by rfl⟩
    ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z =
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z rewards C_star C_h
        event.property.1 s (p.T - s) event.property.2 hspan ell t.val ∧
    ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h ell t z =
      (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
        s hsT ell event t.val).getD ∅ := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + (p.T - s) ≤ p.T := by dsimp only [s]; omega
  have hsT : s ≤ p.T := by dsimp only [s]; exact hT
  let event : ReferenceSourceReleaseWaitingReadouts.SourceEvent
      rate rewards C_star C_h s := ⟨z, hcross, by rfl⟩
  have hs' : s ≤ t.val := by simpa only [s] using hs
  have hentry := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
    rate rewards C_star C_h ell t s hs' event
  have hpending := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
    rate rewards C_star C_h ell t s hs' event
  exact ⟨hentry, hpending⟩

/-- An absent ranked start has no release date. This is the source-side empty
case for no launch, terminal launch, and any rank beyond the inclusive stop. -/
public theorem kthReleaseDates_eq_empty_of_absent_rank
    (k : Fin (p.T + 1))
    (hk : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    kthReleaseDates rate rewards C_star C_h z k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hwindow := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht |>.1
  have hempty := ReferenceOriginalStoppedTransferSignedReindex.absent_ranked_window_empty
    rate rewards C_star C_h z k hk
  rw [hempty] at hwindow
  simp at hwindow

private theorem suffix_time
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val := by
  have h := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
    rate rewards C_star C_h z j
  omega

private theorem suffix_actual
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val] := by
  have ht := suffix_time rate rewards C_star C_h z j
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ht, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem j.isLt

private theorem entry_gate_iff (ell : ℕ) (t : Fin p.T) :
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z).map
        Prod.fst = some true ↔
      ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time = t ∧
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell t
          (ReferenceActivePhysicalStepMeasurability.encodeState
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[j.val].input.state) = true := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  constructor
  · intro h
    have hs : s ≤ t.val := by
      by_contra hn
      have ha := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h t z (show t.val <
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h from
          Nat.lt_of_not_ge hn)
      simp only [ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming, ha, Option.map_none] at h
      cases h
    have hj : t.val - s < R.length := by
      have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
        rate z rewards C_star C_h
      have ht := t.isLt
      change R.length = p.T - s at hlen
      omega
    let j : Fin R.length := ⟨t.val - s, hj⟩
    have ht : R[j.val].input.time = t := by
      apply Fin.ext
      have htime := suffix_time rate rewards C_star C_h z j
      change R[j.val].input.time.val = s + (t.val - s) at htime
      omega
    refine ⟨j, ht, ?_⟩
    have ha := suffix_actual rate rewards C_star C_h z j
    rw [ht] at ha
    simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, ha, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
      Option.some.injEq] using h
  · rintro ⟨j, ht, hg⟩
    have ha := suffix_actual rate rewards C_star C_h z j
    rw [ht] at ha
    simp only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, ha, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hg]

private theorem release_dates_iff (t : Fin p.T) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
      rate rewards C_star C_h z ↔
      ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time = t ∧
        ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[j.val] ∧
        t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z := by
  constructor
  · intro ht
    obtain ⟨j, hj, htime⟩ := Finset.mem_image.mp ht
    obtain ⟨_, hret, hrel⟩ := Finset.mem_filter.mp hj
    exact ⟨j, htime, hrel, by
      have hb := hret.2
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time.val + 1 ≤
        min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T at hb
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time = t at htime
      rw [htime] at hb
      exact (Nat.le_min.mp hb).1⟩
  · rintro ⟨j, htime, hrel, hbad⟩
    obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
      rate rewards C_star C_h z j
    have hlaunch : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
        rate rewards C_star C_h z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
      change ReferenceInitializationRun.launchRound
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate) = _
      unfold ReferenceInitializationRun.launchRound
      rw [hc]
      rfl
    have htimeval := suffix_time rate rewards C_star C_h z j
    rw [htime] at htimeval
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hrel⟩, htime⟩
    constructor
    · rw [hlaunch]
      change _ ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time.val + 1
      rw [htime]
      omega
    · change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time.val + 1 ≤
        min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T
      rw [htime]
      exact Nat.le_min.mpr ⟨hbad, by have ht := t.isLt; omega⟩

private theorem selected_empty_iff_release
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some selected)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input = none) :
    selected.view.pendingAtChoice = ∅ ↔
      ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val] := by
  constructor
  · intro he
    rcases ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_phase_availability
      rate rewards C_star C_h z j with ⟨c, hc⟩ | ⟨other, ho, _, hm⟩ | hr
    · change ReferenceCollectionSegmentExtraction.choice
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input = some c at hc
      rw [hchoice] at hc
      cases hc
    · have hs : other = selected := Option.some.inj (ho.symm.trans hselected)
      subst other
      rw [he] at hm
      exact (Finset.not_nonempty_empty hm).elim
    · exact hr
  · rintro ⟨other, ho, _, he⟩
    have hs : other = selected := Option.some.inj (ho.symm.trans hselected)
    exact hs ▸ he

private theorem suffix_same_date
    (i j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (ht : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.time =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time) : i = j := by
  have hi := suffix_time rate rewards C_star C_h z i
  have hj := suffix_time rate rewards C_star C_h z j
  have hh := congrArg Fin.val ht
  apply Fin.ext
  omega

private theorem entry_gate_support_iff (ell : ℕ) (t : Fin p.T) :
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z).map
        Prod.fst = some true ↔
      t.val + 1 ∈ ReferenceLocalReleaseGateChronology.gateSupport ell
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) := by
  rw [entry_gate_iff, ReferenceLocalReleaseGateChronology.mem_gateSupport]
  constructor
  · rintro ⟨j, ht, hg⟩
    refine ⟨_, List.getElem_mem j.isLt, ?_, ?_⟩
    · rw [ht]
      exact hg
    · rw [ht]
  · rintro ⟨r, hr, hg, hd⟩
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
    have ht : r.input.time = t := Fin.ext (by omega)
    refine ⟨⟨j, hj⟩, heq ▸ ht, ?_⟩
    rw [heq, ← ht]
    exact hg

private theorem initial_entry_iff (t : Fin p.T) :
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) t z).map
        Prod.fst = some true ↔
      ∃ j : Fin (ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
        rate rewards C_star C_h z).length,
        (ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
          rate rewards C_star C_h z)[j.val].input.time = t ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
          (ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
            rate rewards C_star C_h z)[j.val] = ∅ := by
  rw [entry_gate_support_iff]
  have hcal := ReferenceFirstLiveInitialTransferChronology.raw_release_calendar
    rate rewards C_star C_h z
  change ReferenceLocalReleaseGateChronology.gateSupport
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) = _ at hcal
  rw [hcal]
  constructor
  · intro h
    obtain ⟨r, hr, hd⟩ := Finset.mem_image.mp h
    obtain ⟨hr, hm⟩ := Finset.mem_filter.mp hr
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    exact ⟨⟨j, hj⟩, heq ▸ Fin.ext (by omega), heq ▸ hm⟩
  · rintro ⟨j, ht, hm⟩
    refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.getElem_mem j.isLt), hm⟩, ?_⟩
    rw [ht]

private theorem later_entry_iff
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) (t : Fin p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let h := (V.takeWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) t z).map
        Prod.fst = some true ↔
      ∃ j : Fin V.length, V[j.val].input.time = t ∧ h ≤ j.val := by
  intro R V h
  have hf := ReferencePostReplacementCollectionReleaseSupport.later_release_filter_eq
    rate rewards C_star C_h z b hb
  have hdrop : V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice =
      V.drop h := by
    have he : V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice ++
        V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice = V :=
      List.takeWhile_append_dropWhile
    have hd := congrArg (List.drop h) he
    simpa only [h, List.drop_append_length] using hd
  change R.filter _ = V.dropWhile _ at hf
  rw [hdrop] at hf
  rw [entry_gate_support_iff, ReferenceLocalReleaseGateChronology.mem_gateSupport]
  constructor
  · rintro ⟨r, hr, hg, hd⟩
    have hm : r ∈ V.drop h := by
      rw [← hf]
      exact List.mem_filter.mpr ⟨hr, hg⟩
    obtain ⟨u, hu, heq⟩ := List.mem_drop_iff_getElem.mp hm
    refine ⟨⟨h + u, by omega⟩, ?_, Nat.le_add_right h u⟩
    change V[h + u].input.time = t
    rw [heq]
    exact Fin.ext (by omega)
  · rintro ⟨j, ht, hj⟩
    have hm : V[j.val] ∈ V.drop h := by
      apply List.mem_drop_iff_getElem.mpr
      refine ⟨j.val - h, by omega, ?_⟩
      have he : h + (j.val - h) = j.val := by omega
      simp only [he]
    rw [← hf] at hm
    obtain ⟨hr, hg⟩ := List.mem_filter.mp hm
    exact ⟨V[j.val], hr, hg, by rw [ht]⟩

private theorem first_selection_birth
    (r : Record rate) (hf : r.input.state.coordinator = .first)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    ReferenceAssignmentPayloadPersistence.InstallationBirth r selected.view.payload := by
  have hd : r.output.preparation.coordinator = .first
      (CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput r.input)) := by
    rw [r.output_eq]
    exact ReferenceActivePhysicalStep.dispatch_first r.input hf
  rw [hd] at hs
  cases hc : CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput r.input) with
  | chosen installed arm =>
    rw [hc] at hs
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt] at hs
    split at hs
    · cases hs
      unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
      rw [hd, hc]
      exact ⟨rfl, ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
        r.input installed arm hc⟩
    · cases hs
  | _ => simp only [hc, ReferenceActivePhysicalStep.DispatchCut.selection] at hs; cases hs

private theorem gate_stored_eq_selected
    (ell : ℕ) (r : Record rate)
    (hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
      some selected.view.payload := by
  obtain ⟨registers, owned, base, hc, _, _, _, _⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live ell r.input.time r.input.state hg
  have hd : r.output.preparation.coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput r.input registers owned base)) := by
    rw [r.output_eq]
    change ReferenceActivePhysicalStep.dispatch r.input = _
    simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hd] at hs
  have hp : selected.view.payload = registers.payload := by
    cases hdispatch : CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput r.input registers owned base) <;>
      simp only [hdispatch, ReferenceActivePhysicalStep.DispatchCut.selection] at hs
    all_goals try { cases hs }
    all_goals
      unfold ReferenceActivePhysicalStep.selectionAt at hs
      split at hs
      · cases hs
        rfl
      · cases hs
  rw [hc]
  exact congrArg some hp.symm

private theorem observer_fields
    (ell : ℕ) (t : Fin p.T) (r : Record rate) (ht : r.input.time = t)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry
      rate rewards C_star C_h ell t z).map Prod.fst = some true)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    selected.view.payload.sigma.val = ell ∧
    ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
      some selected.view.payload ∧
    ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell t
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true ∧
    ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h ell t z =
      ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r ∧
    ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h ell t z =
      some (true, some (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r)) := by
  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate ell t
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
      Option.some.injEq] using hg
  obtain ⟨M, hstamp, hstored, _, hpending, hentry⟩ :=
    entry_and_pending_of_actual_gate rate rewards C_star C_h z ell t r ht hr hgate
  have hstored' := gate_stored_eq_selected rate ell r (by rw [ht]; exact hgate) selected hs
  have heq : M = selected.view.payload := Option.some.inj (hstored.symm.trans hstored')
  subst M
  exact ⟨hstamp, hstored, hgate, hpending, hentry⟩

private theorem slot_index (n : ℕ) (r : Record rate)
    (hs : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n]? = some r) :
    ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, j.val = n ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val] = r := by
  obtain ⟨hn, he⟩ := List.getElem?_eq_some_iff.mp hs
  exact ⟨⟨n, hn⟩, rfl, he⟩

private theorem selected_empty_iff_release_at_slot (n : ℕ) (r : Record rate)
    (hslot : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n]? = some r)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = none) :
    selected.view.pendingAtChoice = ∅ ↔
      ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate r := by
  obtain ⟨j, _, rfl⟩ := slot_index rate rewards C_star C_h z n r hslot
  exact selected_empty_iff_release rate rewards C_star C_h z j selected hs hc

private theorem initial_rank_alignment
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (hb : b.val = 0)
    (hf : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.coordinator = .first) :
    ∃ M : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] M ∧
      kthReleaseDates rate rewards C_star C_h z k =
        fixedLabelReleaseDates rate rewards C_star C_h z
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) ∧
      ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
        ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length,
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[j.val].input.time = t ∧
          ∃ selected : ReferenceActivePhysicalStep.Selection
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[j.val].input,
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
    rate rewards C_star C_h z
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rate rewards C_star C_h k z
  obtain ⟨hW, _hE, hclip, hglobal, M, _hM, hfields, _⟩ :=
    ReferenceOriginalStoppedTransferPhaseIntervals.initial_rank_stopped_transfer_phase_intervals
      rate rewards C_star C_h k z hk hstart
  change 0 < W.length at hW
  let zero : Fin W.length := ⟨0, hW⟩
  have hzero : R[b.val] = W[0] := by
    have hh := (hfields zero).1
    change R[0]? = some W[0] at hh
    have hh' : R[b.val]? = some W[0] := by simpa only [hb] using hh
    exact Option.some.inj ((List.getElem?_eq_getElem b.isLt).symm.trans hh')
  obtain ⟨selected0, hs0, hp0, _⟩ := (hfields zero).2.2.2.2
  have hbirth := first_selection_birth rate W[0] (by rw [← hzero]; exact hf) selected0 hs0
  rw [hp0] at hbirth
  have hloc : ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
      ∃ j : Fin W.length, W[j.val].input.time = t ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ := by
    intro t ht
    obtain ⟨hw, hr⟩ := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht
    have hbounds : _ ≤ t.val + 1 ∧ t.val + 1 < E :=
      (Finset.mem_filter.mp hw).2
    obtain ⟨q, hqt, hrel, _⟩ := (release_dates_iff rate rewards C_star C_h z t).mp hr
    have hbefore : R[q.val].input.time.val + 1 < E := by rw [hqt]; exact hbounds.2
    have hqW : q.val < W.length := ((hglobal q).mp hbefore).1
    let j : Fin W.length := ⟨q.val, hqW⟩
    have heq : R[q.val] = W[j.val] := by
      exact Option.some.inj ((List.getElem?_eq_getElem q.isLt).symm.trans (hfields j).1)
    have hrelW : ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate W[j.val] :=
      heq ▸ hrel
    obtain ⟨selected, hs, hp, _, _⟩ := (hfields j).2.2.2.2
    have hempty := (selected_empty_iff_release_at_slot rate rewards C_star C_h z
      j.val W[j.val] (hfields j).1 selected hs (hfields j).2.2.2.1).mpr hrelW
    exact ⟨j, heq ▸ hqt, selected, hs, hp, hempty⟩
  have halign : kthReleaseDates rate rewards C_star C_h z k =
      fixedLabelReleaseDates rate rewards C_star C_h z (s + b.val) := by
    ext t
    constructor
    · intro ht
      obtain ⟨j, hjt, selected, hs, _, he⟩ := hloc t ht
      apply (mem_fixedLabelReleaseDates_iff rate rewards C_star C_h z (s + b.val) t).mpr
      constructor
      · rw [hb, Nat.add_zero]
        apply (initial_entry_iff rate rewards C_star C_h z t).mpr
        refine ⟨j, hjt, ?_⟩
        change ((W[j.val].output.preparation.coordinator.selection).map
          fun selected => selected.view.pendingAtChoice).getD ∅ = ∅
        rw [hs]
        exact he
      · obtain ⟨_, hr⟩ := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht
        exact ((release_dates_iff rate rewards C_star C_h z t).mp hr).choose_spec.2.2
    · intro ht
      obtain ⟨hg, hbad⟩ := (mem_fixedLabelReleaseDates_iff
        rate rewards C_star C_h z (s + b.val) t).mp ht
      rw [hb, Nat.add_zero] at hg
      obtain ⟨j, hjt, hm⟩ := (initial_entry_iff rate rewards C_star C_h z t).mp hg
      obtain ⟨selected, hs, _, _, _⟩ := (hfields j).2.2.2.2
      have hempty : selected.view.pendingAtChoice = ∅ := by
        change ((W[j.val].output.preparation.coordinator.selection).map
          fun selected => selected.view.pendingAtChoice).getD ∅ = ∅ at hm
        rw [hs] at hm
        exact hm
      have hrel := (selected_empty_iff_release_at_slot rate rewards C_star C_h z
        j.val W[j.val] (hfields j).1 selected hs (hfields j).2.2.2.1).mp hempty
      have hd := (hfields j).2.1
      change W[j.val].input.time.val + 1 = s + j.val + 1 at hd
      rw [hjt] at hd
      have hstop : t.val + 1 < E := (hclip (t.val + 1)).mpr ⟨by have hj := j.isLt; omega, hbad⟩
      apply (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hstop⟩, ?_⟩
      · rw [hstart]
        omega
      · obtain ⟨q, _, heq⟩ := slot_index rate rewards C_star C_h z j.val W[j.val] (hfields j).1
        apply (release_dates_iff rate rewards C_star C_h z t).mpr
        exact ⟨q, heq.symm ▸ hjt, heq.symm ▸ hrel, hbad⟩
  refine ⟨M, hzero.symm ▸ hbirth, halign, ?_⟩
  intro t ht
  obtain ⟨j, hjt, selected, hs, hp, he⟩ := hloc t ht
  obtain ⟨q, _, heq⟩ := slot_index rate rewards C_star C_h z j.val W[j.val] (hfields j).1
  refine ⟨q, heq.symm ▸ hjt, ?_⟩
  rw [heq]
  exact ⟨selected, hs, hp, he⟩

private theorem later_rank_alignment
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hnotinitial : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≠
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1) :
    kthReleaseDates rate rewards C_star C_h z k = ∅ ∨
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      ∃ M : ReferenceActivePhysicalStep.Payload rate,
        ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input = true ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val] M ∧
        kthReleaseDates rate rewards C_star C_h z k =
          fixedLabelReleaseDates rate rewards C_star C_h z
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) ∧
        ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
          ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).length,
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[j.val].input.time = t ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[j.val].input,
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rate rewards C_star C_h k z
  obtain ⟨i, hi, hbranch⟩ :=
    ReferenceOriginalStoppedTransferPhaseIntervals.present_stopped_transfer_collection_intervals
      rate rewards C_star C_h k z hk
  rcases hbranch with ⟨hzero, _, _⟩ | hcollection
  · exact (hnotinitial (by simpa only [hzero, Nat.add_zero] using hi)).elim
  obtain ⟨registers, owned, base, seg, _hstate, _hat, _hentry, _hpayload, _hne,
    hCfields, _hCactual, _hCiff, hend⟩ := hcollection
  rcases hend with ⟨_hterminal, _hE, hchoices, _⟩ | hlater
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨hw, hr⟩ := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht
    have hbounds := (Finset.mem_filter.mp hw).2
    obtain ⟨q, hqt, hrel, _⟩ := (release_dates_iff rate rewards C_star C_h z t).mp hr
    have hqdate := suffix_time rate rewards C_star C_h z q
    rw [hqt] at hqdate
    have hqi : i.val ≤ q.val := by rw [hi] at hbounds; omega
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hchoices q hqi)
    exact ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_collection_release_disjoint
      rate rewards C_star C_h z q ⟨⟨c, hc⟩, hrel⟩
  obtain ⟨b, hbi, hb, _hexit, _hstateb, _hempty, hlen, _hE, hclip, hglobal,
    M, hbirth, hfields, _hactual, _hHiff, _hRiff, _⟩ := hlater
  let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let h := (V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
  have hloc : ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
      ∃ j : Fin V.length, V[j.val].input.time = t ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
          V[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ := by
    intro t ht
    obtain ⟨hw, hr⟩ := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht
    have hbounds : _ ≤ t.val + 1 ∧ t.val + 1 < E := (Finset.mem_filter.mp hw).2
    obtain ⟨q, hqt, hrel, _⟩ := (release_dates_iff rate rewards C_star C_h z t).mp hr
    have hqdate := suffix_time rate rewards C_star C_h z q
    rw [hqt] at hqdate
    have hqi : i.val ≤ q.val := by rw [hi] at hbounds; omega
    have hbefore : R[q.val].input.time.val + 1 < E := by rw [hqt]; exact hbounds.2
    have hqend : q.val < b.val + V.length := ((hglobal q).mp ⟨hqi, hbefore⟩).2.1
    have hqb : b.val ≤ q.val := by
      by_contra hn
      let c : Fin seg.records.length := ⟨q.val - i.val, by omega⟩
      have hslot := (hCfields c).1
      have hindex : i.val + c.val = q.val := by dsimp only [c]; omega
      rw [hindex, List.getElem?_eq_getElem q.isLt] at hslot
      have heq : R[q.val] = seg.records[c.val] := Option.some.inj hslot
      obtain ⟨chosen, hc, _⟩ := (hCfields c).2.2
      have hchoice : ReferenceCollectionSegmentExtraction.choice R[q.val].input = some chosen := by
        rw [heq]
        exact hc
      exact ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_collection_release_disjoint
        rate rewards C_star C_h z q ⟨⟨chosen, hchoice⟩, hrel⟩
    let j : Fin V.length := ⟨q.val - b.val, by omega⟩
    have hindex : b.val + j.val = q.val := by dsimp only [j]; omega
    have hslot := (hfields j).1
    rw [hindex, List.getElem?_eq_getElem q.isLt] at hslot
    have heq : R[q.val] = V[j.val] := Option.some.inj hslot
    obtain ⟨selected, hs, hp, _, _⟩ := (hfields j).2.2.2
    have he := (selected_empty_iff_release_at_slot rate rewards C_star C_h z
      (b.val + j.val) V[j.val] (hfields j).1 selected hs (hfields j).2.2.1).mpr (heq ▸ hrel)
    exact ⟨j, heq ▸ hqt, selected, hs, hp, he⟩
  have halign : kthReleaseDates rate rewards C_star C_h z k =
      fixedLabelReleaseDates rate rewards C_star C_h z (s + b.val) := by
    ext t
    constructor
    · intro ht
      obtain ⟨j, hjt, selected, hs, _, he⟩ := hloc t ht
      apply (mem_fixedLabelReleaseDates_iff rate rewards C_star C_h z (s + b.val) t).mpr
      constructor
      · apply (later_entry_iff rate rewards C_star C_h z b hb t).mpr
        obtain ⟨other, ho, _, _, heiff⟩ := (hfields j).2.2.2
        have heq : other = selected := Option.some.inj (ho.symm.trans hs)
        subst other
        exact ⟨j, hjt, heiff.mp he⟩
      · obtain ⟨_, hr⟩ := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mp ht
        exact ((release_dates_iff rate rewards C_star C_h z t).mp hr).choose_spec.2.2
    · intro ht
      obtain ⟨hg, hbad⟩ := (mem_fixedLabelReleaseDates_iff
        rate rewards C_star C_h z (s + b.val) t).mp ht
      obtain ⟨j, hjt, hj⟩ := (later_entry_iff rate rewards C_star C_h z b hb t).mp hg
      obtain ⟨selected, hs, _, _, heiff⟩ := (hfields j).2.2.2
      have he := heiff.mpr hj
      have hrel := (selected_empty_iff_release_at_slot rate rewards C_star C_h z
        (b.val + j.val) V[j.val] (hfields j).1 selected hs (hfields j).2.2.1).mp he
      have hd := (hfields j).2.1
      change V[j.val].input.time.val + 1 = s + b.val + j.val + 1 at hd
      rw [hjt] at hd
      have hstop : t.val + 1 < E := (hclip (t.val + 1)).mpr
        ⟨by have hjlt := j.isLt; omega, hbad⟩
      apply (mem_kthReleaseDates_iff rate rewards C_star C_h z k t).mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hstop⟩, ?_⟩
      · rw [hi]
        omega
      · obtain ⟨q, _, heq⟩ := slot_index rate rewards C_star C_h z
          (b.val + j.val) V[j.val] (hfields j).1
        apply (release_dates_iff rate rewards C_star C_h z t).mpr
        exact ⟨q, heq.symm ▸ hjt, heq.symm ▸ hrel, hbad⟩
  right
  refine ⟨b, M, hb, hbirth, halign, ?_⟩
  intro t ht
  obtain ⟨j, hjt, selected, hs, hp, he⟩ := hloc t ht
  obtain ⟨q, _, heq⟩ := slot_index rate rewards C_star C_h z
    (b.val + j.val) V[j.val] (hfields j).1
  refine ⟨q, heq.symm ▸ hjt, ?_⟩
  rw [heq]
  exact ⟨selected, hs, hp, he⟩

/-- Every original ranked stopped release window is either empty or is the
literal, globally timestamp-indexed source gate of one actual installation.
The same birth payload appears in every selected release operation and in the
stored incoming state. Coordinator confirmations and follower pending tasks
are kept separate, and the first detecting update is retained inclusively.

This pointwise identity supplies no conditional law or random-label tower
substitution. -/
public theorem kthReleaseDates_eq_empty_or_actual_installation
    (k : Fin (p.T + 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    kthReleaseDates rate rewards C_star C_h z k = ∅ ∨
      ∃ (b : Fin R.length) (M : ReferenceActivePhysicalStep.Payload rate),
        ((b.val = 0 ∧ R[b.val].input.state.coordinator = .first) ∨
          ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true) ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
        R[b.val].input.time.val = s + b.val ∧
        M.sigma.val = s + b.val ∧
        kthReleaseDates rate rewards C_star C_h z k =
          fixedLabelReleaseDates rate rewards C_star C_h z (s + b.val) ∧
        ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
          ∃ j : Fin R.length,
            R[j.val].input.time = t ∧
            ReferenceSourcePrefixHistoryFiltration.actualRecord
              rate rewards C_star C_h t z = some R[j.val] ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection R[j.val].input,
              R[j.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ ∧
              ReferenceAssignmentPayloadPersistence.storedPayload
                R[j.val].input.state.coordinator = some M ∧
              ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val) t
                (ReferenceActivePhysicalStepMeasurability.encodeState R[j.val].input.state) = true ∧
              ReferenceSourcePrefixHistoryFiltration.pending
                rate rewards C_star C_h (s + b.val) t z =
                  ReferencePhysicalReleaseQuota.pendingSet M R[j.val] ∧
              ReferenceSourcePrefixHistoryFiltration.entry
                rate rewards C_star C_h (s + b.val) t z =
                  some (true, some (ReferencePhysicalReleaseQuota.pendingSet M R[j.val])) ∧
              ∃ (hcross : (ReferenceInitializationRun.output
                    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true),
                let hsT : s ≤ p.T :=
                  ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
                let hspan : s + (p.T - s) ≤ p.T := by omega
                let event : ReferenceSourceReleaseWaitingReadouts.SourceEvent
                    rate rewards C_star C_h s := ⟨z, hcross, rfl⟩
                ReferenceSourcePrefixHistoryFiltration.entry
                    rate rewards C_star C_h (s + b.val) t z =
                  ReferenceLocalReleaseCalendarCounts.calendarEntry rate z rewards C_star C_h
                    event.property.1 s (p.T - s) event.property.2 hspan (s + b.val) t.val ∧
                ReferenceSourcePrefixHistoryFiltration.pending
                    rate rewards C_star C_h (s + b.val) t z =
                  (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
                    s hsT (s + b.val) event t.val).getD ∅ := by
  intro R s
  by_cases hempty : kthReleaseDates rate rewards C_star C_h z k = ∅
  · exact Or.inl hempty
  obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T := by
    have hw := (mem_kthReleaseDates_iff rate rewards C_star C_h z k t0).mp ht0 |>.1
    have hb := (Finset.mem_filter.mp hw).2.1
    have ht := t0.isLt
    omega
  have hlocal : ∃ (b : Fin R.length) (M : ReferenceActivePhysicalStep.Payload rate),
      ((b.val = 0 ∧ R[b.val].input.state.coordinator = .first) ∨
        ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true) ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
      kthReleaseDates rate rewards C_star C_h z k =
        fixedLabelReleaseDates rate rewards C_star C_h z (s + b.val) ∧
      ∀ t ∈ kthReleaseDates rate rewards C_star C_h z k,
        ∃ j : Fin R.length, R[j.val].input.time = t ∧
          ∃ selected : ReferenceActivePhysicalStep.Selection R[j.val].input,
            R[j.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ := by
    by_cases hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = s + 1
    · obtain ⟨q, b, r, hq, hb, _hr, _hbranch⟩ :=
        ReferenceOriginalTransferPhysicalIntervals.present_start_actual_suffix_record
          rate rewards C_star C_h k z hk
      have hb0 : b.val = 0 := by change s + b.val = q.val at hb; omega
      have htime : R[b.val].input.time.val = s := by
        have hh := suffix_time rate rewards C_star C_h z b
        change R[b.val].input.time.val = s + b.val at hh
        omega
      have hmarker := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_of_launch
        rate rewards C_star C_h R[b.val].input.time z htime
      obtain ⟨first, hlookup, hfirst⟩ :=
        (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
          rate rewards C_star C_h R[b.val].input.time z).mp hmarker
      have hactual := suffix_actual rate rewards C_star C_h z b
      have hsame : first = R[b.val] := Option.some.inj (hlookup.symm.trans hactual)
      have hf : R[b.val].input.state.coordinator = .first := hsame ▸ hfirst
      obtain ⟨M, hbirth, heq, hfields⟩ :=
        initial_rank_alignment rate rewards C_star C_h z k hk hstart b hb0 hf
      exact ⟨b, M, Or.inl ⟨hb0, hf⟩, hbirth, heq, hfields⟩
    · rcases later_rank_alignment rate rewards C_star C_h z k hk hstart with
        he | ⟨b, M, hb, hbirth, heq, hfields⟩
      · exact (hempty he).elim
      · exact ⟨b, M, Or.inr hb, hbirth, heq, hfields⟩
  obtain ⟨b, M, hbranch, hbirth, heq, hfields⟩ := hlocal
  have htime := suffix_time rate rewards C_star C_h z b
  have hstamp : M.sigma.val = s + b.val :=
    (ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] M hbirth).trans htime
  right
  refine ⟨b, M, hbranch, hbirth, htime, hstamp, heq, ?_⟩
  intro t ht
  obtain ⟨j, hjt, selected, hs, hp, he⟩ := hfields t ht
  have hr := suffix_actual rate rewards C_star C_h z j
  rw [hjt] at hr
  have hg := ((mem_fixedLabelReleaseDates_iff rate rewards C_star C_h z (s + b.val) t).mp
    (heq ▸ ht)).1
  obtain ⟨_hselectedStamp, hstored, hgate, hpending, hentry⟩ :=
    observer_fields rate rewards C_star C_h z (s + b.val) t R[j.val] hjt hr hg selected hs
  rw [hp] at hstored hpending hentry
  obtain ⟨hcross, _hspan, _hrecord⟩ :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z j
  have hsourceStart : s ≤ t.val := by
    have hdate := suffix_time rate rewards C_star C_h z j
    rw [hjt] at hdate
    change t.val = s + j.val at hdate
    omega
  refine ⟨j, hjt, hr, selected, hs, hp, he, hstored, hgate, hpending, hentry, hcross, ?_⟩
  exact entry_pending_source_calendar rate rewards C_star C_h z
    (s + b.val) t hsourceStart hcross

end Bandits.Support.ReferenceOriginalKthReleaseGateAlignment

end noncomputable section
