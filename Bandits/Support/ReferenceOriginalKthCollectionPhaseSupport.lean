/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment
public import Bandits.Support.ReferenceOriginalKthCollectionAwaitedService

import Mathlib.Tactic

/-!
# Predictable support of the original kth collection interval

This module exposes the pending set read from the original incoming
coordinator code on the actual kth stopped collection interval. Its phase
endpoints are the original ranked transfer start and the first excluded
pending date.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthCollectionPhaseSupport

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceOriginalKthCollectionCutoffAlignment.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalKthCollectionCutoffAlignment.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalKthCollectionCutoffAlignment.GridRewardTable p

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- The original kth physical transfer start, retaining its actual absent
sentinel and its original one-based ranked-start semantics. -/
def sigma (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k z

/-- The actual pending projection on the original kth C stratum. The option
absence, off-stratum, and beyond-horizon branches all mean no C task. -/
def P (k : Fin (p.T + 1)) (n : ℕ) (z : SourceInput p) : Finset (Fin (p.m - 1)) :=
  if hn : n < p.T then
    let t : Fin p.T := ⟨n, hn⟩
    if ReferenceOriginalKthCollectionSourceSections.kthCStratum
        rate rewards C_star C_h k t z then
      ((ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z).map fun data => data.2.1).getD ∅
    else ∅
  else ∅

/-- Candidate first-excluded dates in the finite interval from the original
ranked start through the horizon sentinel. -/
def firstEmptyCandidates (k : Fin (p.T + 1)) (z : SourceInput p) : Finset ℕ :=
  (Finset.Icc (sigma rate rewards C_star C_h k z) (p.T + 1)).filter
    (fun r => P rate rewards C_star C_h k (r - 1) z = ∅)

private theorem sigma_pos (k : Fin (p.T + 1)) (z : SourceInput p) :
    1 ≤ sigma rate rewards C_star C_h k z := by
  change 1 ≤ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k z
  by_cases hpresent : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T
  · have hmem :=
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
        rate rewards C_star C_h k z).mp hpresent
    obtain ⟨q, _hq, hdate⟩ :=
      (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
        rate rewards C_star C_h
          (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z) z).mp hmem
    rw [← hdate]
    omega
  · have hEq : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = p.T + 1 := by
      have hu := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_sentinel
        rate rewards C_star C_h k z
      omega
    rw [hEq]
    omega

theorem firstEmptyCandidates_nonempty (k : Fin (p.T + 1))
    (z : SourceInput p) : (firstEmptyCandidates rate rewards C_star C_h k z).Nonempty := by
  refine ⟨p.T + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_sentinel
      rate rewards C_star C_h k z), le_rfl⟩, ?_⟩⟩
  simp [P]

/-- The canonical first date after the actual pending set is empty. It is the
minimum of the explicitly nonempty source interval candidate set. -/
def theta (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  (firstEmptyCandidates rate rewards C_star C_h k z).min'
    (firstEmptyCandidates_nonempty rate rewards C_star C_h k z)

theorem sigma_le_sentinel (k : Fin (p.T + 1)) (z : SourceInput p) :
    sigma rate rewards C_star C_h k z ≤ p.T + 1 :=
  ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_sentinel
    rate rewards C_star C_h k z

theorem theta_mem_candidates (k : Fin (p.T + 1)) (z : SourceInput p) :
    theta rate rewards C_star C_h k z ∈ firstEmptyCandidates rate rewards C_star C_h k z :=
  Finset.min'_mem _ (firstEmptyCandidates_nonempty rate rewards C_star C_h k z)

theorem endpoint_bounds (k : Fin (p.T + 1)) (z : SourceInput p) :
    1 ≤ sigma rate rewards C_star C_h k z ∧
      sigma rate rewards C_star C_h k z ≤ theta rate rewards C_star C_h k z ∧
      theta rate rewards C_star C_h k z ≤ p.T + 1 := by
  have hmem := theta_mem_candidates rate rewards C_star C_h k z
  have hmem' := Finset.mem_filter.mp hmem
  have hbounds := Finset.mem_Icc.mp hmem'.1
  exact ⟨sigma_pos rate rewards C_star C_h k z,
    hbounds.1, hbounds.2⟩

theorem P_empty_before_theta (k : Fin (p.T + 1)) (z : SourceInput p) :
    (P rate rewards C_star C_h k
      (theta rate rewards C_star C_h k z - 1) z) = ∅ := by
  exact (Finset.mem_filter.mp (theta_mem_candidates rate rewards C_star C_h k z)).2

/-- The exact finite calendar of dates with an actual nonempty kth C task. -/
def supportIndices (k : Fin (p.T + 1)) (z : SourceInput p) : Finset ℕ :=
  (Finset.range p.T).filter fun n => (P rate rewards C_star C_h k n z).Nonempty

theorem mem_supportIndices_iff (k : Fin (p.T + 1)) (z : SourceInput p)
    (n : ℕ) :
    n ∈ supportIndices rate rewards C_star C_h k z ↔
      n < p.T ∧ (P rate rewards C_star C_h k n z).Nonempty := by
  simp [supportIndices]

private theorem actualRecord_of_prechoiceData (t : Fin p.T) (z : SourceInput p)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r := by
  unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData at hdata
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming] at hdata
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [hr] at hdata
  | some r => exact ⟨r, rfl⟩

private theorem actualRecord_suffixIndex (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val] = r ∧ r.input.time = t := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hr
    let j : Fin R.length := ⟨t.val - s, hj⟩
    have htime := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
      rate rewards C_star C_h z j
    have hrecord : R[j.val]'j.isLt = r := hget
    rw [hrecord] at htime
    have htimeFin : r.input.time = t := by
      apply Fin.ext
      dsimp [j, s] at htime
      omega
    exact ⟨j, by simpa [R] using hrecord, htimeFin⟩
  · cases hr

private theorem actualLaunchRound_eq_physicalStart_succ
    (z : SourceInput p) (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active) :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
        rate rewards C_star C_h z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
  have hcross :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
  have hcross' : (ReferenceInitializationRun.output
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedInput] using hcross
  change ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
    ReferenceInitializationRun.elapsed p
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).completed + 1
  unfold ReferenceInitializationRun.launchRound
  rw [hcross']
  rfl

private theorem actualLaunchRound_le_recordDate
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
        rate rewards C_star C_h z ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val]'j.isLt).input.time.val + 1 := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hR : R = [] := by
        simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch]
      have hj := j.isLt
      simp [R, hR] at hj
  | some active =>
      have hdate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z j
      have hlaunchDate := actualLaunchRound_eq_physicalStart_succ
        rate rewards C_star C_h z active hlaunch
      rw [hlaunchDate]
      omega

private theorem prechoice_pending_nonempty (t : Fin p.T) (z : SourceInput p)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) : data.2.1.Nonempty := by
  obtain ⟨r, hr⟩ := actualRecord_of_prechoiceData rate rewards C_star C_h t z data hdata
  rw [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
    rate rewards C_star C_h t z r hr] at hdata
  cases hstate : r.input.state.coordinator with
  | first => simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate] at hdata
  | dagger => simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate] at hdata
  | live registers owned base =>
      simp only [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate] at hdata
      split at hdata
      · have heq := Option.some.inj hdata
        have hpend : data.2.1 = Finset.univ := by
          exact (congrArg (fun d : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData
            rate => d.2.1) heq).symm
        rw [hpend]
        exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by have hm := p.two_le_m; omega⟩⟩
      · cases hdata
  | collection payload ledger saved =>
      by_cases hp : ledger.pending.Nonempty
      · simp only [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, hp] at hdata
        have heq := Option.some.inj hdata
        have hpend : data.2.1 = ledger.pending := by
          exact (congrArg (fun d : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData
            rate => d.2.1) heq).symm
        rw [hpend]
        exact hp
      · simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, hp] at hdata

/-- Every supported date has the actual choice pending set, including its
literal cutoff initialization, and that incoming pending set is nonempty. -/
theorem P_eq_actualChoicePending_of_mem_kthCDates
    (k : Fin (p.T + 1)) (t : Fin p.T) (z : SourceInput p)
    (ht : t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
      rate rewards C_star C_h z k) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      P rate rewards C_star C_h k t.val z = c.preLedger.pending ∧
      c.preLedger.pending.Nonempty := by
  obtain ⟨_hwindow, ⟨j, hjphase, hjtime⟩⟩ :=
    (ReferenceOriginalKthCollectionCutoffAlignment.mem_kthCDates_iff
      rate rewards C_star C_h z k t).mp ht
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    (R[j.val]'(by simpa [R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords]
      using j.isLt))
  have htime : r.input.time = t := by
    simpa [r, R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using hjtime
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    rw [← htime]
    simpa [r, R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using
      ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
        rate rewards C_star C_h z j.val
        (by simpa [R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using j.isLt)
  obtain ⟨hretained, hchoice⟩ :=
    (ReferenceOriginalKthCollectionCutoffAlignment.mem_collectionPhaseIndices_iff
      rate rewards C_star C_h z j).mp hjphase
  obtain ⟨c, hc⟩ := hchoice
  obtain ⟨_selected, data, _hselection, _hpayload, _hpending, hdata,
      _hdataPayload, hdataPending, _hcutoff, _hframe⟩ :=
    ReferenceOriginalKthCollectionCutoffAlignment.actual_choice_pending_frame
      rate rewards C_star C_h z t r hr c hc
  have hwindow := (ReferenceOriginalKthCollectionCutoffAlignment.kthCStratum_iff_mem_window
    rate rewards C_star C_h z k t).mpr _hwindow
  have hident : P rate rewards C_star C_h k t.val z = data.2.1 := by
    simp [P, t.isLt, hwindow, hdata]
  have hnonempty := prechoice_pending_nonempty rate rewards C_star C_h t z data hdata
  exact ⟨r, c, hr, hc, hident.trans hdataPending, hdataPending ▸ hnonempty⟩

/-- Nonemptiness of the actual pending set is exactly membership in the
original kth collection calendar, proved using its actual choice records. -/
theorem P_nonempty_iff_mem_kthCDates
    (k : Fin (p.T + 1)) (n : ℕ) (z : SourceInput p) (hn : n < p.T) :
    (P rate rewards C_star C_h k n z).Nonempty ↔
      (⟨n, hn⟩ : Fin p.T) ∈
        ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
          rate rewards C_star C_h z k := by
  let t : Fin p.T := ⟨n, hn⟩
  constructor
  · intro hP
    have hstratum : ReferenceOriginalKthCollectionSourceSections.kthCStratum
        rate rewards C_star C_h k t z := by
      by_contra hs
      simp [P, t, hn, hs] at hP
    have hdata : ∃ data,
        ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
          rate rewards C_star C_h t z = some data ∧ data.2.1.Nonempty := by
      have hP' :
          ((ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
            rate rewards C_star C_h t z).map
              (fun data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate =>
                data.2.1)).getD ∅ |>.Nonempty := by
        simpa [P, t, hn, hstratum] using hP
      cases hd : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
          rate rewards C_star C_h t z with
      | none => simp [hd] at hP'
      | some data =>
          have hnonempty : data.2.1.Nonempty := by
            simpa only [hd, Option.map_some, Option.getD_some] using hP'
          exact ⟨data, rfl, hnonempty⟩
    obtain ⟨data, hdata, _⟩ := hdata
    obtain ⟨r, hr⟩ := actualRecord_of_prechoiceData rate rewards C_star C_h t z data hdata
    obtain ⟨c, hc, _hpayload, _hpending, _hcutoff⟩ :=
      ReferenceOriginalKthCollectionAwaitedService.kthCPrechoiceData_actual_collectionChoice
        rate rewards C_star C_h t z r hr data hdata
    obtain ⟨j, hrecord, htime⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
    have hjA := j.isLt
    change j.val < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length at hjA
    let jA : Fin (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
        rate rewards C_star C_h z).length := ⟨j.val, hjA⟩
    have hwindow := (ReferenceOriginalKthCollectionCutoffAlignment.kthCStratum_iff_mem_window
      rate rewards C_star C_h z k t).mp hstratum
    have hjdate :
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val]'j.isLt).input.time = t := by
      calc
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val]'j.isLt).input.time = r.input.time := by
            rw [hrecord]
        _ = t := htime
    have hjdateA :
        ((ReferenceOriginalCalendarTransferPhaseCover.actualRecords
          rate rewards C_star C_h z)[jA.val]'jA.isLt).input.time = t := by
      simpa [jA, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using hjdate
    have hretained :
        ReferenceOriginalCalendarTransferPhaseCover.retainedByFirstBadDate
          rate rewards C_star C_h z jA := by
      dsimp [ReferenceOriginalCalendarTransferPhaseCover.retainedByFirstBadDate,
        ReferenceOriginalCalendarTransferPhaseCover.recordDate]
      constructor
      · exact actualLaunchRound_le_recordDate rate rewards C_star C_h z jA
      · have hbad := hstratum.2.2
        have hT : t.val + 1 ≤ p.T := by omega
        have htimeVal := congrArg Fin.val hjdateA
        rw [htimeVal]
        exact le_min hbad hT
    have hc' : ReferenceCollectionSegmentExtraction.choice
        ((ReferenceOriginalCalendarTransferPhaseCover.actualRecords
          rate rewards C_star C_h z)[jA.val]'jA.isLt).input = some c := by
      have hrecord' :
          (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
            rate rewards C_star C_h z)[jA.val]'jA.isLt = r := by
        simpa [jA, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using hrecord
      rw [hrecord']
      exact hc
    have hphase :=
      (ReferenceOriginalKthCollectionCutoffAlignment.mem_collectionPhaseIndices_iff
        rate rewards C_star C_h z jA).2 ⟨hretained, ⟨c, hc'⟩⟩
    rw [ReferenceOriginalKthCollectionCutoffAlignment.mem_kthCDates_iff]
    exact ⟨hwindow, ⟨jA, hphase, hjdateA⟩⟩
  · intro ht
    obtain ⟨_r, _c, _hr, _hc, hEq, hne⟩ :=
      P_eq_actualChoicePending_of_mem_kthCDates
        rate rewards C_star C_h k t z (by simpa [t] using ht)
    rw [hEq]
    exact hne

/-- Beyond the source horizon the pending set is the literal empty set. -/
theorem P_eq_empty_of_horizon (k : Fin (p.T + 1)) (n : ℕ) (z : SourceInput p)
    (hn : p.T ≤ n) : P rate rewards C_star C_h k n z = ∅ := by
  simp [P, not_lt.mpr hn]

/-- Each pending follower is measurable in the original pre-round field. The
continuous payload stays in its existing product carrier while only its
finite pending projection is tested. -/
theorem P_mem_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (n : ℕ) (hn : n < p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (n + 1)]
      {z : SourceInput p | i ∈ P rate rewards C_star C_h k n z} := by
  let t : Fin p.T := ⟨n, hn⟩
  let F := sourcePrefixFiltration control0 (n + 1)
  let : MeasurableSpace (SourceInput p) := F
  let Data := ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate
  let Pending := Finset (Fin (p.m - 1))
  let : MeasurableSpace Pending := ⊤
  let : MeasurableSpace (Option Pending) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let prechoice := ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
    rate rewards C_star C_h t
  have hdata : Measurable (fun z : SourceInput p => prechoice z) := by
    simpa [prechoice, F, t] using
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_preRound_measurable
        rate rewards C_star C_h control0 t
  have hprojection : Measurable (fun d : Data => d.2.1) := by
    exact measurable_fst.comp measurable_snd
  have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun q : Data × SourceInput p => q.1.2.1)
    (by
      change Measurable (fun q : Data × SourceInput p => (fun d : Data => d.2.1) q.1)
      exact hprojection.comp measurable_fst)
    prechoice hdata
  have hget : Measurable (fun e : Option Pending => e.getD ∅) := by
    have h := (show Measurable
        (Sum.elim id (fun _ : PUnit => (∅ : Pending)) : Pending ⊕ PUnit → Pending) from
      measurable_id.sumElim measurable_const).comp
        (comap_measurable (Equiv.optionEquivSumPUnit Pending))
    convert h using 1
    funext e
    cases e <;> rfl
  let projected : SourceInput p → Pending := fun z => (prechoice z).map (fun d => d.2.1) |>.getD ∅
  have hprojected : Measurable projected := by
    change Measurable (fun z => ((prechoice z).map (fun d : Data => d.2.1)).getD ∅)
    exact hget.comp hmap
  have hstratum : MeasurableSet[F]
      {z : SourceInput p |
        ReferenceOriginalKthCollectionSourceSections.kthCStratum
          rate rewards C_star C_h k t z} := by
    simpa [F, t] using
      ReferenceOriginalKthCollectionSourceSections.kthCStratum_preRound_measurable
        rate rewards C_star C_h control0 k t
  have hevent :
      {z : SourceInput p | i ∈ P rate rewards C_star C_h k n z} =
        {z | ReferenceOriginalKthCollectionSourceSections.kthCStratum
          rate rewards C_star C_h k t z} ∩ {z | i ∈ projected z} := by
    ext z
    by_cases hs : ReferenceOriginalKthCollectionSourceSections.kthCStratum
        rate rewards C_star C_h k t z
    · simp [P, projected, prechoice, t, hn, hs]
    · simp [P, projected, prechoice, t, hn, hs]
  rw [hevent]
  have hi : MeasurableSet {s : Pending | i ∈ s} := MeasurableSpace.measurableSet_top
  exact hstratum.inter (hprojected hi)

/-- Natural dates beyond the source horizon have a constant empty pending
projection, so membership remains measurable in their pre-round fields. -/
theorem P_mem_preRound_measurable_any
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (n + 1)]
      {z : SourceInput p | i ∈ P rate rewards C_star C_h k n z} := by
  by_cases hn : n < p.T
  · exact P_mem_preRound_measurable rate rewards C_star C_h control0 k n hn i
  · have hset : {z : SourceInput p | i ∈ P rate rewards C_star C_h k n z} = ∅ := by
      ext z
      simp [P, hn]
    rw [hset]
    exact (sourcePrefixFiltration control0 (n + 1)).measurableSet_empty

/-- The original kth physical start is already an accepted pre-round stopping
time for the same source-prefix filtration. -/
theorem sigma_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1)) :
    PhaseServiceWaiting.IsPreRoundStoppingTime (sourcePrefixFiltration control0)
      (sigma rate rewards C_star C_h k) := by
  exact ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    rate rewards C_star C_h control0 k

private theorem theta_le_iff_candidate_le (k : Fin (p.T + 1))
    (z : SourceInput p) (n : ℕ) :
    theta rate rewards C_star C_h k z ≤ n ↔
      ∃ r ∈ firstEmptyCandidates rate rewards C_star C_h k z, r ≤ n := by
  constructor
  · intro htheta
    exact ⟨theta rate rewards C_star C_h k z,
      theta_mem_candidates rate rewards C_star C_h k z, htheta⟩
  · rintro ⟨r, hr, hrn⟩
    exact (Finset.min'_le _ _ hr).trans hrn

/-- Every date from the original start and strictly before `theta` is
nonempty. This records the canonical minimum's first-failure property. -/
theorem P_nonempty_before_theta (k : Fin (p.T + 1)) (z : SourceInput p)
    (r : ℕ) (hstart : sigma rate rewards C_star C_h k z ≤ r)
    (hr : r < theta rate rewards C_star C_h k z) :
    (P rate rewards C_star C_h k (r - 1) z).Nonempty := by
  have hrbound : r ≤ p.T + 1 := by
    exact hr.le.trans (endpoint_bounds rate rewards C_star C_h k z).2.2
  by_contra hnonempty
  have hempty : P rate rewards C_star C_h k (r - 1) z = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hcandidate : r ∈ firstEmptyCandidates rate rewards C_star C_h k z :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hstart, hrbound⟩, hempty⟩
  have hmin : theta rate rewards C_star C_h k z ≤ r := by
    change (firstEmptyCandidates rate rewards C_star C_h k z).min'
      (firstEmptyCandidates_nonempty rate rewards C_star C_h k z) ≤ r
    exact Finset.min'_le _ r hcandidate
  omega

/-- An empty original kth collection calendar has zero support at its actual
ranked start; its first-excluded endpoint therefore equals that start. -/
theorem theta_eq_sigma_of_empty_kthCDates (k : Fin (p.T + 1)) (z : SourceInput p)
    (hempty : ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
      rate rewards C_star C_h z k = ∅) :
    theta rate rewards C_star C_h k z = sigma rate rewards C_star C_h k z := by
  by_cases hpresent : sigma rate rewards C_star C_h k z ≤ p.T
  · have hsigmaPos := sigma_pos rate rewards C_star C_h k z
    have hindex : sigma rate rewards C_star C_h k z - 1 < p.T := by omega
    have hpending : P rate rewards C_star C_h k
        (sigma rate rewards C_star C_h k z - 1) z = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      have hmem := (P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k
        (sigma rate rewards C_star C_h k z - 1) z hindex).mp hne
      rw [hempty] at hmem
      simp at hmem
    have hcand : sigma rate rewards C_star C_h k z ∈
        firstEmptyCandidates rate rewards C_star C_h k z := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, sigma_le_sentinel rate rewards C_star C_h k z⟩, ?_⟩
      simpa [Nat.sub_add_cancel hsigmaPos] using hpending
    have hmin := Finset.min'_le (firstEmptyCandidates rate rewards C_star C_h k z)
      (sigma rate rewards C_star C_h k z) hcand
    exact Nat.le_antisymm hmin (endpoint_bounds rate rewards C_star C_h k z).2.1
  · have hsigma : sigma rate rewards C_star C_h k z = p.T + 1 := by
      have hbound := sigma_le_sentinel rate rewards C_star C_h k z
      omega
    have hbounds := endpoint_bounds rate rewards C_star C_h k z
    omega

/-- The first-excluded endpoint is a pre-round stopping time. Its event is a
finite union of possible first-empty dates, each determined by the start and
pending fields available by that date. -/
theorem theta_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1)) :
    PhaseServiceWaiting.IsPreRoundStoppingTime (sourcePrefixFiltration control0)
      (theta rate rewards C_star C_h k) := by
  intro n
  let F := sourcePrefixFiltration control0
  have hevent :
      {z : SourceInput p | theta rate rewards C_star C_h k z ≤ n} =
        ⋃ r ∈ Finset.range (p.T + 2),
          {z | sigma rate rewards C_star C_h k z ≤ r ∧
            P rate rewards C_star C_h k (r - 1) z = ∅ ∧ r ≤ n} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro htheta
      refine ⟨theta rate rewards C_star C_h k z,
        by have := (endpoint_bounds rate rewards C_star C_h k z).2.2; omega, ?_⟩
      exact ⟨(endpoint_bounds rate rewards C_star C_h k z).2.1,
        P_empty_before_theta rate rewards C_star C_h k z, htheta⟩
    · rintro ⟨r, hrbound, hstart, hempty, hrn⟩
      have hsentinel : r ≤ p.T + 1 := by omega
      have hcandidate : r ∈ firstEmptyCandidates rate rewards C_star C_h k z :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hstart, hsentinel⟩, hempty⟩
      exact (theta_le_iff_candidate_le rate rewards C_star C_h k z n).2
        ⟨r, hcandidate, hrn⟩
  rw [hevent]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro hr
  have hrlt : r < p.T + 2 := Finset.mem_range.mp hr
  have hrT : r ≤ p.T + 1 := by omega
  by_cases hrn : r ≤ n
  · rw [show {z : SourceInput p |
        sigma rate rewards C_star C_h k z ≤ r ∧
          P rate rewards C_star C_h k (r - 1) z = ∅ ∧ r ≤ n} =
        {z | sigma rate rewards C_star C_h k z ≤ r ∧
          P rate rewards C_star C_h k (r - 1) z = ∅} by
        ext z
        simp [hrn]]
    by_cases hrzero : r = 0
    · subst r
      have hemptyEvent : {z : SourceInput p |
          sigma rate rewards C_star C_h k z ≤ 0 ∧
            P rate rewards C_star C_h k (0 - 1) z = ∅} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have hpos := sigma_pos rate rewards C_star C_h k z
        omega
      rw [hemptyEvent]
      exact (sourcePrefixFiltration control0 n).measurableSet_empty
    · have hrpos : 1 ≤ r := by omega
      by_cases hrT' : r ≤ p.T
      · have hindex : r - 1 < p.T := by omega
        have hmem : ∀ i : Fin (p.m - 1),
            MeasurableSet[sourcePrefixFiltration control0 r]
              {z : SourceInput p | i ∈ P rate rewards C_star C_h k (r - 1) z} := by
          intro i
          have h := P_mem_preRound_measurable
            rate rewards C_star C_h control0 k (r - 1) hindex i
          rw [Nat.sub_add_cancel hrpos] at h
          exact h
        have hPempty : MeasurableSet[sourcePrefixFiltration control0 r]
            {z : SourceInput p | P rate rewards C_star C_h k (r - 1) z = ∅} := by
          have heq : {z : SourceInput p | P rate rewards C_star C_h k (r - 1) z = ∅} =
              ⋂ i : Fin (p.m - 1), {z | i ∉ P rate rewards C_star C_h k (r - 1) z} := by
            ext z
            simp only [Set.mem_iInter, Set.mem_ofPred_eq,
              Finset.eq_empty_iff_forall_notMem]
          rw [heq]
          exact MeasurableSet.iInter fun i => (hmem i).compl
        have hinter : MeasurableSet[sourcePrefixFiltration control0 r]
            {z : SourceInput p | sigma rate rewards C_star C_h k z ≤ r ∧
              P rate rewards C_star C_h k (r - 1) z = ∅} :=
          (sigma_is_pre_round_stopping_time rate rewards C_star C_h control0 k r).inter hPempty
        exact (sourcePrefixFiltration control0).mono hrn _ hinter
      · have hrEq : r = p.T + 1 := by omega
        have hPempty (z : SourceInput p) :
            P rate rewards C_star C_h k (r - 1) z = ∅ :=
          P_eq_empty_of_horizon rate rewards C_star C_h k (r - 1) z (by omega)
        have hstop : MeasurableSet[sourcePrefixFiltration control0 r]
            {z : SourceInput p | sigma rate rewards C_star C_h k z ≤ r} :=
          sigma_is_pre_round_stopping_time rate rewards C_star C_h control0 k r
        have hEq : {z : SourceInput p | sigma rate rewards C_star C_h k z ≤ r ∧
              P rate rewards C_star C_h k (r - 1) z = ∅} =
            {z | sigma rate rewards C_star C_h k z ≤ r} := by
          ext z
          constructor
          · exact fun hz => hz.1
          · intro hz
            exact ⟨hz, hPempty z⟩
        rw [hEq]
        have hinter : MeasurableSet[sourcePrefixFiltration control0 r]
            {z : SourceInput p | sigma rate rewards C_star C_h k z ≤ r} := hstop
        exact (sourcePrefixFiltration control0).mono hrn _ hinter
  · have hempty : {z : SourceInput p |
        sigma rate rewards C_star C_h k z ≤ r ∧
          P rate rewards C_star C_h k (r - 1) z = ∅ ∧ r ≤ n} = ∅ := by
      ext z
      simp [hrn]
    rw [hempty]
    exact (sourcePrefixFiltration control0 n).measurableSet_empty

/-- The actual cutoff calendar is one interval, including the detecting
round under the inclusive first-bad gate. Empty ranks retain their start. -/
private theorem exists_support_interval (k : Fin (p.T + 1)) (z : SourceInput p) :
    ∃ b : ℕ, sigma rate rewards C_star C_h k z ≤ b ∧ b ≤ p.T + 1 ∧
      ∀ n : ℕ, (P rate rewards C_star C_h k n z).Nonempty ↔
        sigma rate rewards C_star C_h k z ≤ n + 1 ∧ n + 1 < b := by
  let S := sigma rate rewards C_star C_h k z
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  obtain hempty | ⟨e, registers, owned, base, seg, hdate, _hstate, _hat,
      _hentry, hne, _hcut, _hpayload, hcalendar, hprojection, hrun, _hno, _hend⟩ :=
    ReferenceOriginalKthCollectionCutoffAlignment.kthCDates_empty_or_actual_cutoff_segment
      rate rewards C_star C_h z k
  · refine ⟨S, le_rfl, sigma_le_sentinel rate rewards C_star C_h k z, ?_⟩
    intro n
    by_cases hn : n < p.T
    · rw [P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k n z hn, hempty]
      simp only [Finset.notMem_empty, false_iff, not_and_or, not_le, not_lt]
      omega
    · rw [P_eq_empty_of_horizon rate rewards C_star C_h k n z (by omega)]
      simp only [Finset.not_nonempty_empty, false_iff, not_and_or, not_le, not_lt]
      omega
  · have hS : S = s + e.val + 1 := hdate
    rw [hrun] at hprojection
    have hlen : 0 < seg.records.length := List.length_pos_iff.mpr hne
    let last : Fin seg.records.length := ⟨seg.records.length - 1, by omega⟩
    have hlast := (hcalendar last).2.1
    have hlastT := (seg.records[last.val]).input.time.isLt
    have hendT : s + e.val + seg.records.length + 1 ≤ p.T + 1 := by
      dsimp only [last] at hlast
      change _ + 1 = s + e.val + (seg.records.length - 1) + 1 at hlast
      omega
    let b := max S (min (s + e.val + seg.records.length + 1) (beta + 1))
    have hbT : b ≤ p.T + 1 := max_le (sigma_le_sentinel rate rewards C_star C_h k z)
      ((min_le_left _ _).trans hendT)
    refine ⟨b, le_max_left _ _, hbT, ?_⟩
    intro n
    by_cases hn : n < p.T
    · rw [P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k n z hn, hprojection,
        ReferenceOriginalKthCollectionCutoffAlignment.mem_actualCutoffChoiceDates_iff]
      constructor
      · rintro ⟨r, hr, _hc, hbeta, ht⟩
        obtain ⟨j, hj, hrj⟩ := List.mem_iff_getElem.mp hr
        have hd := (hcalendar ⟨j, hj⟩).2.1
        rw [hrj, ht] at hd
        change n + 1 = s + e.val + j + 1 at hd
        rw [ht] at hbeta
        change n + 1 ≤ beta at hbeta
        change S ≤ n + 1 ∧ n + 1 < b
        dsimp only [b]
        omega
      · rintro ⟨hstart, hb⟩
        change S ≤ n + 1 at hstart
        have hbounds : n + 1 < s + e.val + seg.records.length + 1 ∧
            n + 1 ≤ beta := by
          dsimp only [b] at hb
          omega
        let j : Fin seg.records.length := ⟨n - (s + e.val), by omega⟩
        obtain ⟨_hlookup, hd, c, hc, _hp⟩ := hcalendar j
        have ht : seg.records[j.val].input.time = (⟨n, hn⟩ : Fin p.T) := by
          apply Fin.ext
          have hjval : j.val = n - (s + e.val) := rfl
          change _ = n
          omega
        refine ⟨seg.records[j.val], List.getElem_mem j.isLt, ?_, ?_, ht⟩
        · rw [hc]; rfl
        · rw [ht]
          exact hbounds.2
    · rw [P_eq_empty_of_horizon rate rewards C_star C_h k n z (by omega)]
      simp only [Finset.not_nonempty_empty, false_iff, not_and_or, not_le, not_lt]
      omega

/-- On every natural index the literal pending support has exactly the
original start and its canonical first-excluded endpoint. -/
theorem P_nonempty_iff_phase (k : Fin (p.T + 1)) (z : SourceInput p) (n : ℕ) :
    (P rate rewards C_star C_h k n z).Nonempty ↔
      sigma rate rewards C_star C_h k z ≤ n + 1 ∧
        n + 1 < theta rate rewards C_star C_h k z := by
  obtain ⟨b, hSb, hbT, hphase⟩ := exists_support_interval rate rewards C_star C_h k z
  have hbempty : P rate rewards C_star C_h k (b - 1) z = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rw [hphase]
    have hbpos : 1 ≤ b := (sigma_pos rate rewards C_star C_h k z).trans hSb
    omega
  have hcand : b ∈ firstEmptyCandidates rate rewards C_star C_h k z :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hSb, hbT⟩, hbempty⟩
  have hthetab : theta rate rewards C_star C_h k z ≤ b := Finset.min'_le _ _ hcand
  have hbtheta : b ≤ theta rate rewards C_star C_h k z := by
    have he := P_empty_before_theta rate rewards C_star C_h k z
    have hbounds := endpoint_bounds rate rewards C_star C_h k z
    have hthetaPos : 1 ≤ theta rate rewards C_star C_h k z := hbounds.1.trans hbounds.2.1
    have hnot : ¬ (P rate rewards C_star C_h k
        (theta rate rewards C_star C_h k z - 1) z).Nonempty := by rw [he]; simp
    rw [hphase] at hnot
    omega
  have heq : theta rate rewards C_star C_h k z = b := Nat.le_antisymm hthetab hbtheta
  rw [heq]
  exact hphase n

private theorem connected_adjacent
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (j : ℕ) (hj : j + 1 < records.length) :
    (records[j + 1]'hj).input.state = (records[j]'(by omega)).output.next := by
  induction j generalizing records initial with
  | zero =>
      cases records with
      | nil => simp at hj
      | cons r rest =>
          cases rest with
          | nil => simp at hj
          | cons q tail => exact hchain.2.1
  | succ j ih =>
      cases records with
      | nil => simp at hj
      | cons r rest =>
          exact ih rest r.output.next hchain.2 (by simpa using hj)

private theorem collection_step_pending_subset
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload cp : ReferenceActivePhysicalStep.Payload rate)
    (old out : ReferenceActivePhysicalStep.Ledger rate) (proposal saved : Option (Fin p.T × Bool))
    (hc : x.state.coordinator = .collection payload old proposal)
    (hf : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection cp out saved) :
    out.pending ⊆ old.pending := by
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
    change (match ReferenceActivePhysicalStep.dispatch x with
      | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => true
      | _ => false) = false
    by_cases hv : 1 ≤ old.cutoff ∧ old.cutoff ≤ p.T
    all_goals simp only [ReferenceActivePhysicalStep.dispatch, hc, hv,
      ↓reduceDIte, CoordinatorRoundDispatch.dispatch]
    all_goals rfl
  obtain ⟨tail, ht, hp, _hs⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame x cp out saved hf
  obtain ⟨_hn, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin ht
  rcases horigin with ⟨htrue, _⟩ | ⟨_hfalse, op, ol, os, ho, he⟩
  · rw [hcut] at htrue
    contradiction
  · rw [hc] at ho
    cases ho
    rw [he] at hp
    rw [hp]
    cases ReferenceCollectionPhaseHistory.acceptedLabel x with
    | none => exact Finset.Subset.refl _
    | some i => exact Finset.erase_subset i old.pending

/-- The actual task set shrinks after its original start. A detecting round
uses its incoming pending set; an excluded successor is simply empty. -/
theorem P_succ_subset (k : Fin (p.T + 1)) (z : SourceInput p) (n : ℕ)
    (hstart : sigma rate rewards C_star C_h k z ≤ n + 1) :
    P rate rewards C_star C_h k (n + 1) z ⊆ P rate rewards C_star C_h k n z := by
  by_cases hnext : (P rate rewards C_star C_h k (n + 1) z).Nonempty
  · have hnextPhase := (P_nonempty_iff_phase rate rewards C_star C_h k z (n + 1)).mp hnext
    have hprev : (P rate rewards C_star C_h k n z).Nonempty :=
      (P_nonempty_iff_phase rate rewards C_star C_h k z n).mpr ⟨hstart, by omega⟩
    have hn1 : n + 1 < p.T := by
      by_contra h
      rw [P_eq_empty_of_horizon rate rewards C_star C_h k (n + 1) z (by omega)] at hnext
      exact Finset.not_nonempty_empty hnext
    have hn : n < p.T := by omega
    obtain ⟨r, c, hr, hc, hP, _hne⟩ := P_eq_actualChoicePending_of_mem_kthCDates
      rate rewards C_star C_h k ⟨n, hn⟩ z
      ((P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k n z hn).mp hprev)
    obtain ⟨q, d, hq, hd, hQ, _hneQ⟩ := P_eq_actualChoicePending_of_mem_kthCDates
      rate rewards C_star C_h k ⟨n + 1, hn1⟩ z
      ((P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k (n + 1) z hn1).mp hnext)
    rw [hP, hQ]
    obtain ⟨_selected, _data, _hsel, _hpay, _hpend, _hdata, _hdpay, _hdpend,
      _hdcut, hframe⟩ := ReferenceOriginalKthCollectionCutoffAlignment.actual_choice_pending_frame
        rate rewards C_star C_h z ⟨n, hn⟩ r hr c hc
    rcases hframe with ⟨_live, _owned, _base, _init, _hs, _hi, _hchecked, huniv⟩ |
      ⟨payload, old, proposal, hstate, hledger, _hinit⟩
    · rw [huniv]
      exact Finset.subset_univ _
    · obtain ⟨j, hjr, hjtime⟩ := actualRecord_suffixIndex rate rewards C_star C_h ⟨n, hn⟩ z r hr
      obtain ⟨a, haq, hatime⟩ := actualRecord_suffixIndex rate rewards C_star C_h ⟨n + 1, hn1⟩ z q hq
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      have hjdate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z j
      have hadate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z a
      rw [hjr, hjtime] at hjdate
      rw [haq, hatime] at hadate
      change n + 1 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val + 1 at hjdate
      change n + 1 + 1 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a.val + 1 at hadate
      have haj : a.val = j.val + 1 := by omega
      have hlink : q.input.state = r.output.next := by
        cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate z rewards C_star C_h with
        | none =>
            have hempty : R = [] := by
              simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch]
            have hj := j.isLt
            change j.val < R.length at hj
            rw [hempty] at hj
            simp at hj
        | some active =>
            have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
              rate z rewards C_star C_h active hlaunch
            have h := connected_adjacent rate _ _ _ hchain j.val
              (by have ha := a.isLt; omega)
            have h' : R[a.val].input.state = R[j.val].output.next := by
              simpa only [haj] using h
            exact (congrArg (fun rr : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate) => rr.input.state) haq).symm.trans
                (h'.trans (congrArg (fun rr : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) => rr.output.next) hjr))
      have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
        (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights
      rw [← ReferenceCollectionSegmentExtraction.choice_tail r.input c hc] at hphase
      change ReferenceCollectionPhaseHistory.CollectionPhase
        (ReferenceActivePhysicalStep.step r.input).next.coordinator at hphase
      rw [← r.output_eq, ← hlink] at hphase
      rcases hphase with hdagger | ⟨cp, out, saved, hout⟩
      · simp [ReferenceCollectionSegmentExtraction.choice, ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, hdagger,
          ReferenceActivePhysicalStep.DispatchCut.selection] at hd
      · have hdledger := (ReferenceCollectionSegmentExtraction.choice_collection_pre
          q.input cp out saved d hout hd).1
        rw [hdledger, hledger]
        apply collection_step_pending_subset rate r.input payload cp old out proposal saved hstate
        rw [← r.output_eq, ← hlink]
        exact hout
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnext]
    exact Finset.empty_subset _

/-- Every later prefix retains a subset of the actual tasks at an earlier
prefix after the original ranked start. This is the nesting input for phase
waiting, without an additional restriction on the later endpoint. -/
theorem P_subset_of_le (k : Fin (p.T + 1)) (z : SourceInput p) (a b : ℕ)
    (hab : a ≤ b) (hstart : sigma rate rewards C_star C_h k z ≤ a + 1) :
    P rate rewards C_star C_h k b z ⊆ P rate rewards C_star C_h k a z := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b hab ih =>
      exact (P_succ_subset rate rewards C_star C_h k z b (by omega)).trans ih

/-- The original collection support charge is literally the finite natural
sum charged on nonempty actual pending sets. -/
theorem collection_support_charge_eq (k : Fin (p.T + 1)) (z : SourceInput p) :
    (∑ t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k,
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)) =
    ∑ n ∈ Finset.range p.T,
      if hn : n < p.T then
        if (P rate rewards C_star C_h k n z).Nonempty then
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards ⟨n, hn⟩ : ℝ)
        else 0
      else 0 := by
  have hfilter : (Finset.univ.filter fun t : Fin p.T =>
      (P rate rewards C_star C_h k t.val z).Nonempty) =
      ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact P_nonempty_iff_mem_kthCDates rate rewards C_star C_h k t.val z t.isLt
  calc
    _ = ∑ t : Fin p.T, if (P rate rewards C_star C_h k t.val z).Nonempty then
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
        else 0 := by rw [← hfilter, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro t _ht
      simp only [t.isLt, dite_eq_left]

end Bandits.Support.ReferenceOriginalKthCollectionPhaseSupport

end
