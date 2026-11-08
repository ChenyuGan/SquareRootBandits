/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase
public import Bandits.Support.ReferenceOriginalInstallationReleaseDataSection
public import Bandits.Support.ReferenceOriginalInstallationReleaseUpSection
public import Bandits.Support.ReferenceOriginalInstallationReleaseSignedCharge

import Mathlib.Tactic

/-!
# Later-installation predictable release projections on the original source

Sources: `sources/zip4/manuscript/05_binary_transport.tex:293-349` and
`sources/zip4/manuscript/06_interruptions.tex:431-490`.

These are analysis projections on the original source input. They retain the
fixed absolute installation timestamp and the existing stopped-release
observer.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalLaterReleasePredictableService

variable {p : ConstructorDimensions.Parameters}

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev RateInput (p : ConstructorDimensions.Parameters) :=
  ReferenceActivePhysicalStep.RateInput p
abbrev GridRewardTable (p : ConstructorDimensions.Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-! The following birth predicate reads the existing actual source record at
the fixed physical timestamp. It does not choose a suffix witness. -/

public def laterBirth (s : ℕ) (z : Source p) : Prop :=
  ∃ hs : s < p.T,
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ⟨s, hs⟩ z = some r ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true

public def Llate (s k : ℕ) (z : Source p) : Prop :=
  laterBirth rate rewards C_star C_h s z ∧
    ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h s k z

public def Plate (s k : ℕ) (z : Source p) : Finset (Fin (p.m - 1)) :=
  if laterBirth rate rewards C_star C_h s z then
    ReferenceOriginalInstallationStoppedReleasePhase.pendingAt
      rate rewards C_star C_h s k z
  else ∅

public def c_i (i : Fin (p.m - 1)) (s k : ℕ) (z : Source p) : ℝ :=
  if Llate rate rewards C_star C_h s k z then
    if hk : k < p.T then
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          ⟨k, hk⟩ z with
      | none => 0
      | some r =>
        match r.output.preparation.coordinator.selection with
        | none => 0
        | some selected =>
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards ⟨k, hk⟩)
            (selected.view.payload.assignment.assigned i)
    else 0
  else 0

public def omega (s k : ℕ) (z : Source p) : ℝ :=
  if Llate rate rewards C_star C_h s k z then
    if hk : k < p.T then
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          ⟨k, hk⟩ z with
      | none => 0
      | some r =>
        match r.output.preparation.coordinator.selection with
        | none => 0
        | some selected =>
          ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
            rate selected
            (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
              rate selected) *
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards ⟨k, hk⟩)
              (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
                rate selected).val
    else 0
  else 0

public def Dlate (s k : ℕ) (z : Source p) : ℝ :=
  if Llate rate rewards C_star C_h s k z then
    if hk : k < p.T then
      ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
        rate rewards C_star C_h s ⟨k, hk⟩ z
    else 0
  else 0

theorem Plate_eq_pending_of_Llate (s k : ℕ) (z : Source p)
    (h : Llate rate rewards C_star C_h s k z) :
  Plate rate rewards C_star C_h s k z =
      ReferenceOriginalInstallationStoppedReleasePhase.pendingAt
        rate rewards C_star C_h s k z := by
  simp [Plate, h.1]

theorem Plate_eq_empty_of_not_laterBirth (s k : ℕ) (z : Source p)
    (h : ¬ laterBirth rate rewards C_star C_h s z) :
    Plate rate rewards C_star C_h s k z = ∅ := by
  simp [Plate, h]

theorem Plate_mem_iff (i : Fin (p.m - 1)) (s k : ℕ) (z : Source p) :
    i ∈ Plate rate rewards C_star C_h s k z ↔
      laterBirth rate rewards C_star C_h s z ∧
        i ∈ ReferenceOriginalInstallationStoppedReleasePhase.pendingAt
          rate rewards C_star C_h s k z := by
  by_cases hb : laterBirth rate rewards C_star C_h s z <;>
    simp [Plate, hb]

theorem Dlate_eq_signed_of_Llate (s k : ℕ) (z : Source p)
    (h : Llate rate rewards C_star C_h s k z) (hk : k < p.T) :
    Dlate rate rewards C_star C_h s k z =
      ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
        rate rewards C_star C_h s ⟨k, hk⟩ z := by
  simp [Dlate, h, hk]

theorem Dlate_eq_zero_of_not_Llate (s k : ℕ) (z : Source p)
    (h : ¬ Llate rate rewards C_star C_h s k z) :
    Dlate rate rewards C_star C_h s k z = 0 := by
  simp [Dlate, h]

theorem Dlate_abs_le (s k : ℕ) (z : Source p) :
    |Dlate rate rewards C_star C_h s k z| ≤ 2 * (p.m : ℝ) := by
  by_cases hl : Llate rate rewards C_star C_h s k z
  · by_cases hk : k < p.T
    · rw [Dlate_eq_signed_of_Llate rate rewards C_star C_h s k z hl hk]
      exact ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_abs_le
        rate rewards C_star C_h s ⟨k, hk⟩ z
    · simp [Dlate, hl, hk]
  · simp [Dlate, hl]

theorem Llate_birth_precedes_round (s k : ℕ) (z : Source p)
    (hlate : Llate rate rewards C_star C_h s k z) : s < k := by
  have hsupported := hlate.2
  have hk : k < p.T := by
    by_contra hnot
    have hge : p.T ≤ k := Nat.le_of_not_gt hnot
    exact (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_false_of_ge_horizon
      rate rewards C_star C_h s k z hge) hsupported
  let t : Fin p.T := ⟨k, hk⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hsupport :=
    (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_stopped_originalGate
      rate rewards C_star C_h s k z hk).mp hsupported
  have hgateMem : k + 1 ∈
      ReferenceLocalReleaseGateChronology.gateSupport s R := by
    simpa [R, ReferenceOriginalInstallationStoppedReleasePhase.originalGateSupport] using
      hsupport.1
  obtain ⟨gatedRecord, hrecordMem, hgate, hdate⟩ :=
    (ReferenceLocalReleaseGateChronology.mem_gateSupport
      (rate := rate) s (k + 1) R).mp hgateMem
  have hlaunch :=
    ReferenceOriginalInstallationStoppedReleasePhase.supportAt_actualLaunchBy
      rate rewards C_star C_h s t z hsupported
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome =
        true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hlaunch.1
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hlaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active := by
    simpa only [active] using
      ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross
  have helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = start := by
    dsimp [start, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hstartLe : start ≤ p.T :=
    ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : start + (p.T - start) ≤ p.T := by omega
  have hrun : (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
      hcross start (p.T - start) helapsed hspan).records = R := by
    simpa [R, start, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceLocalReleaseGateChronology.sourceRun] using
      (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h active hlaunch').symm
  have hrecordMem' : gatedRecord ∈
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
        hcross start (p.T - start) helapsed hspan).records := by
    rw [hrun]
    exact hrecordMem
  obtain ⟨_payload, _birth, _stored₁, _stored₂, _stamp, _birthMem,
    _installationBirth, _birthTime, hbefore, _hbefore₂⟩ :=
    ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
      rate z rewards C_star C_h hcross start (p.T - start) helapsed hspan s
      gatedRecord hrecordMem' gatedRecord hrecordMem' hgate hgate
  have htime : gatedRecord.input.time.val = k := by omega
  rw [htime] at hbefore
  exact hbefore

theorem laterBirth_actualSuffixIndex (s : ℕ) (z : Source p)
    (hbirth : laterBirth rate rewards C_star C_h s z) :
    ∃ hs : s < p.T,
      ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length,
        s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val ∧
        ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input = true ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          ⟨s, hs⟩ z =
            some (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[b.val] := by
  rcases hbirth with ⟨hs, r, hr, hlater⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hstart : start ≤ s := by
    by_contra hnot
    have hnot' : ¬ start ≤ s := by omega
    have hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ⟨s, hs⟩ z = none := by
      simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hnot']
    rw [hnone] at hr
    cases hr
  have hget : R[s - start]? = some r := by
    simpa [R, start, ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart] using hr
  have hget' : some r = R[s - start]? := hget.symm
  rw [eq_comm, List.getElem?_eq_some_iff] at hget'
  rcases hget' with ⟨hindex, hrecord⟩
  let b : Fin R.length := ⟨s - start, hindex⟩
  have htime : s = start + b.val := by
    dsimp [b, start]
    omega
  have hR : R[b.val] = r := by
    simpa only [b] using hrecord
  refine ⟨hs, b, ?_, ?_, ?_⟩
  · simpa [start] using htime
  · rw [hR]
    exact hlater
  · rw [hR]
    exact hr

theorem laterBirth_of_actualSuffixIndex
    (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    laterBirth rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) z := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z b
  have hs : start + b.val < p.T := by
    dsimp [start] at htime ⊢
    omega
  have hstart : start ≤ start + b.val := by omega
  have hindex : (start + b.val) - start = b.val := by omega
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ⟨start + b.val, hs⟩ z = some R[b.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left hstart, hindex]
    exact List.getElem?_eq_getElem b.isLt
  exact ⟨hs, R[b.val], by simpa [R, start] using hrecord, hb⟩

theorem actual_selection_on_Llate
    (_control0 : TimeControl p) (s : ℕ) (t : Fin p.T) (z : Source p)
    (hlate : Llate rate rewards C_star C_h s t.val z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        r.input.time = t := by
  obtain ⟨hlater, hsupported⟩ := hlate
  obtain ⟨_hs, b, htime, hbirth, _hbirthRecord⟩ :=
    laterBirth_actualSuffixIndex rate rewards C_star C_h s z hlater
  have hgate :=
    (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
      rate rewards C_star C_h s t.val z t.isLt).mp hsupported
  rw [htime] at hgate
  obtain ⟨r, hr, hrtime, hframe⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame
      rate rewards C_star C_h _control0 z b t hbirth hgate.1
  rcases hframe with ⟨_registers, _owned, _base, selected, _states, _memories, hrest⟩
  exact ⟨r, selected, hr, hrest.2.2.2.1, hrtime⟩

theorem c_i_eq_actual_assignment
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (s : ℕ) (t : Fin p.T)
    (z : Source p) (hlate : Llate rate rewards C_star C_h s t.val z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        c_i rate rewards C_star C_h i s t.val z =
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i) := by
  obtain ⟨r, selected, hr, hselection, _hrtime⟩ :=
    actual_selection_on_Llate rate rewards C_star C_h control0 s t z hlate
  have hdef : c_i rate rewards C_star C_h i s t.val z =
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (selected.view.payload.assignment.assigned i) := by
    simp [c_i, hlate, t.isLt, hr, hselection]
  exact ⟨r, selected, hr, hselection, hdef⟩

theorem omega_eq_actual_auxiliary
    (control0 : TimeControl p) (s : ℕ) (t : Fin p.T) (z : Source p)
    (hlate : Llate rate rewards C_star C_h s t.val z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        omega rate rewards C_star C_h s t.val z =
          ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
            rate selected
            (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
              rate selected) *
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
              rate selected).val := by
  obtain ⟨r, selected, hr, hselection, _hrtime⟩ :=
    actual_selection_on_Llate rate rewards C_star C_h control0 s t z hlate
  have hdef : omega rate rewards C_star C_h s t.val z =
      ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
        rate selected
        (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
          rate selected) *
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
          rate selected).val := by
    simp [omega, hlate, t.isLt, hr, hselection]
  exact ⟨r, selected, hr, hselection, hdef⟩

private theorem actual_later_index_gate_pending
    (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hlate : Llate rate rewards C_star C_h s t.val z)
    (hi : i ∈ Plate rate rewards C_star C_h s t.val z) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val ∧
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input = true ∧
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        t z).map Prod.fst = some true ∧
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        t z := by
  have hiPhase := (Plate_mem_iff rate rewards C_star C_h i s t.val z).mp hi
  have hiObserved :=
    (ReferenceOriginalInstallationStoppedReleasePhase.pendingAt_eq_observed_of_support
      rate rewards C_star C_h s t.val z t.isLt hlate.2) ▸ hiPhase.2
  obtain ⟨_hs, b, htime, hbirth, _hbirthRecord⟩ :=
    laterBirth_actualSuffixIndex rate rewards C_star C_h s z hlate.1
  have hgate :=
    (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
      rate rewards C_star C_h s t.val z t.isLt).mp hlate.2
  rw [htime] at hgate
  refine ⟨b, htime, hbirth, hgate.1, ?_⟩
  simpa only [htime] using hiObserved

private theorem selectedFastArmMass_auxiliary_le_one
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x) :
    0 ≤ ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass rate selected
        (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
          rate selected) ∧
      ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass rate selected
        (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
          rate selected) ≤ 1 := by
  classical
  let e := ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
    rate selected
  have hnonneg (j : CanonicalFastSampling.FastArm selected.view.payload.slowSet) :
      0 ≤ ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
        rate selected j :=
    CanonicalFastSampling.qGamma_nonneg p rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      selected.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _ j
  have hsum : ∑ j : CanonicalFastSampling.FastArm selected.view.payload.slowSet,
      ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
        rate selected j = 1 :=
    CanonicalFastSampling.qGamma_sum_eq_one p rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      selected.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _
  refine ⟨hnonneg e, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ e)

theorem c_i_bounds
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (s k : ℕ) (z : Source p) :
    0 ≤ c_i rate rewards C_star C_h i s k z ∧
      c_i rate rewards C_star C_h i s k z ≤ 1 := by
  by_cases hlate : Llate rate rewards C_star C_h s k z
  · by_cases hk : k < p.T
    · let t : Fin p.T := ⟨k, hk⟩
      obtain ⟨_, selected, _, _, hci⟩ :=
        c_i_eq_actual_assignment rate rewards C_star C_h control0 i s t z hlate
      rw [hci]
      have hchi : 0 ≤ ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (selected.view.payload.assignment.assigned i) ∧
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i) ≤ 1 := by
        unfold ReleaseRoundKernel.chi
        split_ifs <;> norm_num
      exact hchi
    · simp [c_i, hlate, hk]
  · simp [c_i, hlate]

theorem omega_bounds
    (control0 : TimeControl p) (s k : ℕ) (z : Source p) :
    0 ≤ omega rate rewards C_star C_h s k z ∧
      omega rate rewards C_star C_h s k z ≤ 1 := by
  by_cases hlate : Llate rate rewards C_star C_h s k z
  · by_cases hk : k < p.T
    · let t : Fin p.T := ⟨k, hk⟩
      obtain ⟨r, selected, _, _, hω⟩ :=
        omega_eq_actual_auxiliary rate rewards C_star C_h control0 s t z hlate
      rw [hω]
      let e := ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
        rate selected
      have hmass := selectedFastArmMass_auxiliary_le_one rate selected
      have hchi :
          0 ≤ ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) e.val ∧
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) e.val ≤ 1 := by
        unfold ReleaseRoundKernel.chi
        split_ifs <;> norm_num
      refine ⟨mul_nonneg hmass.1 hchi.1, ?_⟩
      have hmassRest : 0 ≤ 1 -
          ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
            rate selected e := sub_nonneg.mpr hmass.2
      have hchiRest : 0 ≤ 1 -
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) e.val :=
        sub_nonneg.mpr hchi.2
      have hrest := mul_nonneg hmassRest hchi.1
      nlinarith
    · simp [omega, hlate, hk]
  · simp [omega, hlate]

theorem actual_data_condExp_on_Llate
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (s : ℕ) (t : Fin p.T) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      Llate rate rewards C_star C_h s t.val z →
      i ∈ Plate rate rewards C_star C_h s t.val z →
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] z =
        c_i rate rewards C_star C_h i s t.val z / (2 * (p.K : ℝ)) := by
  filter_upwards
    [ReferenceOriginalInstallationReleaseDataSection.actual_later_local_release_data_condExp
      rate rewards C_star C_h control0 i t] with z hsection
  intro hlate hi
  obtain ⟨b, _htime, hbirth, hgate, hipending⟩ :=
    actual_later_index_gate_pending rate rewards C_star C_h s i t z hlate hi
  obtain ⟨r, selected, hr, hselection, hvalue⟩ :=
    hsection b hbirth hgate hipending
  obtain ⟨r', selected', hr', hselection', hci⟩ :=
    c_i_eq_actual_assignment rate rewards C_star C_h control0 i s t z hlate
  have hrEq : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  have hselectionEq : selected' = selected :=
    Option.some.inj (hselection'.symm.trans hselection)
  subst selected'
  simpa only [hci] using hvalue

theorem actual_data_condExp_all_on_Llate
    (control0 : TimeControl p) (s : ℕ) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ t : Fin p.T, ∀ i : Fin (p.m - 1),
        Llate rate rewards C_star C_h s t.val z →
        i ∈ Plate rate rewards C_star C_h s t.val z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
              rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z =
        c_i rate rewards C_star C_h i s t.val z / (2 * (p.K : ℝ)) := by
  rw [ae_all_iff]
  intro t
  rw [ae_all_iff]
  intro i
  exact actual_data_condExp_on_Llate rate rewards C_star C_h control0 i s t

theorem actual_up_condExp_lower_on_Llate
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (s : ℕ) (t : Fin p.T) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      Llate rate rewards C_star C_h s t.val z →
      i ∈ Plate rate rewards C_star C_h s t.val z →
      omega rate rewards C_star C_h s t.val z /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
              rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z := by
  filter_upwards
    [ReferenceOriginalInstallationReleaseUpSection.actualUpControlSection_condExp_on_later_local_release
      rate rewards C_star C_h control0 i t] with z hsection
  intro hlate hi
  obtain ⟨b, _htime, hbirth, hgate, hipending⟩ :=
    actual_later_index_gate_pending rate rewards C_star C_h s i t z hlate hi
  obtain ⟨_hglobal, hcase⟩ := hsection
  obtain ⟨r, selected, hr, hselection, _hweights, _hmass, hlower⟩ :=
    hcase b hbirth hgate hipending
  obtain ⟨r', selected', hr', hselection', hω⟩ :=
    omega_eq_actual_auxiliary rate rewards C_star C_h control0 s t z hlate
  have hrEq : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  have hselectionEq : selected' = selected :=
    Option.some.inj (hselection'.symm.trans hselection)
  subst selected'
  let e := ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
    rate selected
  let χ := ReleaseRoundKernel.chi
    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) e.val
  have hχ : 0 ≤ χ := by
    dsimp [χ, ReleaseRoundKernel.chi]
    split_ifs <;> positivity
  have hmass : ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
      rate selected e ≤ 1 := by
    exact (selectedFastArmMass_auxiliary_le_one rate selected).2
  have hproduct : ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
      rate selected e * χ ≤ χ := by
    have hfactor : 0 ≤ 1 -
        ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass rate selected e :=
      sub_nonneg.mpr hmass
    have hnonneg := mul_nonneg hfactor hχ
    nlinarith
  have haux : e.val = selected.view.payload.assignment.auxiliary := rfl
  have hweighted : omega rate rewards C_star C_h s t.val z ≤
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        selected.view.payload.assignment.auxiliary := by
    rw [hω]
    rw [haux]
    simpa [χ, e, haux] using hproduct
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)
  have hm' : 0 ≤ (p.m : ℝ) - 1 := sub_nonneg.mpr hm
  have hK : (0 : ℝ) < (p.K : ℝ) := by
    exact_mod_cast ConstructorDimensions.K_pos p
  have hdenom : 0 ≤ 12 * (p.m - 1 : ℝ) * (p.K : ℝ) := by positivity
  calc
    omega rate rewards C_star C_h s t.val z /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected.view.payload.assignment.auxiliary /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) :=
      div_le_div_of_nonneg_right hweighted hdenom
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] z := hlower

theorem actual_up_condExp_lower_all_on_Llate
    (control0 : TimeControl p) (s : ℕ) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ t : Fin p.T, ∀ i : Fin (p.m - 1),
        Llate rate rewards C_star C_h s t.val z →
        i ∈ Plate rate rewards C_star C_h s t.val z →
        omega rate rewards C_star C_h s t.val z /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
                rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
              control0 (t.val + 1)] z := by
  rw [ae_all_iff]
  intro t
  rw [ae_all_iff]
  intro i
  exact actual_up_condExp_lower_on_Llate rate rewards C_star C_h control0 i s t

/-- Only the collection tag and its existing pending ledger are inspected. -/
def emptyCollectionCode
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) : Bool :=
  match code.1 with
  | .inr (.inr (.inl (_, ledger, _))) => decide (ledger.pending = ∅)
  | _ => false

private theorem emptyCollectionCode_measurable :
    Measurable (emptyCollectionCode (p := p) rate) := by
  let read : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool :=
    Sum.elim (fun _ => false) (Sum.elim (fun _ => false)
      (Sum.elim (fun c => decide (c.2.1.pending = ∅)) (fun _ => false)))
  have hread : Measurable read :=
    measurable_const.sumElim (measurable_const.sumElim
      (((measurable_of_countable (fun l : ReferenceActivePhysicalStep.Ledger rate =>
        decide (l.pending = ∅))).comp
          (measurable_fst.comp measurable_snd)).sumElim measurable_const))
  convert hread.comp measurable_fst using 1
  funext code
  rcases code with ⟨coord, rest⟩
  cases coord with
  | inl u => rfl
  | inr tail => cases tail with
    | inl live => rfl
    | inr tail => cases tail <;> rfl

private theorem actual_empty_collection_laterChosen
    (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hc : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.coordinator = .collection P l saved)
    (he : l.pending = ∅) :
    ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true := by
  have h := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z b
  dsimp only at h
  rw [hc] at h
  obtain ⟨u, _hu, core, started, hstart, instruction, hassignment, _htime, _hkind,
    consistent, output, hlocal, _hlater, clockData, installation, selected,
    _hinstall, _hresult, _hdispatch, hprepared, _rest⟩ := h he
  have hprep : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].output.preparation =
      ReferenceActivePhysicalStep.prepare (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input := by
    rw [(ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen
  rw [← hprep, hprepared]

/-- On an actual record the administrative birth test is exactly its incoming
collection tag with an empty pending ledger. This uses the actual corrected or
renewal producer, including the boundary equality case. -/
theorem laterBirth_iff_incoming (s : Fin p.T) (z : Source p) :
    laterBirth rate rewards C_star C_h s.val z ↔
      ReferenceCollectionOutcomeMeasurability.optionalElim false
        (emptyCollectionCode rate) (incoming rate rewards C_star C_h s z) = true := by
  cases hr : actualRecord rate rewards C_star C_h s z with
  | none =>
      simp only [incoming, hr, Option.map_none,
        ReferenceCollectionOutcomeMeasurability.optionalElim]
      constructor
      · rintro ⟨hs, r, hr', _⟩
        rw [hr] at hr'
        cases hr'
      · intro h
        cases h
  | some r =>
      simp only [incoming, hr, Option.map_some,
        ReferenceCollectionOutcomeMeasurability.optionalElim]
      constructor
      · rintro ⟨hs, r', hr', hb⟩
        have heq : r' = r := Option.some.inj (hr'.symm.trans hr)
        subst r'
        obtain ⟨P, l, saved, hc, he⟩ :=
          ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hb
        simp only [emptyCollectionCode, ReferenceActivePhysicalStepMeasurability.encodeState,
          hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator, he, decide_true]
      · intro he
        have hs : ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h ≤ s.val := by
          by_contra hn
          simp only [actualRecord, ite_eq_right hn] at hr
          cases hr
        have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[s.val - ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h]? = some r := by
          simpa only [actualRecord, ite_eq_left hs] using hr
        obtain ⟨hb, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
        let b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length := ⟨_, hb⟩
        have hbr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val] = r := hrecord
        refine ⟨s.isLt, r, hr, ?_⟩
        cases hc : r.input.state.coordinator with
        | first => simp [emptyCollectionCode, ReferenceActivePhysicalStepMeasurability.encodeState,
            hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator] at he
        | live registers owned base =>
            simp [emptyCollectionCode, ReferenceActivePhysicalStepMeasurability.encodeState,
              hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator] at he
        | dagger => simp [emptyCollectionCode, ReferenceActivePhysicalStepMeasurability.encodeState,
            hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator] at he
        | collection P l saved =>
            have hempty : l.pending = ∅ := by
              simpa only [emptyCollectionCode, ReferenceActivePhysicalStepMeasurability.encodeState,
                hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator, decide_eq_true_eq] using he
            rw [← hbr]
            exact actual_empty_collection_laterChosen rate rewards C_star C_h z b P l saved
              (hbr ▸ hc) hempty

theorem laterBirth_prefix_factor (control0 : TimeControl p) (s : Fin p.T)
    (k : ℕ) (hsk : s.val ≤ k) (z : Source p) :
    laterBirth rate rewards C_star C_h s.val z ↔
      laterBirth rate rewards C_star C_h s.val (sourcePrefix control0 k z) := by
  rw [laterBirth_iff_incoming rate rewards C_star C_h s z,
    laterBirth_iff_incoming rate rewards C_star C_h s (sourcePrefix control0 k z),
    incoming_factor rate rewards C_star C_h control0 s z,
    incoming_factor rate rewards C_star C_h control0 s (sourcePrefix control0 k z),
    sourcePrefix_sourcePrefix control0 s.val k hsk z]

/-- The birth is tested only on stopped support, where its physical timestamp
has already occurred. No predictability before the birth is asserted. -/
theorem Llate_prefix_factor (control0 : TimeControl p) (s : ℕ)
    (t : Fin p.T) (z : Source p) :
    Llate rate rewards C_star C_h s t.val z ↔
      Llate rate rewards C_star C_h s t.val (sourcePrefix control0 t.val z) := by
  have hsupp := supportAt_prefix_factor rate rewards C_star C_h control0 s t z
  by_cases hs : s < p.T
  · by_cases hst : s ≤ t.val
    · exact and_congr (laterBirth_prefix_factor rate rewards C_star C_h control0
        ⟨s, hs⟩ t.val hst z) hsupp
    · constructor
      · intro h; exact False.elim (hst (Nat.le_of_lt
          (Llate_birth_precedes_round rate rewards C_star C_h s t.val z h)))
      · intro h; exact False.elim (hst (Nat.le_of_lt
          (Llate_birth_precedes_round rate rewards C_star C_h s t.val _ h)))
  · constructor <;> intro h <;> exact False.elim (hs h.1.choose)

theorem laterBirth_measurable (s : ℕ) :
    MeasurableSet {z : Source p | laterBirth rate rewards C_star C_h s z} := by
  by_cases hs : s < p.T
  · have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
        (emptyCollectionCode rate) (emptyCollectionCode_measurable rate)).comp
      (measurable_incoming rate rewards C_star C_h ⟨s, hs⟩)
    have heq : {z : Source p | laterBirth rate rewards C_star C_h s z} =
        {z | ReferenceCollectionOutcomeMeasurability.optionalElim false
          (emptyCollectionCode rate) (incoming rate rewards C_star C_h ⟨s, hs⟩ z) = true} := by
      ext z
      exact laterBirth_iff_incoming rate rewards C_star C_h ⟨s, hs⟩ z
    rw [heq]
    exact hm (measurableSet_singleton true)
  · have heq : {z : Source p | laterBirth rate rewards C_star C_h s z} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hs h.choose
    rw [heq]
    exact MeasurableSet.empty

theorem Llate_preRound_measurable (control0 : TimeControl p) (s : ℕ) (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | Llate rate rewards C_star C_h s t.val z} := by
  have hsupport := ((sourcePrefixFiltration control0).le (t.val + 1)) _
    (supportAt_preRound_measurable rate rewards C_star C_h control0 s t)
  have hm : MeasurableSet {z : Source p | Llate rate rewards C_star C_h s t.val z} :=
    (laterBirth_measurable rate rewards C_star C_h s).inter hsupport
  rw [sourcePrefixFiltration_succ]
  convert hm.preimage (comap_measurable (sourcePrefix control0 t.val)) using 1
  ext z
  exact Llate_prefix_factor rate rewards C_star C_h control0 s t z

theorem Llate_replaceSourceControl (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : Source p) (u : TimeControl p) :
    Llate rate rewards C_star C_h s t.val z ↔
      Llate rate rewards C_star C_h s t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) := by
  rw [Llate_prefix_factor rate rewards C_star C_h control0 s t z,
    Llate_prefix_factor rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z u]

theorem Plate_mem_iff_Llate (i : Fin (p.m - 1)) (s k : ℕ) (z : Source p) :
    i ∈ Plate rate rewards C_star C_h s k z ↔
      Llate rate rewards C_star C_h s k z ∧
        i ∈ pendingAt rate rewards C_star C_h s k z := by
  rw [Plate_mem_iff]
  constructor
  · rintro ⟨hb, hi⟩
    have hs : supportAt rate rewards C_star C_h s k z := by
      by_contra hn
      rw [pendingAt_eq_empty_of_not_support rate rewards C_star C_h s k z hn] at hi
      exact Finset.notMem_empty i hi
    exact ⟨⟨hb, hs⟩, hi⟩
  · exact fun h => ⟨h.1.1, h.2⟩

theorem Plate_prefix_factor (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : Source p) :
    Plate rate rewards C_star C_h s t.val z =
      Plate rate rewards C_star C_h s t.val (sourcePrefix control0 t.val z) := by
  ext i
  rw [Plate_mem_iff_Llate, Plate_mem_iff_Llate,
    Llate_prefix_factor rate rewards C_star C_h control0 s t z,
    pendingAt_prefix_factor rate rewards C_star C_h control0 s t z]

theorem Plate_replaceSourceControl (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : Source p) (u : TimeControl p) :
    Plate rate rewards C_star C_h s t.val z =
      Plate rate rewards C_star C_h s t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) := by
  rw [Plate_prefix_factor rate rewards C_star C_h control0 s t z,
    Plate_prefix_factor rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z u]

theorem Plate_mem_preRound_measurable (control0 : TimeControl p) (s : ℕ)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | i ∈ Plate rate rewards C_star C_h s t.val z} := by
  have heq : {z : Source p | i ∈ Plate rate rewards C_star C_h s t.val z} =
      {z | Llate rate rewards C_star C_h s t.val z} ∩
        {z | i ∈ pendingAt rate rewards C_star C_h s t.val z} := by
    ext z
    exact Plate_mem_iff_Llate rate rewards C_star C_h i s t.val z
  rw [heq]
  exact (Llate_preRound_measurable rate rewards C_star C_h control0 s t).inter
    (pendingAt_mem_preRound_measurable rate rewards C_star C_h control0 s t i)

/-- The signed projection is the predictable support indicator times the
accepted signed deficit, including supported empty-pending dates. -/
theorem Dlate_eq_indicator (s : ℕ) (t : Fin p.T) :
    Dlate rate rewards C_star C_h s t.val =
      {z : Source p | Llate rate rewards C_star C_h s t.val z}.indicator
        (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
          rate rewards C_star C_h s t) := by
  funext z
  simp only [Dlate, dite_eq_left t.isLt, Set.indicator_apply, Set.mem_ofPred_eq]

theorem Dlate_roundEnd_stronglyMeasurable (control0 : TimeControl p)
    (s : ℕ) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 2)]
      (Dlate rate rewards C_star C_h s t.val) := by
  have hd : Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
        rate rewards C_star C_h s t) := by
    rw [show t.val + 2 = (t.val + 1) + 1 by omega, sourcePrefixFiltration_succ]
    convert (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_measurable
      rate rewards C_star C_h s t).comp
      (comap_measurable (sourcePrefix control0 (t.val + 1))) using 1
    funext z
    exact ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_prefix
      rate rewards C_star C_h control0 s t z
  rw [Dlate_eq_indicator]
  exact (hd.indicator (((sourcePrefixFiltration control0).mono (show t.val + 1 ≤ t.val + 2 by omega)) _
    (Llate_preRound_measurable rate rewards C_star C_h control0 s t))).stronglyMeasurable

theorem Dlate_integrable (control0 : TimeControl p) (s : ℕ) (t : Fin p.T) :
    Integrable (Dlate rate rewards C_star C_h s t.val) (sourceInputLaw p) := by
  rw [Dlate_eq_indicator]
  exact (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_integrable
    rate rewards C_star C_h s t).indicator
    (((sourcePrefixFiltration control0).le (t.val + 1)) _
      (Llate_preRound_measurable rate rewards C_star C_h control0 s t))

/-- One original-source exceptional set suffices for every fixed calendar
label and every finite round. Only the proved predictable mask is pulled out. -/
theorem Dlate_condExp_signed_envelope (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T,
      (sourceInputLaw p)[Dlate rate rewards C_star C_h s t.val |
          sourcePrefixFiltration control0 (t.val + 1)] z ≤
        (∑ i ∈ Plate rate rewards C_star C_h s t.val z,
          c_i rate rewards C_star C_h i s t.val z) +
        (if (Plate rate rewards C_star C_h s t.val z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s t.val z := by
  have hpull : ∀ s : ℕ, ∀ t : Fin p.T,
      (sourceInputLaw p)[Dlate rate rewards C_star C_h s t.val |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      {z : Source p | Llate rate rewards C_star C_h s t.val z}.indicator
        ((sourceInputLaw p)[
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h s t | sourcePrefixFiltration control0 (t.val + 1)]) := by
    intro s t
    rw [Dlate_eq_indicator]
    exact condExp_indicator
      (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_integrable
        rate rewards C_star C_h s t)
      (Llate_preRound_measurable rate rewards C_star C_h control0 s t)
  have hpullAll : ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T, _ :=
    (ae_all_iff.mpr fun s => ae_all_iff.mpr fun t => hpull s t)
  filter_upwards [hpullAll,
    ReferenceOriginalInstallationReleaseSignedCharge.actual_later_local_release_signed_condExp_bound
      rate rewards C_star C_h control0] with z hz hsection
  intro s t
  rw [hz s t]
  by_cases hl : Llate rate rewards C_star C_h s t.val z
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hl, ite_true]
    obtain ⟨_hs, b, htime, hb, _hrbirth⟩ :=
      laterBirth_actualSuffixIndex rate rewards C_star C_h s z hl.1
    have hg := ((supportAt_iff rate rewards C_star C_h s t.val z t.isLt).mp hl.2).1
    obtain ⟨r, selected, hr, hsel, hpend, _hbound, hbound, _hempty⟩ :=
      hsection s b t htime hb hg
    have hPlate : Plate rate rewards C_star C_h s t.val z =
        ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
      rw [Plate_eq_pending_of_Llate rate rewards C_star C_h s t.val z hl,
        pendingAt_eq_observed_of_support rate rewards C_star C_h s t.val z t.isLt hl.2,
        hpend]
    have hc (i : Fin (p.m - 1)) : c_i rate rewards C_star C_h i s t.val z =
        ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
          (selected.view.payload.assignment.assigned i) := by
      simp only [c_i, hl, ite_true, dite_eq_left t.isLt, hr, hsel]
    have hw : omega rate rewards C_star C_h s t.val z =
        ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass rate selected
          (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm rate selected) *
        ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
          (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm rate selected).val := by
      simp only [omega, hl, ite_true, dite_eq_left t.isLt, hr, hsel]
    simpa only [hPlate, hc, hw, mul_assoc] using hbound
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hl, ite_false]
    have hP : Plate rate rewards C_star C_h s t.val z = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hl ((Plate_mem_iff_Llate rate rewards C_star C_h i s t.val z).mp hi).1
    simp only [hP, Finset.sum_empty, Finset.not_nonempty_empty, ite_false, zero_mul,
      add_zero, le_refl]

/-- Supported empty pending dates keep the signed deficit; their conditional
expectation, rather than their physical deficit, is nonpositive. -/
theorem Dlate_condExp_nonpos_of_Plate_empty (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T,
      Plate rate rewards C_star C_h s t.val z = ∅ →
      (sourceInputLaw p)[Dlate rate rewards C_star C_h s t.val |
        sourcePrefixFiltration control0 (t.val + 1)] z ≤ 0 := by
  filter_upwards [Dlate_condExp_signed_envelope rate rewards C_star C_h control0] with z hz
  intro s t he
  simpa only [he, Finset.sum_empty, Finset.not_nonempty_empty, ite_false, zero_mul, add_zero]
    using hz s t

/-- Numerical service readout on the existing incoming live coordinates.
The continuous anchor and whole current weight vector keep their Borel carriers. -/
def liveServiceValue (i : Fin (p.m - 1)) (t : Fin p.T)
    (v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : ℝ × ℝ :=
  (ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) (v.1.assignment.assigned i),
    ReferencePostReplacementCollectionSentinelSectionLaw.liveDataAuxiliaryMass rate v *
      ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) v.1.assignment.auxiliary)

private theorem liveDataWeights_measurable :
    Measurable (ReferencePostReplacementCollectionSentinelSectionLaw.liveDataWeights rate) := by
  let V := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  have hobs : Measurable (fun v : V =>
      LaterAssignmentStartMeasurability.payloadObservation v.1) :=
    (comap_measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta))).comp measurable_fst
  have hanchor : Measurable (fun v : V => v.1.anchor) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp measurable_fst
  apply measurable_pi_iff.mpr
  intro a
  exact ((measurable_pi_apply a).comp hanchor).ite
    ((measurableSet_mem_finset a).preimage hobs.snd.snd.fst)
    ((measurable_of_countable (fun d : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (d.scores a))).comp measurable_snd)

private theorem qGammaFormula_joint_measurable :
    Measurable (fun x : (Finset (Fin p.K) × Fin p.K) ×
        ((Fin p.K → ℝ) × (Fin p.K → ℝ)) =>
      ReferenceLiveRecorderJointMeasurability.qGammaFormula (p := p) (rate := rate)
        x.1.1 x.2 x.1.2) :=
  measurable_from_prod_countable_right fun key =>
    ReferenceLiveRecorderJointMeasurability.measurable_qGammaFormula
      (p := p) (rate := rate) key.1 key.2

private theorem liveDataAuxiliaryMass_measurable :
    Measurable (ReferencePostReplacementCollectionSentinelSectionLaw.liveDataAuxiliaryMass rate) := by
  let V := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  have hobs : Measurable (fun v : V =>
      LaterAssignmentStartMeasurability.payloadObservation v.1) :=
    (comap_measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta))).comp measurable_fst
  have hanchor : Measurable (fun v : V => v.1.anchor) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp measurable_fst
  have haux : Measurable (fun v : V => v.1.assignment.auxiliary) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp measurable_fst
  have hkey : Measurable (fun v : V => (v.1.slowSet.val, v.1.assignment.auxiliary)) :=
    hobs.snd.snd.fst.prodMk haux
  exact (qGammaFormula_joint_measurable rate).comp
    (hkey.prodMk (hanchor.prodMk (liveDataWeights_measurable rate)))

private theorem liveServiceValue_measurable (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (liveServiceValue rate rewards i t) := by
  let V := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  have haux : Measurable (fun v : V => v.1.assignment.auxiliary) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp measurable_fst
  have hslow : Measurable (fun v : V => v.1.slowSet) :=
    ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp measurable_fst
  have hassigned : Measurable (fun v : V => v.1.assignment.assigned i) :=
    (measurable_of_countable (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m U i)).comp hslow
  exact ((measurable_of_countable (ReleaseRoundKernel.chi (wholeGridRewardRow rewards t))).comp
    hassigned).prodMk ((liveDataAuxiliaryMass_measurable rate).mul
      ((measurable_of_countable (ReleaseRoundKernel.chi (wholeGridRewardRow rewards t))).comp haux))

/-- Administrative option elimination, with no new physical play branch. -/
def incomingServiceValue (i : Fin (p.m - 1)) (t : Fin p.T)
    (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) : ℝ × ℝ :=
  ReferenceCollectionOutcomeMeasurability.optionalElim (0, 0)
    (fun c => match c.1 with
      | .inr (.inl live) => liveServiceValue rate rewards i t live
      | _ => (0, 0)) code

private theorem incomingServiceValue_measurable (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (incomingServiceValue rate rewards i t) := by
  let read : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → ℝ × ℝ :=
    Sum.elim (fun _ => (0, 0)) (Sum.elim (liveServiceValue rate rewards i t)
      (fun _ => (0, 0)))
  have hread : Measurable read := measurable_const.sumElim
    ((liveServiceValue_measurable rate rewards i t).sumElim measurable_const)
  have heq : (fun c : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      match c.1 with
      | .inr (.inl live) => liveServiceValue rate rewards i t live
      | _ => (0, 0)) = read ∘ Prod.fst := by
    funext c
    rcases c with ⟨coord, rest⟩
    cases coord with
    | inl u => rfl
    | inr tail => cases tail <;> rfl
  have hm := hread.comp (measurable_fst : Measurable
    (Prod.fst : ReferenceActivePhysicalStepMeasurability.StateCode p rate → _))
  rw [← heq] at hm
  exact ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0, 0) _ hm

/-- The readout uses exactly the actual selected payload and numerical weights.
All chronology and selection witnesses are obtained internally on this source. -/
theorem service_eq_incoming (control0 : TimeControl p) (i : Fin (p.m - 1))
    (s : ℕ) (t : Fin p.T) (z : Source p) :
    (c_i rate rewards C_star C_h i s t.val z, omega rate rewards C_star C_h s t.val z) =
      if Llate rate rewards C_star C_h s t.val z then
        incomingServiceValue rate rewards i t (incoming rate rewards C_star C_h t z)
      else (0, 0) := by
  by_cases hl : Llate rate rewards C_star C_h s t.val z
  · obtain ⟨_hs, b, htime, hb, _hrbirth⟩ :=
      laterBirth_actualSuffixIndex rate rewards C_star C_h s z hl.1
    have hg := ((supportAt_iff rate rewards C_star C_h s t.val z t.isLt).mp hl.2).1
    rw [htime] at hg
    obtain ⟨r, hr, _ht, registers, owned, base, selected, states, memories,
      hstate, _hpayload, _hpending, hselection, _hselectedPending, _hcutoff, _hlive,
      _hvalid, _hordinary, _hfields, _hcarried, _hnext, _hweights, _hfast,
      _hactions, _hfeedback, _hcost, dispatched, hstart, continuation, arm, hcoord⟩ :=
      ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame
        rate rewards C_star C_h control0 z b t hb hg
    have hprepared : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
        some selected := by
      simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselection
    have heq := Option.some.inj ((ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
      r.input registers owned base dispatched hstart continuation arm hcoord).symm.trans hprepared)
    subst selected
    have hweight : ReferencePostReplacementCollectionSentinelSectionLaw.liveDataWeights rate
        (registers.payload, ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base) =
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights registers.payload
          registers.complementWeights := by
      funext a
      unfold ReferencePostReplacementCollectionSentinelSectionLaw.liveDataWeights
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
      split_ifs with ha
      · rfl
      · have hf : a ∈ CanonicalFastSampling.fastArmFinset registers.payload.slowSet :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
        simp only [ReferenceActivePhysicalStepMeasurability.encodeLive,
          ReferenceActivePhysicalStepMeasurability.extendComplement, dite_eq_left hf]
        rfl
    simp only [c_i, omega, hl, ite_true, dite_eq_left t.isLt, hr, hselection,
      incomingServiceValue, incoming, Option.map_some,
      ReferenceCollectionOutcomeMeasurability.optionalElim,
      ReferenceActivePhysicalStepMeasurability.encodeState, hstate,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, liveServiceValue]
    rw [ReferencePostReplacementCollectionSentinelSectionLaw.liveDataAuxiliaryMass, hweight]
    rfl
  · simp only [c_i, omega, hl, ite_false]

theorem service_preRound_stronglyMeasurable (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (s : ℕ) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => (c_i rate rewards C_star C_h i s t.val z,
        omega rate rewards C_star C_h s t.val z)) := by
  have hm : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => if Llate rate rewards C_star C_h s t.val z then
        incomingServiceValue rate rewards i t (incoming rate rewards C_star C_h t z)
      else (0, 0)) := ((incomingServiceValue_measurable rate rewards i t).comp
    (incoming_measurable rate rewards C_star C_h control0 t)).ite
      (Llate_preRound_measurable rate rewards C_star C_h control0 s t) measurable_const
  convert hm.stronglyMeasurable using 1
  funext z
  exact service_eq_incoming rate rewards C_star C_h control0 i s t z

theorem c_i_preRound_stronglyMeasurable (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (s : ℕ) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      (c_i rate rewards C_star C_h i s t.val) :=
  (service_preRound_stronglyMeasurable rate rewards C_star C_h control0 i s t).fst

theorem omega_preRound_stronglyMeasurable (control0 : TimeControl p)
    (s : ℕ) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      (omega rate rewards C_star C_h s t.val) := by
  let i : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
  exact (service_preRound_stronglyMeasurable rate rewards C_star C_h control0 i s t).snd

theorem service_prefix_factor (control0 : TimeControl p) (i : Fin (p.m - 1))
    (s : ℕ) (t : Fin p.T) (z : Source p) :
    (c_i rate rewards C_star C_h i s t.val z, omega rate rewards C_star C_h s t.val z) =
      (c_i rate rewards C_star C_h i s t.val (sourcePrefix control0 t.val z),
        omega rate rewards C_star C_h s t.val (sourcePrefix control0 t.val z)) := by
  rw [service_eq_incoming rate rewards C_star C_h control0 i s t z,
    service_eq_incoming rate rewards C_star C_h control0 i s t (sourcePrefix control0 t.val z),
    ← Llate_prefix_factor rate rewards C_star C_h control0 s t z,
    ← incoming_factor rate rewards C_star C_h control0 t z]

theorem service_replaceSourceControl (control0 : TimeControl p) (i : Fin (p.m - 1))
    (s : ℕ) (t : Fin p.T) (z : Source p) (u : TimeControl p) :
    (c_i rate rewards C_star C_h i s t.val z, omega rate rewards C_star C_h s t.val z) =
      (c_i rate rewards C_star C_h i s t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
        omega rate rewards C_star C_h s t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) := by
  rw [service_prefix_factor rate rewards C_star C_h control0 i s t z,
    service_prefix_factor rate rewards C_star C_h control0 i s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z u]

/-- Provenance on every supported later date, including dates with no pending
follower. The index is constructed on this actual source only. -/
theorem Llate_actualSuffixGate (s : ℕ) (t : Fin p.T) (z : Source p)
    (hl : Llate rate rewards C_star C_h s t.val z) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val ∧
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input = true ∧
      (entry rate rewards C_star C_h s t z).map Prod.fst = some true ∧
      Plate rate rewards C_star C_h s t.val z = pending rate rewards C_star C_h s t z := by
  obtain ⟨_hs, b, htime, hb, _hrecord⟩ :=
    laterBirth_actualSuffixIndex rate rewards C_star C_h s z hl.1
  exact ⟨b, htime, hb,
    ((supportAt_iff rate rewards C_star C_h s t.val z t.isLt).mp hl.2).1,
    (Plate_eq_pending_of_Llate rate rewards C_star C_h s t.val z hl).trans
      (pendingAt_eq_observed_of_support rate rewards C_star C_h s t.val z t.isLt hl.2)⟩

/-- The unmasked physical DATA and UP flags satisfy both service inequalities
on one original-source AE set for all fixed labels, rounds and followers. -/
theorem actual_service_condExp_all (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T, ∀ i : Fin (p.m - 1),
      i ∈ Plate rate rewards C_star C_h s t.val z →
      (sourceInputLaw p)[(fun w => if actualData rate rewards C_star C_h i t w
          then (1 : ℝ) else 0) | sourcePrefixFiltration control0 (t.val + 1)] z =
        c_i rate rewards C_star C_h i s t.val z / (2 * (p.K : ℝ)) ∧
      omega rate rewards C_star C_h s t.val z / (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        (sourceInputLaw p)[(fun w => if actualUp rate rewards C_star C_h i t w
          then (1 : ℝ) else 0) | sourcePrefixFiltration control0 (t.val + 1)] z := by
  have hd := ae_all_iff.mpr (fun s : ℕ =>
    actual_data_condExp_all_on_Llate rate rewards C_star C_h control0 s)
  have hu := ae_all_iff.mpr (fun s : ℕ =>
    actual_up_condExp_lower_all_on_Llate rate rewards C_star C_h control0 s)
  filter_upwards [hd, hu] with z hdata hup
  intro s t i hi
  have hl := ((Plate_mem_iff_Llate rate rewards C_star C_h i s t.val z).mp hi).1
  exact ⟨hdata s t i hl hi, hup s t i hl hi⟩

theorem Llate_false_of_ge_horizon (s k : ℕ) (z : Source p) (hk : p.T ≤ k) :
    ¬ Llate rate rewards C_star C_h s k z :=
  fun h => supportAt_false_of_ge_horizon rate rewards C_star C_h s k z hk h.2

theorem Plate_eq_empty_of_not_Llate (s k : ℕ) (z : Source p)
    (hl : ¬ Llate rate rewards C_star C_h s k z) :
    Plate rate rewards C_star C_h s k z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hl ((Plate_mem_iff_Llate rate rewards C_star C_h i s k z).mp hi).1

theorem projections_zero_of_not_laterBirth (i : Fin (p.m - 1)) (s k : ℕ)
    (z : Source p) (hb : ¬ laterBirth rate rewards C_star C_h s z) :
    ¬ Llate rate rewards C_star C_h s k z ∧
      Plate rate rewards C_star C_h s k z = ∅ ∧
      c_i rate rewards C_star C_h i s k z = 0 ∧
      omega rate rewards C_star C_h s k z = 0 ∧ Dlate rate rewards C_star C_h s k z = 0 := by
  have hl : ¬ Llate rate rewards C_star C_h s k z := fun h => hb h.1
  exact ⟨hl, Plate_eq_empty_of_not_laterBirth rate rewards C_star C_h s k z hb,
    by simp only [c_i, hl, ite_false], by simp only [omega, hl, ite_false],
    Dlate_eq_zero_of_not_Llate rate rewards C_star C_h s k z hl⟩

theorem Llate_preRound_measurable_nat (control0 : TimeControl p) (s k : ℕ) :
    MeasurableSet[sourcePrefixFiltration control0 (k + 1)]
      {z : Source p | Llate rate rewards C_star C_h s k z} := by
  by_cases hk : k < p.T
  · exact Llate_preRound_measurable rate rewards C_star C_h control0 s ⟨k, hk⟩
  · have he : {z : Source p | Llate rate rewards C_star C_h s k z} = ∅ := by
      ext z
      exact iff_false_intro (Llate_false_of_ge_horizon rate rewards C_star C_h s k z (by omega))
    rw [he]
    exact @MeasurableSet.empty (Source p) (sourcePrefixFiltration control0 (k + 1))

theorem Plate_mem_preRound_measurable_nat (control0 : TimeControl p)
    (s k : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (k + 1)]
      {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
  have he : {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} =
      {z | Llate rate rewards C_star C_h s k z} ∩
        {z | i ∈ pendingAt rate rewards C_star C_h s k z} := by
    ext z
    exact Plate_mem_iff_Llate rate rewards C_star C_h i s k z
  rw [he]
  exact (Llate_preRound_measurable_nat rate rewards C_star C_h control0 s k).inter
    (pendingAt_mem_measurable rate rewards C_star C_h control0 s k i)

theorem service_preRound_stronglyMeasurable_nat (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (s k : ℕ) :
    StronglyMeasurable[sourcePrefixFiltration control0 (k + 1)]
      (fun z => (c_i rate rewards C_star C_h i s k z, omega rate rewards C_star C_h s k z)) := by
  by_cases hk : k < p.T
  · exact service_preRound_stronglyMeasurable rate rewards C_star C_h control0 i s ⟨k, hk⟩
  · have he : (fun z => (c_i rate rewards C_star C_h i s k z,
        omega rate rewards C_star C_h s k z)) = fun _ : Source p => (0, 0) := by
      funext z
      simp [c_i, omega, hk]
    rw [he]
    exact stronglyMeasurable_const

theorem Dlate_roundEnd_stronglyMeasurable_nat (control0 : TimeControl p) (s k : ℕ) :
    StronglyMeasurable[sourcePrefixFiltration control0 (k + 2)]
      (Dlate rate rewards C_star C_h s k) := by
  by_cases hk : k < p.T
  · exact Dlate_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 s ⟨k, hk⟩
  · have he : Dlate rate rewards C_star C_h s k = fun _ : Source p => 0 := by
      funext z
      simp [Dlate, hk]
    rw [he]
    exact stronglyMeasurable_const

theorem Dlate_integrable_nat (control0 : TimeControl p) (s k : ℕ) :
    Integrable (Dlate rate rewards C_star C_h s k) (sourceInputLaw p) := by
  by_cases hk : k < p.T
  · exact Dlate_integrable rate rewards C_star C_h control0 s ⟨k, hk⟩
  · have he : Dlate rate rewards C_star C_h s k = fun _ : Source p => 0 := by
      funext z
      simp [Dlate, hk]
    rw [he]
    exact integrable_zero _ _ _

/-- Restriction to the later family uses the existing phase endpoints. -/
theorem Plate_empty_outside_interval (s k : ℕ) (z : Source p)
    (hout : ¬ (sigmaR rate rewards C_star C_h s z ≤ k + 1 ∧
      k + 1 < thetaR rate rewards C_star C_h s z)) :
    Plate rate rewards C_star C_h s k z = ∅ := by
  simp only [Plate, pendingAt_empty_outside_interval rate rewards C_star C_h s k z hout,
    ite_self]

theorem Plate_nested_inside_interval (s : ℕ) (z : Source p) (j k : ℕ)
    (hjk : j ≤ k) (hstart : sigmaR rate rewards C_star C_h s z ≤ j + 1)
    (hexit : k + 1 < thetaR rate rewards C_star C_h s z) :
    Plate rate rewards C_star C_h s k z ⊆ Plate rate rewards C_star C_h s j z := by
  by_cases hb : laterBirth rate rewards C_star C_h s z
  · simpa only [Plate, hb, ite_true] using
      pendingAt_nested_inside_interval rate rewards C_star C_h s z j k hjk hstart hexit
  · simp only [Plate, hb, ite_false, Finset.Subset.refl]

theorem Plate_strict_prior_N_lt_one (s : ℕ) (z : Source p) (k : ℕ)
    (i : Fin (p.m - 1)) (hi : i ∈ Plate rate rewards C_star C_h s k z) :
    PhaseServiceWaiting.N (Plate rate rewards C_star C_h s)
        (upObservation rate rewards C_star C_h) i k z < 1 ∧
      PhaseServiceWaiting.N (Plate rate rewards C_star C_h s)
        (dataObservation rate rewards C_star C_h) i k z < 1 := by
  obtain ⟨hb, hip⟩ := (Plate_mem_iff rate rewards C_star C_h i s k z).mp hi
  have hq := strict_prior_N_lt_one_at_pending rate rewards C_star C_h s z k i hip
  simpa only [PhaseServiceWaiting.N, Plate, hb, ite_true] using hq

/-- At each actual later installation the restricted analysis recovers the
accepted stopped support and pending observers at every natural index. -/
theorem projections_at_actualLater
    (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) (k : ℕ) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
    (Llate rate rewards C_star C_h s k z ↔ supportAt rate rewards C_star C_h s k z) ∧
      Plate rate rewards C_star C_h s k z = pendingAt rate rewards C_star C_h s k z := by
  have hbirth := laterBirth_of_actualSuffixIndex rate rewards C_star C_h z b hb
  dsimp only
  simp only [Llate, Plate, hbirth, true_and, ite_true, and_self]

/-- An actual FIRST incoming record is outside this later-only analysis.
This asserts no vanishing of the initial family's physical release charge. -/
theorem not_laterBirth_of_actual_first (s : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h s z = some r)
    (hf : r.input.state.coordinator = .first) :
    ¬ laterBirth rate rewards C_star C_h s.val z := by
  rw [laterBirth_iff_incoming rate rewards C_star C_h s z]
  simp only [incoming, hr, Option.map_some,
    ReferenceCollectionOutcomeMeasurability.optionalElim, emptyCollectionCode,
    ReferenceActivePhysicalStepMeasurability.encodeState, hf,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, Bool.false_eq_true, not_false_eq_true]

/-- The natural-index envelope extends by the literal zero/horizon branch. -/
theorem Dlate_condExp_signed_envelope_nat (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s k : ℕ,
      (sourceInputLaw p)[Dlate rate rewards C_star C_h s k |
          sourcePrefixFiltration control0 (k + 1)] z ≤
        (∑ i ∈ Plate rate rewards C_star C_h s k z,
          c_i rate rewards C_star C_h i s k z) +
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z := by
  filter_upwards [Dlate_condExp_signed_envelope rate rewards C_star C_h control0] with z hz
  intro s k
  by_cases hk : k < p.T
  · exact hz s ⟨k, hk⟩
  · have hD : Dlate rate rewards C_star C_h s k = (0 : Source p → ℝ) := by
      funext w
      simp [Dlate, hk]
    have hP := Plate_eq_empty_of_not_Llate rate rewards C_star C_h s k z
      (Llate_false_of_ge_horizon rate rewards C_star C_h s k z (by omega))
    simp only [hD, condExp_zero, Pi.zero_apply, hP, Finset.sum_empty,
      Finset.not_nonempty_empty, ite_false, zero_mul, add_zero, le_refl]

end Bandits.Support.ReferenceOriginalLaterReleasePredictableService

end
