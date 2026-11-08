/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

import Mathlib.Tactic

/-!
# Stopped release observations for a fixed original installation label

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-210,293-349`
and `sources/zip4/manuscript/06_interruptions.tex:431-490`.

The projections below retain the original source input and its whole reward
table. The fixed label is the absolute, zero-based installation timestamp used
by the existing entry and pending observers.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase

variable {p : ConstructorDimensions.Parameters}

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev RateInput (p : ConstructorDimensions.Parameters) :=
  ReferenceActivePhysicalStep.RateInput p
abbrev GridRewardTable (p : ConstructorDimensions.Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨congrArg e, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

/-- Literal original-source stopped R support at a fixed absolute installation
label. The first bad date is inclusive, so the detecting update is retained. -/
def supportAt (s k : ℕ) (z : Source p) : Prop :=
  if hk : k < p.T then
    (entry rate rewards C_star C_h s ⟨k, hk⟩ z).map Prod.fst = some true ∧
      k + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z
  else False

/-- The local-gate support of the actual complete original suffix, at an
arbitrary absolute installation label. -/
def originalGateSupport (s : ℕ) (z : Source p) : Finset ℕ :=
  ReferenceLocalReleaseGateChronology.gateSupport s
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)

private theorem entry_true_iff_actual_local_gate (s : ℕ) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (z : Source p) (hrecord : actualRecord rate rewards C_star C_h t z = some r) :
    (entry rate rewards C_star C_h s t z).map Prod.fst = some true ↔
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s t
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
  simp [entry, incoming, hrecord,
    ReferenceRetainedReleasePhaseObservation.localReleaseEntry]

/-- On the original complete suffix, the fixed-label entry observer is exactly
the actual local release gate, including true gates with empty pending sets.
No successful-history condition is used. -/
theorem originalGateSupport_mem_iff_entry (s : ℕ) (t : Fin p.T) (z : Source p) :
    t.val + 1 ∈ originalGateSupport rate rewards C_star C_h s z ↔
      (entry rate rewards C_star C_h s t z).map Prod.fst = some true := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h
  by_cases hcross : boundary.crossing.isSome = true
  · have hcross' : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcross
    let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross'
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active := by
      simpa only [active] using
        ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross'
    have hElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed =
        start := by
      dsimp [start, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    have hstart_le : start ≤ p.T := by
      exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hspan : start + (p.T - start) ≤ p.T := by omega
    have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart active start := by
      have h := (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross').2.1
      exact hElapsed ▸ h
    have hrun :
        (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
          start (p.T - start) hElapsed hspan).records =
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
      simpa [start, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceLocalReleaseGateChronology.sourceRun] using
        (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h active hlaunch).symm
    by_cases hbefore : start ≤ t.val
    · have hsourceRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
        rate rewards C_star C_h t z active hlaunch (by simpa [start] using hbefore)
      have hrecord : actualRecord rate rewards C_star C_h t z = some
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
            (t.val - start) (by omega) hactive) := by
        simpa [start] using hsourceRecord
      have hrecordTime :
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
            (t.val - start) (by omega) hactive).input.time = t := by
        apply Fin.ext
        simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt]
        omega
      have hgateSupportEq : originalGateSupport rate rewards C_star C_h s z =
          ReferenceLocalReleaseGateChronology.gateSupport s
            (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
              start (p.T - start) hElapsed hspan).records := by
        unfold originalGateSupport
        rw [← hrun]
      have hmem : t.val + 1 ∈ originalGateSupport rate rewards C_star C_h s z ↔
          ∃ j : Fin (p.T - start),
            ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start j.val
                (by omega) hactive).input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start j.val
                  (by omega) hactive).input.state) = true ∧
            start + j.val + 1 = t.val + 1 := by
        rw [hgateSupportEq]
        simpa [ReferenceLocalReleaseGateChronology.sourceRun] using
          ReferenceLocalReleaseGateChronology.mem_run_gateSupport active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start hactive
            (p.T - start) hspan s (t.val + 1)
      let gateAt : Fin (p.T - start) → Bool := fun j =>
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start j.val
            (by omega) hactive).input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start j.val
              (by omega) hactive).input.state)
      have hentryGate := entry_true_iff_actual_local_gate rate rewards C_star C_h s t
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
          (t.val - start) (by omega) hactive) z hrecord
      constructor
      · intro hgate
        obtain ⟨j, hjgate, hjdate⟩ := hmem.mp hgate
        have hjval : j.val = t.val - start := by omega
        have hj : j = ⟨t.val - start, by omega⟩ := Fin.ext hjval
        have hgateEq : gateAt j = gateAt ⟨t.val - start, by omega⟩ := congrArg gateAt hj
        change gateAt j = true at hjgate
        rw [hgateEq] at hjgate
        have hgate'' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
              (t.val - start) (by omega) hactive).input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
                (t.val - start) (by omega) hactive).input.state) = true := by
          simpa only [gateAt] using hjgate
        exact hentryGate.mpr (by simpa only [hrecordTime] using hgate'')
      · intro hentry
        have hlocal := hentryGate.mp hentry
        have hlocal' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
              (t.val - start) (by omega) hactive).input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
                (t.val - start) (by omega) hactive).input.state) = true := by
          have hgateEq := congrArg
            (fun τ : Fin p.T => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s τ
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
                  (t.val - start) (by omega) hactive).input.state)) hrecordTime
          exact hgateEq.trans hlocal
        have hoffset : start + (t.val - start) = t.val := Nat.add_sub_of_le hbefore
        have hindex : t.val - start < p.T - start := by omega
        apply hmem.mpr
        refine ⟨⟨t.val - start, hindex⟩, ?_, ?_⟩
        · change gateAt ⟨t.val - start, hindex⟩ = true
          simpa only [gateAt] using hlocal'
        · rw [hoffset]
    · have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h t z (by simpa [start] using (Nat.lt_of_not_ge hbefore))
      have hnot : t.val + 1 ∉ originalGateSupport rate rewards C_star C_h s z := by
        intro hv
        have hv' := hv
        unfold originalGateSupport at hv'
        rw [← hrun] at hv'
        obtain ⟨j, _hg, hdate⟩ :=
          (ReferenceLocalReleaseGateChronology.mem_run_gateSupport active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start hactive
            (p.T - start) hspan s (t.val + 1)).mp hv'
        have : start ≤ t.val := by omega
        exact (hbefore this).elim
      constructor
      · intro hgate
        exact False.elim (hnot hgate)
      · intro hentry
        simp [entry, incoming, hnone] at hentry
  · have hnone : boundary.crossing = none := by
      cases h : boundary.crossing with
      | none => rfl
      | some value => simp [h] at hcross
    have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
      rate z rewards C_star C_h).2 (by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hnone)
    have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hlaunch
    have hsupport : originalGateSupport rate rewards C_star C_h s z = ∅ := by
      unfold originalGateSupport
      rw [hhistory.2.1]
      simp [ReferenceLocalReleaseGateChronology.gateSupport]
    have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
      rate rewards C_star C_h t z hnone
    rw [hsupport]
    simp [entry, incoming, hrecord]

private theorem originalGateSupport_between (s d₁ d d₂ : ℕ) (z : Source p)
    (h₁ : d₁ ∈ originalGateSupport rate rewards C_star C_h s z)
    (h₂ : d₂ ∈ originalGateSupport rate rewards C_star C_h s z)
    (horder : d₁ ≤ d ∧ d ≤ d₂) :
    d ∈ originalGateSupport rate rewards C_star C_h s z := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h
  by_cases hcross : boundary.crossing.isSome = true
  · have hcross' : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcross
    let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross'
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active := by
      simpa only [active] using
        ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross'
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed =
        start := by
      dsimp [start, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    have hspan : start + (p.T - start) ≤ p.T := by
      have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      omega
    have hrun :
        (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
          start (p.T - start) helapsed hspan).records =
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
      simpa [start, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceLocalReleaseGateChronology.sourceRun] using
        (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h active hlaunch).symm
    have hgateEq : originalGateSupport rate rewards C_star C_h s z =
        ReferenceLocalReleaseGateChronology.gateSupport s
          (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
            start (p.T - start) helapsed hspan).records := by
      unfold originalGateSupport
      rw [← hrun]
    have hinterval := (ReferenceLocalReleaseGateChronology.source_local_gate_interval
      rate z rewards C_star C_h hcross' start (p.T - start) helapsed hspan s).1
    rw [hgateEq, hinterval, Finset.mem_Ico] at h₁ h₂ ⊢
    exact ⟨by omega, by omega⟩
  · have hnone : boundary.crossing = none := by
      cases h : boundary.crossing with
      | none => rfl
      | some value => simp [h] at hcross
    have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
      rate z rewards C_star C_h).2 (by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hnone)
    have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hlaunch
    have hsupport : originalGateSupport rate rewards C_star C_h s z = ∅ := by
      unfold originalGateSupport
      rw [hhistory.2.1]
      simp [ReferenceLocalReleaseGateChronology.gateSupport]
    rw [hsupport] at h₁
    simp at h₁

/-- The stopped support is the exact all-assignment local gate support cut at
the inclusive first-bad date. -/
theorem supportAt_iff_stopped_originalGate (s k : ℕ) (z : Source p)
    (hk : k < p.T) :
    supportAt rate rewards C_star C_h s k z ↔
      k + 1 ∈ originalGateSupport rate rewards C_star C_h s z ∧
        k + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z := by
  simp only [supportAt, dite_eq_left hk]
  rw [originalGateSupport_mem_iff_entry rate rewards C_star C_h s ⟨k, hk⟩ z]

private theorem supportAt_between (s : ℕ) (t₁ t t₂ : Fin p.T) (z : Source p)
    (h₁ : supportAt rate rewards C_star C_h s t₁.val z)
    (h₂ : supportAt rate rewards C_star C_h s t₂.val z)
    (horder : t₁.val ≤ t.val ∧ t.val ≤ t₂.val) :
    supportAt rate rewards C_star C_h s t.val z := by
  have h₁' := (supportAt_iff_stopped_originalGate rate rewards C_star C_h s
    t₁.val z t₁.isLt).mp h₁
  have h₂' := (supportAt_iff_stopped_originalGate rate rewards C_star C_h s
    t₂.val z t₂.isLt).mp h₂
  have hgate := originalGateSupport_between rate rewards C_star C_h s
    (t₁.val + 1) (t.val + 1) (t₂.val + 1) z h₁'.1 h₂'.1 (by omega)
  apply (supportAt_iff_stopped_originalGate rate rewards C_star C_h s t.val z t.isLt).mpr
  exact ⟨hgate, by omega⟩

/-- The pending readout on stopped support, and empty elsewhere. -/
def pendingAt (s k : ℕ) (z : Source p) : Finset (Fin (p.m - 1)) :=
  if hk : k < p.T then
    if supportAt rate rewards C_star C_h s k z then
      pending rate rewards C_star C_h s ⟨k, hk⟩ z else ∅
  else ∅

/-- Raw actual UP observation; outside the physical horizon it is false. -/
def upObservation (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : Bool :=
  if hk : k < p.T then actualUp rate rewards C_star C_h i ⟨k, hk⟩ z else false

/-- Raw actual DATA observation; outside the physical horizon it is false. -/
def dataObservation (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : Bool :=
  if hk : k < p.T then actualData rate rewards C_star C_h i ⟨k, hk⟩ z else false

/-- The set of all one-based dates in the literal stopped support. -/
def supportDates (s : ℕ) (z : Source p) : Finset ℕ :=
  ((Finset.univ : Finset (Fin p.T)).filter fun t =>
    supportAt rate rewards C_star C_h s t.val z).image fun t => t.val + 1

/-- First supported one-based date, with the empty phase sentinel `T+1`. -/
def sigmaR (s : ℕ) (z : Source p) : ℕ :=
  (supportDates rate rewards C_star C_h s z ∪ {p.T + 1}).min' (by
    exact ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩)

/-- First excluded one-based date, one after the last supported date. -/
def thetaR (s : ℕ) (z : Source p) : ℕ := by
  classical
  exact if h : (supportDates rate rewards C_star C_h s z).Nonempty then
    (supportDates rate rewards C_star C_h s z).max' h + 1 else p.T + 1

theorem supportAt_iff (s k : ℕ) (z : Source p) (hk : k < p.T) :
    supportAt rate rewards C_star C_h s k z ↔
      (entry rate rewards C_star C_h s ⟨k, hk⟩ z).map Prod.fst = some true ∧
        k + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z := by
  simp [supportAt, hk]

theorem supportAt_false_of_ge_horizon (s k : ℕ) (z : Source p) (hk : p.T ≤ k) :
    ¬ supportAt rate rewards C_star C_h s k z := by
  simp [supportAt, Nat.not_lt.mpr hk]

/-- The fixed-label support factors through the exact source prefix available
at the current pre-round time. The stop test remains inclusive. -/
theorem supportAt_prefix_factor (control0 : ContinuousLearningRows.TimeControl p)
    (s : ℕ) (t : Fin p.T) (z : Source p) :
    supportAt rate rewards C_star C_h s t.val z ↔
      supportAt rate rewards C_star C_h s t.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  have hentryEq := congrArg (fun e => e.map Prod.fst)
    (ReferenceSourcePrefixHistoryFiltration.entry_factor rate rewards C_star C_h
      control0 s t z)
  have hbad := ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
    rate rewards C_star C_h control0 t z
  rw [supportAt_iff rate rewards C_star C_h s t.val z t.isLt,
    supportAt_iff rate rewards C_star C_h s t.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) t.isLt]
  constructor
  · rintro ⟨he, hb⟩
    exact ⟨hentryEq ▸ he, hbad.mp hb⟩
  · rintro ⟨he, hb⟩
    exact ⟨hentryEq.symm ▸ he, hbad.mpr hb⟩

/-- Replacing the whole current selected control preserves the support event;
the actual incoming gate and the exact detector both factor through the strict
prefix before that control. -/
theorem supportAt_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : Source p) (control : ContinuousLearningRows.TimeControl p) :
    supportAt rate rewards C_star C_h s t.val z ↔
      supportAt rate rewards C_star C_h s t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  rw [supportAt_prefix_factor rate rewards C_star C_h control0 s t z,
    supportAt_prefix_factor rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z control]

/-- Measurability of the literal fixed-label support in the actual source
pre-round filtration. -/
theorem supportAt_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : Source p | supportAt rate rewards C_star C_h s t.val z} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let : MeasurableSpace (Option (Finset (Fin (p.m - 1)))) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let EntryValue := Bool × Option (Finset (Fin (p.m - 1)))
  let GateValues : Set (Option EntryValue) := {e | e.map Prod.fst = some true}
  have hgateSet : MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace]
      GateValues := by
    have hrepr : GateValues = ⋃ pending : Option (Finset (Fin (p.m - 1))),
        ({some (true, pending)} : Set (Option EntryValue)) := by
      ext e
      cases e with
      | none => simp [GateValues]
      | some pair =>
          rcases pair with ⟨flag, pending⟩
          cases flag with
          | false =>
              simp [GateValues]
              intro x heq
              cases heq
          | true => simp [GateValues]
    rw [hrepr]
    exact MeasurableSet.iUnion fun pending =>
      measurableSet_option_singleton (some (true, pending))
  have hentry := ReferenceSourcePrefixHistoryFiltration.entry_measurable
    rate rewards C_star C_h control0 s t
  have hgate : MeasurableSet[F (t.val + 1)]
      {z : Source p | (entry rate rewards C_star C_h s t z).map Prod.fst = some true} := by
    change MeasurableSet[F (t.val + 1)]
      ((entry rate rewards C_star C_h s t) ⁻¹' GateValues)
    exact hgateSet.preimage hentry
  have hstop : MeasurableSet[F (t.val + 1)]
      {z : Source p | t.val + 1 ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z} := by
    have hset : {z : Source p | t.val + 1 ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z} =
        {z | ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore
          rate rewards C_star C_h z t} := by
      ext z
      exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff
        rate rewards C_star C_h z t)
    rw [hset]
    exact ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_strictPrefix_measurable
      rate rewards C_star C_h control0 t
  have hset : {z : Source p | supportAt rate rewards C_star C_h s t.val z} =
      {z | (entry rate rewards C_star C_h s t z).map Prod.fst = some true} ∩
        {z | t.val + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z} := by
    ext z
    exact supportAt_iff rate rewards C_star C_h s t.val z t.isLt
  rw [hset]
  exact hgate.inter hstop

/-- Individual stopped-pending membership is predictable in the same
source-prefix field. -/
theorem pendingAt_mem_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : Source p | i ∈ pendingAt rate rewards C_star C_h s t.val z} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let PendingValues : Set (Finset (Fin (p.m - 1))) := {P | i ∈ P}
  have hpendSet : MeasurableSet PendingValues := (Set.to_countable PendingValues).measurableSet
  have hpend := ReferenceSourcePrefixHistoryFiltration.pending_measurable
    rate rewards C_star C_h control0 s t
  have hpend' : MeasurableSet[F (t.val + 1)]
      {z : Source p | i ∈ pending rate rewards C_star C_h s t z} := by
    change MeasurableSet[F (t.val + 1)]
      ((pending rate rewards C_star C_h s t) ⁻¹' PendingValues)
    exact hpendSet.preimage hpend
  have hsupport := supportAt_preRound_measurable rate rewards C_star C_h control0 s t
  have hset : {z : Source p | i ∈ pendingAt rate rewards C_star C_h s t.val z} =
      {z : Source p | supportAt rate rewards C_star C_h s t.val z} ∩
        {z : Source p | i ∈ pending rate rewards C_star C_h s t z} := by
    ext z
    by_cases hs : supportAt rate rewards C_star C_h s t.val z
    · simp [pendingAt, t.isLt, hs]
    · simp [pendingAt, t.isLt, hs]
  rw [hset]
  exact hsupport.inter hpend'

theorem sigmaR_le_iff_exists_supported_date (s : ℕ) (z : Source p) (n : ℕ)
    (hn : n ≤ p.T) :
    sigmaR rate rewards C_star C_h s z ≤ n ↔
      ∃ t : Fin p.T, t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z := by
  classical
  let D := supportDates rate rewards C_star C_h s z
  have hsentinel : (D ∪ {p.T + 1}).Nonempty :=
    ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  have hminmem : sigmaR rate rewards C_star C_h s z ∈ D ∪ {p.T + 1} := by
    exact Finset.min'_mem _ hsentinel
  constructor
  · intro hstart
    rcases Finset.mem_union.mp hminmem with hD | hsent
    · obtain ⟨t, ht, hdate⟩ := Finset.mem_image.mp hD
      have hsupp : supportAt rate rewards C_star C_h s t.val z :=
        (Finset.mem_filter.mp ht).2
      refine ⟨t, ?_, hsupp⟩
      rw [hdate]
      exact hstart
    · have : sigmaR rate rewards C_star C_h s z = p.T + 1 :=
        Finset.mem_singleton.mp hsent
      omega
  · rintro ⟨t, ht, hsupp⟩
    have htD : t.val + 1 ∈ D := by
      apply Finset.mem_image.mpr
      refine ⟨t, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp⟩
    change (D ∪ {p.T + 1}).min' hsentinel ≤ n
    exact (Finset.min'_le _ _ (Finset.mem_union_left _ htD)).trans ht

private theorem supported_date_through_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (s n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 n]
      {z : Source p | ∃ t : Fin p.T,
        t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hset : {z : Source p | ∃ t : Fin p.T,
      t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z} =
      ⋃ t : Fin p.T, {z : Source p |
        t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hset]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t.val + 1 ≤ n
  · have hsupport := supportAt_preRound_measurable rate rewards C_star C_h control0 s t
    have hsupport' : MeasurableSet[F n]
        {z : Source p | supportAt rate rewards C_star C_h s t.val z} :=
      (F.mono ht) _ hsupport
    simpa only [ht, true_and, Set.ofPred_and] using hsupport'
  · simp only [ht, false_and, Set.ofPred_false]
    exact @MeasurableSet.empty (Source p) (F n)

theorem pendingAt_eq_observed_of_support (s k : ℕ) (z : Source p)
    (hk : k < p.T) (hs : supportAt rate rewards C_star C_h s k z) :
    pendingAt rate rewards C_star C_h s k z =
      pending rate rewards C_star C_h s ⟨k, hk⟩ z := by
  simp [pendingAt, hk, hs]

theorem pendingAt_eq_empty_of_not_support (s k : ℕ) (z : Source p)
    (hs : ¬ supportAt rate rewards C_star C_h s k z) :
    pendingAt rate rewards C_star C_h s k z = ∅ := by
  by_cases hk : k < p.T <;> simp [pendingAt, hk, hs]

theorem mem_pendingAt_iff (s k : ℕ) (z : Source p) (i : Fin (p.m - 1)) :
    i ∈ pendingAt rate rewards C_star C_h s k z ↔
      supportAt rate rewards C_star C_h s k z ∧
        ∃ hk : k < p.T, i ∈ pending rate rewards C_star C_h s ⟨k, hk⟩ z := by
  by_cases hk : k < p.T
  · by_cases hs : supportAt rate rewards C_star C_h s k z
    · simp [pendingAt, hs, hk]
    · simp [pendingAt, hs, hk]
  · have hs : ¬ supportAt rate rewards C_star C_h s k z :=
      supportAt_false_of_ge_horizon rate rewards C_star C_h s k z (Nat.le_of_not_gt hk)
    simp [pendingAt, hk, hs]

theorem upObservation_eq_actual_of_lt (i : Fin (p.m - 1)) (k : ℕ) (z : Source p)
    (hk : k < p.T) :
    upObservation rate rewards C_star C_h i k z =
      actualUp rate rewards C_star C_h i ⟨k, hk⟩ z := by
  simp [upObservation, hk]

theorem dataObservation_eq_actual_of_lt (i : Fin (p.m - 1)) (k : ℕ) (z : Source p)
    (hk : k < p.T) :
    dataObservation rate rewards C_star C_h i k z =
      actualData rate rewards C_star C_h i ⟨k, hk⟩ z := by
  simp [dataObservation, hk]

theorem upObservation_false_of_ge_horizon (i : Fin (p.m - 1)) (k : ℕ) (z : Source p)
    (hk : p.T ≤ k) : upObservation rate rewards C_star C_h i k z = false := by
  simp [upObservation, Nat.not_lt.mpr hk]

theorem dataObservation_false_of_ge_horizon (i : Fin (p.m - 1)) (k : ℕ) (z : Source p)
    (hk : p.T ≤ k) : dataObservation rate rewards C_star C_h i k z = false := by
  simp [dataObservation, Nat.not_lt.mpr hk]

theorem mem_supportDates_iff (s k : ℕ) (z : Source p) :
    k + 1 ∈ supportDates rate rewards C_star C_h s z ↔
      k < p.T ∧ supportAt rate rewards C_star C_h s k z := by
  classical
  simp only [supportDates, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨t, ht, hdate⟩
    have hval : t.val = k := by omega
    subst k
    exact ⟨t.isLt, ht⟩
  · rintro ⟨hk, hs⟩
    exact ⟨⟨k, hk⟩, hs, rfl⟩

theorem sigmaR_bounds (s : ℕ) (z : Source p) :
    1 ≤ sigmaR rate rewards C_star C_h s z ∧
      sigmaR rate rewards C_star C_h s z ≤ thetaR rate rewards C_star C_h s z ∧
      thetaR rate rewards C_star C_h s z ≤ p.T + 1 := by
  classical
  let D := supportDates rate rewards C_star C_h s z
  have hdate_bounds : ∀ d, d ∈ D → 1 ≤ d ∧ d ≤ p.T := by
    intro d hd
    obtain ⟨t, ht, hdate⟩ := Finset.mem_image.mp hd
    have ht' : supportAt rate rewards C_star C_h s t.val z :=
      (Finset.mem_filter.mp ht).2
    rw [← hdate]
    exact ⟨by omega, Nat.succ_le_of_lt t.isLt⟩
  by_cases hD : D.Nonempty
  · have hmin := Finset.min'_mem (D ∪ {p.T + 1})
      ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    have hmax := Finset.max'_mem D hD
    have hmax_le : D.max' hD ≤ p.T := by
      exact (hdate_bounds _ hmax).2
    have hsigma_pos : 1 ≤ (D ∪ {p.T + 1}).min'
        ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ := by
      rcases Finset.mem_union.mp hmin with hd | hd
      · exact (hdate_bounds _ hd).1
      · simp only [Finset.mem_singleton] at hd
        omega
    have hsigma_le_max : (D ∪ {p.T + 1}).min'
        ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ ≤ D.max' hD :=
      Finset.min'_le _ _ (Finset.mem_union_left _ hmax)
    have hboundsD :
        1 ≤ (D ∪ {p.T + 1}).min'
            ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ ∧
          (D ∪ {p.T + 1}).min'
            ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩ ≤
            D.max' hD + 1 ∧ D.max' hD + 1 ≤ p.T + 1 :=
      ⟨hsigma_pos, by omega, by omega⟩
    simpa [sigmaR, thetaR, D, hD] using hboundsD
  · have hEmpty : supportDates rate rewards C_star C_h s z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hD
    have hsigma : sigmaR rate rewards C_star C_h s z = p.T + 1 := by
      simp [sigmaR, hEmpty]
    rw [hsigma]
    simp [thetaR, hEmpty]

/-- The support dates form exactly the half-open interval determined by the
first and last supported one-based dates. -/
theorem supportDates_eq_Ico_sigma_theta (s : ℕ) (z : Source p) :
    supportDates rate rewards C_star C_h s z =
      Finset.Ico (sigmaR rate rewards C_star C_h s z)
        (thetaR rate rewards C_star C_h s z) := by
  classical
  let D := supportDates rate rewards C_star C_h s z
  by_cases hD : D.Nonempty
  · have hsentinel : (D ∪ {p.T + 1}).Nonempty :=
      ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    have hminUnion : sigmaR rate rewards C_star C_h s z ∈ D ∪ {p.T + 1} := by
      exact Finset.min'_mem (D ∪ {p.T + 1}) hsentinel
    have hminD : sigmaR rate rewards C_star C_h s z ∈ D := by
      rcases Finset.mem_union.mp hminUnion with h | h
      · exact h
      · obtain ⟨d, hd⟩ := hD
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
        have htlt : t.val + 1 ≤ p.T := by omega
        have hminle : sigmaR rate rewards C_star C_h s z ≤ t.val + 1 := by
          change (D ∪ {p.T + 1}).min' hsentinel ≤ t.val + 1
          exact Finset.min'_le _ _ (Finset.mem_union_left _ hd)
        have hsent : sigmaR rate rewards C_star C_h s z = p.T + 1 := by
          simpa only [Finset.mem_singleton] using h
        omega
    have hmaxD : D.max' hD ∈ D := Finset.max'_mem D hD
    obtain ⟨tmin, htmin, hminDate⟩ := Finset.mem_image.mp hminD
    obtain ⟨tmax, htmax, hmaxDate⟩ := Finset.mem_image.mp hmaxD
    have hsigmaDate : sigmaR rate rewards C_star C_h s z = tmin.val + 1 := hminDate.symm
    have hthetaDate : thetaR rate rewards C_star C_h s z = tmax.val + 1 + 1 := by
      simp [thetaR, D, hD, hmaxDate.symm]
    have hsmin : supportAt rate rewards C_star C_h s tmin.val z :=
      (Finset.mem_filter.mp htmin).2
    have hsmax : supportAt rate rewards C_star C_h s tmax.val z :=
      (Finset.mem_filter.mp htmax).2
    ext d
    rw [Finset.mem_Ico]
    constructor
    · intro hd
      have hleft : sigmaR rate rewards C_star C_h s z ≤ d := by
        change (D ∪ {p.T + 1}).min' _ ≤ d
        exact Finset.min'_le _ _ (Finset.mem_union_left _ hd)
      have hright := Finset.le_max' D d hd
      rw [hsigmaDate] at hleft
      rw [hmaxDate.symm] at hright
      rw [hsigmaDate, hthetaDate]
      omega
    · intro hbound
      rw [hsigmaDate, hthetaDate] at hbound
      have hdleT : d ≤ p.T := by omega
      let t : Fin p.T := ⟨d - 1, by omega⟩
      have hmiddle := supportAt_between rate rewards C_star C_h s tmin t tmax z
        hsmin hsmax (by dsimp [t]; omega)
      have hmem := (mem_supportDates_iff rate rewards C_star C_h s (d - 1) z).2
        ⟨by dsimp [t] at hmiddle; exact t.isLt, by simpa [t] using hmiddle⟩
      have hdate : (d - 1) + 1 = d := by omega
      simpa [D, hdate] using hmem
  · have hEmpty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hsigma : sigmaR rate rewards C_star C_h s z = p.T + 1 := by
      simp [sigmaR, D, hEmpty]
    have htheta : thetaR rate rewards C_star C_h s z = p.T + 1 := by
      simp [thetaR, D, hEmpty]
    simpa [D, hsigma, htheta] using hEmpty

/-- In the interior of the horizon, the last-date sublevel event records an
earlier support occurrence and the current excluded date. The interval theorem
is what makes the current exclusion certify that the phase has ended. -/
theorem thetaR_le_iff_earlier_support_and_current_empty (s : ℕ) (z : Source p)
    (n : ℕ) (hnpos : 1 ≤ n) (hnT : n ≤ p.T) :
    thetaR rate rewards C_star C_h s z ≤ n ↔
      (∃ t : Fin p.T, t.val + 1 < n ∧ supportAt rate rewards C_star C_h s t.val z) ∧
        ¬ supportAt rate rewards C_star C_h s (n - 1) z := by
  classical
  let D := supportDates rate rewards C_star C_h s z
  have hinterval := supportDates_eq_Ico_sigma_theta rate rewards C_star C_h s z
  have hinterval' : D = Finset.Ico (sigmaR rate rewards C_star C_h s z)
      (thetaR rate rewards C_star C_h s z) := by simpa [D] using hinterval
  constructor
  · intro htheta
    have hD : D.Nonempty := by
      by_contra hempty
      have hempty' : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hsent : thetaR rate rewards C_star C_h s z = p.T + 1 := by
        simp [thetaR, D, hempty']
      omega
    have hbounds := sigmaR_bounds rate rewards C_star C_h s z
    have hsigmaLt : sigmaR rate rewards C_star C_h s z <
        thetaR rate rewards C_star C_h s z := by
      rcases hbounds with ⟨_, hst, _⟩
      have hs : sigmaR rate rewards C_star C_h s z ≠ thetaR rate rewards C_star C_h s z := by
        intro heq
        have hIco : D = ∅ := by
          rw [hinterval']
          simp [heq]
        have hemptyD : D = ∅ := hIco
        rw [hemptyD] at hD
        exact Finset.not_nonempty_empty hD
      omega
    have hfirstD : sigmaR rate rewards C_star C_h s z ∈ D := by
      rw [hinterval']
      exact Finset.mem_Ico.mpr ⟨le_rfl, hsigmaLt⟩
    obtain ⟨t, ht, hdate⟩ := Finset.mem_image.mp hfirstD
    have hfirstSupport : supportAt rate rewards C_star C_h s t.val z :=
      (Finset.mem_filter.mp ht).2
    have hfirstLT : t.val + 1 < n := by
      rw [hdate]
      omega
    have hcurrent : ¬ supportAt rate rewards C_star C_h s (n - 1) z := by
      intro hcur
      have hcurD : n ∈ D := by
        have hmem := (mem_supportDates_iff rate rewards C_star C_h s (n - 1) z).2
          ⟨by omega, hcur⟩
        simpa [Nat.sub_add_cancel hnpos] using hmem
      rw [hinterval'] at hcurD
      have := (Finset.mem_Ico.mp hcurD).2
      omega
    exact ⟨⟨t, hfirstLT, hfirstSupport⟩, hcurrent⟩
  · rintro ⟨⟨t, htdate, hsupport⟩, hcurrent⟩
    have hmemD : t.val + 1 ∈ D := by
      have hmem := (mem_supportDates_iff rate rewards C_star C_h s t.val z).2
        ⟨t.isLt, hsupport⟩
      simpa [D] using hmem
    have hintervalMem := Finset.mem_Ico.mp (hinterval'.symm ▸ hmemD)
    have hsigmaLe : sigmaR rate rewards C_star C_h s z ≤ n := by omega
    have hnotD : n ∉ D := by
      intro hnD
      have hcurMem : (n - 1) + 1 ∈ D := by
        simpa [Nat.sub_add_cancel hnpos] using hnD
      have hcurSupport := (mem_supportDates_iff rate rewards C_star C_h s (n - 1) z).mp hcurMem
      exact hcurrent hcurSupport.2
    by_contra hnotTheta
    have hnD : n ∈ D := by
      rw [hinterval']
      exact Finset.mem_Ico.mpr ⟨hsigmaLe, Nat.lt_of_not_ge hnotTheta⟩
    exact hnotD hnD

private theorem earlier_support_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (s n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 n]
      {z : Source p | ∃ t : Fin p.T,
        t.val + 1 < n ∧ supportAt rate rewards C_star C_h s t.val z} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hset : {z : Source p | ∃ t : Fin p.T,
      t.val + 1 < n ∧ supportAt rate rewards C_star C_h s t.val z} =
      ⋃ t : Fin p.T, {z : Source p |
        t.val + 1 < n ∧ supportAt rate rewards C_star C_h s t.val z} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hset]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t.val + 1 < n
  · have hsupport := supportAt_preRound_measurable rate rewards C_star C_h control0 s t
    have hsupport' : MeasurableSet[F n]
        {z : Source p | supportAt rate rewards C_star C_h s t.val z} :=
      (F.mono (by omega)) _ hsupport
    simpa only [ht, true_and, Set.ofPred_and] using hsupport'
  · simp only [ht, false_and, Set.ofPred_false]
    exact @MeasurableSet.empty (Source p) (F n)

theorem thetaR_sublevel_zero (s : ℕ) :
    {z : Source p | thetaR rate rewards C_star C_h s z ≤ 0} = ∅ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  have hb := sigmaR_bounds rate rewards C_star C_h s z
  have hpos : 1 ≤ thetaR rate rewards C_star C_h s z := by omega
  exact Nat.not_le_of_gt (by omega)

theorem thetaR_sublevel_after_horizon (s n : ℕ) (hn : p.T + 1 ≤ n) :
    {z : Source p | thetaR rate rewards C_star C_h s z ≤ n} = Set.univ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact (sigmaR_bounds rate rewards C_star C_h s z).2.2.trans hn

theorem thetaR_stopping (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (thetaR rate rewards C_star C_h s) := by
  intro n
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  by_cases hn0 : n = 0
  · subst n
    rw [thetaR_sublevel_zero rate rewards C_star C_h s]
    exact @MeasurableSet.empty (Source p) (F 0)
  · by_cases hnT : n ≤ p.T
    · have hnpos : 1 ≤ n := by omega
      let t : Fin p.T := ⟨n - 1, by omega⟩
      have hcur := supportAt_preRound_measurable rate rewards C_star C_h control0 s t
      have htidx : t.val + 1 = n := by dsimp [t]; omega
      have htval : t.val = n - 1 := rfl
      have hcur' : MeasurableSet[F n]
          {z : Source p | supportAt rate rewards C_star C_h s (n - 1) z} := by
        change MeasurableSet[F (t.val + 1)]
          {z : Source p | supportAt rate rewards C_star C_h s t.val z}
        rw [htidx, htval]
        exact hcur
      have hset : {z : Source p | thetaR rate rewards C_star C_h s z ≤ n} =
          {z : Source p | (∃ u : Fin p.T,
            u.val + 1 < n ∧ supportAt rate rewards C_star C_h s u.val z) ∧
              ¬ supportAt rate rewards C_star C_h s (n - 1) z} := by
        ext z
        exact thetaR_le_iff_earlier_support_and_current_empty rate rewards C_star C_h
          s z n hnpos hnT
      rw [hset]
      exact (earlier_support_measurable rate rewards C_star C_h control0 s n).inter hcur'.compl
    · rw [thetaR_sublevel_after_horizon rate rewards C_star C_h s n (by omega)]
      exact MeasurableSet.univ

/-- The first supported date is a stopping time in the actual original
source-prefix filtration. Its sublevel events are exactly first occurrences
of the measurable support indicators, including the empty and terminal cases.
-/
theorem sigmaR_stopping (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (sigmaR rate rewards C_star C_h s) := by
  intro n
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  by_cases hn0 : n = 0
  · subst n
    have hset : {z : Source p | sigmaR rate rewards C_star C_h s z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact Nat.not_le_of_gt ((sigmaR_bounds rate rewards C_star C_h s z).1)
    rw [hset]
    exact @MeasurableSet.empty (Source p) (F 0)
  · by_cases hnT : n ≤ p.T
    · have hset : {z : Source p | sigmaR rate rewards C_star C_h s z ≤ n} =
        {z : Source p | ∃ t : Fin p.T,
          t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z} := by
        ext z
        exact sigmaR_le_iff_exists_supported_date rate rewards C_star C_h s z n hnT
      rw [hset]
      exact supported_date_through_measurable rate rewards C_star C_h control0 s n
    · have hset : {z : Source p | sigmaR rate rewards C_star C_h s z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rcases sigmaR_bounds rate rewards C_star C_h s z with ⟨hpos, hst, hupper⟩
        omega
      rw [hset]
      exact MeasurableSet.univ

/-- The inclusive detecting update becomes a strict endpoint without moving
 the no-bad sentinel beyond the physical horizon. -/
def detectorEndpoint (z : Source p) : ℕ :=
  min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z + 1)
    (p.T + 1)

theorem detectorEndpoint_bounds (z : Source p) :
    1 ≤ detectorEndpoint rate rewards C_star C_h z ∧
      detectorEndpoint rate rewards C_star C_h z ≤ p.T + 1 := by
  have := ReferenceCompleteSignedFirstBadCalendar.firstBadDate_lower_bound
    rate rewards C_star C_h z
  unfold detectorEndpoint
  omega

theorem lt_detectorEndpoint_iff (k : ℕ) (z : Source p) (hk : k < p.T) :
    k + 1 < detectorEndpoint rate rewards C_star C_h z ↔
      k + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z := by
  unfold detectorEndpoint
  omega

private theorem entry_gate_source_calendar (s : ℕ) (t : Fin p.T) (a : ℕ)
    (ha : a ≤ t.val)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a) :
    (entry rate rewards C_star C_h s t z.val).map Prod.fst =
      ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
        z.property.1 a (p.T - a) z.property.2 (by omega) s t.val := by
  rw [entry_source_calendar rate rewards C_star C_h s t a ha z]
  unfold ReferenceLocalReleaseCalendarCounts.calendarEntry
    ReferenceLocalReleaseCalendarCounts.calendarGate
  cases ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
    z.property.1 a (p.T - a) z.property.2 (by omega) t.val <;> rfl

private theorem pendingAt_source_calendar (s a : ℕ) (ha : a ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a) (k : ℕ) :
    pendingAt rate rewards C_star C_h s k z.val =
      ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h a ha s
        (fun w => detectorEndpoint rate rewards C_star C_h w.val) k z := by
  by_cases hk : k < p.T
  · by_cases hak : a ≤ k
    · have hpend := pending_source_calendar rate rewards C_star C_h s ⟨k, hk⟩ a hak z
      have hgate := entry_gate_source_calendar rate rewards C_star C_h s ⟨k, hk⟩ a hak z
      by_cases hcut : k + 1 < detectorEndpoint rate rewards C_star C_h z.val
      · have hbad := (lt_detectorEndpoint_iff rate rewards C_star C_h k z.val hk).mp hcut
        by_cases hg : (entry rate rewards C_star C_h s ⟨k, hk⟩ z.val).map Prod.fst = some true
        · have hs : supportAt rate rewards C_star C_h s k z.val :=
            (supportAt_iff rate rewards C_star C_h s k z.val hk).mpr ⟨hg, hbad⟩
          simp only [pendingAt, dite_eq_left hk, ite_eq_left hs,
            ReferenceLocalReleaseWaitingPaths.pendingTheta, ite_eq_left hcut]
          exact hpend
        · have hempty : (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
              rate rewards C_star C_h a ha s z k).getD ∅ = ∅ := by
            cases hp : ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
                rate rewards C_star C_h a ha s z k with
            | none => rfl
            | some P =>
                have hg' := ReferenceLocalReleaseCalendarCounts.calendarPending_some_implies_gate
                  rate z.val rewards C_star C_h z.property.1 a (p.T - a) z.property.2
                  (by omega) s k P hp
                exact (hg (hgate.trans hg')).elim
          have hs : ¬ supportAt rate rewards C_star C_h s k z.val := by
            rw [supportAt_iff rate rewards C_star C_h s k z.val hk]
            exact fun h => hg h.1
          simp only [pendingAt, dite_eq_left hk, ite_eq_right hs,
            ReferenceLocalReleaseWaitingPaths.pendingTheta, ite_eq_left hcut, hempty]
      · have hbad : ¬ k + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z.val :=
          mt (lt_detectorEndpoint_iff rate rewards C_star C_h k z.val hk).mpr hcut
        have hs : ¬ supportAt rate rewards C_star C_h s k z.val := by
          rw [supportAt_iff rate rewards C_star C_h s k z.val hk]
          exact fun h => hbad h.2
        simp only [pendingAt, dite_eq_left hk, ite_eq_right hs,
          ReferenceLocalReleaseWaitingPaths.pendingTheta, ite_eq_right hcut]
    · have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val
          rewards C_star C_h = a := z.property.2
      have hrecord := actualRecord_eq_none_of_future_start rate rewards C_star C_h
        ⟨k, hk⟩ z.val (by change k < _; rw [hstart]; omega)
      have hspan : ¬ (a ≤ k ∧ k < a + (p.T - a)) := by omega
      simp [pendingAt, supportAt, hk, entry, incoming, hrecord,
        ReferenceLocalReleaseWaitingPaths.pendingTheta,
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
        ReferenceLocalReleaseCalendarCounts.calendarPending,
        ReferenceLocalReleaseCalendarCounts.calendarEntry,
        ReferenceLocalReleaseCalendarCounts.calendarRecord, hspan]
  · have hspan : ¬ (a ≤ k ∧ k < a + (p.T - a)) := by omega
    simp [pendingAt, hk, ReferenceLocalReleaseWaitingPaths.pendingTheta,
      ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
      ReferenceLocalReleaseCalendarCounts.calendarPending,
      ReferenceLocalReleaseCalendarCounts.calendarEntry,
      ReferenceLocalReleaseCalendarCounts.calendarRecord, hspan]

private theorem observations_source_calendar (s a : ℕ) (ha : a ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a)
    (i : Fin (p.m - 1)) (k : ℕ) :
    upObservation rate rewards C_star C_h i k z.val =
        ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h a ha s i k z ∧
      dataObservation rate rewards C_star C_h i k z.val =
        ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h a ha s i k z := by
  by_cases hk : k < p.T
  · by_cases hak : a ≤ k
    · have hflags := flags_source_calendar rate rewards C_star C_h s i ⟨k, hk⟩ a hak z
      exact ⟨(upObservation_eq_actual_of_lt rate rewards C_star C_h i k z.val hk).trans
        hflags.1, (dataObservation_eq_actual_of_lt rate rewards C_star C_h i k z.val hk).trans
        hflags.2.1⟩
    · have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val
          rewards C_star C_h = a := z.property.2
      have hrecord := actualRecord_eq_none_of_future_start rate rewards C_star C_h
        ⟨k, hk⟩ z.val (by change k < _; rw [hstart]; omega)
      have hspan : ¬ (a ≤ k ∧ k < a + (p.T - a)) := by omega
      simp [upObservation, dataObservation, hk, actualUp, actualData, hrecord,
        ReferenceLocalReleaseWaitingPaths.upObservation,
        ReferenceLocalReleaseWaitingPaths.dataObservation,
        ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
        ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
        ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
        ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
        ReferenceLocalReleaseCalendarCounts.calendarFlag,
        ReferenceLocalReleaseCalendarCounts.calendarRecord, hspan]
  · have hspan : ¬ (a ≤ k ∧ k < a + (p.T - a)) := by omega
    simp [upObservation, dataObservation, hk,
      ReferenceLocalReleaseWaitingPaths.upObservation,
      ReferenceLocalReleaseWaitingPaths.dataObservation,
      ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
      ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
      ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
      ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
      ReferenceLocalReleaseCalendarCounts.calendarFlag,
      ReferenceLocalReleaseCalendarCounts.calendarRecord, hspan]

private theorem waiting_counts_source_calendar (s a : ℕ) (ha : a ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a)
    (i : Fin (p.m - 1)) (v : ℕ) :
    PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (upObservation rate rewards C_star C_h) i v z.val =
      PhaseServiceWaiting.N
        (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h a ha s
          (fun w => detectorEndpoint rate rewards C_star C_h w.val))
        (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h a ha s) i v z ∧
    PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (dataObservation rate rewards C_star C_h) i v z.val =
      PhaseServiceWaiting.N
        (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h a ha s
          (fun w => detectorEndpoint rate rewards C_star C_h w.val))
        (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h a ha s) i v z := by
  constructor <;> apply Finset.sum_congr rfl <;> intro k _hk
  · rw [pendingAt_source_calendar rate rewards C_star C_h s a ha z k,
      (observations_source_calendar rate rewards C_star C_h s a ha z i k).1]
  · rw [pendingAt_source_calendar rate rewards C_star C_h s a ha z k,
      (observations_source_calendar rate rewards C_star C_h s a ha z i k).2]

private theorem pendingAt_empty_of_no_crossing (s : ℕ) (z : Source p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome ≠ true)
    (k : ℕ) : pendingAt rate rewards C_star C_h s k z = ∅ := by
  by_cases hk : k < p.T
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing = none := by
      change (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing = none
      cases hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing
      · rfl
      · simp [hc] at hcross
    have hr := actualRecord_eq_none_of_no_crossing rate rewards C_star C_h ⟨k, hk⟩ z hnone
    simp [pendingAt, supportAt, hk, entry, incoming, hr]
  · simp [pendingAt, hk]

/-- Genuine original-source quotas, transported from the same canonical launch
and its actual local pending history. The horizon `v` is unrestricted. -/
theorem waiting_N_le_one (s : ℕ) (z : Source p) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (upObservation rate rewards C_star C_h) i v z ≤ 1 ∧
      PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (dataObservation rate rewards C_star C_h) i v z ≤ 1 := by
  by_cases hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
  · let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have ha : a ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate z rewards C_star C_h
    let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a := ⟨z, hc, rfl⟩
    have heq := waiting_counts_source_calendar rate rewards C_star C_h s a ha w i v
    rw [heq.1, heq.2]
    exact ⟨ReferenceLocalReleaseWaitingPaths.up_N_le_one rate rewards C_star C_h a ha s
      (fun u => detectorEndpoint rate rewards C_star C_h u.val)
      (fun u => detectorEndpoint_bounds rate rewards C_star C_h u.val) w v i,
      ReferenceLocalReleaseWaitingPaths.data_N_le_one rate rewards C_star C_h a ha s
      (fun u => detectorEndpoint rate rewards C_star C_h u.val)
      (fun u => detectorEndpoint_bounds rate rewards C_star C_h u.val) w v i⟩
  · simp [PhaseServiceWaiting.N, pendingAt_empty_of_no_crossing rate rewards C_star C_h s z hc]

/-- A still-pending task has no incoming service observation. This is the
strict quota required by waiting, with zero-based current index `k`. -/
theorem strict_prior_N_zero_at_pending (s : ℕ) (z : Source p) (k : ℕ)
    (i : Fin (p.m - 1)) (hi : i ∈ pendingAt rate rewards C_star C_h s k z) :
    PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (upObservation rate rewards C_star C_h) i k z = 0 ∧
      PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (dataObservation rate rewards C_star C_h) i k z = 0 := by
  by_cases hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
  · let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have ha : a ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate z rewards C_star C_h
    let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a := ⟨z, hc, rfl⟩
    have hi' : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h a ha s
        (fun u => detectorEndpoint rate rewards C_star C_h u.val) k w := by
      rw [← pendingAt_source_calendar rate rewards C_star C_h s a ha w k]
      exact hi
    have hq := ReferenceLocalReleaseWaitingPaths.strict_prior_N_zero_at_pending
      rate rewards C_star C_h a ha s (fun u => detectorEndpoint rate rewards C_star C_h u.val)
      (fun u => detectorEndpoint_bounds rate rewards C_star C_h u.val) w k i hi'
    have heq := waiting_counts_source_calendar rate rewards C_star C_h s a ha w i k
    exact ⟨heq.1.trans hq.2.1, heq.2.trans hq.2.2.1⟩
  · simp [pendingAt_empty_of_no_crossing rate rewards C_star C_h s z hc k] at hi

/-- Exact support characterization at every natural calendar index. -/
theorem supportAt_iff_interval (s k : ℕ) (z : Source p) :
    supportAt rate rewards C_star C_h s k z ↔
      sigmaR rate rewards C_star C_h s z ≤ k + 1 ∧
        k + 1 < thetaR rate rewards C_star C_h s z := by
  have hmem := mem_supportDates_iff rate rewards C_star C_h s k z
  rw [supportDates_eq_Ico_sigma_theta, Finset.mem_Ico] at hmem
  constructor
  · intro h
    have hk : k < p.T := by
      by_contra hn
      exact supportAt_false_of_ge_horizon rate rewards C_star C_h s k z (by omega) h
    exact hmem.mpr ⟨hk, h⟩
  · exact fun h => (hmem.mp h).2

theorem pendingAt_empty_outside_interval (s k : ℕ) (z : Source p)
    (hout : ¬ (sigmaR rate rewards C_star C_h s z ≤ k + 1 ∧
      k + 1 < thetaR rate rewards C_star C_h s z)) :
    pendingAt rate rewards C_star C_h s k z = ∅ := by
  exact pendingAt_eq_empty_of_not_support rate rewards C_star C_h s k z
    (mt (supportAt_iff_interval rate rewards C_star C_h s k z).mp hout)

/-- A supported round itself produces the genuine crossing and prelaunch
bound; these are not caller-supplied successful-history conditions. -/
theorem supportAt_actualLaunchBy (s : ℕ) (t : Fin p.T) (z : Source p)
    (hs : supportAt rate rewards C_star C_h s t.val z) :
    actualLaunchBy rate rewards C_star C_h t.val z := by
  by_contra hn
  have hr := actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hn
  have hg := ((supportAt_iff rate rewards C_star C_h s t.val z t.isLt).mp hs).1
  simp [entry, incoming, hr] at hg

private theorem supportAt_local_interval (s a : ℕ) (ha : a ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a)
    (k : ℕ) (hk : k < p.T) (hs : supportAt rate rewards C_star C_h s k z.val) :
    ReferenceLocalReleaseWaitingPaths.localPhaseSigma rate rewards C_star C_h a ha s
        (fun w => detectorEndpoint rate rewards C_star C_h w.val) z ≤ k + 1 ∧
      k + 1 < ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
        rate rewards C_star C_h a ha s
        (fun w => detectorEndpoint rate rewards C_star C_h w.val) z := by
  have hl := supportAt_actualLaunchBy rate rewards C_star C_h s ⟨k, hk⟩ z.val hs
  have hak : a ≤ k := by
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val
        rewards C_star C_h = a := z.property.2
    simpa only [hstart] using hl.2
  have hs' := (supportAt_iff rate rewards C_star C_h s k z.val hk).mp hs
  have hg := (entry_gate_source_calendar rate rewards C_star C_h s ⟨k, hk⟩ a hak z).symm.trans hs'.1
  have hraw := ReferenceLocalReleaseCalendarCounts.calendarGate_inside_interval
    rate z.val rewards C_star C_h z.property.1 a (p.T - a) z.property.2 (by omega) s k hg
  have hcut := (lt_detectorEndpoint_iff rate rewards C_star C_h k z.val hk).mpr hs'.2
  have hleft : ReferenceLocalReleaseWaitingPaths.localGateAlpha
      rate rewards C_star C_h a ha s z ≤ k + 1 := hraw.1
  have hright : k + 1 < ReferenceLocalReleaseWaitingPaths.localGateBeta
      rate rewards C_star C_h a ha s z := hraw.2
  have hnonempty : ReferenceLocalReleaseWaitingPaths.localGateAlpha
      rate rewards C_star C_h a ha s z < min
        (ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h a ha s z)
        (detectorEndpoint rate rewards C_star C_h z.val) := by omega
  simp only [ReferenceLocalReleaseWaitingPaths.localPhaseSigma,
    ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint, hnonempty, ite_true]
  exact ⟨hleft, by omega⟩

/-- Pending tasks shrink while the actual stopped release interval continues,
including when either pending set is empty. -/
theorem pendingAt_nested_inside_interval (s : ℕ) (z : Source p) (j k : ℕ)
    (hjk : j ≤ k)
    (hstart : sigmaR rate rewards C_star C_h s z ≤ j + 1)
    (hexit : k + 1 < thetaR rate rewards C_star C_h s z) :
    pendingAt rate rewards C_star C_h s k z ⊆ pendingAt rate rewards C_star C_h s j z := by
  have hb := sigmaR_bounds rate rewards C_star C_h s z
  have hk : k < p.T := by omega
  have hj : j < p.T := by omega
  have hsJ := (supportAt_iff_interval rate rewards C_star C_h s j z).mpr ⟨hstart, by omega⟩
  have hsK := (supportAt_iff_interval rate rewards C_star C_h s k z).mpr ⟨by omega, hexit⟩
  have hl := supportAt_actualLaunchBy rate rewards C_star C_h s ⟨j, hj⟩ z hsJ
  let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have ha : a ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h a := ⟨z, hl.1, rfl⟩
  have hJ := supportAt_local_interval rate rewards C_star C_h s a ha w j hj hsJ
  have hK := supportAt_local_interval rate rewards C_star C_h s a ha w k hk hsK
  rw [pendingAt_source_calendar rate rewards C_star C_h s a ha w k,
    pendingAt_source_calendar rate rewards C_star C_h s a ha w j]
  exact ReferenceLocalReleaseWaitingPaths.pendingTheta_nested_inside_interval
    rate rewards C_star C_h a ha s (fun u => detectorEndpoint rate rewards C_star C_h u.val)
    (fun u => detectorEndpoint_bounds rate rewards C_star C_h u.val) w j k hjk hk hJ.1 hK.2

/-- The whole stopped pending set factors through the actual strict prefix. -/
theorem pendingAt_prefix_factor (control0 : ContinuousLearningRows.TimeControl p)
    (s : ℕ) (t : Fin p.T) (z : Source p) :
    pendingAt rate rewards C_star C_h s t.val z =
      pendingAt rate rewards C_star C_h s t.val (sourcePrefix control0 t.val z) := by
  have hs := supportAt_prefix_factor rate rewards C_star C_h control0 s t z
  have hp := pending_factor rate rewards C_star C_h control0 s t z
  simp only [pendingAt, dite_eq_left t.isLt]
  rw [hs, hp]

theorem pendingAt_replaceSourceControl (control0 : ContinuousLearningRows.TimeControl p)
    (s : ℕ) (t : Fin p.T) (z : Source p) (control : ContinuousLearningRows.TimeControl p) :
    pendingAt rate rewards C_star C_h s t.val z =
      pendingAt rate rewards C_star C_h s t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  rw [pendingAt_prefix_factor rate rewards C_star C_h control0 s t z,
    pendingAt_prefix_factor rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control),
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z control]

/-- The literal incoming counts obey the strict quota-one condition. -/
theorem strict_prior_N_lt_one_at_pending (s : ℕ) (z : Source p) (k : ℕ)
    (i : Fin (p.m - 1)) (hi : i ∈ pendingAt rate rewards C_star C_h s k z) :
    PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (upObservation rate rewards C_star C_h) i k z < 1 ∧
      PhaseServiceWaiting.N (pendingAt rate rewards C_star C_h s)
        (dataObservation rate rewards C_star C_h) i k z < 1 := by
  obtain ⟨hu, hd⟩ := strict_prior_N_zero_at_pending rate rewards C_star C_h s z k i hi
  omega

/-- At an actual later installation, the fixed absolute label selects exactly
its genuine release suffix, cut only by the inclusive first-bad date. The
occurrence selector is used pointwise, not as an all-calendar history premise. -/
theorem supportAt_iff_later_release_member (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) (t : Fin p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
    let Rel := (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)).dropWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    supportAt rate rewards C_star C_h s t.val z ↔
      (∃ r ∈ Rel, r.input.time = t) ∧
        t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
  intro R s Rel
  have hfilter := ReferencePostReplacementCollectionReleaseSupport.later_release_filter_eq
    rate rewards C_star C_h z b hb
  change R.filter (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate
    rate s r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) = Rel
    at hfilter
  rw [supportAt_iff_stopped_originalGate rate rewards C_star C_h s t.val z t.isLt]
  unfold originalGateSupport
  change t.val + 1 ∈ ReferenceLocalReleaseGateChronology.gateSupport s R ∧ _ ↔ _
  rw [ReferenceLocalReleaseGateChronology.mem_gateSupport]
  constructor
  · rintro ⟨⟨r, hr, hg, hdate⟩, hbad⟩
    have hrel : r ∈ Rel := by
      rw [← hfilter]
      exact List.mem_filter.mpr ⟨hr, hg⟩
    exact ⟨⟨r, hrel, Fin.ext (by omega)⟩, hbad⟩
  · rintro ⟨⟨r, hr, ht⟩, hbad⟩
    rw [← hfilter] at hr
    obtain ⟨hr, hg⟩ := List.mem_filter.mp hr
    exact ⟨⟨r, hr, hg, by rw [ht]⟩, hbad⟩

private theorem actualRecord_source_fields (t : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hl : actualLaunchBy rate rewards C_star C_h t.val z
  · have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hl.1
    have hrec := actualRecord_on_launch rate rewards C_star C_h t z _ hlaunch hl.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hl.2
    omega
  · rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hl] at hr
    cases hr

/-- Whole birth payload, exact absolute stamp, actual record, whole public bank,
selected row and whole reward table on the same later-installation release
segment. Pending sets retain their literal source meaning after stopping. -/
theorem later_release_payload_and_pending (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
    let Rel := (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)).dropWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    ∃ M : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧ M.sigma.val = s ∧
      ∀ r ∈ Rel,
        actualRecord rate rewards C_star C_h r.input.time z = some r ∧
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        r.input.rows = z.1.2 ∧
        r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        r.input.rewards = rewards ∧
        (supportAt rate rewards C_star C_h s r.input.time.val z ↔
          r.input.time.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z) ∧
        pendingAt rate rewards C_star C_h s r.input.time.val z =
          if r.input.time.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
              rate rewards C_star C_h z then ReferencePhysicalReleaseQuota.pendingSet M r else ∅ := by
  intro R s Rel
  obtain ⟨M, hbirth, hstamp, hread⟩ :=
    ReferencePostReplacementCollectionReleaseSupport.later_release_member_readouts
      rate rewards C_star C_h z b hb
  refine ⟨M, hbirth, hstamp, ?_⟩
  intro r hr
  obtain ⟨hstored, _hgate, hrecord, _hentry, hpending⟩ := hread r hr
  obtain ⟨hrows, hselected, _htime, hrewards⟩ :=
    actualRecord_source_fields rate rewards C_star C_h r.input.time z r hrecord
  have hsupp : supportAt rate rewards C_star C_h s r.input.time.val z ↔
      r.input.time.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z := by
    have h := supportAt_iff_later_release_member rate rewards C_star C_h z b hb r.input.time
    change supportAt rate rewards C_star C_h s r.input.time.val z ↔
      (∃ u ∈ Rel, u.input.time = r.input.time) ∧ _ at h
    rw [h]
    exact and_iff_right ⟨r, hr, rfl⟩
  refine ⟨hrecord, hstored, hrows, hselected, hrewards, hsupp, ?_⟩
  by_cases hbad : r.input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  · rw [ite_eq_left hbad, pendingAt_eq_observed_of_support rate rewards C_star C_h s
      r.input.time.val z r.input.time.isLt (hsupp.mpr hbad)]
    exact hpending
  · rw [ite_eq_right hbad]
    exact pendingAt_eq_empty_of_not_support rate rewards C_star C_h s r.input.time.val z
      (mt hsupp.mp hbad)

/-- Finite first-occurrence sublevels, including zero and every sentinel or
post-horizon index. -/
theorem sigmaR_le_iff (s : ℕ) (z : Source p) (n : ℕ) :
    sigmaR rate rewards C_star C_h s z ≤ n ↔
      p.T + 1 ≤ n ∨ ∃ t : Fin p.T,
        t.val + 1 ≤ n ∧ supportAt rate rewards C_star C_h s t.val z := by
  by_cases hn : n ≤ p.T
  · rw [sigmaR_le_iff_exists_supported_date rate rewards C_star C_h s z n hn]
    simp only [show ¬ p.T + 1 ≤ n by omega, false_or]
  · have hb := sigmaR_bounds rate rewards C_star C_h s z
    exact ⟨fun _ => Or.inl (by omega), fun _ => by omega⟩

/-- Finite end sublevels are an earlier support occurrence followed by current
exclusion, or the horizon sentinel. This identity uses actual no-return. -/
theorem thetaR_le_iff (s : ℕ) (z : Source p) (n : ℕ) :
    thetaR rate rewards C_star C_h s z ≤ n ↔
      p.T + 1 ≤ n ∨
        (∃ t : Fin p.T, t.val + 1 < n ∧ supportAt rate rewards C_star C_h s t.val z) ∧
          ¬ supportAt rate rewards C_star C_h s (n - 1) z := by
  by_cases hn : n ≤ p.T
  · by_cases hzero : n = 0
    · subst n
      have hb := sigmaR_bounds rate rewards C_star C_h s z
      constructor
      · intro h
        omega
      · rintro (h | ⟨⟨t, ht, _⟩, _⟩) <;> omega
    · rw [thetaR_le_iff_earlier_support_and_current_empty rate rewards C_star C_h s z n
        (by omega) hn]
      simp only [show ¬ p.T + 1 ≤ n by omega, false_or]
  · have hb := sigmaR_bounds rate rewards C_star C_h s z
    exact ⟨fun _ => Or.inl (by omega), fun _ => by omega⟩

/-- Predictability on the whole natural calendar; post-horizon support is
literally false. -/
theorem supportAt_measurable (control0 : ContinuousLearningRows.TimeControl p) (s k : ℕ) :
    MeasurableSet[sourcePrefixFiltration control0 (k + 1)]
      {z : Source p | supportAt rate rewards C_star C_h s k z} := by
  by_cases hk : k < p.T
  · exact supportAt_preRound_measurable rate rewards C_star C_h control0 s ⟨k, hk⟩
  · have hset : {z : Source p | supportAt rate rewards C_star C_h s k z} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact supportAt_false_of_ge_horizon rate rewards C_star C_h s k z (by omega)
    rw [hset]
    exact @MeasurableSet.empty (Source p) (sourcePrefixFiltration control0 (k + 1))

theorem pendingAt_mem_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (s k : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (k + 1)]
      {z : Source p | i ∈ pendingAt rate rewards C_star C_h s k z} := by
  by_cases hk : k < p.T
  · exact pendingAt_mem_preRound_measurable rate rewards C_star C_h control0 s ⟨k, hk⟩ i
  · have hset : {z : Source p | i ∈ pendingAt rate rewards C_star C_h s k z} = ∅ := by
      ext z
      simp [pendingAt, hk]
    rw [hset]
    exact @MeasurableSet.empty (Source p) (sourcePrefixFiltration control0 (k + 1))

end Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase

end noncomputable section
