/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarPathAgreement

import Mathlib.Tactic

/-!
# Archived LIVE-empty payoff on the generated calendar

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

The auxiliary reward uses the slow set and FAST arm of the dated logical
cell. Its identification with a physical diagnostic requires an actual LIVE
choice with empty pending confirmation and a clear numerical PRE. In
particular the first detecting UPDATE is retained. These are pathwise payoff
identities, without a marginal law or an expectation/accounting assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceActualLiveEmptySignedRewardCalendar
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarLivePayoff

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Record" => ReferenceFirstLiveChronologicalPrefixFoundation.Record

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Cell" => LogicalCell p rate
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h

/-- The manuscript's literal auxiliary reward on this dated logical cell. -/
def logicalReward (e : Cell) : ℝ :=
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards e.time
  ReleaseRoundKernel.slowReward row e.slowSet + row.val e.fastArm

/-- The actual LIVE-empty gate for the selector already retained by a native
source cell. No recorder success or POST-clear test is imposed. -/
theorem sourceCell_liveEmptyGate (r : Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (hempty : c.selected.view.pendingAtChoice = ∅) :
    liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection c.selected) := by
  refine ⟨?_, hempty⟩
  rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
    _ _ r.input.time rfl]
  exact decide_eq_true c.assignment_live

/-- Both arm identifications hold for the SAME actual logical update. The
FAST equality uses empty confirmation, not merely the LIVE label. -/
theorem appendLogicalCell_live_empty_arms (r : Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (S : RecordedQueueRun.RunState p.K)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hpre : S.overflow = false) (hempty : c.selected.view.pendingAtChoice = ∅) :
    (appendLogicalCell r c S a).slowSet = c.selected.view.payload.slowSet ∧
      (appendLogicalCell r c S a).fastArm = c.selected.arm := by
  constructor
  · simp only [appendLogicalCell, hpre, Bool.false_eq_true, ite_false]
  · simp only [appendLogicalCell, hpre, Bool.false_eq_true, ite_false]
    exact reservedFastArm_eq_selected_of_empty r c hempty

/-- The physical diagnostic becomes the logical auxiliary reward only after
the slow set AND coordinator FAST draw have been identified. -/
theorem appendLogicalCell_live_empty_payoff (t : Fin p.T) (z : Source)
    (r : Record rate) (hr : recordAt t z = some r)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (S : RecordedQueueRun.RunState p.K)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hpre : S.overflow = false) (hempty : c.selected.view.pendingAtChoice = ∅) :
    let e := appendLogicalCell r c S a
    e.time = t ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.slowSet = c.selected.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      physicalDiagnostic rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection c.selected) = logicalReward rate rewards e ∧
      observation rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
        some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  dsimp only
  have hd := actual_live_empty_diagnostic rate rewards C_star C_h t z r hr c.selected
    c.selection_actual (sourceCell_liveEmptyGate rate r c hempty)
  have ha := appendLogicalCell_live_empty_arms rate r c S a hpre hempty
  have hfast : (appendLogicalCell r c S a).fastArm =
      r.actions (ActiveRoundActions.coordinator p.two_le_m) :=
    ha.2.trans hd.2.2.2.2.2.1.symm
  have ht : (appendLogicalCell r c S a).time = t := hd.1
  have he : physicalDiagnostic rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection c.selected) =
        logicalReward rate rewards (appendLogicalCell r c S a) := by
    unfold logicalReward physicalDiagnostic
    rw [ht, ha.1, hfast]
    rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.1]
    rfl
  refine ⟨ht, rfl, ha.1, hfast, he, ?_⟩
  rw [← he]
  exact hd.2.2.2.2.2.2.2.2.1

/-- The inclusive physical gate forces any present canonical numerical PRE
to be clear, including the PRE of the first overflow-detecting UPDATE. -/
theorem prefixNumerical_clear_of_inclusive_gate (t : Fin p.T) (z : Source)
    (S : RecordedQueueRun.RunState p.K)
    (hS : prefixNumerical rate rewards C_star C_h t.castSucc z = some S)
    (hgate : ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z t) : S.overflow = false := by
  obtain ⟨L, hL, hrun⟩ := Option.map_eq_some_iff.mp hS
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h t.val z = some L at hL
  have hr : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h t.val z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout S) := by
    rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hL,
      Option.map_some, hrun]
  have hno := (ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    rate rewards C_star C_h z t).mp hgate t.val le_rfl _ hr
  cases ho : S.overflow with
  | false => rfl
  | true =>
      obtain ⟨arm, harm⟩ := (RecordedQueueRun.run_overflow_iff_cutoff Q L).mp (hrun ▸ ho)
      rw [hrun] at harm
      exact False.elim (hno arm ((RecordedQueueRun.overflowCutoff_iff Q _).mpr harm))

/-- No actual collection recorder call has a LIVE selected choice. This
uses the dispatcher's own cutoff/collection frame, including disabled dates. -/
private theorem not_live_of_collection_call (r : Record rate)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hc : (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r).isSome = true) :
    ¬ CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
  have hf := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hc
  split at hc
  · cases hd : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
    | live regs owned base outcome =>
        cases outcome <;> simp only [hd] at hc hsel hf
        all_goals try cases hc
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, dite_true] at hsel
        have he := Option.some.inj hsel
        exact he ▸ hf.1
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd] at hc hsel hf
        all_goals try cases hc
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection] at hsel
        have he := Option.some.inj hsel
        exact he ▸ hf.1
    | invalidCollectionCutoff => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
    | dagger => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
  · cases hc

/-- The actual selected LIVE branch after launch is continuing LIVE when
there is no native assignment call. The phase witness is produced internally. -/
theorem continuingDomain_of_live_selection (t : Fin p.T) (z : Source)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < t.val)
    (hn : ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h t z)
    (r : Record rate) (hr : recordAt t z = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time) :
    z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h t := by
  rcases noncall_phase_coverage rate rewards C_star C_h t z hstart hn with h | h
  · exact h
  · obtain ⟨s, hs, _hen, hc⟩ := h
    have he : s = r := Option.some.inj (hs.symm.trans hr)
    subst s
    exact False.elim (not_live_of_collection_call rate r sel hsel hc hlive)

variable (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0

/-- Whole native cells on an archived source already carry the SAME final
source's physical record. Empty confirmation is tested on that actual record. -/
theorem nativeCell_live_empty_payoff (t : Fin p.T)
    (z : InvocationSource rate rewards C_star C_h t) (x : ContinuousControlSlice.Scalar)
    (hgate : ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z.val t)
    (hempty : (nativeSourceCell rate rewards C_star C_h t z).selected.view.pendingAtChoice = ∅) :
    let e := nativeCell rate rewards C_star C_h control0 t z x
    let r := nativeRecord rate rewards C_star C_h t z
    e.time = t ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.slowSet = (nativeSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      observation rate rewards t e.physical =
        some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  dsimp only
  have hpre := prefixNumerical_clear_of_inclusive_gate rate rewards C_star C_h t z.val
    (nativeBefore rate rewards C_star C_h control0 t z)
    (nativeBefore_prefix rate rewards C_star C_h control0 t z) hgate
  have h := appendLogicalCell_live_empty_payoff rate rewards C_star C_h t z.val
    (nativeRecord rate rewards C_star C_h t z) (nativeSourceCell_spec rate rewards C_star C_h t z).1
    (nativeSourceCell rate rewards C_star C_h t z)
    (nativeBefore rate rewards C_star C_h control0 t z)
    (Function.update ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
      ((nativeRecord rate rewards C_star C_h t z).input.time, 1) x) hpre hempty
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

/-- The continuing cell uses its full original numerical PRE, not a supplied
seed or a last-POST surrogate. -/
theorem continuingLogicalCell_live_empty_payoff (t : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h t)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hgate : ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h z.val t)
    (hempty : (continuingSourceCell rate rewards C_star C_h t z).selected.view.pendingAtChoice = ∅) :
    let e := continuingLogicalCell rate rewards C_star C_h t z a
    let r := continuingRecord rate rewards C_star C_h t z
    e.time = t ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.slowSet = (continuingSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      observation rate rewards t e.physical =
        some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  dsimp only
  have hpre := prefixNumerical_clear_of_inclusive_gate rate rewards C_star C_h t z.val
    (continuingBefore rate rewards C_star C_h t z)
    (continuingBefore_spec rate rewards C_star C_h t z) hgate
  have h := appendLogicalCell_live_empty_payoff rate rewards C_star C_h t z.val
    (continuingRecord rate rewards C_star C_h t z) (continuingSourceCell_spec rate rewards C_star C_h t z).1
    (continuingSourceCell rate rewards C_star C_h t z)
    (continuingBefore rate rewards C_star C_h t z) a hpre hempty
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

private theorem calendarObservation_noncall_source (j : ℕ)
    (hj : t0.val + 1 + j < p.T) (w : Sample j)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (hc : callFlag j (by omega) w = false) :
    current (j + 1) (by omega) (w, v) = current j hj.le w := by
  let q : Fin p.T := ⟨t0.val + 1 + j, hj⟩
  let o : TaggedPrefix rate q.castSucc := observe j hj.le w
  have hn : ¬ (o.2, ((original j w).1.2, v)) ∈
      calendarCallEvent rate rewards C_star C_h o.1 q := by
    change ¬ callFlag j (by omega) w = true
    rw [hc]
    exact Bool.false_ne_true
  change (calendarStep rate rewards C_star C_h control0 q
    (o, ((original j w).1.2, v))).2.val.1.1.1.2 = _
  rw [calendarStep, dite_eq_right hn]
  rfl

private theorem calendarObservation_call_tag (j : ℕ)
    (hj : t0.val + 1 + j < p.T) (w : Sample j)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (hc : callFlag j (by omega) w = true) :
    (observe (j + 1) (by omega) (w, v)).1 = ⟨t0.val + 1 + j, hj⟩ := by
  let q : Fin p.T := ⟨t0.val + 1 + j, hj⟩
  let o : TaggedPrefix rate q.castSucc := observe j hj.le w
  have he : (o.2, ((original j w).1.2, v)) ∈
      calendarCallEvent rate rewards C_star C_h o.1 q := hc
  change (calendarStep rate rewards C_star C_h control0 q
    (o, ((original j w).1.2, v))).1 = q
  rw [calendarStep, dite_eq_left he]

/-- Retrieve the last native cell of ANY earlier boundary inside the final
archive, recomputed on the SAME final current source. -/
theorem calendar_archived_lastNative (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) (j : ℕ) (hj : j ≤ k) :
    let prev := observe j (by omega) (ancestor k j hj w)
    ∃ (z : InvocationSource rate rewards C_star C_h prev.1)
      (x : ContinuousControlSlice.Scalar), z.val = current k hk w ∧
      nativeCell rate rewards C_star C_h control0 prev.1 z x ∈ (stored k hk w).2 := by
  dsimp only
  let earlier := ancestor k j hj w
  let prev := observe j (by omega) earlier
  let x := (original j earlier).1.2 (prev.1,
    if calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0 j (by omega) earlier then 0 else 1)
  obtain ⟨z, hz, he⟩ := calendarObservation_archived_native rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj
  refine ⟨z, x, hz, ?_⟩
  rw [he]
  have hinit := (calendarObservation_native_prefix rate rewards C_star C_h control0 b0 u0 t0 j
    (by omega) earlier).1
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0
    k hk w j hj).1
  apply hp.sublist.subset
  apply hinit.sublist.subset
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem calendarObservation_root_tag (w : Sample 0) :
    (observe 0 (by omega) w).1 = t0 := by
  cases b0 <;> rfl

theorem calendar_archived_root (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    ∃ (z : InvocationSource rate rewards C_star C_h t0) (x : ContinuousControlSlice.Scalar),
      z.val = current k hk w ∧ nativeCell rate rewards C_star C_h control0 t0 z x ∈ (stored k hk w).2 := by
  have h := calendar_archived_lastNative rate rewards C_star C_h control0 b0 u0 t0 k hk w 0 (Nat.zero_le _)
  dsimp only at h
  let P := fun t : Fin p.T => ∃ (z : InvocationSource rate rewards C_star C_h t)
    (x : ContinuousControlSlice.Scalar), z.val = current k hk w ∧
      nativeCell rate rewards C_star C_h control0 t z x ∈ (stored k hk w).2
  exact Eq.mp (congrArg P (calendarObservation_root_tag rate rewards C_star C_h control0 b0 u0 t0 _)) h

theorem calendarCurrentSource_start_le_root (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    ReferenceCompletePhysicalHistory.physicalStart rate (current k hk w) rewards C_star C_h ≤ t0.val := by
  obtain ⟨z, _x, hz, _hmem⟩ := calendar_archived_root rate rewards C_star C_h control0 b0 u0 t0 k hk w
  obtain ⟨_i, _hi, _hr, hs⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h t0 z.val (nativeRecord rate rewards C_star C_h t0 z)
    (nativeSourceCell_spec rate rewards C_star C_h t0 z).1
  exact hz ▸ hs

private theorem callAt_congr_prefix (t : Fin p.T) (n : ℕ) (htn : t.val ≤ n) (z z' : Source)
    (h : sourcePrefix control0 n z = sourcePrefix control0 n z') :
    ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z =
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z' := by
  have he := congrArg (sourcePrefix control0 t.val) h
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ htn,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ htn] at he
  rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 t z,
    he, ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 t z']

/-- An actual selected LIVE date at or after this branch's root has an
internally retrieved canonical native or continuing cell in the final list.
Both alternatives use the SAME final complete source, through future insertions. -/
theorem calendar_archived_live_cell (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (t : Fin p.T) (ht0 : t0.val ≤ t.val) (ht : t.val < t0.val + 1 + k)
    (hscan : ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h (current k hk w) t)
    (r : Record rate) (hr : recordAt t (current k hk w) = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time) :
    (∃ (z : InvocationSource rate rewards C_star C_h t) (x : ContinuousControlSlice.Scalar),
      z.val = current k hk w ∧ nativeCell rate rewards C_star C_h control0 t z x ∈ (stored k hk w).2) ∨
    (∃ (z : ContinuingLiveSource rate rewards C_star C_h t)
      (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p),
      z.val = current k hk w ∧ continuingLogicalCell rate rewards C_star C_h t z a ∈ (stored k hk w).2) := by
  by_cases heq : t = t0
  · subst t
    exact Or.inl (calendar_archived_root rate rewards C_star C_h control0 b0 u0 t0 k hk w)
  have ht0lt : t0.val < t.val := by
    have hne : t.val ≠ t0.val := fun h => heq (Fin.ext h)
    omega
  let j := t.val - (t0.val + 1)
  have hj : j < k := by dsimp only [j]; omega
  have hjdate : t0.val + 1 + j = t.val := by dsimp only [j]; omega
  let x : Sample (j + 1) := ancestor k (j + 1) (by omega) w
  have hxt : (⟨t0.val + 1 + j, by omega⟩ : Fin p.T) = t := Fin.ext hjdate
  have hp := calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    (j + 1) (by omega)
  change (stored (j + 1) (by omega) x).2 <+: (stored k hk w).2 ∧
    sourcePrefix control0 (t0.val + 1 + (j + 1)) (current k hk w) =
      sourcePrefix control0 (t0.val + 1 + (j + 1)) (current (j + 1) (by omega) x) ∧ _ at hp
  cases hc : callFlag j (by omega) x.1 with
  | true =>
      left
      have htag : (observe (j + 1) (by omega) x).1 = t :=
        (calendarObservation_call_tag rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 hc).trans hxt
      have h := calendar_archived_lastNative rate rewards C_star C_h control0 b0 u0 t0 k hk w (j + 1) (by omega)
      dsimp only at h
      let P := fun q : Fin p.T => ∃ (z : InvocationSource rate rewards C_star C_h q)
        (a : ContinuousControlSlice.Scalar), z.val = current k hk w ∧
          nativeCell rate rewards C_star C_h control0 q z a ∈ (stored k hk w).2
      exact Eq.mp (congrArg P htag) h
  | false =>
      right
      have hs := calendarObservation_noncall_source rate rewards C_star C_h control0 b0 u0 t0 j
        (by omega) x.1 x.2 hc
      change current (j + 1) (by omega) x = current j (by omega) x.1 at hs
      have hprefix : sourcePrefix control0 (t.val + 1) (current k hk w) =
          sourcePrefix control0 (t.val + 1) (current j (by omega) x.1) := by
        have h := hp.2.1
        rw [hs] at h
        have hdate : t0.val + 1 + (j + 1) = t.val + 1 := by omega
        rw [hdate] at h
        exact h
      have hcall := callAt_congr_prefix rate rewards C_star C_h control0 t (t.val + 1)
        (Nat.le_succ _) (current k hk w) (current j (by omega) x.1) hprefix
      have hn : ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h t (current k hk w) := by
        rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none, hcall]
        apply Option.not_isSome_iff_eq_none.mp
        have hc' : (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t
            (current j (by omega) x.1)).isSome = false := by
          simpa only [calendarCallFlag, hxt] using hc
        rw [hc']
        exact Bool.false_ne_true
      have hstart := calendarCurrentSource_start_le_root rate rewards C_star C_h control0 b0 u0 t0 k hk w
      have hdom := continuingDomain_of_live_selection rate rewards C_star C_h t (current k hk w)
        (hstart.trans_lt ht0lt) hn r hr sel hsel hlive
      let z : ContinuingLiveSource rate rewards C_star C_h t := ⟨current k hk w, hdom⟩
      let a := (original j x.1).1.2
      let e := continuingLogicalCell rate rewards C_star C_h t z a
      have hcell : noncallDateCell rate rewards C_star C_h t (current j (by omega) x.1) a
          (stored j (by omega) x.1).1 = some e := by
        rw [noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (t.val + 1) (by omega)
          t (Nat.lt_succ_self _) (current j (by omega) x.1), ← hprefix,
          ← noncallDateCell_sourcePrefix rate rewards C_star C_h control0 (t.val + 1) (by omega)
            t (Nat.lt_succ_self _) (current k hk w)]
        rw [noncallDateCell, dite_eq_left hdom]
      have hpre := prefixNumerical_clear_of_inclusive_gate rate rewards C_star C_h t (current k hk w)
        (continuingBefore rate rewards C_star C_h t z)
        (continuingBefore_spec rate rewards C_star C_h t z) hscan
      have hnum : (observe j (by omega) x.1).2.val.2.2.1 = some e.before := by
        rw [calendarObservation_numerical]
        have hb : calendarBoundary t0 j (by omega) = t.castSucc := Fin.ext hjdate
        let oldSource : Source := current j (by omega) x.1
        have hn : prefixNumerical rate rewards C_star C_h t.castSucc oldSource = some e.before := by
          rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 t.castSucc
            (t.val + 1) (Nat.le_succ _) oldSource, ← hprefix,
            ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 t.castSucc
              (t.val + 1) (Nat.le_succ _) (current k hk w)]
          exact continuingBefore_spec rate rewards C_star C_h t z
        exact (congrArg (fun n => prefixNumerical rate rewards C_star C_h n oldSource) hb).trans hn
      have hclear : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1).2 = true := by
        change (observe j (by omega) x.1).2.val.2.2.1.any (fun S => !S.overflow) = true
        rw [hnum, Option.any_some, Bool.not_eq_true']
        exact hpre
      have hcell' : noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + j, by omega⟩
          (current j (by omega) x.1) a (stored j (by omega) x.1).1 = some e := by
        rw [hxt]
        exact hcell
      have hgenerated := calendarObservation_noncall_clear_cell rate rewards C_star C_h control0 b0 u0 t0
        j (by omega) x.1 x.2 hc hclear e hcell'
      have he : e ∈ (stored (j + 1) (by omega) x).2 := by
        change e ∈ (stored (j + 1) (by omega) (x.1, x.2)).2
        rw [hgenerated.2.2]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      exact ⟨z, a, rfl, hp.1.sublist.subset he⟩

/-- Actual physical selection and the inclusive first-bad calendar produce
the archived witness and signed observation identity. No matching logical
cell, seed, source history, or payoff assertion is an input. -/
theorem calendar_archived_live_empty_payoff (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (t : Fin p.T) (ht0 : t0.val ≤ t.val) (ht : t.val < t0.val + 1 + k)
    (htbad : t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h (current k hk w))
    (r : Record rate) (hr : recordAt t (current k hk w) = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hgate : liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel)) :
    ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h (current k hk w) t ∧
    ∃ e ∈ (stored k hk w).2, e.time = t ∧
      e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      physicalDiagnostic rate rewards t e.physical
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) = logicalReward rate rewards e ∧
      observation rate rewards t e.physical =
        some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  have hscan := ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
    rate rewards C_star C_h (current k hk w) t htbad
  refine ⟨hscan, ?_⟩
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
    have h := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) r.input.time rfl
    rw [hgate.1] at h
    exact of_decide_eq_true h.symm
  have finish (s : Record rate) (hs : recordAt t (current k hk w) = some s)
      (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
      (S : RecordedQueueRun.RunState p.K)
      (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
      (hS : prefixNumerical rate rewards C_star C_h t.castSucc (current k hk w) = some S)
      (hmem : appendLogicalCell s c S a ∈ (stored k hk w).2) :
      ∃ e ∈ (stored k hk w).2, e.time = t ∧
        e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
        e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
        e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
        physicalDiagnostic rate rewards t e.physical
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) = logicalReward rate rewards e ∧
        observation rate rewards t e.physical =
          some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
    have he : s = r := Option.some.inj (hs.symm.trans hr)
    subst s
    have hc : c.selected = sel := Option.some.inj (c.selection_actual.symm.trans hsel)
    have hempty : c.selected.view.pendingAtChoice = ∅ := by rw [hc]; exact hgate.2
    have hpre := prefixNumerical_clear_of_inclusive_gate rate rewards C_star C_h t (current k hk w) S hS hscan
    have h := appendLogicalCell_live_empty_payoff rate rewards C_star C_h t (current k hk w)
      r hr c S a hpre hempty
    refine ⟨appendLogicalCell r c S a, hmem, h.1, h.2.1, hpre, ?_, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
    · exact h.2.2.1.trans (congrArg (fun s => s.view.payload.slowSet) hc)
    · rw [← hc]
      exact h.2.2.2.2.1
  rcases calendar_archived_live_cell rate rewards C_star C_h control0 b0 u0 t0 k hk w
    t ht0 ht hscan r hr sel hsel hlive with ⟨z, x, hz, hmem⟩ | ⟨z, a, hz, hmem⟩
  · have hs := (nativeSourceCell_spec rate rewards C_star C_h t z).1
    have hS := nativeBefore_prefix rate rewards C_star C_h control0 t z
    rw [hz] at hs hS
    exact finish (nativeRecord rate rewards C_star C_h t z) hs (nativeSourceCell rate rewards C_star C_h t z)
      (nativeBefore rate rewards C_star C_h control0 t z)
      (Function.update ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
        ((nativeRecord rate rewards C_star C_h t z).input.time, 1) x) hS hmem
  · have hs := (continuingSourceCell_spec rate rewards C_star C_h t z).1
    have hS := continuingBefore_spec rate rewards C_star C_h t z
    rw [hz] at hs hS
    exact finish (continuingRecord rate rewards C_star C_h t z) hs
      (continuingSourceCell rate rewards C_star C_h t z)
      (continuingBefore rate rewards C_star C_h t z) a hS hmem

/-- At POST `T`, all processed LIVE-empty dates in the branch retain their
dated cells and their physical signed observations on the SAME final source.
The final horizon boundary is not an additional round or draw. -/
theorem ae_calendarLaw_terminal_live_empty_payoff :
    ∀ᵐ w ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0
      (p.T - (t0.val + 1)) (by omega),
    let k := p.T - (t0.val + 1)
    let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
    (stored k hk w).2.Pairwise (fun e f => e.time.val < f.time.val) ∧
    (∀ e ∈ (stored k hk w).2, e.time.val < p.T) ∧
    ∀ (t : Fin p.T), t0.val ≤ t.val →
      t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h (current k hk w) →
      ∀ (r : Record rate), recordAt t (current k hk w) = some r →
      ∀ (sel : ReferenceActivePhysicalStep.Selection r.input),
        r.output.preparation.coordinator.selection = some sel →
        liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) →
        ∃ e ∈ (stored k hk w).2, e.time = t ∧
          e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
          e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
          e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
          observation rate rewards t e.physical =
            some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  filter_upwards [ae_calendarLaw_archived_path rate rewards C_star C_h control0 b0 u0 t0
    (p.T - (t0.val + 1)) (by omega),
    ae_calendarLaw_terminal_path_readout rate rewards C_star C_h control0 b0 u0 t0] with w hpath hterminal
  dsimp only
  refine ⟨hpath.2.2.2.2.1, hterminal.2.1, ?_⟩
  intro t ht0 htbad r hr sel hsel hgate
  obtain ⟨_hscan, e, hmem, he, hphysical, hpre, hslow, hfast, _hdiagnostic, hobs⟩ :=
    calendar_archived_live_empty_payoff rate rewards C_star C_h control0 b0 u0 t0
      (p.T - (t0.val + 1)) (by omega) w t ht0 (by omega) htbad r hr sel hsel hgate
  exact ⟨e, hmem, he, hphysical, hpre, hslow, hfast, hobs⟩

private theorem calendarPast_prefix_extendedPast (n : ℕ) (hn : n ≤ p.T) (z : Source)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) n <+:
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h ⟨n, by omega⟩ (z, a) := by
  let u := ReferenceFirstCollectionLogicalPrefixExtension.collectionStart rate rewards C_star C_h z
  by_cases hu : n ≤ u
  · rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPast,
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
        rate rewards C_star C_h n hn z a hu]
  · have hun : u ≤ n := by omega
    have huT : u ≤ p.T := hun.trans hn
    have hcal (m : ℕ) (hum : u ≤ m) :
        ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) m =
          firstLiveChronologicalPrefix rate rewards C_star C_h (z, a) := by
      rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed]
      apply List.take_of_length_le
      rw [firstLiveChronologicalPrefix_length]
      change ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z ≤
        m - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
      dsimp only [u, ReferenceFirstCollectionLogicalPrefixExtension.collectionStart] at hum
      omega
    rw [hcal n hun]
    have hp := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_prefix
      rate rewards C_star C_h n hn u hun (z, a)
    rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
      rate rewards C_star C_h u huT z a le_rfl, hcal u le_rfl] at hp
    exact hp

private theorem calendarCurrentSource_root_firstCell (w : Sample 0) :
    current 0 (by omega) w ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u0 t0 := by
  cases b0 with
  | false =>
      exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts rate rewards C_star C_h u0 t0
        (ReferenceFirstNextInvocationJointLift.insertEvent rate rewards C_star C_h u0 t0 w.1.1 w.2).val
        (ReferenceFirstNextInvocationJointLift.insertEvent rate rewards C_star C_h u0 t0 w.1.1 w.2).property).1
  | true =>
      exact (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 w.1.1 w.2).property.1

/-- The same final source still has the original first invocation at this
branch's root. Future insertions preserve its strict call history. -/
theorem calendarCurrentSource_firstCell (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    current k hk w ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u0 t0 := by
  let root := ancestor k 0 (Nat.zero_le _) w
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    0 (Nat.zero_le _)).2.1
  have h := congrArg (sourcePrefix control0 t0.val) hp
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega),
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega)] at h
  change sourcePrefix control0 t0.val (current k hk w) =
    sourcePrefix control0 t0.val (current 0 (by omega) root) at h
  rw [ReferenceFirstCollectionCurrentRecordedCell.firstCell_prefix_iff rate rewards C_star C_h control0 u0 t0,
    h, ← ReferenceFirstCollectionCurrentRecordedCell.firstCell_prefix_iff rate rewards C_star C_h control0 u0 t0]
  exact calendarCurrentSource_root_firstCell rate rewards C_star C_h control0 b0 u0 t0 root

include control0 in
private theorem calendarPast_insert (t : Fin p.T) (z : Source)
    (v : AssignmentParameterFibreKernel.AssignmentVector p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (ReferenceFirstCollectionRenewalVectorInsertion.insert t z v, a) t.val =
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) t.val := by
  have hprefix : sourcePrefix control0 t.val (ReferenceFirstCollectionRenewalVectorInsertion.insert t z v) =
      sourcePrefix control0 t.val z :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 t t.val le_rfl _ _
  rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix rate rewards C_star C_h
    control0 t.val t.isLt.le, hprefix,
    ← ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix rate rewards C_star C_h
      control0 t.val t.isLt.le]

private theorem calendar_root_past_prefix (w : Sample 0) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      (current 0 (by omega) w, (original 0 w).1.2) t0.val <+: (stored 0 (by omega) w).2 := by
  cases b0 with
  | false =>
      change (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u0 t0 ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) × AssignmentParameterFibreKernel.AssignmentVector p at w
      have hinit := (calendarObservation_native_prefix rate rewards C_star C_h control0 false u0 t0 0 (by omega) w).1
      have hp := calendarPast_prefix_extendedPast rate rewards C_star C_h t0.val t0.isLt.le w.1.1.val w.1.2
      have hprelist : calendarNativePrelist rate rewards C_star C_h control0 false u0 t0 0 (by omega) w =
          ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h t0.castSucc (w.1.1.val, w.1.2) := by
        unfold calendarNativePrelist
        rw [calendarObservation_initial rate rewards C_star C_h control0 false u0 t0 (by omega) w]
        change (ReferenceFirstNextInstallationTransitionLaw.postHistory
          (ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition rate rewards C_star C_h control0 u0 t0 w)).dropLast = _
        rw [ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition_postHistory, List.dropLast_concat]
      rw [hprelist] at hinit
      change ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (ReferenceFirstCollectionRenewalVectorInsertion.insert t0 w.1.1.val w.2, w.1.2) t0.val <+: _
      rw [calendarPast_insert rate rewards C_star C_h control0]
      exact hp.trans ((List.prefix_append _ _).trans hinit)
  | true =>
      change ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u0 t0 at w
      have hinit := (calendarObservation_native_prefix rate rewards C_star C_h control0 true u0 t0 0 (by omega) w).1
      have hp := calendarPast_prefix_extendedPast rate rewards C_star C_h t0.val t0.isLt.le w.1.1.val w.1.2
      have hprelist : calendarNativePrelist rate rewards C_star C_h control0 true u0 t0 0 (by omega) w =
          ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h t0.castSucc (w.1.1.val, w.1.2) := by
        unfold calendarNativePrelist
        rw [calendarObservation_initial rate rewards C_star C_h control0 true u0 t0 (by omega) w]
        change (ReferenceFirstNextInstallationTransitionLaw.postHistory
          (ReferenceFirstNextInstallationTransitionLaw.renewedTransition rate rewards C_star C_h control0 u0 t0 w)).dropLast = _
        rw [ReferenceFirstNextInstallationTransitionLaw.renewedTransition_postHistory, List.dropLast_concat]
      rw [hprelist] at hinit
      change ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        ((ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u0 t0 w.1.1 w.2).val, w.1.2) t0.val <+: _
      rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val,
        calendarPast_insert rate rewards C_star C_h control0]
      exact hp.trans ((List.prefix_append _ _).trans hinit)

/-- The root's earlier first-LIVE cells also survive on the final current
source, with the SAME original auxiliary array. -/
theorem calendar_archived_root_past (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      (current k hk w, (original k w).1.2) t0.val <+: (stored k hk w).2 := by
  let root := ancestor k 0 (Nat.zero_le _) w
  have hp := calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w
    0 (Nat.zero_le _)
  have h := congrArg (sourcePrefix control0 t0.val) hp.2.1
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega),
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 _ _ (by omega)] at h
  change sourcePrefix control0 t0.val (current k hk w) =
    sourcePrefix control0 t0.val (current 0 (by omega) root) at h
  rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix rate rewards C_star C_h
    control0 t0.val t0.isLt.le, h,
    ← ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix rate rewards C_star C_h
      control0 t0.val t0.isLt.le,
    ← calendarAncestor_original rate rewards C_star C_h b0 u0 t0 k 0 (Nat.zero_le _) w]
  exact (calendar_root_past_prefix rate rewards C_star C_h control0 b0 u0 t0 root).trans hp.1

/-- Before the root invocation, an actual LIVE selection lies in the first
LIVE window. Collection dates are excluded by their actual dispatcher frame,
not by assuming coverage or by relabelling a pilot as FAST. -/
theorem calendar_archived_live_cell_before_root (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) (t : Fin p.T) (ht : t.val < t0.val)
    (r : Record rate) (hr : recordAt t (current k hk w) = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time) :
    ∃ (s : Record rate) (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
      (S : RecordedQueueRun.RunState p.K) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p),
      recordAt t (current k hk w) = some s ∧
      prefixNumerical rate rewards C_star C_h t.castSucc (current k hk w) = some S ∧
      appendLogicalCell s c S a ∈ (stored k hk w).2 := by
  let z := current k hk w
  have hfirst := calendarCurrentSource_firstCell rate rewards C_star C_h control0 b0 u0 t0 k hk w
  have hbound := ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u0 t0 z hfirst
  obtain ⟨_j, _hj, _hjr, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h t z r hr
  have hbefore : t.val < ReferenceFirstCollectionLogicalPrefixExtension.collectionStart rate rewards C_star C_h z := by
    by_contra h
    have hdom := ReferenceFirstCollectionLogicalPrefixExtension.actualDomain_of_collection_interval
      rate rewards C_star C_h t z (Nat.le_of_not_gt h) (by rw [hbound]; exact ht)
    obtain ⟨s, hs, hm⟩ := hdom
    have he : s = r := Option.some.inj (hs.symm.trans hr)
    subst s
    obtain ⟨call, _ht, _hread, hc, _rest⟩ := ReferenceFirstCollectionOneRoundLogicalCell.actual_data
      rewards C_star C_h z t r hr hm
    have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r).isSome = true := by rw [hc]; rfl
    exact not_live_of_collection_call rate r sel hsel hsome hlive
  let W := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z
  let i : Fin W.length := ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, by
    dsimp only [ReferenceFirstCollectionLogicalPrefixExtension.collectionStart,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] at hbefore
    dsimp only [W]
    omega⟩
  have hp : W <+: ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
    List.takeWhile_prefix _
  have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[i.val]? = some r := by
    have hi : i.val = _j.val := by dsimp only [i]; omega
    rw [hi, List.getElem?_eq_getElem _j.isLt, _hjr]
  obtain ⟨hiR, hRi⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hwr : W[i.val] = r := (hp.getElem i.isLt).trans hRi
  let a := (original k w).1.2
  let c := wholeLiveCell rate rewards C_star C_h z W[i.val] (List.getElem_mem i.isLt)
  let S := RecordedQueueRun.run Q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take i.val)
  have he := firstLiveChronologicalPrefix_get rate rewards C_star C_h z a i
  have hmem : appendLogicalCell W[i.val] c S a ∈ (stored k hk w).2 := by
    apply (calendar_archived_root_past rate rewards C_star C_h control0 b0 u0 t0 k hk w).sublist.subset
    rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed]
    change appendLogicalCell W[i.val] c S a ∈ (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)).take
      (t0.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val, lt_min ?_ ?_, he⟩
    · dsimp only [i]; omega
    · rw [firstLiveChronologicalPrefix_length]; exact i.isLt
  have hlaunch := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u0 t0 z hfirst
  have hword := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_liveWord rate rewards C_star C_h u0 t0 z hfirst
  have hdates := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates rate rewards C_star C_h u0 t0 z hfirst
  have hiu : i.val ≤ u0.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    rw [hdates.2.2.1] at hbefore
    dsimp only [i]
    omega
  have hS : prefixNumerical rate rewards C_star C_h t.castSucc z = some S := by
    rw [prefixNumerical_actualWord rate rewards C_star C_h t.castSucc z hlaunch hstart]
    dsimp only [S]
    rw [hword, List.take_take, Nat.min_eq_left hiu]
    rfl
  refine ⟨W[i.val], c, S, a, ?_, hS, hmem⟩
  exact hr.trans (congrArg some hwr.symm)

/-- All applicable processed LIVE-empty dates, including the root PRE list,
have their actual signed payoff on the SAME final source through first bad.
The only local hypotheses select actual physical branches and calendar dates. -/
theorem calendar_all_live_empty_payoff (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (t : Fin p.T) (ht : t.val < t0.val + 1 + k)
    (htbad : t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h (current k hk w))
    (r : Record rate) (hr : recordAt t (current k hk w) = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hgate : liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel)) :
    ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
      rate rewards C_star C_h (current k hk w) t ∧
    ∃ e ∈ (stored k hk w).2, e.time = t ∧
      e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      physicalDiagnostic rate rewards t e.physical
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) = logicalReward rate rewards e ∧
      observation rate rewards t e.physical =
        some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) := by
  by_cases ht0 : t0.val ≤ t.val
  · exact calendar_archived_live_empty_payoff rate rewards C_star C_h control0 b0 u0 t0 k hk w
      t ht0 ht htbad r hr sel hsel hgate
  have hscan := ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
    rate rewards C_star C_h (current k hk w) t htbad
  refine ⟨hscan, ?_⟩
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
    have h := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) r.input.time rfl
    rw [hgate.1] at h
    exact of_decide_eq_true h.symm
  obtain ⟨s, c, S, a, hs, hS, hmem⟩ := calendar_archived_live_cell_before_root rate rewards C_star C_h control0 b0 u0 t0
    k hk w t (Nat.lt_of_not_ge ht0) r hr sel hsel hlive
  have he : s = r := Option.some.inj (hs.symm.trans hr)
  subst s
  have hc : c.selected = sel := Option.some.inj (c.selection_actual.symm.trans hsel)
  have hempty : c.selected.view.pendingAtChoice = ∅ := by rw [hc]; exact hgate.2
  have hpre := prefixNumerical_clear_of_inclusive_gate rate rewards C_star C_h t (current k hk w) S hS hscan
  have h := appendLogicalCell_live_empty_payoff rate rewards C_star C_h t (current k hk w) r hr c S a hpre hempty
  refine ⟨appendLogicalCell r c S a, hmem, h.1, h.2.1, hpre, ?_, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
  · exact h.2.2.1.trans (congrArg (fun s => s.view.payload.slowSet) hc)
  · rw [← hc]
    exact h.2.2.2.2.1

/-- Final POST-`T` readout on the actual unnormalized produced law. Every
applicable physical LIVE-empty record retrieves its dated archived logical
cell, including the root PRE list, and the SAME complete physical calendar
contains its signed auxiliary-minus-own-total observation. The first-bad
calendar is the literal complete-source detector; no later auxiliary tail or
expectation bound is asserted here. -/
theorem ae_calendarLaw_terminal_all_live_empty_payoff :
    ∀ᵐ w ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0
      (p.T - (t0.val + 1)) (by omega),
    let k := p.T - (t0.val + 1)
    let hk : t0.val + 1 + k ≤ p.T := by dsimp only [k]; omega
    SignedStoppedRegretAccounting.firstBadCalendar
      (ReferenceCompleteSignedFirstBadCalendar.badRounds rate rewards C_star C_h (current k hk w))
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h (current k hk w)) ∧
    (stored k hk w).2.Pairwise (fun e f => e.time.val < f.time.val) ∧
    (∀ e ∈ (stored k hk w).2, e.time.val < p.T) ∧
    ∀ (t : Fin p.T),
      t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h (current k hk w) →
      ∀ (r : Record rate), recordAt t (current k hk w) = some r →
      ∀ (sel : ReferenceActivePhysicalStep.Selection r.input),
        r.output.preparation.coordinator.selection = some sel →
        liveEmptyGate (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) →
        ∃ e ∈ (stored k hk w).2, e.time = t ∧
          e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
          e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
          e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
          physicalDiagnostic rate rewards t e.physical
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) = logicalReward rate rewards e ∧
          observation rate rewards t e.physical =
            some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward) ∧
          (t, some (logicalReward rate rewards e, r.totalReward, logicalReward rate rewards e - r.totalReward)) ∈
            calendar rate rewards C_star C_h (current k hk w) := by
  filter_upwards [ae_calendarLaw_archived_path rate rewards C_star C_h control0 b0 u0 t0
    (p.T - (t0.val + 1)) (by omega),
    ae_calendarLaw_terminal_path_readout rate rewards C_star C_h control0 b0 u0 t0] with w hpath hterminal
  dsimp only
  refine ⟨ReferenceCompleteSignedFirstBadCalendar.firstBadDate_firstBadCalendar rate rewards C_star C_h _,
    hpath.2.2.2.2.1, hterminal.2.1, ?_⟩
  intro t htbad r hr sel hsel hgate
  obtain ⟨_hscan, e, hmem, he, hphysical, hpre, hslow, hfast, hdiagnostic, hobs⟩ :=
    calendar_all_live_empty_payoff rate rewards C_star C_h control0 b0 u0 t0
      (p.T - (t0.val + 1)) (by omega) w t (by omega) htbad r hr sel hsel hgate
  have hcalendar := actualRecord_calendar_value rate rewards C_star C_h
    (current (p.T - (t0.val + 1)) (by omega) w) t r hr
  rw [← hphysical, hobs] at hcalendar
  exact ⟨e, hmem, he, hphysical, hpre, hslow, hfast, hdiagnostic, hobs, hcalendar⟩

end Bandits.Support.ReferenceGeneratedCalendarLivePayoff

end
