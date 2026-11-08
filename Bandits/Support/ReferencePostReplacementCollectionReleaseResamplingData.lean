/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
public import Bandits.Support.ReferencePostReplacementCollectionReleaseProjection

import Mathlib.Tactic

/-!
# Stopped post-rawK release resampling geometry and DATA sections

The whole current selected-row control is integrated while the original strict
source prefix, release-date mask, and incoming pending mask are kept fixed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData

variable {p : ConstructorDimensions.Parameters}

private theorem completeRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hcal : k.val < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).length := by
    rw [← htimes, List.length_map]
    exact k.isLt
  have hget :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).map (fun r => r.input.time.val))[k.val]'(by
          rw [List.length_map]; exact k.isLt) =
        (ReferenceActivePhysicalHorizon.calendar
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))[k.val]'hcal := by
    simp only [htimes]
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using hget

private theorem actualRecord_eq_completeRecord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time) z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] := by
  have ht := completeRecord_time rate rewards C_star C_h z k
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]).input.time.val := by omega
  rw [ite_eq_left hs, ht, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem k.isLt]

private theorem rawReleaseRecord_mem_completeSuffixRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z) :
    r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
    rate rewards C_star C_h z
  by_cases hK : K = []
  · unfold ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords at hr
    rw [ite_eq_left hK] at hr
    simp at hr
  · by_cases hb : c + K.length < R.length
    · have hdrop : r ∈
          (R[c + K.length] ::
            ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (c + K.length + 1)) := by
        have hr' := hr
        rw [ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords,
          ite_eq_right hK, dite_eq_left hb] at hr'
        exact (List.dropWhile_sublist _).subset hr'
      rcases List.mem_cons.mp hdrop with hhead | htail
      · rw [hhead]
        exact List.getElem_mem _
      · have htail' : r ∈ R.drop (c + K.length + 1) := by
          change r ∈ ((R.drop (c + K.length + 1)).takeWhile
            ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest) at htail
          exact (List.takeWhile_sublist _).subset htail
        exact (List.drop_sublist _ _).subset htail'
    · unfold ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords at hr
      rw [ite_eq_right hK, dite_eq_right hb] at hr
      simp at hr

private theorem sourcePrefix_replace_current_before
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (t : Fin p.T)
    (hn : n ≤ t.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < n
      · have hne : v ≠ t := by
          intro heq
          subst v
          omega
        simp only [hv, ite_true, Function.update_of_ne hne]
      · simp only [hv, ite_false]
    · have hq' : q ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := hq
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_of_ne hq']
  · rfl

private theorem sourcePrefix_replace_current
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z :=
  sourcePrefix_replace_current_before control0 t.val t le_rfl z control

private theorem preRound_event_factor
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hA : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)] A) :
    ∃ B : Set (BootstrapPrivateRoundStreams.SourceInput p),
      MeasurableSet B ∧
        A = (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val) ⁻¹' B := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hA
  obtain ⟨B, hB, hfactor⟩ := MeasurableSpace.measurableSet_comap.mp hA
  exact ⟨B, hB, hfactor.symm⟩

/-- The fixed post-rawK occurrence is unchanged by a later current-control
replacement: its phase scan is measurable at the strictly earlier prefix. -/
theorem postRawKOccurrence_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (hut : u.val < t.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
        rate rewards C_star C_h u
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
        rate rewards C_star C_h u z := by
  let A : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {x | ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
      rate rewards C_star C_h u x}
  have hA : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (u.val + 2)] A := by
    simpa only [A, Set.ofPred_mem_eq] using
      ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_measurable
        rate rewards C_star C_h control0 u
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hA
  obtain ⟨B, hB, hfactor⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have hprefix := sourcePrefix_replace_current_before control0 (u.val + 1) t
    (by omega) z control
  apply propext
  change (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control ∈ A) ↔
    z ∈ A
  rw [← hfactor]
  simp only [Set.mem_preimage, hprefix]

/-- The exact incoming encoded state at the active physical time is the same
for every replacement of that time's whole selected-row control. -/
theorem incomingStateCode_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := by
  calc
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) :=
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t _
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
      rw [sourcePrefix_replace_current]
    _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z :=
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
        control0 t z).symm

/-- The literal retained payload read from the incoming state code is aligned
before the fresh current control is applied. The option is preserved so
absent and dagger states remain absent instead of gaining a fabricated
payload. -/
def incomingStoredPayload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (Option
      (ReferenceActivePhysicalStep.Payload (p := p) (rate := rate))) :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
    (ReferenceRetainedReleasePhaseObservation.localStoredPayload (rate := rate))

/-- The payload observation is measurable at the accepted pre-choice source
field because it is a literal option-map of the incoming lossless state code. -/
theorem incomingStoredPayload_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)]
      (incomingStoredPayload rate rewards C_star C_h t) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1)
  unfold incomingStoredPayload
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate ×
      BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceRetainedReleasePhaseObservation.localStoredPayload
          (rate := rate) v.1)
    ((ReferenceReleaseStrictPastFactor.measurable_localStoredPayload rate).comp
      measurable_fst)
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t)
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)

/-- The actual whole incoming payload readout is unchanged under arbitrary
replacement of only the whole selected-row current control. -/
theorem incomingStoredPayload_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    incomingStoredPayload rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      incomingStoredPayload rate rewards C_star C_h t z := by
  unfold incomingStoredPayload
  exact congrArg
    (Option.map
      (ReferenceRetainedReleasePhaseObservation.localStoredPayload (rate := rate)))
    (incomingStateCode_replace_current rate rewards C_star C_h control0 t z control)

/-- Every actual stopped release date reads the same whole payload supplied
by the accepted post-rawK source record theorem. The proof identifies the
literal actual calendar record; it does not construct a replacement payload. -/
theorem incomingStoredPayload_eq_stoppedPayload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z) :
    ∃ M : ReferenceActivePhysicalStep.Payload (p := p) (rate := rate),
      incomingStoredPayload rate rewards C_star C_h t z = some (some M) := by
  obtain ⟨r, hrRaw, htime⟩ :=
    (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z t).2 hkeep.1
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro hempty
    rw [hempty] at hrRaw
    simp at hrRaw
  obtain ⟨_hc, _a, _cutoff, M, _hlo, _hhi, _hstamp, _hrecords, hread⟩ :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords_source
      rate rewards C_star C_h control0 z hrel
  have hrKeep :
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h r.input.time z := by
    rw [htime]
    exact hkeep
  have hrStopped : r ∈
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords
        rate rewards C_star C_h z := by
    unfold ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords
    rw [List.mem_filter]
    exact ⟨hrRaw, by simp [hrKeep]⟩
  have hrComplete := rawReleaseRecord_mem_completeSuffixRecords
    rate rewards C_star C_h z r hrRaw
  obtain ⟨n, hn, hrecord⟩ := List.mem_iff_getElem.mp hrComplete
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := ⟨n, hn⟩
  have htimeRecord :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[n]).input.time = t := by
    rw [hrecord]
    exact htime
  have hactualRecord :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some r := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[n].input.time) z := by
            rw [← htimeRecord]
      _ = some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[n] :=
        actualRecord_eq_completeRecord rate rewards C_star C_h z k
      _ = some r := by rw [hrecord]
  refine ⟨M, ?_⟩
  unfold incomingStoredPayload ReferenceSourcePrefixHistoryFiltration.incoming
  rw [hactualRecord]
  simp only [Option.map_some]
  rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
    ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  exact congrArg some (hread r hrStopped).1

/-- The assigned-arm chi coefficient on a stopped pending coordinate is read
from the actual incoming payload and the literal reward row. Outside that
observation mask it is explicitly zero. -/
def stoppedAssignedChi
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z then
    match incomingStoredPayload rate rewards C_star C_h t z with
    | some (some M) =>
        ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (M.assignment.assigned i)
    | _ => 0
  else 0

/-- On the literal stopped pending mask, the assigned chi coefficient is the
actual payload's assigned-arm reward indicator. -/
theorem stoppedAssignedChi_eq_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : i ∈
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
        rate rewards C_star C_h t z) :
    ∃ M : ReferenceActivePhysicalStep.Payload (p := p) (rate := rate),
      incomingStoredPayload rate rewards C_star C_h t z = some (some M) ∧
      stoppedAssignedChi rate rewards C_star C_h t i z =
        ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (M.assignment.assigned i) := by
  have hdate :=
    (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_iff
      rate rewards C_star C_h t z i).mp hpending |>.1
  obtain ⟨M, hpayload⟩ := incomingStoredPayload_eq_stoppedPayload
    rate rewards C_star C_h control0 t z hdate
  refine ⟨M, hpayload, ?_⟩
  simp [stoppedAssignedChi, hpending, hpayload]

/-- The zero-extended assigned chi observation is bounded and nonnegative on
every source, including the explicit off-support branch. -/
theorem stoppedAssignedChi_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ stoppedAssignedChi rate rewards C_star C_h t i z ∧
      stoppedAssignedChi rate rewards C_star C_h t i z ≤ 1 := by
  classical
  have hchi (a : Fin p.K) :
      0 ≤ ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) a ∧
        ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) a ≤ 1 := by
    unfold ReleaseRoundKernel.chi
    split_ifs <;> norm_num
  unfold stoppedAssignedChi
  by_cases hpending : i ∈
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
        rate rewards C_star C_h t z
  · simp only [hpending]
    cases hpayload : incomingStoredPayload rate rewards C_star C_h t z with
    | none => simp
    | some inner =>
        cases inner with
        | none => simp
        | some M => simpa [hpayload] using hchi (M.assignment.assigned i)
  · simp [hpending]

/-- Entry and incoming pending readouts at a fixed earlier assignment time
are unchanged before the fresh current control is integrated. -/
theorem entryPendingReadouts_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (a : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t z ∧
    ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t z := by
  have hprefix := sourcePrefix_replace_current control0 t z control
  constructor
  · calc
      _ = ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) :=
        ReferenceSourcePrefixHistoryFiltration.entry_factor rate rewards C_star C_h
          control0 a t _
      _ = ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
        rw [hprefix]
      _ = ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t z :=
        (ReferenceSourcePrefixHistoryFiltration.entry_factor rate rewards C_star C_h
          control0 a t z).symm
  · calc
      _ = ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) :=
        ReferenceSourcePrefixHistoryFiltration.pending_factor rate rewards C_star C_h
          control0 a t _
      _ = ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
        rw [hprefix]
      _ = ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t z :=
        (ReferenceSourcePrefixHistoryFiltration.pending_factor rate rewards C_star C_h
          control0 a t z).symm

/-- The same unique strict-past rawK assignment occurrence and its true gate
entry are retained by every resampled current control. -/
private theorem stopped_date_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t z := by
  let A : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {x | ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t x}
  have hA : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)] A := by
    simpa only [A, Set.ofPred_mem_eq] using
      Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate_measurable_preRound
        rate rewards C_star C_h control0 t
  obtain ⟨B, hB, hfactor⟩ := preRound_event_factor control0 t A hA
  have hprefix := sourcePrefix_replace_current control0 t z control
  apply propext
  change (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control ∈ A) ↔
    z ∈ A
  rw [hfactor]
  simp only [Set.mem_preimage, hprefix]

theorem postRawKStoppedDate_same_occurrence_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z)
    (control : ContinuousLearningRows.TimeControl p) :
    ∃! u : Fin p.T,
      u.val < t.val ∧
        ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
          rate rewards C_star C_h u
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) ∧
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          u.val t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)).map
          Prod.fst = some true := by
  have hkeep' : Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
    rw [stopped_date_replace_current rate rewards C_star C_h control0 t z control]
    exact hkeep
  obtain ⟨u, hu, _huunique⟩ :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate_unique_occurrence
      rate rewards C_star C_h t z hkeep
  have hoccEq := postRawKOccurrence_replace_current rate rewards C_star C_h control0 u t
    hu.1 z control
  have hocc : ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
      rate rewards C_star C_h u
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
    rw [hoccEq]
    exact hu.2.1
  have hread := entryPendingReadouts_replace_current rate rewards C_star C_h control0
    u.val t z control
  have hgate :
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h u.val t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)).map
          Prod.fst = some true := by
    rw [hread.1]
    exact hu.2.2
  obtain ⟨v, hv, hvunique⟩ :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate_unique_occurrence
      rate rewards C_star C_h t _ hkeep'
  have huv : u = v := hvunique u ⟨hu.1, hocc, hgate⟩
  refine ⟨u, ⟨hu.1, hocc, hgate⟩, ?_⟩
  intro w hw
  exact (hvunique w hw).trans huv.symm

/-- A stopped pending ID keeps its actual membership on the same unique
strict-past occurrence after current-control resampling. -/
theorem postRawKStoppedPendingDate_same_occurrence_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z)
    (hpending : Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingDate
      rate rewards C_star C_h t i z)
    (control : ContinuousLearningRows.TimeControl p) :
    ∃ u : Fin p.T,
      u.val < t.val ∧
        ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
          rate rewards C_star C_h u
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) ∧
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          u.val t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)).map
          Prod.fst = some true ∧
        i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
          u.val t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  obtain ⟨u, hut, hu, hentry, hi⟩ :=
    Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingDate_same_occurrence
      rate rewards C_star C_h t i z hkeep hpending
  have hoccEq := postRawKOccurrence_replace_current rate rewards C_star C_h control0 u t hut z control
  have hocc : ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
      rate rewards C_star C_h u
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
    rw [hoccEq]
    exact hu
  have hread := entryPendingReadouts_replace_current rate rewards C_star C_h control0
    u.val t z control
  have hentry' :
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h u.val t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)).map
          Prod.fst = some true := by
    rw [hread.1]
    exact hentry
  have hipending' :
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h u.val t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
    rw [hread.2]
    exact hi
  exact ⟨u, hut, hocc, hentry', hipending'⟩

/-- The actual stopped post-rawK release-date mask is invariant under
replacing only the whole current selected-row control. The proof factors the
accepted strict-past measurable event through the original source prefix. -/
theorem postRawKStoppedDate_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t z :=
  stopped_date_replace_current rate rewards C_star C_h control0 t z control

/-- Each incoming pending-coordinate mask is invariant under the same whole
current-control replacement, using its own accepted pre-round readout. -/
theorem postRawKStoppedPendingDate_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingDate
        rate rewards C_star C_h t i
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingDate
        rate rewards C_star C_h t i z := by
  let A : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {x | ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingDate
      rate rewards C_star C_h t i x}
  have hA : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)] A := by
    simpa only [A, Set.ofPred_mem_eq] using
      Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPending_measurable_preRound
        rate rewards C_star C_h control0 t i
  obtain ⟨B, hB, hfactor⟩ := preRound_event_factor control0 t A hA
  have hprefix := sourcePrefix_replace_current control0 t z control
  apply propext
  change (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control ∈ A) ↔
    z ∈ A
  rw [hfactor]
  simp only [Set.mem_preimage, hprefix]

/-- The literal finite pending set on the stopped support is preserved by
resampling the whole current selected-row control. -/
theorem postRawKStoppedPendingSet_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
        rate rewards C_star C_h t z := by
  classical
  unfold ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
  rw [postRawKStoppedDate_replace_current rate rewards C_star C_h control0 t z control]
  by_cases hkeep : Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z
  · simp only [hkeep, ↓reduceIte]
    apply Finset.filter_congr
    intro i hi
    exact Iff.of_eq (postRawKStoppedPendingDate_replace_current rate rewards C_star C_h
      control0 t i z control)
  · simp [hkeep]

/-- On one original-source null set, each actual stopped-pending follower's
physical UP and DATA flags have the accepted whole-control conditional
sections at the source-prefix pre-choice field. These are the literal flag
indicators; no supplied coefficient or history law is used. -/
theorem stoppedPending_actualFlagConditionalSections
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p),
      ∀ (i : Fin (p.m - 1)) (t : Fin p.T),
        i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
            rate rewards C_star C_h i t source = true then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (t.val + 1)] z =
            ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
              rate rewards C_star C_h control0 i t z ∧
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source = true then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (t.val + 1)] z =
            ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
              rate rewards C_star C_h control0 i t z := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro t
  have hdata := ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
    rate rewards C_star C_h control0 i t
  have hup := ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
    rate rewards C_star C_h control0 i t
  filter_upwards [hdata, hup] with z hdata hup
  intro _hpending
  exact ⟨hdata, hup⟩

/-- The accepted all-source release projection specialized to a literal rawK
release record. The live registers and whole selected payload are retained,
including every pending or released follower and the signed physical cost. -/
theorem rawReleaseRecord_actualGeometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z) :
    ∃ (selected : ReferenceActivePhysicalStep.Selection r.input)
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      r.input.state.coordinator = .live registers owned base ∧
      registers.payload = selected.view.payload ∧
      registers.pendingAtChoice = ∅ ∧
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = ∅ ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff r.input.time ∧
      (∀ i, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary (states i) (memories i)) ∧
      (∀ i, (states i).status ≠ .unoccupied ∧
        (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
      let input := ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
      input.fast = selected.arm ∧
      (∀ i : ActiveRoundActions.Follower p.m,
        (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status = .pending →
        (ReferencePhysicalReleaseQuota.upFlag selected.view.payload r
            (ReferenceFirstLiveReleaseGeometry.followerToFin i) = true ↔
          input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
          input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
            selected.view.payload.assignment.auxiliary ∧
          input.fast ≠ selected.view.payload.assignment.auxiliary ∧
          0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time).val
            selected.view.payload.assignment.auxiliary)) ∧
      (∀ i : ActiveRoundActions.Follower p.m,
        (states (ReferenceFirstLiveReleaseGeometry.followerToFin i)).status = .pending →
        (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload r
            (ReferenceFirstLiveReleaseGeometry.followerToFin i) = true ↔
          input.slot = PublicDiscreteDraws.dataSlot ∧
          input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
            selected.view.payload.assignment.assigned i ∧
          0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time).val
            (selected.view.payload.assignment.assigned i))) ∧
      ReleaseRoundKernel.slowReward
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time)
          selected.view.payload.slowSet +
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time).val
          selected.arm - (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time)
            (selected.view.payload.assignment.assigned i)) +
        (if selected.arm = selected.view.payload.assignment.auxiliary ∧
            (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time).val
            selected.view.payload.assignment.auxiliary else 0) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
    rate rewards C_star C_h z
  change r ∈ (if K = [] then [] else
    if hb : c + K.length < R.length then
      (R[c + K.length] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (c + K.length + 1)).dropWhile
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice else []) at hr
  by_cases hK : K = []
  · simp only [hK, ↓reduceIte, List.not_mem_nil] at hr
  by_cases hb : c + K.length < R.length
  · let b : Fin R.length := ⟨c + K.length, hb⟩
    have hocc : ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
        rate rewards C_star C_h R[b.val].input.time z :=
      (ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_iff_endpoint
        rate rewards C_star C_h z _).2
        ⟨hK, hb, by simpa only [b] using completeRecord_time rate rewards C_star C_h z b⟩
    obtain ⟨_payload, _onset, birth, _hphase, hbirth, hchosen⟩ :=
      (ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_iff_actualLaterChosen
        rate rewards C_star C_h _ z).1 hocc
    have hbirthEq : birth = R[b.val] := Option.some.inj
      (hbirth.symm.trans (actualRecord_eq_completeRecord rate rewards C_star C_h z b))
    subst birth
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let Rel := (R[b.val] :: W).dropWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    have hrRel : r ∈ Rel := by
      simpa only [ite_eq_right hK, dite_eq_left hb] using hr
    obtain ⟨n, hn, hnr⟩ := List.mem_iff_getElem.mp hrRel
    have hprojection :=
      (ReferencePostReplacementCollectionReleaseProjection.raw_collection_release_suffix_projection_and_signed_cost
        rate rewards C_star C_h z).2 b rfl
    rw [ite_eq_left hchosen] at hprojection
    obtain ⟨j, hj, hrel, k, _hk, selected, states, memories, input,
      hrecord, hselection, hempty, hlive, _hvalid, hchoices, hstatus,
      _hcarry, _hcarryNext, hinput, hfast, _hnot, _hactions, _hobservations,
      _hrelease, hup, hdata, hcost⟩ := hprojection n hn
    subst input
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hchosen] at hhistory
    obtain ⟨_rb, _qb, beta, _birthSelected, _hnext, _hbirth, _hlater,
      _hbSelection, _hbPayload, _hbPending, _hrbPending, _hbNoEvent,
      _hbFollowers, _hcontinued, _hnoRelease, hframes⟩ := hhistory
    obtain ⟨registers, owned, selectedFrame, _next, _nextOwned, _states, _memories,
      hstate, hregisterPayload, hframeSelection, hframePayload, hframePending,
      _houtput, _hnextPayload, _hnextPending, _hordinary, _hoccupied,
      _hcleared, _hfollowing⟩ := hframes ⟨j, hj⟩
    have hframe : ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (selectedFrame : ReferenceActivePhysicalStep.Selection R[k.val].input),
        R[k.val].input.state.coordinator = .live registers owned beta ∧
        registers.payload = selectedFrame.view.payload ∧
        R[k.val].output.preparation.coordinator.selection = some selectedFrame ∧
        selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
      have hwitness : ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (selectedFrame : ReferenceActivePhysicalStep.Selection W[j].input),
          W[j].input.state.coordinator = .live registers owned beta ∧
          registers.payload = selectedFrame.view.payload ∧
          W[j].output.preparation.coordinator.selection = some selectedFrame ∧
          selectedFrame.view.pendingAtChoice = registers.pendingAtChoice :=
        ⟨registers, owned, selectedFrame, hstate,
          hregisterPayload.trans hframePayload.symm, hframeSelection, hframePending⟩
      exact hrecord ▸ hwitness
    obtain ⟨registers, owned, selectedFrame, hstate, hpayload, hframeSelection,
      hframePending⟩ := hframe
    have hselectedEq : selectedFrame = selected :=
      Option.some.inj (hframeSelection.symm.trans hselection)
    subst selectedFrame
    have hrEq : R[k.val] = r := hrecord.symm.trans (hrel.symm.trans hnr)
    rw [← hrEq]
    exact ⟨selected, registers, owned, beta, states, memories, hstate,
      hpayload, hframePending.symm.trans hempty, hselection, hempty, hlive,
      hchoices, hstatus, hfast, hup, hdata, hcost⟩
  · simp only [ite_eq_right hK, dite_eq_right hb, List.not_mem_nil] at hr

private theorem actualRecord_input_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- Identify the actual stopped record and its incoming payload and pending
readouts, without any selected-control or successful-service premise. -/
theorem stoppedDate_record_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      r ∈ ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
        rate rewards C_star C_h z ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧ r.input.time = t ∧
      ∀ M : ReferenceActivePhysicalStep.Payload (p := p) (rate := rate),
        incomingStoredPayload rate rewards C_star C_h t z = some (some M) →
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t z = ReferencePhysicalReleaseQuota.pendingSet M r := by
  obtain ⟨r, hr, ht⟩ :=
    (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z t).2 hkeep.1
  obtain ⟨n, hn, hnr⟩ := List.mem_iff_getElem.mp
    (rawReleaseRecord_mem_completeSuffixRecords rate rewards C_star C_h z r hr)
  have ha : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    have hh := actualRecord_eq_completeRecord rate rewards C_star C_h z ⟨n, hn⟩
    simpa only [hnr, ht] using hh
  refine ⟨r, hr, ha, ht, ?_⟩
  intro M hM
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      r.input.state.coordinator = some M := by
    simpa only [incomingStoredPayload, ReferenceSourcePrefixHistoryFiltration.incoming,
      ha, Option.map_some, ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState,
      Option.some.injEq] using hM
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro he
    simp only [he, List.not_mem_nil] at hr
  obtain ⟨_hc, _a, _cutoff, M', _hlo, _hhi, _hstamp, _hrecords, hread⟩ :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords_source
      rate rewards C_star C_h control0 z hrel
  have hrStopped : r ∈
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords
        rate rewards C_star C_h z := by
    simp only [ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedRecords,
      List.mem_filter, hr, true_and]
    exact decide_eq_true (ht ▸ hkeep)
  obtain ⟨hM', hP⟩ := hread r hrStopped
  have heq : M' = M := Option.some.inj (hM'.symm.trans hstored)
  exact ⟨hstored, by simpa only [heq, ht] using hP⟩

/-- DATA geometry on every resampled whole current control uses the same
incoming whole payload and literal pending mask of the original source. -/
theorem stoppedPending_actualDataGeometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z) :
    ∃ M : ReferenceActivePhysicalStep.Payload (p := p) (rate := rate),
      incomingStoredPayload rate rewards C_star C_h t z = some (some M) ∧
      ∀ control : ContinuousLearningRows.TimeControl p,
        (ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) = true ↔
          PublicDiscreteDraws.slotDraw control.1 = PublicDiscreteDraws.dataSlot ∧
          PublicDiscreteDraws.pilotDraw (K_pos p)
            (ActiveRoundActions.coordinator p.two_le_m) control.1 = M.assignment.assigned i ∧
          0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
            (M.assignment.assigned i)) := by
  obtain ⟨M, hM, _hchi⟩ := stoppedAssignedChi_eq_actual
    rate rewards C_star C_h control0 t i z hpending
  refine ⟨M, hM, ?_⟩
  intro control
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
  have hpending' : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z' := by
    rw [postRawKStoppedPendingSet_replace_current rate rewards C_star C_h control0]
    exact hpending
  have hkeep := (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_iff
    rate rewards C_star C_h t z' i).mp hpending' |>.1
  have hM' : incomingStoredPayload rate rewards C_star C_h t z' = some (some M) := by
    rw [incomingStoredPayload_replace_current rate rewards C_star C_h control0]
    exact hM
  obtain ⟨r, hr, ha, ht, hread⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z' hkeep
  obtain ⟨hstored, hP⟩ := hread M hM'
  obtain ⟨selected, registers, owned, base, states, memories,
    hstate, hregisterPayload, hemptyRegisters, hselected, hempty, _hlive,
    hchoices, _hstatus, _hfast, _hup, hdata, _hcost⟩ :=
    rawReleaseRecord_actualGeometry rate rewards C_star C_h z' r hr
  have hselectedPayload : selected.view.payload = M := by
    rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live,
      hregisterPayload] at hstored
    exact Option.some.inj hstored
  have hi : (states i).status = .pending := by
    have hp : i ∈ ReferencePhysicalReleaseQuota.pendingSet M r := hP ▸ hpending'
    have hchoice : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
      simpa only [ReferenceFollowerFixedReply.actualChoice, r.output_eq,
        ReferenceActivePhysicalStep.step] using hchoices i
    exact (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare M r.input
      registers owned base hstate (hregisterPayload.trans hselectedPayload)
      hemptyRegisters i (states i) (memories i) hchoice).mp hp
  have hgeometry := hdata i hi
  have hfields := actualRecord_input_fields rate rewards C_star C_h t z' r ha
  have hcontrol : r.input.row.2 r.input.time = control := by
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hfields.1,
      hfields.2.1, ht, z', ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      Function.update_self]
  have hcontrolT : r.input.row.2 t = control := by simpa only [ht] using hcontrol
  change ReferenceSourcePrefixHistoryFiltration.actualData
    rate rewards C_star C_h i t z' = true ↔ _
  rw [ReferenceSourcePrefixHistoryFiltration.actualData, ha, Option.bind_some,
    hstored, Option.map_some, Option.getD_some]
  simpa only [ReferenceFirstLiveReleaseGeometry.followerToFin, hselectedPayload,
    ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
    ReleaseRoundKernel.releaseRoundInput, hcontrolT, ht, Fin.eta] using hgeometry

private theorem actualData_prefix_restore
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control) =
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
  have hcurrent : (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 t = control := by
    simp only [z', ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  have hprefix := ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t z'
  rw [sourcePrefix_replace_current control0 t z control, hcurrent] at hprefix
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  exact ((ReferenceSourcePrefixHistoryFiltration.flags_factor rate rewards C_star C_h
    control0 i t z').2.1.trans (congrArg
      (ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t)
      hprefix)).symm

private theorem data_kernel_coordinates
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hempty : selected.view.pendingAtChoice = ∅)
    (hstatus : ∀ j : ActiveRoundActions.Follower p.m,
      (states j).status = .pending ∨ (states j).status = .released)
    (i : ActiveRoundActions.Follower p.m) (hi : (states i).status = .pending)
    (row : ActiveRoundActions.RewardRow p.K)
    (slice : ContinuousControlSlice.Slice p.m p.K) :
    let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states
    let input := ReleaseRoundKernel.releaseRoundInput p selected.view.payload.assignment
      selected.view.payload.slowSet selected.view.payload.assignment_image.symm
      rate.eta rate.eta.property selected.view.payload.eta_le_source_cap
      selected.view.payload.anchor (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      selected.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) slice
    (ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i ∧
      input.slot = PublicDiscreteDraws.dataSlot) ↔
      PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot ∧
      PublicDiscreteDraws.pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) slice =
        selected.view.payload.assignment.assigned i ∧
      0 < row.val (selected.view.payload.assignment.assigned i) := by
  intro snapshot input
  have hreward (hslot : input.slot = PublicDiscreteDraws.dataSlot) :
      ActiveRoundActions.feedback p.two_le_m snapshot input row
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          row.val (selected.view.payload.assignment.assigned i) := by
    have hfree : FiniteBanditModel.collisionFreeFor
        (ActiveRoundActions.actions p.two_le_m snapshot input)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      intro q hq hsame
      rcases ActiveRoundActions.player_cases p.two_le_m q with hcoord | ⟨j, hj⟩
      · rw [hcoord, ActiveRoundActions.actions_coordinator,
          ActiveRoundActions.coordinatorAction_fast p.two_le_m snapshot input hempty,
          ActiveRoundActions.actions_follower,
          ActiveRoundActions.followerAction_occupied_data p.two_le_m snapshot input i
            (Or.inl hi) hslot] at hsame
        exact input.fast_outside i hsame
      · have hji : j ≠ i := fun h => hq (h ▸ hj)
        rw [hj, ActiveRoundActions.actions_follower,
          ActiveRoundActions.followerAction_occupied_data p.two_le_m snapshot input j
            (hstatus j) hslot, ActiveRoundActions.actions_follower,
          ActiveRoundActions.followerAction_occupied_data p.two_le_m snapshot input i
            (Or.inl hi) hslot] at hsame
        exact hji (selected.view.payload.assignment.injective hsame)
    rw [ActiveRoundActions.feedback_eq_reward_of_collision_free p.two_le_m snapshot input row _ hfree,
      ActiveRoundActions.actions_follower,
      ActiveRoundActions.followerAction_occupied_data p.two_le_m snapshot input i (Or.inl hi) hslot]
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hup, _, _⟩ | ⟨_hslot, hpilot⟩
    · exact False.elim ((by decide : PublicDiscreteDraws.upSlot ≠
        PublicDiscreteDraws.dataSlot) (hup.symm.trans houter))
    · exact ⟨houter, hpilot, by simpa only [hreward houter] using hpos⟩
  · rintro ⟨hslot, hpilot, hpos⟩
    exact ⟨⟨by rw [hreward hslot]; exact hpos, Or.inr ⟨hslot, hpilot⟩⟩, hslot⟩

/-- The literal actual DATA section is evaluated on the later stopped pending
support. All geometry, payload matching, occupied statuses and weight bounds
are produced from the original source, rather than supplied by the caller. -/
theorem stoppedPending_actualDataControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z) :
    ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z =
      stoppedAssignedChi rate rewards C_star C_h t i z / (2 * (p.K : ℝ)) := by
  obtain ⟨M, hM, hgeometry⟩ := stoppedPending_actualDataGeometry
    rate rewards C_star C_h control0 t i z hpending
  have hkeep := (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_iff
    rate rewards C_star C_h t z i).mp hpending |>.1
  obtain ⟨r, hr, _ha, _ht, hread⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z hkeep
  obtain ⟨hstored, hP⟩ := hread M hM
  obtain ⟨selected, registers, owned, base, states, memories,
    hstate, hregisterPayload, hemptyRegisters, _hselected, hempty, _hlive,
    hchoices, hfields, _hfast, _hup, _hdata, _hcost⟩ :=
    rawReleaseRecord_actualGeometry rate rewards C_star C_h z r hr
  have hselectedPayload : selected.view.payload = M := by
    rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live,
      hregisterPayload] at hstored
    exact Option.some.inj hstored
  have hi : (states i).status = .pending := by
    have hp : i ∈ ReferencePhysicalReleaseQuota.pendingSet M r := hP ▸ hpending
    have hchoice : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
      simpa only [ReferenceFollowerFixedReply.actualChoice, r.output_eq,
        ReferenceActivePhysicalStep.step] using hchoices i
    exact (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare M r.input
      registers owned base hstate (hregisterPayload.trans hselectedPayload)
      hemptyRegisters i (states i) (memories i) hchoice).mp hp
  have hstatus : ∀ j, (states j).status = .pending ∨ (states j).status = .released := by
    intro j
    cases hs : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let E : Set (ContinuousControlSlice.Slice p.m p.K) := {slice |
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot ∧
    PublicDiscreteDraws.pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) slice =
      M.assignment.assigned i ∧ 0 < row.val (M.assignment.assigned i)}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun PublicDiscreteDraws.measurable_slotDraw measurable_const).inter
      ((measurableSet_eq_fun (PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m)) measurable_const).inter
        (MeasurableSet.const _))
  have hmass : ContinuousControlSlice.sliceLaw p.m p.K E =
      ENNReal.ofReal (ReleaseRoundKernel.chi row (M.assignment.assigned i) / (2 * (p.K : ℝ))) := by
    have hprob := ReleaseRoundKernel.actual_data_release_probability p
      selected.view.payload.assignment
      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states) row
      rate.eta rate.eta.property selected.view.payload.eta_le_source_cap
      selected.view.payload.anchor (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      selected.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
      selected.view.payload.slowSet selected.view.payload.assignment_image.symm hempty hstatus i hi
    have hset : {slice | ActiveRoundActions.releaseObservation p.two_le_m
        (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInput selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) slice) row i ∧
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInput selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) slice).slot =
            PublicDiscreteDraws.dataSlot} = E := by
      ext slice
      apply (data_kernel_coordinates selected states hempty hstatus i hi row slice).trans
      simp only [E, hselectedPayload, Set.mem_ofPred_eq]
    rw [← hset]
    calc
      _ = ENNReal.ofReal (ReleaseRoundKernel.chi row
          (selected.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))) := hprob
      _ = _ := by rw [hselectedPayload]
  have hwhole : ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E) =
      ContinuousControlSlice.sliceLaw p.m p.K E :=
    (ContinuousLearningRows.measurePreserving_slice p).measure_preimage hE.nullMeasurableSet
  have hintegral : ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
      rate rewards C_star C_h control0 i t z =
        (ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E)).toReal := by
    unfold ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSectionIntegrand
    have hfun : (fun control : ContinuousLearningRows.TimeControl p =>
        if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control)
        then (1 : ℝ) else 0) = (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext control
      rw [actualData_prefix_restore rate rewards C_star C_h control0 t i z control]
      simp only [Set.indicator, Set.mem_preimage, E, Set.mem_ofPred_eq]
      exact if_congr (hgeometry control) rfl rfl
    rw [hfun]
    exact integral_indicator_one (hE.preimage measurable_fst)
  have hnonneg : 0 ≤ ReleaseRoundKernel.chi row (M.assignment.assigned i) / (2 * (p.K : ℝ)) := by
    unfold ReleaseRoundKernel.chi
    split_ifs <;> positivity
  rw [hintegral, hwhole, hmass, ENNReal.toReal_ofReal hnonneg]
  simp only [stoppedAssignedChi, hpending, ↓reduceIte, hM, row]

/-- The actual assigned chi observation is predictable at the original
source-prefix pre-choice field, including its explicit off-support zero. -/
theorem stoppedAssignedChi_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (stoppedAssignedChi rate rewards C_star C_h t i) := by
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hslow : Measurable (fun M : ReferenceActivePhysicalStep.Payload rate => M.slowSet) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))).subtype_mk
  have hcoeff : Measurable (fun M : ReferenceActivePhysicalStep.Payload rate =>
      ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (M.assignment.assigned i)) :=
    (measurable_of_countable (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (CanonicalAssignmentVector.followerArm p.two_le_m U i))).comp hslow
  have hinner := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ)
    (fun M : ReferenceActivePhysicalStep.Payload rate =>
      ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (M.assignment.assigned i)) hcoeff
  have houter := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ)
    (ReferenceCollectionOutcomeMeasurability.optionalElim (0 : ℝ)
      (fun M : ReferenceActivePhysicalStep.Payload rate =>
        ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (M.assignment.assigned i))) hinner
  have hvalue := houter.comp
    (incomingStoredPayload_measurable_preChoice rate rewards C_star C_h control0 t)
  have hvalue' : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => match incomingStoredPayload rate rewards C_star C_h t z with
        | some (some M) => ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (M.assignment.assigned i)
        | _ => (0 : ℝ)) := by
    convert hvalue using 1
    funext z
    dsimp only [Function.comp_def]
    cases incomingStoredPayload rate rewards C_star C_h t z with
    | none => rfl
    | some inner => cases inner <;> rfl
  exact hvalue'.ite
    (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_measurable_preRound
      rate rewards C_star C_h control0 t i) measurable_const

/-- Boundedness and predictability give integrability on the canonical
original source law, without a moment assumption. -/
theorem stoppedAssignedChi_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (stoppedAssignedChi rate rewards C_star C_h t i)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hm := (stoppedAssignedChi_measurable_preChoice
    rate rewards C_star C_h control0 t i).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hb := stoppedAssignedChi_bounds rate rewards C_star C_h t i z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

/-- On one original-source null set for all followers and dates, the actual
stopped-pending DATA indicator has its evaluated conditional mean. The
literal pending mask is applied to an observation, not to an invented run. -/
theorem stoppedPending_actualData_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p),
      ∀ (i : Fin (p.m - 1)) (t : Fin p.T),
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          ({source | i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
            rate rewards C_star C_h t source}.indicator
            (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
              rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z =
            stoppedAssignedChi rate rewards C_star C_h t i z / (2 * (p.K : ℝ)) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro t
  have hmask :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_measurable_preRound
      rate rewards C_star C_h control0 t i
  have hpull := condExp_indicator
    (ReferenceSourcePhysicalFlagConditionalLaw.actualData_observation_integrable
      rate rewards C_star C_h control0 i t) hmask
  filter_upwards [hpull, ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
    rate rewards C_star C_h control0 i t] with z hpull hdata
  rw [hpull]
  by_cases hp : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z
  · simp only [Set.indicator, Set.mem_ofPred_eq, hp, ↓reduceIte, hdata]
    exact stoppedPending_actualDataControlSection rate rewards C_star C_h control0 t i z hp
  · simp only [Set.indicator, Set.mem_ofPred_eq, hp, ↓reduceIte, stoppedAssignedChi, zero_div]

private theorem selectionAt_payload_weights
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (M : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm M.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection M started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hs : ReferenceActivePhysicalStep.selectionAt x M started time weights arm = some selected) :
    selected.view.payload = M ∧ HEq selected.view.complementWeights weights := by
  unfold ReferenceActivePhysicalStep.selectionAt at hs
  split at hs
  · cases hs
    exact ⟨rfl, HEq.rfl⟩
  · cases hs

private theorem live_selected_payload_weights
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live registers owned base)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = registers.payload ∧
      HEq selected.view.complementWeights registers.complementWeights := by
  let liveInput := ReferenceActivePhysicalStep.liveInput x registers owned base
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live registers owned base (CoordinatorRoundDispatch.dispatchLive liveInput) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hs : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
      (CoordinatorRoundDispatch.dispatchLive liveInput)).selection = some selected := by
    simpa only [ReferenceActivePhysicalStep.prepare, hdispatch] using hselected
  cases hout : CoordinatorRoundDispatch.dispatchLive liveInput with
  | clockFailure failure hfailure =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | initializerFailure dispatched hstart checked hchecked =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | localFailure dispatched hstart reason =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | continuingChosen dispatched hstart continuation arm =>
      exact selectionAt_payload_weights x registers.payload dispatched.startResult x.time
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights arm selected
        (by simpa only [hout, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)
  | cutoffChosen dispatched hstart ledger hinitial hledger hvalid hclock hpending hnone arm =>
      exact selectionAt_payload_weights x registers.payload dispatched.startResult x.time
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights arm selected
        (by simpa only [hout, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)

private theorem completeWeights_congr
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M N : ReferenceActivePhysicalStep.Payload rate) (hM : M = N)
    (v : CanonicalFastSampling.FastArm M.slowSet → ℝ)
    (w : CanonicalFastSampling.FastArm N.slowSet → ℝ) (hw : HEq v w) :
    ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights M v =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights N w := by
  cases hM
  cases hw
  rfl

/-- The actual later release selector retains the same whole incoming payload
and complete current weights for every whole current-control replacement.
The positive anchor envelope and auxiliary minimizer are derived internally.
The fresh fast arm itself is allowed to change. -/
theorem stoppedDate_actualWeights_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      incomingStoredPayload rate rewards C_star C_h t z = some (some selected.view.payload) ∧
      (∀ a, 0 < ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
        selected.view.payload.anchor a ≤ ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
        ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ≤ 2 * selected.view.payload.anchor a) ∧
      (∀ a : CanonicalFastSampling.FastArm selected.view.payload.slowSet,
        selected.view.payload.anchor selected.view.payload.assignment.auxiliary ≤
          selected.view.payload.anchor a.val) ∧
      ∀ control : ContinuousLearningRows.TimeControl p,
        ∃ (r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (selected' : ReferenceActivePhysicalStep.Selection r'.input),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) = some r' ∧
          r'.output.preparation.coordinator.selection = some selected' ∧
          selected'.view.payload = selected.view.payload ∧
          ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected' =
            ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected := by
  obtain ⟨r, hr, ha, _ht, _hread⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z hkeep
  obtain ⟨selected, registers, owned, base, _states, _memories, hstate,
    hregisterPayload, _hemptyRegisters, hselection, _hempty, _hlive,
    _hchoices, _hstatus, _hfast, _hup, _hdata, _hcost⟩ :=
    rawReleaseRecord_actualGeometry rate rewards C_star C_h z r hr
  have hpayload : incomingStoredPayload rate rewards C_star C_h t z =
      some (some selected.view.payload) := by
    simp only [incomingStoredPayload, ReferenceSourcePrefixHistoryFiltration.incoming, ha,
      Option.map_some, ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hstate,
      ReferenceAssignmentPayloadPersistence.storedPayload_live, hregisterPayload]
  refine ⟨r, selected, ha, hselection, hpayload,
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected), ?_, ?_⟩
  · intro a
    exact selected.view.payload.auxiliaryArm_anchor_minimum a.val a.property
  · intro control
    let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
    have hkeep' : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t z' := by
      rw [postRawKStoppedDate_replace_current rate rewards C_star C_h control0]
      exact hkeep
    obtain ⟨r', hr', ha', _ht', _hread'⟩ := stoppedDate_record_readouts
      rate rewards C_star C_h control0 t z' hkeep'
    obtain ⟨selected', registers', owned', base', _states', _memories', hstate',
      _hregisterPayload', _hemptyRegisters', hselection', _hempty', _hlive',
      _hchoices', _hstatus', _hfast', _hup', _hdata', _hcost'⟩ :=
      rawReleaseRecord_actualGeometry rate rewards C_star C_h z' r' hr'
    have hcode := incomingStateCode_replace_current rate rewards C_star C_h control0 t z control
    change ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z at hcode
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, ha, ha', Option.map_some,
      Option.some.injEq] at hcode
    have hstates : r'.input.state = r.input.state := by
      simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using
        congrArg (ReferenceActivePhysicalStepMeasurability.decodeState (p := p) (rate := rate)) hcode
    have hregisters : registers' = registers :=
      (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
        (hstate'.symm.trans ((congrArg ReferenceActivePhysicalStep.State.coordinator hstates).trans hstate))).1
    have hsel : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some selected := by
      simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselection
    have hsel' : (ReferenceActivePhysicalStep.prepare r'.input).coordinator.selection = some selected' := by
      simpa only [r'.output_eq, ReferenceActivePhysicalStep.step] using hselection'
    obtain ⟨hM, hw⟩ := live_selected_payload_weights r.input registers owned base hstate selected hsel
    obtain ⟨hM', hw'⟩ := live_selected_payload_weights r'.input registers' owned' base' hstate' selected' hsel'
    have hMboth : selected'.view.payload = selected.view.payload :=
      hM'.trans ((congrArg (fun r => r.payload) hregisters).trans hM.symm)
    refine ⟨r', selected', ha', hselection', hMboth, completeWeights_congr selected'.view.payload selected.view.payload hMboth
      selected'.view.complementWeights selected.view.complementWeights ?_⟩
    have hregWeights : HEq registers'.complementWeights registers.complementWeights := by
      cases hregisters
      rfl
    exact hw'.trans (hregWeights.trans hw.symm)

/-- Empty pending does not remove a genuine supported release date. Its
literal signed physical deficit is nonpositive on that same actual record. -/
theorem stoppedDate_emptyPending_signedDeficit_nonpos
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z)
    (hpending : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z = ∅) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      ReleaseRoundKernel.slowReward
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected.view.payload.slowSet +
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val selected.arm -
        (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤ 0 := by
  obtain ⟨r, hr, ha, ht, hread⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z hkeep
  obtain ⟨selected, registers, owned, base, _states, _memories,
    hstate, hregisterPayload, _hemptyRegisters, hselection, _hempty, _hlive,
    _hchoices, _hstatus, _hfast, _hup, _hdata, hcost⟩ :=
    rawReleaseRecord_actualGeometry rate rewards C_star C_h z r hr
  have hM : incomingStoredPayload rate rewards C_star C_h t z =
      some (some selected.view.payload) := by
    simp only [incomingStoredPayload, ReferenceSourcePrefixHistoryFiltration.incoming, ha,
      Option.map_some, ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hstate,
      ReferenceAssignmentPayloadPersistence.storedPayload_live, hregisterPayload]
  have hP : ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r = ∅ :=
    (hread selected.view.payload hM).2.symm.trans hpending
  refine ⟨r, selected, ha, hselection, ?_⟩
  simpa only [hP, Finset.sum_empty, Finset.not_nonempty_empty, and_false,
    ↓reduceIte, add_zero, ht] using hcost

end Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData

end
