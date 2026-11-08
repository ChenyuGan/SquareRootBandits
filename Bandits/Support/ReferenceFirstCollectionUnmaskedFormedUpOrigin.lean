/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpDetectedWaitingCost

import Lean.Elab.Tactic.Omega

/-!
# Unmasked formed-UP origin and every selected receiver

Sources: `sources/zip4/manuscript/05_binary_transport.tex:33-55`,
`sources/zip4/manuscript/06_interruptions.tex:246-299,327-348,459-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpOrigin

variable {p : ConstructorDimensions.Parameters}

/-- Literal first-collection FORMED-stage positive tests on the original
physical calendar. The pending observer is the literal unmasked `Praw`. -/
def unmaskedFormedUpTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (source : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val source ∧
    source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val source = true

/-- A FORMED test remains localized by the existing original-source pending
mask to the first collection window of the complete physical suffix. -/
private theorem unmasked_test_localizes_to_first_collection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (ht : t ∈ unmaskedFormedUpTests (p := p) rate rewards C_star C_h i source) :
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)).length)[k.val].input.time = t := by
  obtain ⟨hraw, _hformed, _hx⟩ := (Finset.mem_filter.mp ht).2
  exact ReferenceFirstCollectionPendingObservation.Praw_localization
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t source ⟨i, hraw⟩

private theorem singleton_mem_retained_slice
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (f n k : ℕ) (hk : k < B.length)
    (hfk : f ≤ k) (hkn : k < n)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k] i = [e]) :
    e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (n - f)) i := by
  apply List.mem_flatMap.mpr
  have hdrop : k - f < (B.drop f).length := by
    simp only [List.length_drop]
    omega
  have htake : k - f < ((B.drop f).take (n - f)).length := by
    simp only [List.length_take]
    omega
  have hget : ((B.drop f).take (n - f))[k - f]'htake = B[k] := by
    rw [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  refine ⟨B[k], ?_, ?_⟩
  · rw [← hget]
    exact List.getElem_mem htake
  · rw [he]
    exact List.mem_singleton_self e

/-- This backward chronology argument works also at the cutoff coordinate
zero. Its acceptance is in the actual run before the tested input. -/
private theorem formed_input_prior_current_down
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (k : Fin d.stream.window.length)
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (i : Fin (p.m - 1))
    (hold : d.stream.window[k.val].input.state.followers i = .ordinary old memory)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart old) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    ∃ j : Fin E.records.length,
      j.val < w + k.val ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (d.stream.payload.downRecord i) := by
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hlookup : E.records[w + k.val]? = some out.window[k.val] :=
    (out.alignment k).1
  have hindex : w + k.val < E.records.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hget : E.records[w + k.val] = out.window[k.val] :=
    (List.getElem?_eq_some_iff.mp hlookup).2
  have hendpoint : E.records[w + k.val].input.state.followers i = .ordinary old memory := by
    rw [hget]
    exact hold
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
    E.connected (w + k.val) hindex
  obtain ⟨_, _, _, _, _, _, _, hfollowers⟩ :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate source rewards C_star C_h hcross
  obtain ⟨hfirst, _hfirstDown, hfirstStart, _⟩ := hfollowers i
  have hfirstI : I.followers i = .ordinary
      (ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
        (ActualReferenceInitializationBlock.refFollower i))
      (ActiveFollowerLifecycle.initialMemory p) := by
    simpa only [I, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirst
  obtain ⟨first, firstMemory, hfirstOrdinary, _, _, hchange⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology
      hprefix i old memory hendpoint
  have hfirstEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hfirstOrdinary.symm.trans hfirstI)
  have hzero : ReferencePrelaunchFollower.acceptedStart first = 0 := by
    rw [hfirstEq.1]
    exact hfirstStart
  obtain ⟨acceptedRecord, hmem, _sigma, happlied, _, _⟩ := hchange (by omega)
  obtain ⟨j, hjTake, hjRecord⟩ := List.mem_iff_getElem.mp hmem
  have hj : j < w + k.val := by
    simp only [List.length_take] at hjTake
    omega
  have hjE : j < E.records.length := by
    simp only [List.length_take] at hjTake
    omega
  have hjEq : E.records[j] = acceptedRecord := by
    simpa only [List.getElem_take] using hjRecord
  have hjLookup : E.records[j]? = some acceptedRecord := by
    rw [List.getElem?_eq_getElem hjE, hjEq]
  obtain ⟨logged, cut, after, raw, message, scan, registers, lastService,
    hdownInput, hdown, houtcome, _⟩ := happlied
  have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown acceptedRecord i message :=
    ⟨logged, cut, after, raw, scan, registers, lastService, hdownInput, hdown, houtcome⟩
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  rcases horigin.origin with ⟨originCut, P0, _birth, live, owned, base,
    ⟨hw, horiginCut⟩, _huniqueCut, hcoordinator, _hcutoffChosen, hP0,
    _hsigma, _hqueues, _hfirstCutoff, _hbirthMem, _hbirth, _hbirthTime,
    _hbirthSelection, _halignment, _hselection, _hcurrent, hearlier⟩
  have horiginLookup : E.records[w]? = some originCut := by
    rw [horiginCut]
    exact List.getElem?_eq_getElem hw
  have hsameCut : originCut = out.cutoff.cut :=
    Option.some.inj (horiginLookup.symm.trans out.cutoff.cutIndex)
  obtain ⟨execution⟩ := out.cutoffExecution
  have hsameLive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live live owned base =
      .live execution.live execution.owned execution.base := by
    rw [hsameCut] at hcoordinator
    exact hcoordinator.symm.trans execution.actualLive
  have hlive : live = execution.live := by injection hsameLive
  have hP0Out : P0 = out.payload := by
    calc
      P0 = live.payload := hP0
      _ = execution.live.payload := congrArg
        (fun x : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => x.payload) hlive
      _ = out.cutoff.payload := execution.payloadIsLive.symm
      _ = out.payload := out.payloadMatchesCutoff.symm
  have hwindow := out.windowIsActual
  have hkB : k.val < (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length := by
    rw [← hwindow]
    exact k.isLt
  have hmessage : message = out.payload.downRecord i := by
    have h := hearlier ⟨k.val, hkB⟩ j hj acceptedRecord hjLookup i message hretained
    exact h.1.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate =>
      P.downRecord i) hP0Out)
  refine ⟨⟨j, hjE⟩, hj, ?_⟩
  rw [hjEq, ← hmessage]
  exact hretained

private theorem formed_test_stream_coordinate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (t : Fin p.T) (ht : t ∈ unmaskedFormedUpTests rate rewards C_star C_h i source) :
    ∃ n : Fin d.stream.ell,
      (d.stream.window[n.val]'
        (Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow)).input.time = t ∧
      (0 < n.val → i ∈ (d.stream.ledgers ⟨n.val - 1, by omega⟩).pending) := by
  let out := d.stream
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let B := ReferenceFirstCollectionReadyStream.actualWindow
    (rate := rate) source rewards C_star C_h hcross count hspan
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = E.records := by
    cases hcountEq
    exact ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      (rate := rate) rewards C_star C_h source hcross
  obtain ⟨hraw, _hformed, _hx⟩ := (Finset.mem_filter.mp ht).2
  have hloc := unmasked_test_localizes_to_first_collection
    rate rewards C_star C_h i source t ht
  let observed := fun records : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
  have hlocE : observed E.records := Eq.mp (congrArg observed hrecords) hloc
  obtain ⟨k, hkTime⟩ : ∃ k : Fin B.length, B[k.val].input.time = t := hlocE
  -- This readout includes the actual empty-stream suffix; no decoder-failure
  -- erasure or successful renewal is used to obtain the stream index.
  have hQwindow := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    source count hcross hspan hshort d k
  change ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      B[k.val].input.time source =
    (if k.val = 0 then Finset.univ else
      if hk : k.val < out.ell then
        (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le k.val 1) hk⟩).pending
      else ∅) at hQwindow
  have hQmember : i ∈ ReferenceFirstCollectionPendingObservation.Q
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      B[k.val].input.time source := by
    rw [hkTime]
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at] using hraw
  have hkEll : k.val < out.ell := by
    by_cases hkzero : k.val = 0
    · rw [hkzero]
      exact out.positiveLength
    · by_contra hnot
      rw [hQwindow] at hQmember
      simp only [ite_eq_right hkzero, dite_eq_right hnot, Finset.notMem_empty] at hQmember
  have hkWindow : k.val < out.window.length := by
    rw [out.windowIsActual]
    exact k.isLt
  have hget : out.window[k.val]'hkWindow = B[k.val] :=
    List.getElem_of_eq out.windowIsActual hkWindow
  refine ⟨⟨k.val, hkEll⟩, ?_, ?_⟩
  · exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => r.input.time) hget).trans hkTime
  · intro hn
    change 0 < k.val at hn
    rw [hQwindow, ite_eq_right (Nat.ne_of_gt hn), dite_eq_left hkEll] at hQmember
    exact hQmember

private theorem test_launch_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ unmaskedFormedUpTests rate rewards C_star C_h i source) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let count := p.T - s
    ∃ hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hspan : s + count ≤ p.T,
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length < count := by
  intro s count
  obtain ⟨hraw, _hformed, _hx⟩ := (Finset.mem_filter.mp hlatest).2
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h latest.val source := by
    by_contra hnot
    rw [ReferenceFirstCollectionPendingObservation.Praw_at,
      ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        latest source hnot] at hraw
    exact Finset.not_nonempty_empty ⟨i, hraw⟩
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
    simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hlaunch.1
  have hspan : s + count ≤ p.T :=
    ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
      rate rewards C_star C_h source
  have hboundary := ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    latest source ⟨i, hraw⟩
  dsimp only at hboundary
  obtain ⟨pair, hpair, _⟩ := hboundary
  obtain ⟨_, _, _, _, _, hRshort⟩ := hpair
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = E.records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      (rate := rate) rewards C_star C_h source hcross
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : w < count := by
    rw [← hcount]
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < E.records.length
    rw [← hrecords]
    exact hRshort
  exact ⟨hcross, hspan, hshort⟩

private theorem tests_before_zero_empty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (latest : Fin p.T) (n : Fin d.stream.ell)
    (hnTime : (d.stream.window[n.val]'
      (Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow)).input.time = latest)
    (hnzero : n.val = 0) :
    (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
      (fun t => t.val < latest.val) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨htest, hbefore⟩ := Finset.mem_filter.mp ht
  obtain ⟨k, hkTime, _hkPending⟩ := formed_test_stream_coordinate
    rate rewards C_star C_h source i count hcross hspan hshort d hcountEq t htest
  have hnDate := (d.stream.alignment
    ⟨n.val, Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow⟩).2
  have hkDate := (d.stream.alignment
    ⟨k.val, Nat.lt_of_lt_of_le k.isLt d.stream.withinWindow⟩).2
  dsimp only [Fin.val_mk] at hnDate hkDate
  rw [hnTime] at hnDate
  rw [hkTime] at hkDate
  omega

private theorem formed_record_lastDown_ne_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstate : r.input.state.followers i = .ordinary state memory)
    (hformed : source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t)
    (hx : ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val source = true) :
    state.lastDown ≠ none := by
  obtain ⟨rActual, hrActual, _htime, _hrows, _hselected, _hrewards,
    old, oldMemory, hold, _haccepted, hnotnone, _hchannel, _hpositive, _hentry⟩ :=
    ReferenceFirstCollectionFormedStagePositiveEntry.actual_formed_stage_positive_entry
      rate rewards C_star C_h source i t hformed hx
  have hr : rActual = r := Option.some.inj (hrActual.symm.trans hactual)
  rw [hr] at hold
  have hs : old = state :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hold.symm.trans hstate)).1
  simpa only [hs] using hnotnone

/-- Every earlier unmasked formed test has a real retained current-DOWN
origin, hence lies after the same clipped formation point as the latest test. -/
private theorem earlier_tests_in_retained_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (i : Fin (p.m - 1)) (latest : Fin p.T) (n : Fin d.stream.ell)
    (hnTime : (d.stream.window[n.val]'
      (Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow)).input.time = latest) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    ∀ j : Fin E.records.length,
      (∀ j' : Fin E.records.length, j'.val < w + n.val →
        ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
          (out.payload.downRecord i) → j' = j) →
      let f := if j.val < w then 0 else j.val - w + 1
      ∀ v ∈ (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
          (fun t => t.val < latest.val),
        ∃ (k : Fin B.length) (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
          f ≤ k.val ∧ k.val < n.val ∧ B[k.val].input.time = v ∧
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k.val] i = [e] ∧
          e.time = v ∧ e.sample = ((source.1.2 J).2 v).2 (1, i) ∧
          e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            ((B.drop f).take (n.val - f)) i := by
  intro out E w B J j hunique f
  have hwindow : out.window = B := out.windowIsActual
  have hBlength : out.ell ≤ B.length := by
    rw [← hwindow]
    exact out.withinWindow
  intro v hv
  obtain ⟨hvTest, hvBefore⟩ := Finset.mem_filter.mp hv
  obtain ⟨kOut, hkTimeStream, _hkPending⟩ := formed_test_stream_coordinate
    rate rewards C_star C_h source i count hcross hspan hshort d hcountEq v hvTest
  have hkB : kOut.val < B.length := Nat.lt_of_lt_of_le kOut.isLt hBlength
  let k : Fin B.length := ⟨kOut.val, hkB⟩
  have hget : out.window[k.val]'(Nat.lt_of_lt_of_le kOut.isLt out.withinWindow) = B[k.val] :=
    List.getElem_of_eq hwindow (Nat.lt_of_lt_of_le kOut.isLt out.withinWindow)
  have hkTime : B[k.val].input.time = v :=
    (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => r.input.time) hget).symm.trans hkTimeStream
  have hkn : k.val < n.val := by
    have hnDate := (out.alignment
      ⟨n.val, Nat.lt_of_lt_of_le n.isLt out.withinWindow⟩).2
    have hkDate := (out.alignment
      ⟨kOut.val, Nat.lt_of_lt_of_le kOut.isLt out.withinWindow⟩).2
    dsimp only [Fin.val_mk] at hnDate hkDate
    rw [hnTime] at hnDate
    rw [hkTimeStream] at hkDate
    change kOut.val < n.val
    omega
  obtain ⟨_hvRaw, hvFormed, hvX⟩ := (Finset.mem_filter.mp hvTest).2
  obtain ⟨rv, hrv, _hrvTime, _hrvRows, _hrvSelected, _hrvRewards,
    oldv, memoryv, holdv, hacceptedv, _hnotnonev, hchannelv, hpositivev,
    e, he, heTime, heSample⟩ :=
    ReferenceFirstCollectionFormedStagePositiveEntry.actual_formed_stage_positive_entry
      rate rewards C_star C_h source i v hvFormed hvX
  have hrecordK := ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_lookup
    rate source rewards C_star C_h count hcross hspan hshort k
  have hactualK : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h v source = some B[k.val] := by
    rw [← hkTime]
    exact hrecordK.1
  have hrvB : rv = B[k.val] := Option.some.inj (hrv.symm.trans hactualK)
  rw [hrvB] at holdv hpositivev he
  have hkWindow : k.val < out.window.length := by
    rw [hwindow]
    exact k.isLt
  have hgetWindow : out.window[k.val]'hkWindow = B[k.val] :=
    List.getElem_of_eq hwindow hkWindow
  have holdWindow : out.window[k.val].input.state.followers i = .ordinary oldv memoryv := by
    rw [hgetWindow]
    exact holdv
  obtain ⟨jv, hjvBefore, hjvRetained⟩ := formed_input_prior_current_down
    rate source rewards C_star C_h count hcross hspan hshort d
    ⟨k.val, hkWindow⟩ oldv memoryv i holdWindow hacceptedv
  change jv.val < w + k.val at hjvBefore
  have hjvEq : jv = j := hunique jv
    (Nat.lt_trans hjvBefore (Nat.add_lt_add_left hkn w)) hjvRetained
  have hjk : j.val < w + k.val := by
    rw [← hjvEq]
    exact hjvBefore
  have hfk : f ≤ k.val := by
    dsimp only [f]
    split <;> omega
  exact ⟨k, e, hfk, hkn, hkTime, he, heTime, heSample,
    singleton_mem_retained_slice B i f n.val k.val k.isLt hfk hkn e he⟩

/-- Reading the literal selector into the two public control draws. -/
private theorem selected_up_draws
    (c : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p c.1 = some (1, i)) :
    PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i := by
  unfold ReferenceSelectedAffinePairLaw.selectedChannel
    ReferenceSelectedAffinePairLaw.channelFromDraws at hchannel
  split at hchannel
  · have hbad : (0 : Fin 2) = 1 := congrArg Prod.fst (Option.some.inj hchannel)
    exact ((by decide : (0 : Fin 2) ≠ 1) hbad).elim
  · split at hchannel
    · exact ⟨by assumption, congrArg Prod.snd (Option.some.inj hchannel)⟩
    · cases hchannel

/-- The real ordinary cutoff receiver is awaited whenever its selected sender
has this offer. No positive observation is required. -/
private theorem cutoff_awaited_of_offer
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (finished : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) (s : ℕ)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hnext : r.output.next.coordinator = .collection payload finished saved)
    (hlive : r.input.state.coordinator = .live registers owned base)
    (hsigma : finished.sigma = s + 1)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hU : U.val.sigma = s + 1)
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (r.input.row.2 r.input.time).1 = some (1, i))
    (hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input) = some
        (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) :
    ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i U := by
  obtain ⟨tail0, htail0, _hpending0, hsig0⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame r.input payload finished saved
      (by rw [← r.output_eq]; exact hnext)
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true := by
    rcases (ReferenceCollectionPhaseHistory.executedTail_origin htail0).2 with hcut | hcollection
    · exact hcut.1
    · obtain ⟨_, P, L, proposal, hcollection, _⟩ := hcollection
      rw [hlive] at hcollection
      cases hcollection
  have hordinary : r.output.next.coordinator ≠ .dagger := by
    rw [hnext]
    intro h
    cases h
  obtain ⟨tail, recording, L, diagnostic, received, bank, final, clock,
    htail, _hpost, hsite, _htailPending, htailSigma, _htailCutoff, _htailCursor,
    _htailPhase, _hstartedPending, _hrecording, _hstart, hLpending, hLsigma,
    hLcutoff, hLcursor, hcheck, hinput, hdiagnostic, _hreception, _hnoninvalid,
    _hresult, _hfinish, _hclock, _hdecoder, _hraw, _hparsed, _hlocal,
    hdiagnosticExpected, _hmatches, _hbank, _htime, _hsample, _hown, _hwrong⟩ :=
      ReferenceCutoffUpReceiverLocal.actual_ordinary_cutoff_up_receiver r hcut hordinary
  have htailEq : tail = tail0 := Option.some.inj (htail.symm.trans htail0)
  have hLsigma' : L.sigma = s + 1 := by
    calc
      L.sigma = tail.ledger.sigma := hLsigma.trans htailSigma.symm
      _ = tail0.ledger.sigma := congrArg (fun t => t.ledger.sigma) htailEq
      _ = finished.sigma := hsig0.symm
      _ = s + 1 := hsigma
  obtain ⟨L', hsite', hledger', _hbank', htime', _hown', hselected', _hsample',
    hslot', _hrest⟩ := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      r diagnostic hdiagnostic
  have hLL : L' = L := Option.some.inj (hsite'.symm.trans hsite)
  have hledger : diagnostic.input.ledger = L := hledger'.trans hLL
  have hdraw := selected_up_draws (r.input.row.2 r.input.time) i hchannel
  have hselected : diagnostic.input.selectedFollower = i := by
    rw [hselected', CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hdraw.2
  have hslot : diagnostic.input.slot = PublicDiscreteDraws.upSlot := hslot'.trans hdraw.1
  have hcheck' : CoordinatorUpReception.receptionInputCheck diagnostic.input = true := by
    rw [hinput]
    exact hcheck
  have hgate : CoordinatorUpReception.receptionGate diagnostic.input := by
    refine ⟨?_, hslot, ?_⟩
    · rw [hledger, hLcutoff, htime']
      exact Nat.le_refl _
    · rw [hselected, hledger, hLpending]
      exact Finset.mem_univ i
  have haccept : CoordinatorCollectionLedger.acceptUpCheck diagnostic.input.ledger i U = true := by
    rw [hledger]
    simp only [CoordinatorCollectionLedger.acceptUpCheck, hLcutoff, hLcursor,
      Nat.le_refl, decide_true, hLpending, Finset.mem_univ, hU, hLsigma', Bool.and_self]
  exact ⟨diagnostic, hdiagnostic, hselected, hcheck', hgate,
    hdiagnosticExpected.trans hexpected, haccept⟩

/-- The omitted coordinate zero of the positive-index producer is the
actual ordinary cutoff. Observable dispatch identity joins its offer to the
same current reply and retained DOWN origin. -/
private theorem actual_formed_cutoff_offer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let hB : out.ell ≤ B.length := by
      calc
        out.ell ≤ out.window.length := out.withinWindow
        _ = B.length := congrArg List.length out.windowIsActual
    ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (out.payload.downRecord i) →
    ∀ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
    ∀ j : Fin E.records.length, j.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i (out.payload.downRecord i) →
    ∀ k : Fin B.length, k.val = 0 →
      (if j.val < w then 0 else j.val - w + 1) ≤ k.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          B[k.val].input.time).1 = some (1, i) →
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare B[k.val].input) =
        some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) := by
  intro out E w B hB n hn i hi state memory hstate hdown U hU j hj hretained k hkzero hfk hchannel
  obtain ⟨dO, hdata⟩ :=
    ReferenceFirstCollectionFormedUpOfferReceiver.actual_initialized_first_collection_formed_up_offer_receiver
      rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hdata
  obtain ⟨_registers, _owned, _base, _cutRecord, _hcutIndex, _hcutState,
    _hpayload, _hpending, _hBpos, _hcutB0, _hcutRecord, hqueries⟩ := hdata
  let outO := dO.stream
  obtain ⟨_hwindowEq, hpayloadEq, _hsavedEq, hellEq, hledgerEq, _hrest⟩ :=
    ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
      rate source rewards C_star C_h count hcross hspan hshort d dO
  have hnO : n.val < outO.ell := by rw [← hellEq]; exact n.isLt
  let nO : Fin outO.ell := ⟨n.val, hnO⟩
  have hiO : i ∈ (outO.ledgers ⟨n.val - 1, by omega⟩).pending := by
    rw [← hledgerEq
      ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩
      ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) hnO⟩ rfl]
    exact hi
  obtain ⟨r, incoming, cell, stateO, memoryO, hr, _htime, _hrows, _hselected,
    _hrewards, _hincoming, _hiIncoming, _hready, _hservice, hstateO, _hstatus,
    _hvalid, _hS, _hdelta, _hbacklog, _hmass, _hbank, _hcompleted,
    _hlast, hformedData⟩ := hqueries nO hn i hiO
  have hrB : r = (B[n.val]'(n.isLt.trans_le hB)) := by
    rw [outO.windowIsActual] at hr
    exact (List.getElem?_eq_some_iff.mp hr).2.symm
  rw [hrB, hstate] at hstateO
  have hconfig := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hstateO.symm
  rcases hconfig with ⟨hstateEq, hmemoryEq⟩
  subst stateO
  subst memoryO
  have hdownO : state.lastDown = some (outO.payload.downRecord i) := by
    rw [← hpayloadEq]
    exact hdown
  obtain ⟨UO, hUO, hUsigma, _hUpositive, _hcurrentOffer, _hdownSigma, _hstart,
    jO, _hjIndex, _acceptedRecord, _hjBefore, _hjLookup, _hjRetained,
    _hdiagnostics, _hjtime, _hjrows, _hjselected, _hjrewards,
    hjUnique, _hf, _hfn, _hftime, _hfzero, _hfone, _hnested, hAt⟩ := hformedData hdownO
  have hUeq : UO = U := Subtype.ext (hUO.trans hU.symm)
  subst UO
  have hjeq : j.val = jO := by
    apply hjUnique j.val j.isLt E.records[j.val] hj
    · exact List.getElem?_eq_getElem j.isLt
    · rw [← hpayloadEq]
      exact hretained
  have hfkO : (if jO < w then 0 else jO - w + 1) ≤ k.val := by
    rw [← hjeq]
    exact hfk
  obtain ⟨_choice, _choiceMemory, _hchoice, _hchoiceDomain, _hchoiceStatus,
    _hreply, _hchoiceDown, _hchoiceS, _hchoiceDelta, _hchoiceBacklog,
    _hchoiceRow, _hchoiceFollower, _hchoiceActivation, _hchoiceTime,
    _before, _beforeMemory, _hbefore, _hbeforeDomain, _hstartBefore,
    _hreplyBefore, _hpendingCases, hoffers, _hzero, _hpositiveK⟩ :=
      hAt k hfkO (by change k.val ≤ n.val; omega)
  have hfields := ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_source_fields
    rate source rewards C_star C_h count hcross hspan hshort k
  have hchannelRecord : ReferenceSelectedAffinePairLaw.selectedChannel p
      (B[k.val].input.row.2 B[k.val].input.time).1 = some (1, i) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((B[k.val].input.rows B[k.val].input.selected).2 B[k.val].input.time).1 = some (1, i)
    rw [hfields.1, hfields.2.1]
    exact hchannel
  have hdraw := selected_up_draws (B[k.val].input.row.2 B[k.val].input.time) i hchannelRecord
  have hoff := hoffers hdraw.1 hdraw.2
  exact hoff.2.2.2

/-- Actual origin witnesses at a positive collection coordinate. The local
FORMED/positive premises exclude the real never-accepted-DOWN alternative. -/
private theorem actual_origin_dispatch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (count : ℕ) (hcross hspan hshort) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let hB : out.ell ≤ B.length := by
        calc
          out.ell ≤ out.window.length := out.withinWindow
          _ = B.length := congrArg List.length out.windowIsActual
      ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
        i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
      ∀ latest : Fin p.T, (B[n.val]'(n.isLt.trans_le hB)).input.time = latest →
        source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
          (p := p) (rate := rate) rewards C_star C_h i latest →
        ReferenceFirstCollectionRoundEndObservation.x
          (rate := rate) rewards C_star C_h i latest.val source = true →
      ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
        (j : Fin E.records.length),
        (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
        state.lastDown = some (out.payload.downRecord i) ∧
        U.val = ActiveFollowerQueueOperation.upOfferFields state ∧ U.val.sigma = s + 1 ∧
        j.val < w + n.val ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i (out.payload.downRecord i) ∧
        (∀ j' : Fin E.records.length, j'.val < w + n.val →
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
            (out.payload.downRecord i) → j' = j) ∧
        let f := if j.val < w then 0 else j.val - w + 1
        ∃ hf : f < B.length,
          f ≤ n.val ∧ B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
          (j.val < w → f = 0) ∧ (j.val = w → f = 1) := by
  obtain ⟨d, hdata⟩ :=
    ReferenceFirstCollectionFormationOrigin.actual_initialized_first_collection_formation_origin
      rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hdata
  obtain ⟨_registers, _owned, _base, _cutRecord, _hcutIndex, _hcutState,
    _hpayload, _hpending, hqueries⟩ := hdata
  refine ⟨d, ?_⟩
  intro out E w B s hB n hn i hi latest hnTime hformed hx
  have hnB : n.val < B.length := n.isLt.trans_le hB
  have hwindow : out.window = B := out.windowIsActual
  have hlookups := ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_lookup
    rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨r, incoming, cell, state, memory, hr, _htime, _hrows, _hselected,
    _hrewards, _hincoming, _hiIncoming, _hready, _hservice, hstate, hstatus,
    hvalid, _hS, _hdelta, _hbacklog, _hmass, _hbank, _hcompleted,
    hlast, hup, horigin⟩ := hqueries n hn i hi
  have hrB : r = B[n.val] := by
    have hget := (List.getElem?_eq_some_iff.mp hr).2
    have hgetB := List.getElem_of_eq hwindow (List.getElem?_eq_some_iff.mp hr).1
    exact hget.symm.trans hgetB
  have hstateB : B[n.val].input.state.followers i = .ordinary state memory := by
    rw [← hrB]
    exact hstate
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h latest source = some B[n.val] := by
    rw [← hnTime]
    exact (hlookups ⟨n.val, hnB⟩).1
  have hnotnone := formed_record_lastDown_ne_none rate rewards C_star C_h source
    i latest B[n.val] hactual state memory hstateB hformed hx
  have hdown : state.lastDown = some (out.payload.downRecord i) := by
    rcases hlast with hnone | hcurrent
    · exact False.elim (hnotnone hnone.1)
    · exact hcurrent
  obtain ⟨U, hU, _hUpositive, _hUactual⟩ := hup hdown
  obtain ⟨_hdownSigma, hstart, jNat, acceptedRecord, hjBefore, hjLookup,
    hjRetainedRecord, _hacceptance, _hjtime, _hjrows, _hjselected, _hjrewards,
    hjUnique, hf, hfn, hftime, hfzero, hfone⟩ := horigin hdown
  have hUsigma : U.val.sigma = s + 1 := by
    calc
      U.val.sigma = ReferencePrelaunchFollower.acceptedStart state := by rw [hU]; rfl
      _ = s + 1 := hstart
  have hjIndex : jNat < E.records.length := (List.getElem?_eq_some_iff.mp hjLookup).1
  let j : Fin E.records.length := ⟨jNat, hjIndex⟩
  have hjGet : E.records[j.val] = acceptedRecord := (List.getElem?_eq_some_iff.mp hjLookup).2
  have hjRetained : ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
      (out.payload.downRecord i) := by
    rw [hjGet]
    exact hjRetainedRecord
  have hunique : ∀ j' : Fin E.records.length, j'.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
        (out.payload.downRecord i) → j' = j := by
    intro j' hj' hr'
    apply Fin.ext
    exact hjUnique j'.val E.records[j'.val] hj'
      (List.getElem?_eq_getElem j'.isLt) hr'
  exact ⟨state, memory, U, j, hstateB, hstatus, hvalid, hdown, hU, hUsigma,
    hjBefore, hjRetained, hunique, hf, hfn, hftime, hfzero, hfone⟩

/-- Extend the public positive-index receiver interval to every selected
coordinate, using the actual cutoff call for coordinate zero. -/
private theorem actual_every_selected_awaited
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) (hcross hspan hshort)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let hB : out.ell ≤ B.length := by
      calc
        out.ell ≤ out.window.length := out.withinWindow
        _ = B.length := congrArg List.length out.windowIsActual
    ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (out.payload.downRecord i) →
    ∀ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields state → U.val.sigma = s + 1 →
    ∀ j : Fin E.records.length, j.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i (out.payload.downRecord i) →
    let f := if j.val < w then 0 else j.val - w + 1
    ∀ k : Fin B.length, f ≤ k.val → k.val ≤ n.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          B[k.val].input.time).1 = some (1, i) →
      ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate B[k.val] i U := by
  intro out E w B s hB n hn i hi state memory hstate hdown U hU hUsigma j hj hretained f
  obtain ⟨_hlookup, hfields, _hchron, _hpositive, hawait⟩ :=
    ReferenceFirstCollectionFormedUpAwaitedFailure.actual_formed_up_source_data
      rate source rewards C_star C_h count hcross hspan hshort d
      n hn i hi state memory hstate hdown U hU j hj hretained
  intro k hfk hkn hchannel
  by_cases hkzero : k.val = 0
  · have hexpected := actual_formed_cutoff_offer rate source rewards C_star C_h count
      hcross hspan hshort d n hn i hi state memory hstate hdown U hU
      j hj hretained k hkzero hfk hchannel
    have hchannelRecord : ReferenceSelectedAffinePairLaw.selectedChannel p
        (B[k.val].input.row.2 B[k.val].input.time).1 = some (1, i) := by
      change ReferenceSelectedAffinePairLaw.selectedChannel p
        ((B[k.val].input.rows B[k.val].input.selected).2 B[k.val].input.time).1 = some (1, i)
      rw [(hfields k).1, (hfields k).2.1]
      exact hchannel
    have hBpos : 0 < B.length := by have := k.isLt; omega
    have hkEq : k = (⟨0, hBpos⟩ : Fin B.length) := Fin.ext hkzero
    have hgetK : B[k.val] = B[0]'hBpos :=
      congrArg (fun q : Fin B.length => B[q.val]) hkEq
    have hget : out.window[0]'out.windowNonempty = B[0]'hBpos :=
      List.getElem_of_eq out.windowIsActual out.windowNonempty
    have hkCut : B[k.val] = out.cutoff.cut := hgetK.trans (hget.symm.trans out.cutoffIsHead)
    obtain ⟨execution⟩ := out.cutoffExecution
    have hnext : B[k.val].output.next.coordinator =
        .collection out.cutoff.payload out.cutoff.ledger out.cutoff.saved := by
      rw [hkCut]
      exact out.cutoff.outputCoordinator
    have hlive : B[k.val].input.state.coordinator =
        .live execution.live execution.owned execution.base := by
      rw [hkCut]
      exact execution.actualLive
    exact cutoff_awaited_of_offer B[k.val] out.cutoff.payload out.cutoff.ledger
      out.cutoff.saved s execution.live execution.owned execution.base hnext hlive
      out.cutoffContext.1 i U hUsigma hchannelRecord hexpected
  · exact hawait k (max_le hfk (by omega)) hkn hchannel

/-- Assembly on the maximal actual suffix. Launch recovery is performed
separately by the original-source public root below. -/
private theorem origin_interval_on_launched_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ unmaskedFormedUpTests rate rewards C_star C_h i source)
    (count : ℕ)
    (hcountEq : count = p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h)
    (hcross hspan hshort) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      let J := ActualInitializationPhysicalStep.selectedRowIndex p source
      ∃ hB : out.ell ≤ B.length,
        out.window = B ∧
        ∃ n : Fin out.ell,
          (B[n.val]'(n.isLt.trans_le hB)).input.time = latest ∧
          (∀ k : Fin B.length,
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
              B[k.val].input.time source = some B[k.val] ∧
            B[k.val].input.time.val = s + w + k.val ∧
            B[k.val].input.rows = source.1.2 ∧
            B[k.val].input.selected = J ∧ B[k.val].input.rewards = rewards) ∧
          (n.val = 0 → (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
            (fun t => t.val < latest.val) = ∅) ∧
          (0 < n.val →
            i ∈ (out.ledgers ⟨n.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending ∧
            ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p)
              (U : OrdinaryMessageCodec.UpRecord
                (ReferencePrelaunchFollower.codecParams p rate.eta))
              (j : Fin E.records.length),
              (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i =
                .ordinary state memory ∧
              state.status = .unoccupied ∧
              ActiveFollowerLifecycle.localStateDomainValid state ∧
              state.lastDown = some (out.payload.downRecord i) ∧
              U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
              U.val.sigma = s + 1 ∧
              j.val < w + n.val ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
                (out.payload.downRecord i) ∧
              (∀ j' : Fin E.records.length, j'.val < w + n.val →
                ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
                  (out.payload.downRecord i) → j' = j) ∧
              let f := if j.val < w then 0 else j.val - w + 1
              ∃ hf : f < B.length,
                f ≤ n.val ∧
                B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                (∀ k : Fin B.length, f ≤ k.val → k.val ≤ n.val →
                  ReferenceSelectedAffinePairLaw.selectedChannel p
                    ((source.1.2 J).2 B[k.val].input.time).1 = some (1, i) →
                  ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate B[k.val] i U) ∧
                (∀ v ∈ (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
                    (fun t => t.val < latest.val),
                  ∃ (k : Fin B.length)
                    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                    f ≤ k.val ∧ k.val < n.val ∧ B[k.val].input.time = v ∧
                    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k.val] i = [e] ∧
                    e.time = v ∧ e.sample = ((source.1.2 J).2 v).2 (1, i) ∧
                    e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                      ((B.drop f).take (n.val - f)) i)) := by
  intro s
  obtain ⟨d, horigins⟩ := actual_origin_dispatch
    rate rewards C_star C_h source count hcross hspan hshort
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hwindow : out.window = B := out.windowIsActual
  have hB : out.ell ≤ B.length := by
    rw [← hwindow]
    exact out.withinWindow
  have hlookups := ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_lookup
    rate source rewards C_star C_h count hcross hspan hshort
  have hfields := ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_source_fields
    rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨n, hnTimeStream, hnPending⟩ := formed_test_stream_coordinate
    rate rewards C_star C_h source i count hcross hspan hshort d hcountEq latest hlatest
  have hnB : n.val < B.length := n.isLt.trans_le hB
  have hnTime : B[n.val].input.time = latest := by
    have hget : out.window[n.val]'(n.isLt.trans_le out.withinWindow) = B[n.val] :=
      List.getElem_of_eq hwindow (n.isLt.trans_le out.withinWindow)
    exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => r.input.time) hget).symm.trans hnTimeStream
  refine ⟨d, hB, hwindow, n, hnTime, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hlookups k).1, (hlookups k).2, hfields k⟩
  · exact tests_before_zero_empty rate rewards C_star C_h source i count
      hcross hspan hshort d hcountEq latest n hnTimeStream
  · intro hn
    have hi := hnPending hn
    obtain ⟨_hraw, hformed, hx⟩ := (Finset.mem_filter.mp hlatest).2
    obtain ⟨state, memory, U, j, hstateB, hstatus, hvalid, hdown, hU, hUsigma,
      hjBefore, hjRetained, hunique, hf, hfn, hftime, hfzero, hfone⟩ :=
        horigins n hn i hi latest hnTime hformed hx
    have hawait := actual_every_selected_awaited rate source rewards C_star C_h count
      hcross hspan hshort d n hn i hi state memory hstateB hdown U hU hUsigma
      j hjBefore hjRetained
    have hearlier := earlier_tests_in_retained_prefix rate rewards C_star C_h source
      count hcross hspan hshort d hcountEq i latest n hnTimeStream j hunique
    exact ⟨hi, state, memory, U, j, hstateB, hstatus, hvalid, hdown, hU, hUsigma,
      hjBefore, hjRetained, hunique, hf, hfn, hftime, hfzero, hfone, hawait, hearlier⟩

/-- Original-source unmasked formed-UP origin and receiver interval. The
same reply, retained current-DOWN origin and clipped formation coordinate
serve all selected receivers and all earlier positive tests. -/
theorem actual_unmasked_formed_up_origin_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ unmaskedFormedUpTests rate rewards C_star C_h i source) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let count := p.T - s
    ∃ hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hspan : s + count ≤ p.T,
        ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length < count,
          ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
              (rate := rate) source rewards C_star C_h count hcross hspan hshort,
            let out := d.stream
            let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan
            let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
            let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
            let J := ActualInitializationPhysicalStep.selectedRowIndex p source
            ∃ hB : out.ell ≤ B.length,
              out.window = B ∧
              ∃ n : Fin out.ell,
                (B[n.val]'(n.isLt.trans_le hB)).input.time = latest ∧
                (∀ k : Fin B.length,
                  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                    B[k.val].input.time source = some B[k.val] ∧
                  B[k.val].input.time.val = s + w + k.val ∧
                  B[k.val].input.rows = source.1.2 ∧
                  B[k.val].input.selected = J ∧ B[k.val].input.rewards = rewards) ∧
                (n.val = 0 → (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
                  (fun t => t.val < latest.val) = ∅) ∧
                (0 < n.val →
                  i ∈ (out.ledgers ⟨n.val - 1,
                    Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending ∧
                  ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                    (memory : ActiveFollowerLifecycle.LocalMemory p)
                    (U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta))
                    (j : Fin E.records.length),
                    (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i =
                      .ordinary state memory ∧
                    state.status = .unoccupied ∧
                    ActiveFollowerLifecycle.localStateDomainValid state ∧
                    state.lastDown = some (out.payload.downRecord i) ∧
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    U.val.sigma = s + 1 ∧
                    j.val < w + n.val ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
                      (out.payload.downRecord i) ∧
                    (∀ j' : Fin E.records.length, j'.val < w + n.val →
                      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
                        (out.payload.downRecord i) → j' = j) ∧
                    let f := if j.val < w then 0 else j.val - w + 1
                    ∃ hf : f < B.length,
                      f ≤ n.val ∧
                      B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                      (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                      (∀ k : Fin B.length, f ≤ k.val → k.val ≤ n.val →
                        ReferenceSelectedAffinePairLaw.selectedChannel p
                          ((source.1.2 J).2 B[k.val].input.time).1 = some (1, i) →
                        ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate B[k.val] i U) ∧
                      (∀ v ∈ (unmaskedFormedUpTests rate rewards C_star C_h i source).filter
                          (fun t => t.val < latest.val),
                        ∃ (k : Fin B.length)
                          (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                          f ≤ k.val ∧ k.val < n.val ∧ B[k.val].input.time = v ∧
                          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k.val] i = [e] ∧
                          e.time = v ∧ e.sample = ((source.1.2 J).2 v).2 (1, i) ∧
                          e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                            ((B.drop f).take (n.val - f)) i)) := by
  intro s count
  obtain ⟨hcross, hspan, hshort⟩ := test_launch_window
    rate rewards C_star C_h source i latest hlatest
  exact ⟨hcross, hspan, hshort,
    origin_interval_on_launched_window rate rewards C_star C_h source i latest hlatest
      count rfl hcross hspan hshort⟩

end Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpOrigin
