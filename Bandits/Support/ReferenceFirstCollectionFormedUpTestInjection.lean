/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpEventAdapter
public import Bandits.Support.ReferenceFirstCollectionFormedStagePositiveEntry

import Lean.Elab.Tactic.Omega

/-!
# Actual formed-UP tests in the first collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionFormedUpTestInjection

variable {p : ConstructorDimensions.Parameters}

/-- Literal first-collection FORMED-stage positive tests on the original
physical calendar. The detecting mask is the existing OLD `Pdetect` mask. -/
def formedUpTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (source : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  (Finset.univ : Finset (Fin p.T)).filter fun t =>
    i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) t.val source ∧
    source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t ∧
    ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val source = true

/-- A FORMED test remains localized by the existing original-source pending
mask to the first collection window of the complete physical suffix. -/
theorem formed_up_test_localizes_to_first_collection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (ht : t ∈ formedUpTests (p := p) rate rewards C_star C_h i source) :
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
  have hmember : t ∈ (Finset.univ : Finset (Fin p.T)).filter (fun t =>
      i ∈ ReferenceFirstCollectionDetectedQueueMask.Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) t.val source ∧
      source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
        (p := p) (rate := rate) rewards C_star C_h i t ∧
      ReferenceFirstCollectionRoundEndObservation.x
        (rate := rate) rewards C_star C_h i t.val source = true) := ht
  rcases Finset.mem_filter.mp hmember with ⟨_, htest⟩
  rcases htest with ⟨hdetect, _hformed, _hx⟩
  have hraw : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val source).Nonempty := by
    refine ⟨i, ?_⟩
    exact (ReferenceFirstCollectionDetectedQueueMask.Pdetect_subset_Praw
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val source) hdetect
  exact ReferenceFirstCollectionPendingObservation.Praw_localization
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    t source hraw

/-- Calendar dates order localized tests strictly before the actual window
coordinate of a latest selected test. -/
private theorem formed_up_test_strictly_precedes_latest_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest t : Fin p.T)
    (records window : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (start cutoff : ℕ)
    (hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = records)
    (hcutoff : cutoff =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)
    (hwindow : window = ReferenceCollectionPhaseHistory.collectionWindow records cutoff)
    (hdate : ∀ n : Fin window.length,
      window[n.val].input.time.val + 1 = start + cutoff + 1 + n.val)
    (n : Fin window.length)
    (hlatest : window[n.val].input.time = latest)
    (htest : t ∈ formedUpTests (p := p) rate rewards C_star C_h i source)
    (hbefore : t.val < latest.val) :
    ∃ q : Fin window.length,
      q.val < n.val ∧
        window[q.val].input.time = t := by
  obtain ⟨jRaw, hjTimeRaw⟩ := formed_up_test_localizes_to_first_collection
    rate rewards C_star C_h i source t htest
  have hfullWindow : ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)).length = window := by
    calc
      _ = ReferenceCollectionPhaseHistory.collectionWindow records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length := by
        rw [hrecords]
      _ = ReferenceCollectionPhaseHistory.collectionWindow records cutoff :=
        congrArg (ReferenceCollectionPhaseHistory.collectionWindow records) hcutoff.symm
      _ = window := hwindow.symm
  have hlocB : ∃ q : Fin window.length, window[q.val].input.time = t := by
    have hlen : (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)).length).length = window.length :=
      congrArg List.length hfullWindow
    have hqBound : jRaw.val < window.length := by omega
    let q : Fin window.length := ⟨jRaw.val, hqBound⟩
    have hget :
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)).length)[jRaw.val]'jRaw.isLt =
          window[q.val]'q.isLt := List.getElem_of_eq hfullWindow jRaw.isLt
    refine ⟨q, ?_⟩
    exact (congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input.time) hget).symm.trans hjTimeRaw
  rcases hlocB with ⟨q, hqTime⟩
  have hqCalendar : t.val + 1 = start + cutoff + 1 + q.val := by
    calc
      t.val + 1 = window[q.val].input.time.val + 1 :=
        congrArg (fun time : Fin p.T => time.val + 1) hqTime.symm
      _ = start + cutoff + 1 + q.val := hdate q
  have hlatestCalendar : latest.val + 1 = start + cutoff + 1 + n.val := by
    calc
      latest.val + 1 = window[n.val].input.time.val + 1 :=
        congrArg (fun time : Fin p.T => time.val + 1) hlatest.symm
      _ = start + cutoff + 1 + n.val := hdate n
  refine ⟨q, ?_, hqTime⟩
  omega

private theorem actualRecord_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[n.val].input.time
      source = some (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[n.val] ∧
    (ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan)[n.val].input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch
            (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1 + n.val := by
  let s := ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) source rewards C_star C_h
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceFirstCollectionReadyStream.actualWindow
    (rate := rate) source rewards C_star C_h hcross count hspan
  have hwindow := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hactive :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have htime : B[n.val].input.time.val = s + (w + n.val) := by
    have ht := hwindow.2.1
    change B[n.val].input.time.val + 1 = s + w + 1 + n.val at ht
    omega
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + n.val < count := by
    have hb' := (List.getElem?_eq_some_iff.mp hwindow.1).1
    have hb : w + n.val < E.records.length := by
      simpa only [E, w, ReferenceFirstCollectionReadyStream.actualEpoch] using hb'
    omega
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) hactive := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hactive count
      (by simpa only [s, ReferenceFirstCollectionReadyStream.startTime] using hspan)
      ⟨w + n.val, hindex⟩
    apply Option.some.inj
    calc
      some B[n.val] = E.records[w + n.val]? := hwindow.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, initial,
          ReferenceFirstCollectionReadyStream.actualEpoch,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h B[n.val].input.time source initial hlaunch
    (by rw [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime]; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[n.val].input.time source =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hactive) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime, Nat.add_sub_cancel_left] using hsource
  refine ⟨?_, ?_⟩
  · simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow] using
      hsource'.trans (congrArg some hrecordAt.symm)
  · simpa only [B, E, w, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hwindow.2.1

private theorem record_positive_shape
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [] ∨
      ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [e] ∧
        e.time = r.input.time := by
  cases hd : r.output.coordinator.up with
  | none =>
      exact Or.inl (by simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd])
  | some diagnostic =>
      obtain ⟨_, _, _, _, htime, _⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hd
      by_cases hi : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower diagnostic = i
      · by_cases he : AffineBatchDecoder.eligible
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input
              (ReferenceCoordinatorUpDecoderReplay.retainedUpTime diagnostic))
        · right
          refine ⟨AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            (ReferenceCoordinatorUpDecoderReplay.retainedUpTime diagnostic), ?_, ?_⟩
          · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
              hd, hi, ↓reduceIte, AffineBatchDecoder.positiveAt, he]
          · exact htime
        · left
          simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            hd, hi, ↓reduceIte, AffineBatchDecoder.positiveAt, he]
      · left
        simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hd, hi, ↓reduceIte]

private theorem retained_positives_pairwise
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (htimes : records.Pairwise (fun a b => a.input.time.val < b.input.time.val)) :
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).Pairwise
      (fun a b => a.time.val < b.time.val) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro r _hr
    rcases record_positive_shape r i with hnil | ⟨e, he, _htime⟩
    · rw [hnil]
      exact List.Pairwise.nil
    · rw [he]
      simp
  · apply htimes.imp_of_mem
    intro a b _ha _hb hab x hx y hy
    rcases record_positive_shape a i with hnil | ⟨e, he, htime⟩
    · rw [hnil] at hx
      cases hx
    · rw [he, List.mem_singleton] at hx
      subst x
      rcases record_positive_shape b i with hnil | ⟨e', he', htime'⟩
      · rw [hnil] at hy
        cases hy
      · rw [he', List.mem_singleton] at hy
        subst y
        simpa only [htime, htime'] using hab

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
    (t : Fin p.T) (ht : t ∈ formedUpTests rate rewards C_star C_h i source) :
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
  obtain ⟨hdetect, _hformed, _hx⟩ := (Finset.mem_filter.mp ht).2
  have hraw : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val source :=
    ReferenceFirstCollectionDetectedQueueMask.Pdetect_subset_Praw
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val source hdetect
  have hloc := formed_up_test_localizes_to_first_collection
    rate rewards C_star C_h i source t ht
  let observed := fun records : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
  have hlocE : observed E.records := Eq.mp (congrArg observed hrecords) hloc
  obtain ⟨k, hkTime⟩ : ∃ k : Fin B.length, B[k.val].input.time = t := hlocE
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

private theorem stream_pending_predecessor
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (q : ℕ) (hq : 1 < q) (hqell : q < out.ell) :
    (out.ledgers ⟨q - 1, by omega⟩).pending ⊆
      (out.ledgers ⟨q - 2, by omega⟩).pending := by
  let n : Fin out.ell := ⟨q - 1, by omega⟩
  obtain ⟨_j, r, incoming, cell, _hj, _hr, hservice, hincoming⟩ :=
    out.cell_at n (by dsimp only [n]; omega)
  intro i hi
  have hmember : i ∈ cell.serviceLedger.pending := by
    simpa only [hservice] using hi
  rw [ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell] at hmember
  have hsubset : ReferenceCollectionPhaseHistory.eraseEvent incoming.pending
      (ReferenceCollectionPhaseHistory.acceptedLabel r.input) ⊆ incoming.pending := by
    cases he : ReferenceCollectionPhaseHistory.acceptedLabel r.input with
    | none => simp [ReferenceCollectionPhaseHistory.eraseEvent]
    | some label => exact Finset.erase_subset label incoming.pending
  simpa [hincoming, n, Nat.sub_sub] using hsubset hmember

private theorem stream_pending_subset
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (first last : ℕ) (hfirst : 1 ≤ first) (hle : first ≤ last)
    (hlast : last < out.ell) :
    (out.ledgers ⟨last - 1, by omega⟩).pending ⊆
      (out.ledgers ⟨first - 1, by omega⟩).pending := by
  induction last generalizing first with
  | zero => omega
  | succ q ih =>
      by_cases hsame : first = q + 1
      · subst first
        exact Finset.Subset.rfl
      · have hprev := stream_pending_predecessor out (q + 1) (by omega) (by omega)
        have hrest := ih first hfirst (by omega) (by omega)
        have hprev' : (out.ledgers ⟨q, by omega⟩).pending ⊆
            (out.ledgers ⟨q - 1, by omega⟩).pending := by
          simpa only [Nat.add_sub_cancel, show q + 1 - 2 = q - 1 by omega] using hprev
        exact hprev'.trans hrest

private theorem test_launch_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ formedUpTests rate rewards C_star C_h i source) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let count := p.T - s
    ∃ hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hspan : s + count ≤ p.T,
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length < count := by
  intro s count
  obtain ⟨hdetect, _hformed, _hx⟩ := (Finset.mem_filter.mp hlatest).2
  have hraw : i ∈ ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h latest.val source :=
    ReferenceFirstCollectionDetectedQueueMask.Pdetect_subset_Praw
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      latest.val source hdetect
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
    (formedUpTests rate rewards C_star C_h i source).filter
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
      (Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow)).input.time = latest)
    (hi : i ∈ (d.stream.ledgers ⟨n.val - 1,
      Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending) :
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
      let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((B.drop f).take (n.val - f)) i
    Pn.Pairwise (fun a b => a.time.val < b.time.val) ∧
    (∀ v ∈ (formedUpTests rate rewards C_star C_h i source).filter
        (fun t => t.val < latest.val),
      ∃ (k : Fin B.length) (hkn : k.val < n.val),
        f ≤ k.val ∧ B[k.val].input.time = v ∧
        (∀ k' : Fin B.length, B[k'.val].input.time = v → k' = k) ∧
        (0 < k.val →
          i ∈ (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt
            (Nat.sub_le k.val 1) (Nat.lt_trans hkn n.isLt)⟩).pending) ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 J).2 v).1 = some (1, i) ∧
        ReferenceActiveAffinePositiveTest.upPositive B[k.val].input = true ∧
        ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
            B[k.val] i = [e] ∧
          e.time = v ∧
          e.sample = ((source.1.2 J).2 v).2 (1, i) ∧ e ∈ Pn) ∧
    ((formedUpTests rate rewards C_star C_h i source).filter
      (fun t => t.val < latest.val)).card ≤ Pn.length := by
  intro out E w B J j hunique f Pn
  have hwindow : out.window = B := out.windowIsActual
  have hBlength : out.ell ≤ B.length := by
    rw [← hwindow]
    exact out.withinWindow
  have hdate : ∀ k : Fin B.length,
      B[k.val].input.time.val + 1 =
        ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h +
          w + 1 + k.val := by
    intro k
    exact (ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
      rate source rewards C_star C_h count hcross hspan hshort k).2.1
  have hBtimes : B.Pairwise (fun a b => a.input.time.val < b.input.time.val) := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb hab
    have hda := hdate ⟨a, ha⟩
    have hdb := hdate ⟨b, hb⟩
    dsimp only [Fin.val_mk] at hda hdb
    omega
  have hpair : Pn.Pairwise (fun a b => a.time.val < b.time.val) :=
    retained_positives_pairwise _ i (hBtimes.drop.take)
  have htests : ∀ v ∈ (formedUpTests rate rewards C_star C_h i source).filter
      (fun t => t.val < latest.val),
      ∃ (k : Fin B.length) (hkn : k.val < n.val),
        f ≤ k.val ∧ B[k.val].input.time = v ∧
        (∀ k' : Fin B.length, B[k'.val].input.time = v → k' = k) ∧
        (0 < k.val → i ∈ (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt
          (Nat.sub_le k.val 1) (Nat.lt_trans hkn n.isLt)⟩).pending) ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 J).2 v).1 = some (1, i) ∧
        ReferenceActiveAffinePositiveTest.upPositive B[k.val].input = true ∧
        ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k.val] i = [e] ∧
          e.time = v ∧ e.sample = ((source.1.2 J).2 v).2 (1, i) ∧ e ∈ Pn := by
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
    obtain ⟨_hvDetect, hvFormed, hvX⟩ := (Finset.mem_filter.mp hvTest).2
    obtain ⟨rv, hrv, _hrvTime, _hrvRows, _hrvSelected, _hrvRewards,
      oldv, memoryv, holdv, hacceptedv, _hnotnonev, hchannelv, hpositivev,
      e, he, heTime, heSample⟩ :=
      ReferenceFirstCollectionFormedStagePositiveEntry.actual_formed_stage_positive_entry
        rate rewards C_star C_h source i v hvFormed hvX
    have hrecordK := actualRecord_window
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
    have hkUnique : ∀ k' : Fin B.length, B[k'.val].input.time = v → k' = k := by
      intro k' hk'Time
      apply Fin.ext
      have hd := hdate k
      have hd' := hdate k'
      have ht : B[k'.val].input.time = B[k.val].input.time := hk'Time.trans hkTime.symm
      rw [ht] at hd'
      omega
    have hiEarlier : 0 < k.val → i ∈ (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt
        (Nat.sub_le k.val 1) (Nat.lt_trans hkn n.isLt)⟩).pending := by
      intro hkpos
      exact stream_pending_subset out k.val n.val hkpos (Nat.le_of_lt hkn) n.isLt hi
    refine ⟨k, hkn, hfk, hkTime, hkUnique, hiEarlier, hchannelv, hpositivev,
      e, he, heTime, heSample, ?_⟩
    exact singleton_mem_retained_slice B i f n.val k.val k.isLt hfk hkn e he
  have hsubset : (formedUpTests rate rewards C_star C_h i source).filter
      (fun t => t.val < latest.val) ⊆ (Pn.map (fun e => e.time)).toFinset := by
    intro v hv
    obtain ⟨_k, _hkn, _hfk, _hkTime, _hkUnique, _hiEarlier, _hchannelv,
      _hpositivev, e, _he, heTime, _heSample, heMem⟩ := htests v hv
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, heMem, heTime⟩)
  have hcard : ((formedUpTests rate rewards C_star C_h i source).filter
      (fun t => t.val < latest.val)).card ≤ Pn.length := by
    exact (Finset.card_le_card hsubset).trans
      (by simpa only [List.length_map] using (Pn.map (fun e => e.time)).toFinset_card_le)
  exact ⟨hpair, htests, hcard⟩

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

private theorem test_injection_on_launched_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ formedUpTests rate rewards C_star C_h i source)
    (count : ℕ)
    (hcountEq : count = p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (hcross hspan hshort) :
    let s := ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross
      let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
      let J := ActualInitializationPhysicalStep.selectedRowIndex p source
      let X (t : ℕ) (hwt : w + t ≤ count) :=
        (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
          (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
      ∃ hlen : w + out.ell ≤ count,
        ∃ hBlength : out.ell ≤ B.length,
          out.window = B ∧
          ∃ n : Fin out.ell,
            (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.time = latest ∧
            (n.val = 0 →
              (formedUpTests rate rewards C_star C_h i source).filter
                (fun t => t.val < latest.val) = ∅) ∧
            (0 < n.val →
              i ∈ (out.ledgers ⟨n.val - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending ∧
              ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.lastDown = some (out.payload.downRecord i) ∧
                (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state =
                  X n.val (Nat.le_trans
                    (Nat.add_le_add_left (Nat.le_of_lt n.isLt) w) hlen) ∧
                ∃ (U : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta))
                  (j : Fin E.records.length),
                  U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                  1 ≤ U.val.sigma ∧
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
                    let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                      ((B.drop f).take (n.val - f)) i
                    Pn.Pairwise (fun a b => a.time.val < b.time.val) ∧
                    (∀ v ∈ (formedUpTests rate rewards C_star C_h i source).filter
                        (fun t => t.val < latest.val),
                      ∃ (k : Fin B.length) (hkn : k.val < n.val),
                        f ≤ k.val ∧ B[k.val].input.time = v ∧
                        (∀ k' : Fin B.length, B[k'.val].input.time = v → k' = k) ∧
                        (0 < k.val →
                          i ∈ (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt
                            (Nat.sub_le k.val 1) (Nat.lt_trans hkn n.isLt)⟩).pending) ∧
                        ReferenceSelectedAffinePairLaw.selectedChannel p
                          ((source.1.2 J).2 v).1 = some (1, i) ∧
                        ReferenceActiveAffinePositiveTest.upPositive B[k.val].input = true ∧
                        ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
                          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
                            B[k.val] i = [e] ∧
                          e.time = v ∧
                          e.sample = ((source.1.2 J).2 v).2 (1, i) ∧ e ∈ Pn) ∧
                    ((formedUpTests rate rewards C_star C_h i source).filter
                      (fun t => t.val < latest.val)).card ≤ Pn.length) := by
  intro s
  obtain ⟨_hdetect, hformed, hx⟩ := (Finset.mem_filter.mp hlatest).2
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  obtain ⟨d, hdata⟩ :=
    ReferenceFirstCollectionFormationOrigin.actual_initialized_first_collection_formation_origin
      rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hdata
  obtain ⟨_registers, _owned, _base, _cutRecord,
    _hcutIndex, _hcutState, _hpayload, _hpending, hqueries⟩ := hdata
  let out := d.stream
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let X (t : ℕ) (hwt : w + t ≤ count) :=
    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
      (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
  have hwindow : out.window = B := out.windowIsActual
  have hBlength : out.ell ≤ B.length := by
    rw [← hwindow]
    exact out.withinWindow
  have hlen : w + out.ell ≤ count := by
    let last : Fin out.window.length :=
      ⟨out.ell - 1, lt_of_lt_of_le (Nat.sub_lt out.positiveLength (by decide)) out.withinWindow⟩
    have hindex := (List.getElem?_eq_some_iff.mp (out.alignment last).1).1
    change w + (out.ell - 1) < E.records.length at hindex
    have hpos := out.positiveLength
    omega
  obtain ⟨n, hnTimeStream, hnPending⟩ := formed_test_stream_coordinate
    rate rewards C_star C_h source i count hcross hspan hshort d hcountEq latest hlatest
  have hnB : n.val < B.length := lt_of_lt_of_le n.isLt hBlength
  have hnTime : B[n.val].input.time = latest := by
    have hget : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = B[n.val] :=
      List.getElem_of_eq hwindow (lt_of_lt_of_le n.isLt out.withinWindow)
    exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => r.input.time) hget).symm.trans hnTimeStream
  have hnoEarlier := tests_before_zero_empty
    rate rewards C_star C_h source i count hcross hspan hshort d hcountEq latest n hnTimeStream
  refine ⟨d, hlen, hBlength, hwindow, n, hnTime, hnoEarlier, ?_⟩
  intro hn
  have hi := hnPending hn
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
  have hwindowRecord := actualRecord_window
    rate source rewards C_star C_h count hcross hspan hshort ⟨n.val, hnB⟩
  have hactualB : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h latest source = some B[n.val] := by
    rw [← hnTime]
    exact hwindowRecord.1
  have hnotnone := formed_record_lastDown_ne_none
    rate rewards C_star C_h source i latest B[n.val] hactualB state memory hstateB hformed hx
  have hlastDown : state.lastDown = some (out.payload.downRecord i) := by
    rcases hlast with hnone | hcurrent
    · exact False.elim (hnotnone hnone.1)
    · exact hcurrent
  obtain ⟨U, hU, hUpositive, _hUactual⟩ := hup hlastDown
  obtain ⟨_hsigma, _hstart, jNat, acceptedRecord, hjBefore, hjLookup,
    hjRetained, _hacceptance, _hjtime, _hjrows, _hjselected, _hjrewards,
    hjUnique, hformation⟩ := horigin hlastDown
  have hjIndex : jNat < E.records.length := (List.getElem?_eq_some_iff.mp hjLookup).1
  let j : Fin E.records.length := ⟨jNat, hjIndex⟩
  have hjGet : E.records[j.val] = acceptedRecord :=
    (List.getElem?_eq_some_iff.mp hjLookup).2
  have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
      (out.payload.downRecord i) := by
    rw [hjGet]
    exact hjRetained
  have hunique : ∀ j' : Fin E.records.length, j'.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
        (out.payload.downRecord i) → j' = j := by
    intro j' hj' hr'
    apply Fin.ext
    exact hjUnique j'.val E.records[j'.val] hj'
      (List.getElem?_eq_getElem j'.isLt) hr'
  let f := if j.val < w then 0 else j.val - w + 1
  obtain ⟨hf, hfn, hftime, hfzero, hfone⟩ := hformation
  have hstateX : B[n.val].input.state = X n.val
      (Nat.le_trans (Nat.add_le_add_left (Nat.le_of_lt n.isLt) w) hlen) :=
    (ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
      rate source rewards C_star C_h count hcross hspan hshort ⟨n.val, hnB⟩).1
  let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
    ((B.drop f).take (n.val - f)) i
  obtain ⟨hpair, htests, hcard⟩ := earlier_tests_in_retained_prefix
    rate rewards C_star C_h source count hcross hspan hshort d hcountEq i latest n
    hnTimeStream hi j hunique
  exact ⟨hi, state, memory, hstateB, hstatus, hvalid, hlastDown, hstateX,
    U, j, hU, hUpositive, hjBefore, hretained, hunique,
    hf, hfn, hftime, hfzero, hfone, hpair, htests, hcard⟩


/-- Every strictly earlier literal FORMED test contributes its actual stamped
entry to the latest test's same retained UP prefix. This is internal counting
evidence on the original source, without a decoder-success premise. -/
theorem actual_first_collection_formed_up_test_injection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ formedUpTests rate rewards C_star C_h i source) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
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
            let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross
            let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1
            let J := ActualInitializationPhysicalStep.selectedRowIndex p source
            let X (t : ℕ) (hwt : w + t ≤ count) :=
              (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
                (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
            ∃ hlen : w + out.ell ≤ count,
              ∃ hBlength : out.ell ≤ B.length,
                out.window = B ∧
                ∃ n : Fin out.ell,
                  (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.time = latest ∧
                  (n.val = 0 →
                    (formedUpTests rate rewards C_star C_h i source).filter
                      (fun t => t.val < latest.val) = ∅) ∧
                  (0 < n.val →
                    i ∈ (out.ledgers ⟨n.val - 1,
                      Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending ∧
                    ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                      (memory : ActiveFollowerLifecycle.LocalMemory p),
                      (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i =
                        .ordinary state memory ∧
                      state.status = .unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      state.lastDown = some (out.payload.downRecord i) ∧
                      (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state =
                        X n.val (Nat.le_trans
                          (Nat.add_le_add_left (Nat.le_of_lt n.isLt) w) hlen) ∧
                      ∃ (U : OrdinaryMessageCodec.UpRecord
                          (ReferencePrelaunchFollower.codecParams p rate.eta))
                        (j : Fin E.records.length),
                        U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                        1 ≤ U.val.sigma ∧
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
                          let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                            ((B.drop f).take (n.val - f)) i
                          Pn.Pairwise (fun a b => a.time.val < b.time.val) ∧
                          (∀ v ∈ (formedUpTests rate rewards C_star C_h i source).filter
                              (fun t => t.val < latest.val),
                            ∃ (k : Fin B.length) (hkn : k.val < n.val),
                              f ≤ k.val ∧ B[k.val].input.time = v ∧
                              (∀ k' : Fin B.length, B[k'.val].input.time = v → k' = k) ∧
                              (0 < k.val →
                                i ∈ (out.ledgers ⟨k.val - 1, Nat.lt_of_le_of_lt
                                  (Nat.sub_le k.val 1) (Nat.lt_trans hkn n.isLt)⟩).pending) ∧
                              ReferenceSelectedAffinePairLaw.selectedChannel p
                                ((source.1.2 J).2 v).1 = some (1, i) ∧
                              ReferenceActiveAffinePositiveTest.upPositive B[k.val].input = true ∧
                              ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
                                ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
                                  B[k.val] i = [e] ∧
                                e.time = v ∧
                                e.sample = ((source.1.2 J).2 v).2 (1, i) ∧ e ∈ Pn) ∧
                          ((formedUpTests rate rewards C_star C_h i source).filter
                            (fun t => t.val < latest.val)).card ≤ Pn.length) := by
  intro s count
  obtain ⟨hcross, hspan, hshort⟩ := test_launch_window
    rate rewards C_star C_h source i latest hlatest
  exact ⟨hcross, hspan, hshort, test_injection_on_launched_window
    rate rewards C_star C_h source i latest hlatest count rfl hcross hspan hshort⟩

end Bandits.Support.ReferenceFirstCollectionFormedUpTestInjection

end
