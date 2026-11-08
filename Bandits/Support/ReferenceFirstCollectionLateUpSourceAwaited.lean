/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateUpWindowAcceptance
public import Bandits.Support.ReferenceGeneratedUpUnoccupiedGuard
public import Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

/-!
# Original-source late first-collection awaited UP traces

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,240-296,327-348`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,28-79,92-109,139-157`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The exports retain the original initialization source, whole reward grid,
actual continuous rows, and the focal follower's carried state. They produce
an awaited UP trace on the actual late first-collection branch and transport
an explicitly ambiguous actual second batch to the literal original-source
survival event. Sender and receiver operation facts are produced from the
actual run, including selected zero-observation rounds. The second export
retains its ordinary coordinator, current positivity, exact count, and explicit
ambiguity event restrictions. No service or probability conclusion is claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceCoordinatorUpIntervalWindow
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceGeneratedUpUnoccupiedGuard
open Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

namespace Bandits.Support.ReferenceFirstCollectionLateUpSourceAwaited

open scoped Classical

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) active).records := by
  revert hspan hn
  induction total with
  | zero =>
      intro hspan hn
      have hn0 : n = 0 := by omega
      subst n
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ total ih =>
      intro hspan hn
      by_cases heq : n = total + 1
      · subst n
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hn' : n ≤ total := by omega
        rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn')]
        exact ih (by omega) hn'

private theorem run_record_at
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hi : index < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows selected rewards start index (by omega) active) := by
  have h := congrArg (fun records => records[index]?)
    (run_prefix_records initial rows selected rewards start total hspan active
      (index + 1) hi)
  rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt] at h
  simpa [ReferenceActivePhysicalHorizon.run_record_count] using h

private theorem original_input_eq_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s) :
    (originalSourceRunInput (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i ⟨source, hz⟩).val =
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross,
        source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards) := by
  apply Prod.ext
  · have hlaunch := originalSourceRunInput_launch (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i ⟨source, hz⟩
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hlaunch).symm
  · rfl

private theorem collection_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (htail : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    ∃ selected : ReferenceActivePhysicalStep.Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      selected.view.payload = payload := by
  have hnotnone : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    intro hnone
    simp only [ReferenceCollectionPhaseHistory.executedTail, hnone, ite_true] at htail
    cases htail
  have hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hd : (ReferenceActivePhysicalStep.prepare x).coordinator = .invalidCollectionCutoff := by
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, dite_eq_right hbad]
    simp only [hd, ReferenceActivePhysicalStep.DispatchCut.selection] at hnotnone
    exact hnotnone rfl
  cases ho : CoordinatorRoundDispatch.dispatch
      (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
        ⟨ledger.cutoff - 1, by omega⟩)) with
  | collection outcome =>
    have hd : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger _ _ outcome := by
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, dite_eq_left hcut, ho]
      rfl
    cases outcome with
    | continuing core snapshot boundary scores =>
      obtain ⟨selected, hselected⟩ := Option.ne_none_iff_exists.mp hnotnone
      refine ⟨selected, hselected.symm, ?_⟩
      rw [hd] at hselected
      have heq := Option.some.inj hselected
      exact (congrArg (fun picked : ReferenceActivePhysicalStep.Selection x =>
        picked.view.payload) heq)
    | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hd] at htail

private theorem source_channel_draws
    (slice : ContinuousLearningRows.Slice p) (i : Fin (p.m - 1))
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p slice = some (1, i)) :
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice = i := by
  have hdraw : ReferenceSelectedAffinePairLaw.channelFromDraws p
      (PublicDiscreteDraws.slotDraw slice,
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice) = some (1, i) :=
    hchannel
  by_cases hup : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot
  · rw [hup, ReferenceSelectedAffinePairLaw.channelFromDraws] at hdraw
    dsimp only at hdraw
    have hi := congrArg Prod.snd (Option.some.inj hdraw)
    exact ⟨hup, hi⟩
  · by_cases hdown : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.downSlot
    · rw [hdown, ReferenceSelectedAffinePairLaw.channelFromDraws] at hdraw
      dsimp only at hdraw
      have hfalse : (0 : Fin 2) = 1 := congrArg Prod.fst (Option.some.inj hdraw)
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hfalse)
    · rw [ReferenceSelectedAffinePairLaw.channelFromDraws] at hdraw
      simp only [ite_eq_right hdown, ite_eq_right hup] at hdraw
      cases hdraw

private theorem late_record_index
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b n : ℕ) (hbound : b + n ≤ total)
    (window : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hn : n ≤ window.length)
    (hlookup : ∀ h (hh : h < window.length),
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[b + h]? =
        some (window[h]'hh))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (p.T - start) (by omega) active).records)
    (hlower : start + b ≤ record.input.time.val)
    (hupper : record.input.time.val < start + b + n) :
    ∃ (h : ℕ) (_hh : h < n) (hwindow : h < window.length), record = window[h]'hwindow := by
  let h := record.input.time.val - (start + b)
  have hh : h < n := by omega
  have hw : h < window.length := lt_of_lt_of_le hh hn
  have hget := hlookup h hw
  have hfullSpan : start + (p.T - start) ≤ p.T := by omega
  have htotal : total ≤ p.T - start := by omega
  have hi : b + h < total := lt_of_lt_of_le (Nat.add_lt_add_left hh b) hbound
  have hactual : ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
      start (b + h) (by omega) active = window[h]'hw := by
    have ha := run_record_at initial rows selected rewards start total hspan active (b + h) hi
    exact Option.some.inj (ha.symm.trans hget)
  have htime : (window[h]'hw).input.time.val = start + b + h := by
    rw [← hactual]
    change start + (b + h) = start + b + h
    omega
  have hwindowMem : window[h]'hw ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start (p.T - start) hfullSpan active).records := by
    apply List.mem_of_getElem?
    rw [← hactual]
    exact run_record_at initial rows selected rewards start (p.T - start) hfullSpan active
      (b + h) (lt_of_lt_of_le hi htotal)
  refine ⟨h, hh, hw, ?_⟩
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows selected rewards
    start (p.T - start) hfullSpan active hrecord hwindowMem (by rw [htime]; omega)

private theorem record_eq_of_input_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinput : left.input = right.input) : left = right := by
  cases left with
  | mk x output houtput =>
    cases right with
    | mk y output' houtput' =>
      dsimp only at hinput
      cases hinput
      cases houtput
      cases houtput'
      rfl

private theorem current_record_eq_at
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z =
      let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
      ReferenceAssignmentPayloadChronology.actualRunRecordAt input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s (t.val - s) (by omega) input.property := by
  have he : (⟨s + (t.val - s), by omega, by omega⟩ :
      ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ :=
    Subtype.ext (Nat.add_sub_of_le hs)
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let prior := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input
  apply record_eq_of_input_eq
  change ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s input.property prior ⟨t.val, hs, t.isLt⟩ =
    ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s input.property prior ⟨s + (t.val - s), by omega, by omega⟩
  exact congrArg (ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s input.property prior) he.symm

private theorem current_record_mem_full
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z ∈
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records := by
  dsimp only
  rw [current_record_eq_at]
  apply List.mem_of_getElem?
  exact run_record_at _ _ _ _ s (p.T - s) (by omega) _ (t.val - s) (by omega)

private theorem decisionTime_drop_of_last_positive
    (trace : AffineBatchDecoder.Trace p) (rounds : List (Fin p.T)) (time : Fin p.T)
    (hrounds : ∃ before, rounds = before ++ [time])
    (heligible : AffineBatchDecoder.eligible (trace time))
    (offset : ℕ) (hoffset : offset < (AffineBatchDecoder.positives p trace rounds).length) :
    AffineBatchDecoder.decisionTime
      ((AffineBatchDecoder.positives p trace rounds).drop offset) = some time := by
  obtain ⟨before, rfl⟩ := hrounds
  have hlen : ¬ ((AffineBatchDecoder.positives p trace (before ++ [time])).map
      AffineBatchDecoder.Entry.time).length ≤ offset := by
    simpa only [List.length_map] using Nat.not_le.mpr hoffset
  simp only [AffineBatchDecoder.decisionTime, List.map_drop, List.getLast?_drop,
    ite_eq_right hlen]
  simp [AffineBatchDecoder.positives, List.filter_append, heligible,
    AffineBatchDecoder.entry]

/-- Conditional local induction: each incoming collection and executed tail
is supplied for the actual original record. The guard theorem produces all
follower operation domains and preserves the fixed positive-start reply. -/
private theorem original_unoccupied_interval
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (b n : ℕ) (hspan : s + (b + n) ≤ p.T)
    (out : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActiveHorizonMeasurability.runOfInput s b (by omega)
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).finalState.followers i =
        .ordinary out memory)
    (hstatus : out.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart out)
    (hstart : payload.sigma.val + 1 ≤ ReferencePrelaunchFollower.acceptedStart out)
    (hcollection : ∀ h (hh : h < n),
      let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (b + h) (by omega) input.property
      ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
          (tail : ReferenceCollectionPhaseHistory.Tail record.input),
        record.input.state.coordinator = .collection payload ledger saved ∧
        ReferenceCollectionPhaseHistory.executedTail record.input = some tail) :
    ∃ endpoint endpointMemory,
      (ReferenceActiveHorizonMeasurability.runOfInput s (b + n) hspan
        (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).finalState.followers i =
          .ordinary endpoint endpointMemory ∧
      endpoint.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply endpoint = ReferenceFollowerReplyChronology.reply out := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hprefix : ∀ h (hh : h ≤ n), ∃ state stateMemory,
      (ReferenceActiveHorizonMeasurability.runOfInput s (b + h) (by omega) input).finalState.followers i =
        .ordinary state stateMemory ∧ state.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply out := by
    intro h
    induction h with
    | zero =>
      intro _
      exact ⟨out, memory, hseed, hstatus, rfl⟩
    | succ h ih =>
      intro hh
      obtain ⟨state, stateMemory, hord, hstateStatus, hreply⟩ := ih (by omega)
      obtain ⟨ledger, saved, tail, hcoord, htail⟩ := hcollection h (by omega)
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (b + h) (by omega) input.property
      obtain ⟨selected, hselected, hpayload⟩ :=
        collection_selection_payload record.input payload ledger saved hcoord tail htail
      have hpositiveState : 1 ≤ ReferencePrelaunchFollower.acceptedStart state := by
        rw [ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply]
        exact hpositive
      have hfront : selected.view.payload.sigma.val + 1 ≤
          ReferencePrelaunchFollower.acceptedStart state := by
        rw [hpayload, ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply]
        exact hstart
      obtain ⟨_hprepared, post, hnext, _hfailure, hpostReply, hpostStatus,
          _hmarker, _hbuffer, _hdomain, _hchronology, _htimes, _hbatch, _hreset⟩ :=
        original_source_unoccupied_step_of_selected_start_le rewards C_star C_h q t s hs
          control0 i z (b + h) (by omega) state stateMemory hord hstateStatus
          hpositiveState selected hselected hfront
      refine ⟨post, stateMemory, ?_, hpostStatus, hpostReply.trans hreply⟩
      change (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
        input.val.2.2.2 s (b + (h + 1)) (by omega) input.property).finalState.followers i = _
      have hfinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (b + h)
        (by omega) input.property
      have hsuccessor : (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
          input.val.2.2.1 input.val.2.2.2 s (b + (h + 1)) (by omega)
          input.property).finalState = record.output.next := by
        simpa only [Nat.add_assoc] using hfinal
      rw [hsuccessor]
      exact hnext
  exact hprefix n le_rfl

/-- The late retained-DOWN record keeps the single original cutoff payload.
For each retained query, the focal follower's positive-start unoccupied reply
is extended through every ordinary coordinator prefix. A later successful UP
reception is counted from `acceptedLabels`; otherwise the actual original
source is awaited through the selected UP rounds up to the query time.
-/
theorem actual_late_up_source_awaited_cases
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < E.records.length, cutoffRecord = E.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∀ k : Fin B.length,
        E.records[w + k.val]? = some B[k.val] ∧ B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        r.output.next.followers i = .dagger ∨
        r.output.next.coordinator = .dagger ∨
        ∃ (out : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (l0 : ReferenceActivePhysicalStep.Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.output.next.followers i = .ordinary out memory ∧
          r.output.next.coordinator = .collection P0 l0 saved ∧
          out.status = .unoccupied ∧
          let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
          ReferenceFollowerReplyChronology.reply out =
            (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧
          out.lastDown = some M ∧
          ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
          l0.sigma = s + 1 ∧ i ∈ l0.pending ∧
          let b := j + 1
          let Wlate := (E.records.drop b).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
          ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T)
            (hlate : Wlate.length ≤ count - b),
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              hbspan active).finalState = r.output.next ∧
            Wlate = B.drop (k.val + 1) ∧
            (∀ h (hh : h < Wlate.length),
              E.records[b + h]? = some (Wlate[h]'hh) ∧
                (Wlate[h]'hh).input.time.val = u + k.val + h) ∧
            ∃ (U : OrdinaryMessageCodec.UpRecord
                (ReferencePrelaunchFollower.codecParams p rate.eta)),
              U.val = ActiveFollowerQueueOperation.upOfferFields out ∧
              U.val = OrdinaryMessageCodec.UpFields.mk
                (s + 1) (V w).1 ((V w).1 - (V (w - 1)).1) (V w).2 ∧
              0 < U.val.sigma ∧
              ∀ n (hn : n ≤ Wlate.length) (hnpos : 0 < n)
                (control0 : ContinuousLearningRows.TimeControl p),
                let htimeBound : s + b + n - 1 < p.T := by
                  have hspan' : s + count ≤ p.T := hspan
                  have hrest := le_trans hn hlate
                  omega
                let t : Fin p.T := ⟨s + b + n - 1, htimeBound⟩
                ∀ _hselect : ReferenceSelectedAffinePairLaw.selectedChannel p
                    ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
                      some (1, i),
                let beta := s + b
                let prior := (ReferenceCollectionPhaseHistory.acceptedLabels
                  (Wlate.take (n - 1))).toFinset
                ∃ hs : s ≤ t.val,
                  ∃ hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                    (rate := rate) rewards C_star C_h
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s,
                    ∃ hspan_n : s + (b + n) ≤ p.T,
                      let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
                        (rate := rate) rewards C_star C_h
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s i := ⟨source, hz⟩
                      let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
                        hspan_n active
                      Cn.finalState.coordinator = .dagger ∨
                        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
                          (endpointMemory : ActiveFollowerLifecycle.LocalMemory p),
                          Cn.finalState.coordinator ≠ .dagger ∧
                          Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
                          endpoint.status = .unoccupied ∧
                          ReferenceFollowerReplyChronology.reply endpoint =
                            ReferenceFollowerReplyChronology.reply out ∧
                          (i ∈ prior ∨
                            ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace (rate := rate)
                              rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
                              t s hs control0 i z beta U) := by
  classical
  intro x0 b0 s I active E W w B u
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
      hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, hSender⟩ :=
    ReferenceFirstCollectionLateUpSender.actual_first_collection_late_up_sender
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffR, _suffixR, registersR, _ownedR, _baseR, P0R, _birthR,
      _hsplitR, hindexR, _htimeR, hstateR, _hcutoffR, hP0R, _hP0sigmaR,
      _hqueuesR, _hfirstCutoffR, _hbirthR, _hbirthInstallR, _hbirthTimeR,
      _hwindowR, hReceiver⟩ :=
    ReferenceFirstCollectionLateUpReceiverEligibility.actual_first_collection_late_up_receiver_eligibility
      rate source rewards C_star C_h count hcross hspan hshort
  have hcutoffEq : cutoffR = cutoffRecord := by
    obtain ⟨ha, heqa⟩ := hindex
    obtain ⟨hb, heqb⟩ := hindexR
    exact heqb.trans heqa.symm
  rw [hcutoffEq] at hstateR
  have hregistersEq : registersR = registers :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
      (hstateR.symm.trans hstate)).1
  have hpayloadEq : P0R = P0 := by
    rw [hP0R, hregistersEq, ← hP0]
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
    hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  have hquery := hSender k i M hretained
  rcases hquery with hDaggerFollower | hDaggerCoordinator | hordinary
  · exact Or.inl hDaggerFollower
  · exact Or.inr (Or.inl hDaggerCoordinator)
  · rcases hordinary with ⟨out, memory, l0, saved, hfollower, hcoordinator,
        hstatus, hreply, hM, hMsigma, _hrecover, hlastDown, hstart,
        hb, hbspan, hlate, hprefix, hWlate, hlookup, _hprefixFacts,
        _hnoDown, _hboundary, U, hUfields, hUnumeric, hUpositive, hsenderQueries⟩
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
    let b := j + 1
    let Wlate := (E.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hqueryR := hReceiver k i M hretained
    rw [hpayloadEq] at hqueryR
    obtain ⟨_loggedR, _cutDR, _afterR, _rawR, _scanR, _replayedR, _lastR,
        _hinputR, _hdownR, _hacceptedR, _hMR, _hMsigmaR, _hMqR, _hdownStartR,
        _hscanR, _hafterStatusR, _hafterLastR, _hrecoveryR,
        _hreplayedR, _hlastServiceR, _hafterSR, _hafterDeltaR, _hafterBacklogR,
        _hafterReplyR, hnextR⟩ := hqueryR
    rcases hnextR with ⟨hDaggerR, _⟩ | ⟨outR, memoryR, hfollowerR,
        _hstatusR, _hreplyR, _hlastDownR, _hSR, _hdeltaR, _hbacklogR,
        _hstartR, hcoordR⟩
    · rw [hfollower] at hDaggerR
      cases hDaggerR
    have houtEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hfollowerR.symm.trans hfollower)
    have hledgerR := hcoordR
    rcases hcoordR with hcoordDaggerR | ⟨l0R, savedR, hcoordR, hsigmaR,
        hpendingR, _hbR, _hbspanR, _hprefixR, _hWlateR, _hlookupR,
        hmovementR, hreceiverR⟩
    · rw [hcoordinator] at hcoordDaggerR
      cases hcoordDaggerR
    have hledgerEq := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hcoordR.symm.trans hcoordinator)
    have hl0REq : l0R = l0 := hledgerEq.2.1
    rw [hl0REq] at hmovementR hreceiverR hsigmaR hpendingR
    refine Or.inr (Or.inr ⟨out, memory, l0, saved, hfollower, hcoordinator,
      hstatus, hreply, hM, hMsigma, hlastDown, hstart, hsigmaR, hpendingR,
      hb, hbspan, hlate, hprefix, hWlate, hlookup,
      ⟨U, hUfields, hUnumeric, hUpositive, ?_⟩⟩)
    clear hSender hReceiver hledgerR _hprefixFacts _hnoDown _hboundary hmovementR houtEq
    intro n hn hnpos control0 htimeBound t hselect beta prior
    have htime : t.val = s + b + n - 1 := rfl
    have hbound : b + n ≤ count := by
      have hrest : n ≤ count - b := le_trans hn hlate
      omega
    have hspan_n : s + (b + n) ≤ p.T := by omega
    let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
      hspan_n active
    have hs : s ≤ t.val := by omega
    have hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s := by
      refine ⟨(ReferenceSelectedAffinePairLaw.selector_eq_iff p
        (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) source).2
          ⟨rfl, hselect⟩, hcross, ?_⟩
      rfl
    let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t s i := ⟨source, hz⟩
    refine ⟨hs, hz, hspan_n, ?_⟩
    have hsenderN := hsenderQueries n hn
    have hcoordinatorN : Cn.finalState.coordinator = .dagger ∨
        ∃ moving proposal, Cn.finalState.coordinator = .collection P0 moving proposal :=
      hsenderN.1
    rcases hcoordinatorN with hCnDagger | ⟨moving, proposal, hCnCollection⟩
    · exact Or.inl hCnDagger
    have hCnOrdinary : Cn.finalState.coordinator ≠ .dagger := by
      rw [hCnCollection]
      exact fun h => by cases h
    have hinitial :=
      (ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
        rate source rewards C_star C_h count hcross hspan).1
    have hcutN := ReferenceCoordinatorUpIntervalWindow.run_interval_cut I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
      (Nat.le_add_right b n) hspan_n active hinitial hCnOrdinary
    have hseed :
        (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
          hbspan active).finalState.followers i = .ordinary out memory := by
      rw [hprefix]
      exact hfollower
    have hseedStatus : out.status = .unoccupied := hstatus
    have hseedStart : 1 ≤ ReferencePrelaunchFollower.acceptedStart out := by
      rw [hstart]
      omega
    let originalInput := originalSourceRunInput (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
    have hinputEq : originalInput.val = (I, source.1.2,
        ActualInitializationPhysicalStep.selectedRowIndex p source, rewards) :=
      original_input_eq_actual rate source rewards C_star C_h hcross t s hs control0 i hz
    have hinputWhole : originalInput =
        (⟨(I, source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards),
          active⟩ : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s) :=
      Subtype.ext hinputEq
    have hrunRecordsEq (k : ℕ) (hk : s + k ≤ p.T) :
        (ReferenceActiveHorizonMeasurability.runOfInput s k hk originalInput).records =
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k hk active).records :=
      congrArg (fun a => (ReferenceActiveHorizonMeasurability.runOfInput s k hk a).records) hinputWhole
    have hrunFinalEq (k : ℕ) (hk : s + k ≤ p.T) :
        (ReferenceActiveHorizonMeasurability.runOfInput s k hk originalInput).finalState =
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k hk active).finalState :=
      congrArg (fun a => (ReferenceActiveHorizonMeasurability.runOfInput s k hk a).finalState) hinputWhole
    have hfullSpan : s + (p.T - s) ≤ p.T := by omega
    have hcollection : ∀ h (hh : h < n),
        let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
          originalInput.val.1 originalInput.val.2.1 originalInput.val.2.2.1
          originalInput.val.2.2.2 s (b + h) (by omega) originalInput.property
        ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
          (tail : ReferenceCollectionPhaseHistory.Tail record.input),
          record.input.state.coordinator = .collection P0 ledger saved ∧
          ReferenceCollectionPhaseHistory.executedTail record.input = some tail := by
      intro h hh
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        originalInput.val.1 originalInput.val.2.1 originalInput.val.2.2.1
          originalInput.val.2.2.2 s (b + h) (by omega) originalInput.property
      have hrecordActual : record = ReferenceAssignmentPayloadChronology.actualRunRecordAt
          I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s (b + h) (by omega) active := by
        dsimp only [record]
        simp only [show originalInput.val = (I, source.1.2,
          ActualInitializationPhysicalStep.selectedRowIndex p source, rewards) from hinputEq]
      have hgetE : E.records[b + h]? = some record := by
        rw [hrecordActual]
        exact run_record_at I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
          hspan active (b + h) (lt_of_lt_of_le (Nat.add_lt_add_left hh b) hbound)
      have hrecordMem : record ∈ Cn.records := by
        apply List.mem_of_getElem?
        rw [hrecordActual]
        exact run_record_at I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
          hspan_n active (b + h) (by omega)
      have hrecordOrd := hcutN.2.2.2.2.2.2 record hrecordMem
      obtain ⟨hrecordIndex, hreceiverQuery⟩ := hreceiverR h (lt_of_lt_of_le hh hn)
      have hrecordEq : E.records[b + h]'hrecordIndex = record :=
        (List.getElem?_eq_some_iff.mp hgetE).2
      rw [hrecordEq] at hreceiverQuery
      obtain ⟨tail, recording, pre, preSaved, Lsite, diagnostic, received, bank,
          finished, clockFinished, hinputCollection, _hpending, _hsigma,
          htail, _htailLedger, _hrecording, _hstartRound, _hsite, _hsiteCheck,
          _hup, _hinput, _htailReception, _hnotInvalid, _hsitePending,
          _hsiteSigma, _hsiteCursor, _hsiteCutoff, _hbank, _htime, _hsample,
          _hobservation, _hdecoder, _hraw, _hexpected, _hparsed, _hlocal,
          _hrawMatches, _hresult, _hfinish, _hclock, _hzero, _hlocalQueries⟩ :=
        hreceiverQuery hrecordOrd
      exact ⟨pre, preSaved, tail, hinputCollection, htail⟩
    have hseedOriginal : (ReferenceActiveHorizonMeasurability.runOfInput s b hbspan
        originalInput).finalState.followers i = .ordinary out memory := by
      rw [hrunFinalEq]; exact hseed
    obtain ⟨endpoint, endpointMemory, hendpointOriginal, hendpointStatus, hendpointReply⟩ :=
      original_unoccupied_interval rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z P0 b n
        hspan_n out memory hseedOriginal hstatus hseedStart (by rw [hP0sigma, hstart]) hcollection
    have hendpoint : Cn.finalState.followers i = .ordinary endpoint endpointMemory := by
      change (ReferenceActiveHorizonMeasurability.runOfInput s (b + n) hspan_n
        originalInput).finalState.followers i = _ at hendpointOriginal
      rw [hrunFinalEq] at hendpointOriginal
      exact hendpointOriginal
    have hsenderNotDagger : Cn.finalState.followers i ≠ .dagger := by
      rw [hendpoint]
      exact fun h => by cases h
    obtain ⟨_senderEndpoint, _senderMemory, _hsenderFinal, _hsenderStatus,
        _hsenderReply, hchoices⟩ := hsenderN.2.resolve_left hsenderNotDagger
    have hpriorOrAwaited :
        i ∈ (ReferenceCollectionPhaseHistory.acceptedLabels
            (Wlate.take (n - 1))).toFinset ∨
          ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace (rate := rate)
            rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
            t s hs control0 i z beta U := by
      by_cases hprior : i ∈ (ReferenceCollectionPhaseHistory.acceptedLabels
          (Wlate.take (n - 1))).toFinset
      · exact Or.inl hprior
      · right
        -- The actual sender and receiver calls give the literal awaited predicate.
        dsimp only [ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace]
        refine ⟨by omega, by omega, ?_⟩
        intro record hrecord hbeta htimeRecord hchannel
        have hfullMem : record ∈ (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            (p.T - s) hfullSpan active).records := by
          change record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
            (by omega) originalInput).records at hrecord
          rw [hrunRecordsEq] at hrecord; exact hrecord
        obtain ⟨h, hh, hlateIndex, hrecordPair⟩ := late_record_index I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
          b n hbound Wlate hn (fun h hh => (hlookup h hh).1) record hfullMem hbeta (by omega)
        have hgetE := (hlookup h hlateIndex).1
        have hactualLate : ReferenceAssignmentPayloadChronology.actualRunRecordAt I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + h)
            (by omega) active = Wlate[h]'hlateIndex := by
          exact Option.some.inj ((run_record_at I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
            (b + h) (lt_of_lt_of_le (Nat.add_lt_add_left hh b) hbound)).symm.trans hgetE)
        rw [hrecordPair] at hchannel ⊢
        have hdraws := source_channel_draws
          (((Wlate[h]'hlateIndex).input.row.2
            (Wlate[h]'hlateIndex).input.time).1) i hchannel
        have hnoEarlier :
            i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
              (Wlate.take h)).toFinset := by
          intro haccepted
          apply hprior
          have htakePrefix : Wlate.take h <+: Wlate.take (n - 1) := by
            exact List.take_prefix_take_left (by omega)
          have hmemList := List.mem_toFinset.mp haccepted
          obtain ⟨earlier, hearlier, hlabel⟩ := List.mem_filterMap.mp hmemList
          exact List.mem_toFinset.mpr <| List.mem_filterMap.mpr
            ⟨earlier, htakePrefix.subset hearlier, hlabel⟩
        have hchoicesAt := hchoices h hh
        rcases hchoicesAt with ⟨choice, choiceMemory, hchoiceConfig,
            hchoiceStatus, hchoiceReply, hsend⟩
        have hsendFields := hsend hdraws.1 hdraws.2
        rcases hsendFields with ⟨_hoff, _hoffActual, hsent, _hexpected, _⟩
        obtain ⟨hrecordIndex, hreceiverAt⟩ := hreceiverR h (lt_of_lt_of_le hh hn)
        have hrecordE : E.records[b + h]'hrecordIndex = Wlate[h]'hlateIndex := by
          exact (List.getElem?_eq_some_iff.mp hgetE).2
        rw [hrecordE] at hreceiverAt
        have hrecordOrd : (Wlate[h]'hlateIndex).output.next.coordinator ≠ .dagger := by
          apply hcutN.2.2.2.2.2.2
          apply List.mem_of_getElem?
          rw [← hactualLate]
          exact run_record_at I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
            hspan_n active (b + h) (by omega)
        obtain ⟨tail, recording, pre, preSaved, Lsite, diagnostic, received, bank,
            finished, clockFinished, _hinputCollection, _hpending, _hsigma,
            _htail, _htailLedger, _hrecording, _hstartRound, hsite, _hsiteCheck,
            hup, _hinput, _htailReception, _hnotInvalid, _hsitePending,
            _hsiteSigma, _hsiteCursor, _hsiteCutoff, _hbank, _htime, _hsample,
            _hobservation, _hdecoder, _hraw, _hexpected, _hparsed, _hlocal,
            _hrawMatches, _hresult, _hfinish, _hclock, _hzero, hlocalQueries⟩ :=
          hreceiverAt hrecordOrd
        have hnotAccepted := (hlocalQueries hdraws.1 hdraws.2).1 hnoEarlier
        refine ⟨hsent, ?_⟩
        refine ⟨diagnostic, hup, hnotAccepted.1, hnotAccepted.2.2.1,
          hnotAccepted.2.2.2.1, ?_⟩
        change CoordinatorCollectionLedger.acceptUpCheck diagnostic.input.ledger i U = true
        rw [_hinput]
        exact hnotAccepted.2.2.2.2 U (by rw [hUnumeric])
    exact Or.inr ⟨endpoint, endpointMemory, hCnOrdinary, hendpoint,
      hendpointStatus, hendpointReply, hpriorOrAwaited⟩

/-- On the displayed ordinary and exact-count event, ambiguity of the
entire actual second late batch belongs to the original-source survival event.
The inherited first batch is discarded by the literal second-window offset;
no service count, uniqueness probability, or manuscript closure is asserted. -/
theorem actual_late_second_batch_ambiguous_source_coverage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < E.records.length, cutoffRecord = E.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∀ k : Fin B.length,
        E.records[w + k.val]? = some B[k.val] ∧ B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        r.output.next.followers i = .dagger ∨
        r.output.next.coordinator = .dagger ∨
        ∃ (out : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (l0 : ReferenceActivePhysicalStep.Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.output.next.followers i = .ordinary out memory ∧
          r.output.next.coordinator = .collection P0 l0 saved ∧
          out.status = .unoccupied ∧
          let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
          ReferenceFollowerReplyChronology.reply out =
            (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧
          out.lastDown = some M ∧
          ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
          l0.sigma = s + 1 ∧ i ∈ l0.pending ∧
          let b := j + 1
          let Wlate := (E.records.drop b).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
          ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T)
            (hlate : Wlate.length ≤ count - b),
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              hbspan active).finalState = r.output.next ∧
            Wlate = B.drop (k.val + 1) ∧
            (∀ h (hh : h < Wlate.length),
              E.records[b + h]? = some (Wlate[h]'hh) ∧
                (Wlate[h]'hh).input.time.val = u + k.val + h) ∧
            ∃ (U : OrdinaryMessageCodec.UpRecord
                (ReferencePrelaunchFollower.codecParams p rate.eta)),
              U.val = ActiveFollowerQueueOperation.upOfferFields out ∧
              U.val = OrdinaryMessageCodec.UpFields.mk
                (s + 1) (V w).1 ((V w).1 - (V (w - 1)).1) (V w).2 ∧
              0 < U.val.sigma ∧
              ∀ n (hn : n ≤ Wlate.length) (hnpos : 0 < n)
                (control0 : ContinuousLearningRows.TimeControl p),
                let htimeBound : s + b + n - 1 < p.T := by
                  have hspan' : s + count ≤ p.T := hspan
                  have hrest := le_trans hn hlate
                  omega
                let t : Fin p.T := ⟨s + b + n - 1, htimeBound⟩
                ∀ _hselect : ReferenceSelectedAffinePairLaw.selectedChannel p
                    ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
                      some (1, i),
                let beta := s + b
                ∃ hs : s ≤ t.val,
                  ∃ hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                    (rate := rate) rewards C_star C_h
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s,
                    ∃ hspan_n : s + (b + n) ≤ p.T,
                      let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
                        (rate := rate) rewards C_star C_h
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s i := ⟨source, hz⟩
                      let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
                        hspan_n active
                      let preRun := ReferenceActivePhysicalHorizon.run I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b hbspan active
                      let interval := Cn.records.drop b
                      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
                      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
                        hspan_n active
                      let positive := AffineBatchDecoder.positives p trace rounds
                      let channel := preRun.finalState.upDecoderBank i
                      let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
                      let firstBatch := channel.pending ++ positive.take
                        (AffineBatchDecoder.quota p - channel.pending.length)
                      let input := originalSourceRunInput (rate := rate) rewards C_star C_h
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
                      let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
                      let testsSince : ℕ → List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
                        fun alpha => originalSourceTests (rate := rate) rewards C_star C_h
                          (ActualInitializationPhysicalStep.selectedRowIndex p source)
                          t s hs control0 alpha i z
                      let fullEvidence := full.records.map
                        (ReferenceActivePhysicalHorizon.RoundRecord.evidence (p := p) (rate := rate))
                      let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
                      Cn.finalState.coordinator ≠ .dagger →
                      ReferenceActiveAffinePositiveTest.upPositive current.input = true →
                      positive.length = AffineBatchDecoder.quota p - channel.pending.length +
                        AffineBatchDecoder.quota p →
                      (∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p), v₁ ≠ v₂ ∧
                        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₁ ∧
                        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₂) →
                      ∃ (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                        current.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                        (current.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
                        window = (current.input.state.upDecoderBank i).pending ++
                          [AffineBatchDecoder.entry p
                            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] ∧
                        ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace (rate := rate)
                          rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
                          t s hs control0 i z beta U ∧
                        d.decoderAfter.pending = [] ∧
                        d.decoderAfter.completed = channel.completed ++ [firstBatch, window] ∧
                        d.raw = none ∧
                        ∃ (alpha : ℕ),
                          let kept := (testsSince alpha).take (AffineBatchDecoder.quota p)
                          s ≤ alpha ∧ alpha ≤ t.val ∧
                          upBatchBirth (p := p) (rate := rate) i s alpha input.val.1 fullEvidence ∧
                          kept.length = AffineBatchDecoder.quota p ∧
                          kept.Pairwise (fun (a b : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) =>
                            a.time < b.time) ∧
                          kept.map (fun (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) =>
                            (test.time, test.sample)) =
                            window.map (fun (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =>
                              (entry.time.val, entry.sample)) ∧
                          (∀ (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)),
                            test ∈ kept → test.sent = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                          ∃ v : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v ∧
                            v ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
                            source ∈ upSourceSurvivalEvent (rate := rate) rewards C_star C_h
                              (ActualInitializationPhysicalStep.selectedRowIndex p source)
                              control0 alpha v i (AffineBatchDecoder.quota p) := by
  classical
  intro x0 b0 s I active E W w B u
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
      hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, hqueries⟩ :=
    actual_late_up_source_awaited_cases rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffR, _suffixR, registersR, _ownedR, _baseR, P0R, _birthR,
      _hsplitR, hindexR, _htimeR, hstateR, _hcutoffR, hP0R, _hP0sigmaR,
      _hqueuesR, _hfirstCutoffR, _hbirthR, _hbirthInstallR, _hbirthTimeR,
      _hwindowR, hReceiver⟩ :=
    ReferenceFirstCollectionLateUpReceiverEligibility.actual_first_collection_late_up_receiver_eligibility
      rate source rewards C_star C_h count hcross hspan hshort
  have hcutoffEq : cutoffR = cutoffRecord := by
    obtain ⟨_, heqa⟩ := hindex
    obtain ⟨_, heqb⟩ := hindexR
    exact heqb.trans heqa.symm
  rw [hcutoffEq] at hstateR
  have hregistersEq : registersR = registers :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj (hstateR.symm.trans hstate)).1
  have hpayloadEq : P0R = P0 := by rw [hP0R, hregistersEq, ← hP0]
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
    hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  rcases hqueries k i M hretained with hdagger | hdagger | hordinary
  · exact Or.inl hdagger
  · exact Or.inr (Or.inl hdagger)
  · obtain ⟨out, memory, l0, saved, hfollower, hcoordinator, hstatus, hreply,
        hM, hMsigma, hlastDown, hstart, hsigma, hipending,
        hb, hbspan, hlate, hprefix, hWlate, hlookup,
        U, hUfields, hUnumeric, hUpositive, hquery⟩ := hordinary
    let b := j + 1
    let Wlate := (E.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hqueryR := hReceiver k i M hretained
    rw [hpayloadEq] at hqueryR
    obtain ⟨_loggedR, _cutDR, _afterR, _rawR, _scanR, _replayedR, _lastR,
        _hinputR, _hdownR, _hacceptedR, _hMR, _hMsigmaR, _hMqR, _hdownStartR,
        _hscanR, _hafterStatusR, _hafterLastR, _hrecoveryR,
        _hreplayedR, _hlastServiceR, _hafterSR, _hafterDeltaR, _hafterBacklogR,
        _hafterReplyR, hnextR⟩ := hqueryR
    rcases hnextR with ⟨hDaggerR, _⟩ | ⟨outR, memoryR, hfollowerR,
        _hstatusR, _hreplyR, _hlastDownR, _hSR, _hdeltaR, _hbacklogR,
        _hstartR, hcoordR⟩
    · rw [hfollower] at hDaggerR
      cases hDaggerR
    rcases hcoordR with hcoordDaggerR | ⟨l0R, savedR, hcoordR, _hsigmaR,
        _hpendingR, _hbR, _hbspanR, _hprefixR, _hWlateR, _hlookupR,
        _hmovementR, hreceiverR⟩
    · rw [hcoordinator] at hcoordDaggerR
      cases hcoordDaggerR
    have hledgerEq := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hcoordR.symm.trans hcoordinator)
    have hl0REq : l0R = l0 := hledgerEq.2.1
    rw [hl0REq] at hreceiverR
    refine Or.inr (Or.inr ⟨out, memory, l0, saved, hfollower, hcoordinator,
      hstatus, hreply, hM, hMsigma, hlastDown, hstart, hsigma, hipending,
      hb, hbspan, hlate, hprefix, hWlate, hlookup, U, hUfields, hUnumeric, hUpositive, ?_⟩)
    clear hqueries hReceiver _hmovementR
    intro n hn hnpos control0 htimeBound t hselect beta
    have htime : t.val = s + b + n - 1 := rfl
    obtain ⟨hs, hz, hspan_n, hcases⟩ := hquery n hn hnpos control0 hselect
    refine ⟨hs, hz, hspan_n, ?_⟩
    intro z Cn preRun interval trace rounds positive channel window firstBatch input full testsSince fullEvidence current hOrd hp hCount hamb
    obtain ⟨_endpoint, _endpointMemory, _hOrd, _hfollower, _hstatus, _hreply, hpriorOr⟩ :=
      hcases.resolve_left hOrd
    have hbound : b + n ≤ count := by
      have hrest : n ≤ count - b := le_trans hn hlate
      have hb' : b ≤ count := hb
      omega
    have hidx : t.val - s = b + (n - 1) := by omega
    have hinputEq : input.val = (I, source.1.2,
        ActualInitializationPhysicalStep.selectedRowIndex p source, rewards) :=
      original_input_eq_actual rate source rewards C_star C_h hcross t s hs control0 i hz
    have hwhole : input =
        (⟨(I, source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards), active⟩ :
          ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s) :=
      Subtype.ext hinputEq
    have hcurrentAt : current = ReferenceAssignmentPayloadChronology.actualRunRecordAt I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + (n - 1))
        (by omega) active := by
      have h := current_record_eq_at rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
      have ha := congrArg (fun a : ReferenceActiveHorizonMeasurability.ActiveRunInput
          (p := p) (rate := rate) s =>
        ReferenceAssignmentPayloadChronology.actualRunRecordAt a.val.1 a.val.2.1 a.val.2.2.1
          a.val.2.2.2 s (t.val - s) (by omega) a.property) hwhole
      exact h.trans (by simpa only [hidx] using ha)
    have hcurrentGet : Cn.records[b + (n - 1)]? = some current := by
      rw [hcurrentAt]
      exact run_record_at I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (b + n) hspan_n active (b + (n - 1)) (by omega)
    have hcurrentMem : current ∈ Cn.records := List.mem_of_getElem? hcurrentGet
    have hcurrentInterval : current ∈ interval := by
      apply List.mem_of_getElem?
      rw [List.getElem?_drop]
      exact hcurrentGet
    have hcurrentFields := originalSourceCurrentInput_original_fields (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
    have hcurrentTime : current.input.time = t := hcurrentFields.2.2.1
    have hcurrentSelect : ReferenceSelectedAffinePairLaw.selectedChannel p
        (current.input.row.2 current.input.time).1 = some (1, i) := by
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hcurrentTime]
      exact hselect
    have hdraws := source_channel_draws (current.input.row.2 current.input.time).1 i hcurrentSelect
    have hinitial := (ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
      rate source rewards C_star C_h count hcross hspan).1
    have hseed := (ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
      rate source rewards C_star C_h count hcross hspan).2.1 i
    have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
      (Nat.le_add_right b n) hspan_n active hinitial hOrd
    obtain ⟨hrecordIndex, hreceiverAt⟩ := hreceiverR (n - 1)
      (lt_of_lt_of_le (by omega : n - 1 < n) hn)
    have hgetE : E.records[b + (n - 1)]? = some current := by
      rw [hcurrentAt]
      exact run_record_at I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan active (b + (n - 1)) (by omega)
    rw [(List.getElem?_eq_some_iff.mp hgetE).2] at hreceiverAt
    obtain ⟨_tail, _recording, _pre, _preSaved, Lsite, d, _received, _bank,
        _finished, _clockFinished, _hinputCollection, _hpending, _hsigma,
        _htail, _htailLedger, _hrecording, _hstartRound, _hsite, _hsiteCheck,
        hd, _hinput, _htailReception, _hnotInvalid, _hsitePending,
        _hsiteSigma, _hsiteCursor, _hsiteCutoff, hbank, hdtime, _hsample,
        _hobservation, _hdecoder, _hraw, _hexpected, _hparsed, _hlocal,
        _hrawMatches, _hresult, _hfinish, _hclock, _hzero, hlocalQueries⟩ :=
      hreceiverAt (hcut.2.2.2.2.2.2 current hcurrentMem)
    have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
      rw [ReferenceActiveAffinePositiveTest.record_upPositive current, hd,
        ReferenceActiveAffinePositiveTest.upDiagnosticPositive, decide_eq_true_eq] at hp
      exact hp
    have hnoPrior : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
        (Wlate.take (n - 1))).toFinset := by
      intro hpast
      have hdisabled := ((hlocalQueries hdraws.1 hdraws.2).2 hpast).2.2.1
      rw [heligible.1] at hdisabled
      cases hdisabled
    have hi : d.input.selectedFollower = i :=
      ((hlocalQueries hdraws.1 hdraws.2).1 hnoPrior).1
    have hawaited := hpriorOr.resolve_left hnoPrior
    have hroundsOrder := ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
      I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
      (Nat.le_add_right b n) hspan_n active hinitial hOrd
    have horder : interval.Pairwise (fun a b => a.input.time.val < b.input.time.val) := by
      change (interval.map (fun r => r.input.time)).Pairwise
        (fun a b => a.val < b.val) at hroundsOrder
      simpa only [List.pairwise_map] using hroundsOrder
    have htraceCurrent : trace current.input.time = CoordinatorUpReception.roundInput d.input := by
      have h := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
        interval i horder current hcurrentInterval
      simpa only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hd, hi,
        ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true] using h
    have hlastPrefix : Cn.records =
        (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + (n - 1))
          (by omega) active).records ++ [current] := by
      have h := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + (n - 1))
        (by omega) active
      have heq : b + (n - 1) + 1 = b + n := by omega
      simpa only [heq, ← hcurrentAt] using h
    have hroundsLast : ∃ before, rounds = before ++ [t] := by
      refine ⟨((ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + (n - 1))
        (by omega) active).records.drop b).map (fun r => r.input.time), ?_⟩
      change (Cn.records.drop b).map (fun r => r.input.time) = _
      rw [hlastPrefix, List.drop_append_of_le_length (by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; omega), List.map_append]
      simp only [List.map_cons, List.map_nil, hcurrentTime]
    have hdecisionNow : AffineBatchDecoder.decisionTime window = some t :=
      decisionTime_drop_of_last_positive trace rounds t hroundsLast
        (by rw [← hcurrentTime, htraceCurrent]; exact heligible)
        (AffineBatchDecoder.quota p - channel.pending.length) (by
          change _ < positive.length
          rw [hCount]
          exact Nat.lt_add_of_pos_right (AffineBatchDecoder.quota_pos p))
    obtain ⟨first, last, index, record, diagnostic, hfirst, _hfirstLen, hwindowLen,
        _hwindowPair, _hlast, hdecision, _hindex, hrecordMem, hrecordTime,
        hdSaved, _hiSaved, _htimeSaved, _hlastEntry, _hlastSample, _hsiteSaved,
        _hconnected, _hreplay, _hbankSaved, hbefore, hwindow, _hpendingAfter,
        hcompletedAfter, hdecoderAfter, _hrawTransition, _hrawWindow,
        _htransition, _hrun, _hfullBank⟩ :=
      ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
        (Nat.le_add_right b n) hspan_n active hinitial hOrd i hseed hCount
    have hlastTime : last.time = t := Option.some.inj (hdecision.symm.trans hdecisionNow)
    have hrecordEq : record = current :=
      ReferenceAssignmentPayloadChronology.run_records_time_injective I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
        hspan_n active (List.mem_of_mem_drop hrecordMem) hcurrentMem
        (by rw [hrecordTime, hlastTime, hcurrentTime])
    rw [hrecordEq] at hdSaved
    have hdiagEq : diagnostic = d := Option.some.inj (hdSaved.symm.trans hd)
    subst diagnostic
    have hentryEq : AffineBatchDecoder.entry p trace last.time = AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time := by
      rw [hlastTime, ← hcurrentTime]
      simp only [AffineBatchDecoder.entry, htraceCurrent,
        ReferenceCoordinatorUpDecoderReplay.constantInputTrace, hdtime]
    have hwindowActual : (current.input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] = window := by
      rw [hbefore, hbank, hentryEq] at hwindow
      exact hwindow
    have hQ : (current.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p := by
      have h := congrArg List.length hwindowActual
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      exact h.trans hwindowLen
    have hbetaWindow : ∀ entry ∈ window, beta ≤ entry.time.val := by
      intro entry hentry
      have hpos := (AffineBatchDecoder.mem_positives_iff p trace rounds entry).mp
        (List.mem_of_mem_drop hentry)
      exact (ReferenceCoordinatorUpIntervalWindow.run_interval_round_time_bounds I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
        (Nat.le_add_right b n) hspan_n active hinitial hOrd entry.time hpos.1).1
    have hactualBounds : ∀ entry ∈ (current.input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
        beta ≤ entry.time.val := by rw [hwindowActual]; exact hbetaWindow
    have hambActual : ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p), v₁ ≠ v₂ ∧
        AffineBatchDecoder.satisfies
          (((current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₁ ∧
        AffineBatchDecoder.satisfies
          (((current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₂ := by
      rw [hwindowActual]
      exact hamb
    obtain ⟨alpha, ha, hat, hbirth, hkeptLen, hkeptOrder, hcoordinates, hpendingAfter,
        _hcompleted, message, beta', htrace', _hbeta', _hparse, _haccept, _hlocalPending,
        _hmessageSigma, _hmessagePositive, _hplaceholder, hsent, _hsolves,
        hraw, _hother, v, hv, hne, hsurvival⟩ :=
      ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_ambiguous_source_coverage
        rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i z d hd hi (by
          rw [ReferenceActiveAffinePositiveTest.record_upPositive current, hd,
            ReferenceActiveAffinePositiveTest.upDiagnosticPositive, decide_eq_true_eq]
          exact heligible) hQ ⟨U, beta, hawaited, hactualBounds⟩ hambActual
    have hcurrentFull := current_record_mem_full rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z
    have hsentU := (hawaited.2.2 current hcurrentFull
      (by rw [hcurrentTime]; exact hawaited.2.1) (by rw [hcurrentTime]) hcurrentSelect).1
    have hsentMessage := (htrace'.2.2 current hcurrentFull
      (by rw [hcurrentTime]; exact htrace'.2.1) (by rw [hcurrentTime]) hcurrentSelect).1
    have hwordEq : ActiveFollowerArmChoice.offeredUpWord rate.eta message =
        ActiveFollowerArmChoice.offeredUpWord rate.eta U :=
      Option.some.inj (hsentMessage.symm.trans hsentU)
    refine ⟨d, hd, hi, hQ, hwindowActual.symm, hawaited, hpendingAfter, ?_, hraw,
      alpha, ha, hat, hbirth, hkeptLen, hkeptOrder, ?_, ?_, v, ?_, ?_, hsurvival⟩
    · rw [hdecoderAfter]
      simpa only [hfirst] using hcompletedAfter
    · rw [hwindowActual] at hcoordinates
      exact hcoordinates
    · intro test htest
      rw [← hwordEq]
      exact hsent test htest
    · rw [hwindowActual] at hv
      exact hv
    · rw [← hwordEq]
      exact hne

end Bandits.Support.ReferenceFirstCollectionLateUpSourceAwaited

end
