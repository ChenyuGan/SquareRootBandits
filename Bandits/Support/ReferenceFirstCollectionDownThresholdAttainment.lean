/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownThresholdDetection

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection DOWN prefix boundaries and threshold attainment

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.

The boundaries below are original physical prefixes, including the successor
of the last retained round. The cutoff bank retains its entire prehistory.
Threshold attainment is conditional on the produced local boundary having no
accepted DOWN and on its actual positive count reaching the stated threshold.
No physical acceptance, ambiguity event, stopped quota, good event, probability,
UP allowance, waiting bound, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionReadyStream (startTime actualEpoch actualWindow)
open ReferencePrelaunchFollower (acceptedStart)
open ReferenceFollowerDownDecoderReplay

namespace Bandits.Support.ReferenceFirstCollectionDownThresholdAttainment

variable {p : ConstructorDimensions.Parameters}

private theorem positive_entries_append
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    actualDownPositives i (left ++ right) =
      actualDownPositives i left ++ actualDownPositives i right := by
  simp only [actualDownPositives, actualDownCalls, List.filterMap_append,
    positiveCallEntries, List.flatMap_append]

private theorem positive_singleton_length
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (actualDownPositives i [record]).length ≤ 1 := by
  classical
  cases hc : actualDownCall i record with
  | none => simp [actualDownPositives, actualDownCalls, hc, positiveCallEntries]
  | some call =>
      simp only [actualDownPositives, actualDownCalls, List.filterMap_cons,
        List.filterMap_nil, hc, positiveCallEntries, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      unfold AffineBatchDecoder.positiveAt
      split <;> simp

private theorem positive_step_length
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : ℕ) (hn : n < records.length) :
    (actualDownPositives i (records.take (n + 1))).length =
      (actualDownPositives i (records.take n)).length +
        (actualDownPositives i [records[n]]).length := by
  rw [List.take_succ_eq_append_getElem hn, positive_entries_append, List.length_append]

private theorem positive_singleton_selected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hpositive : 0 < (actualDownPositives i [record]).length) :
    ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
      0 < (preparedOwnObservation record i).val.val ∧
      actualDownPositives i [record] =
        [⟨record.input.time, (record.input.row.2 record.input.time).2 (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩] := by
  classical
  cases hc : preparedChoiceConfiguration record i with
  | dagger =>
      simp [actualDownPositives, actualDownCalls, actualDownCall, hc,
        positiveCallEntries] at hpositive
  | ordinary choice memory =>
      have hcall := actualDownCall_ordinary record i choice memory hc
      have helig : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (preparedChoiceRow record i) (preparedChoiceTime record i)
            (preparedOwnObservation record i) rate choice) := by
        by_contra h
        simp [actualDownPositives, actualDownCalls, hcall, positiveCallEntries,
          AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
          h] at hpositive
      have hselected := (actualDownCall_eligible_iff record i choice).1 helig
      have hrow : preparedChoiceRow record i = record.input.row :=
        (record.output.preparation.follower_alignment i).1
      have htime := preparedChoiceTime_eq_recordTime record i
      refine ⟨by simpa only [hrow, htime] using hselected.1, hselected.2.2, ?_⟩
      have hentry : AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i
              (preparedChoiceRow record i) (preparedChoiceTime record i)
              (preparedOwnObservation record i) rate choice))
          (preparedChoiceTime record i) =
          [⟨preparedChoiceTime record i,
            ((preparedChoiceRow record i).2 (preparedChoiceTime record i)).2 (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩] := by
        unfold AffineBatchDecoder.positiveAt
        exact (ite_eq_left helig).trans rfl
      simpa only [actualDownPositives, actualDownCalls, List.filterMap_cons,
        List.filterMap_nil, hcall, positiveCallEntries, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, hrow, htime] using hentry

private theorem first_attainment
    (total quota : ℕ) (f : ℕ → ℕ) (hzero : f 0 = 0)
    (hstep : ∀ n, n < total → f (n + 1) ≤ f n + 1)
    (hquota : 1 < quota) (hreach : quota ≤ f total) :
    ∃ k, 0 < k ∧ k < total ∧ f (k + 1) = quota ∧
      (∀ j, j ≤ k → f j < quota) := by
  classical
  let witness : ∃ n, quota ≤ f n := ⟨total, hreach⟩
  let r := Nat.find witness
  have hfound : quota ≤ f r := Nat.find_spec witness
  have hmin (j : ℕ) (hj : j < r) : f j < quota := by
    have hnot := Nat.find_min witness hj
    omega
  have hle : r ≤ total := Nat.find_min' witness hreach
  have hpos : 0 < r := by
    by_contra h
    have hr : r = 0 := by omega
    rw [hr, hzero] at hfound
    omega
  have hprev := hmin (r - 1) (by omega)
  have hbound := hstep (r - 1) (by omega)
  have hsucc : r - 1 + 1 = r := by omega
  rw [hsucc] at hbound
  have heq : f r = quota := by omega
  have hone : 1 < r := by
    by_contra h
    have hr : r = 1 := by omega
    have hfirst := hstep 0 (by omega)
    have hval : f 1 = quota := by simpa only [hr] using heq
    rw [hzero, hval] at hfirst
    omega
  refine ⟨r - 1, by omega, by omega, by rw [hsucc]; exact heq, ?_⟩
  intro j hj
  exact hmin j (by omega)

private theorem lastDown_none_of_start_zero
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstart : acceptedStart state = 0) : state.lastDown = none := by
  cases hlast : state.lastDown with
  | none => rfl
  | some message =>
      have hpositive := message.property.1
      simp only [acceptedStart, hlast] at hstart
      omega

private theorem run_prefix_records
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total n : ℕ) (hspan : start + total ≤ p.T) (hn : n ≤ total)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) active).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan active).records.take n := by
  obtain ⟨suffix, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) active
  have hsplit' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) active).records ++ suffix := by
    simpa only [Nat.add_sub_of_le hn] using hsplit
  rw [hsplit']
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows
    selected rewards start n (by omega) active
  rw [List.take_append, List.take_of_length_le (by omega), hlength,
    Nat.sub_self, List.take_zero, List.append_nil]

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (source : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (hcross : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
  (count : ℕ)
  (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
  (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)

local notation "s" => startTime (rate := rate) source rewards C_star C_h
local notation "E" => actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan
local notation "w" => List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records E))
local notation "B" => actualWindow (rate := rate) source rewards C_star C_h hcross count hspan
local notation "initial" => ReferenceFirstCollectionEpochAlignment.actualLaunchState
  rate source rewards C_star C_h hcross
local notation "active" => And.left (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
  rate source rewards C_star C_h hcross)

include hshort in
private theorem window_geometry :
    let tail := ((E).records.drop (w + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    (B).length = tail.length + 1 ∧ w + (B).length ≤ count := by
  classical
  dsimp only
  have hcount : (E).records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
  have hhead : (((E).records.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop, hcount]
    omega
  have hlen : (B).length =
      (((E).records.drop (w + 1)).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length + 1 := by
    dsimp only [actualWindow, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append, hhead]
    exact Nat.add_comm 1 _
  have htail := (List.takeWhile_prefix
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.laterChosen record.input)
    (l := (E).records.drop (w + 1))).length_le
  simp only [List.length_drop, hcount] at htail
  exact ⟨hlen, by omega⟩

/-- The prefix is exactly the original physical run through `w + b` rounds.
This abbreviation changes no state, stream, reward table, or calendar. -/
abbrev actualPrefix (b : ℕ) (hb : s + (w + b) ≤ p.T) :=
  ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (w + b) hb active

include hshort in
private theorem prefix_endpoints
    (b : ℕ) (hb : b ≤ (B).length) (hbound : s + (w + b) ≤ p.T) :
    (∀ hlt : b < (B).length,
      (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
        (B[b]'hlt).input.state) ∧
    (∀ hpos : 0 < b,
      (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
        (B[b - 1]'(by omega)).output.next) := by
  constructor
  · intro hlt
    exact (ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
      rate source rewards C_star C_h count hcross hspan hshort ⟨b, hlt⟩).1.symm
  · intro hpos
    cases b with
    | zero => omega
    | succ n =>
        have hn : n < (B).length := by omega
        exact (ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
          rate source rewards C_star C_h count hcross hspan hshort ⟨n, hn⟩).2

private theorem stream_payload_eq
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : ((E).records[w]'(by
      have hcount : (E).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
      omega)).input.state.coordinator = .live r owned base) :
    d.stream.payload = r.payload := by
  obtain ⟨execution⟩ := d.stream.cutoffExecution
  have hrecord : (E).records[w]'(by
      have hcount : (E).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
      omega) = d.stream.cutoff.cut :=
    (List.getElem?_eq_some_iff.mp d.stream.cutoff.cutIndex).2
  rw [hrecord] at hcoord
  have heq := execution.actualLive.symm.trans hcoord
  have hr : execution.live = r := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj heq).1
  exact (d.stream.payloadMatchesCutoff.trans execution.payloadIsLive).trans
    (congrArg CoordinatorLiveChoiceRecorderStep.Registers.payload hr)

include hshort in
/-- Positive boundaries include the terminal successor. In particular no
record is looked up at `b` when `b = B.length`. -/
theorem actual_first_collection_down_positive_prefix_boundary
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (b : ℕ) (hb : b ≤ (B).length) (hpos : 0 < b) :
    ∃ hbound : s + (w + b) ≤ p.T,
      (∀ hlt : b < (B).length,
        (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
          (B[b]'hlt).input.state) ∧
      (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
        (B[b - 1]'(by omega)).output.next ∧
      ((actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.coordinator =
        .dagger ∨ ∃ ledger saved,
        (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.coordinator =
          .collection d.stream.payload ledger saved) ∧
      ∀ i : Fin (p.m - 1), ∃ post memory,
        (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
          .ordinary post memory ∧
        post.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid post ∧
        ActiveFollowerLifecycle.localBufferValid post ∧
        ActiveFollowerLifecycle.downDecoderStateValid post ∧
        post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧ post.backlog ≤ p.T * D p ∧
        post.S + post.backlog ≤ w * D p ∧
        (∀ saved ∈ post.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
        (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
        (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
          saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ post.buffer, saved.calendarRound < s + w + b + 1) ∧
        post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
        (∀ batch ∈ post.downBatch.completed, batch.length = AffineBatchDecoder.quota p) ∧
        (post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0 ∨
          post.lastDown = some (d.stream.payload.downRecord i)) := by
  classical
  have hgeometry := window_geometry rate source rewards C_star C_h hcross count hspan hshort
  let hbound : s + (w + b) ≤ p.T := by omega
  have hprefix :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hcross s rfl count hspan hshort
  rcases hprefix with
    ⟨r, owned, base, _hcoord, _hsigma, _hqueue,
      ⟨_dispatched, _hstart, _ledger, _hinit, _hledger, _hdomain, _hclock,
        _hpending, _hnoAssignment, _selected, _hprepared, _hu, _huT, _huGrid,
        _hsigmaLedger, _hcutoff, _hscan, _hsuccessor, _hmoving, hboundaries, _hrecords⟩⟩
  have hj : b - 1 ≤ (((E).records.drop (w + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by omega
  have hboundary := hboundaries (b - 1) hj
  have hsmall : 1 + (b - 1) = b := by omega
  have hrun : ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s rfl count hspan = E := rfl
  simp only [hrun] at hboundary
  have hendpoints := prefix_endpoints rate source rewards C_star C_h hcross count hspan
    hshort b hb hbound
  have hpayload := stream_payload_eq rate source rewards C_star C_h hcross count hspan
    hshort d r owned base _hcoord
  refine ⟨hbound, hendpoints.1, hendpoints.2 hpos, ?_, ?_⟩
  · simpa only [actualPrefix, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, Nat.add_assoc, hsmall, hpayload] using hboundary.1
  · intro i
    by_cases hlt : b < (B).length
    · obtain ⟨_payloadD, before, memory, hinputD, hstatusD, hdomainD, hbufferD,
          hdecoderD, hSD, hdeltaD, hbacklogD, hmassD, hcalendarD, hnodupD,
          hquantizedD, hpairwiseD, hchronologyD, hpendingD, hcompletedD,
          _hlastD, _hcoordinatorD⟩ :=
        ReferenceFirstCollectionDownThresholdDetection.actual_first_collection_down_positive_boundary
          rate source rewards C_star C_h hcross count hspan hshort ⟨b, hlt⟩ hpos i
      have hstateD :
          (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
            .ordinary before memory := by
        rw [hendpoints.1 hlt]
        exact hinputD
      obtain ⟨post, postMemory, hstateRaw, _hstatusRaw, _hdomainRaw, _hbufferRaw,
          _hdecoderRaw, _hSRaw, _hdeltaRaw, _hbacklogRaw, _hmassRaw,
          _hcalendarRaw, _hnodupRaw, _hquantizedRaw, _hpairwiseRaw,
          _hchronologyRaw, _hpendingRaw, _hcompletedRaw, hlastRaw⟩ := hboundary.2 i
      have hstatePost :
          (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
            .ordinary post postMemory := by
        simpa only [actualPrefix, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
          ReferenceFirstLaunchNumericalCell.launchState, Nat.add_assoc, hsmall] using hstateRaw
      have hsame : before = post :=
        (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hstateD.symm.trans hstatePost)).1
      subst post
      refine ⟨before, memory, hstateD, hstatusD, hdomainD, hbufferD,
        hdecoderD, hSD, hdeltaD, hbacklogD, hmassD, hcalendarD, hnodupD,
        hquantizedD, hpairwiseD, hchronologyD, hpendingD, hcompletedD, ?_⟩
      simpa only [hpayload] using hlastRaw
    · simpa only [actualPrefix, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState, Nat.add_assoc, hsmall, hpayload] using hboundary.2 i


include hshort in
/-- An ordinary OLD boundary supplies every earlier actual ordinary OLD input,
including the cutoff input. The endpoint may be the finite terminal successor. -/
theorem actual_first_collection_down_old_prefix_inputs
    (b : ℕ) (hb : b ≤ (B).length) (hbound : s + (w + b) ≤ p.T)
    (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
      .ordinary last lastMemory)
    (hnone : last.lastDown = none) :
    ∀ j : Fin b, ∃ prior priorMemory,
      (B[j.val]'(Nat.lt_of_lt_of_le j.isLt hb)).input.state.followers i =
        .ordinary prior priorMemory ∧ prior.lastDown = none := by
  intro j
  let pref := actualPrefix rate source rewards C_star C_h hcross count hspan b hbound
  have hgeometry := window_geometry rate source rewards C_star C_h hcross count hspan hshort
  have hlen : w + b ≤ count := by omega
  have hrecords : pref.records = (E).records.take (w + b) :=
    run_prefix_records initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count (w + b)
      hspan hlen active
  have hjB : j.val < (B).length := Nat.lt_of_lt_of_le j.isLt hb
  have hlookup := (ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort ⟨j.val, hjB⟩).1
  have hjE : w + j.val < (E).records.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hrecordE : (E).records[w + j.val]'hjE = B[j.val] :=
    (List.getElem?_eq_some_iff.mp hlookup).2
  have hjPref : w + j.val < pref.records.length := by
    have hlength : pref.records.length = w + b :=
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (w + b) hbound active
    rw [hlength]
    omega
  have hrecord : pref.records[w + j.val]'hjPref = B[j.val] := by
    simpa only [hrecords, List.getElem_take] using hrecordE
  have hsuffix := ReferenceFollowerReplyChronology.connected_drop_from_input
    pref.connected (w + j.val) hjPref
  obtain ⟨prior, priorMemory, hprior, hstart, _hframe, _hwitness⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology hsuffix i last lastMemory hfinal
  have hzero : acceptedStart last = 0 := by simp only [acceptedStart, hnone]
  have hpriorZero : acceptedStart prior = 0 := by omega
  rw [hrecord] at hprior
  exact ⟨prior, priorMemory, hprior, lastDown_none_of_start_zero prior hpriorZero⟩


include hshort in
private theorem threshold_at_old_boundary
    (b : ℕ) (hb : b ≤ (B).length) (hbound : s + (w + b) ≤ p.T)
    (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
      .ordinary last lastMemory)
    (hnone : last.lastDown = none)
    (q : ℕ) (hq : 1 < q)
    (hreach : q ≤ (actualDownPositives i ((B).take b)).length) :
    ∃ k : ℕ, ∃ hkB : k < (B).length,
      0 < k ∧ k < b ∧
      (actualDownPositives i ((B).take (k + 1))).length = q ∧
      (∀ j : ℕ, j ≤ k → (actualDownPositives i ((B).take j)).length < q) ∧
      ActiveFollowerDownAcceptance.downSelected p i (B[k]'hkB).input.row (B[k]'hkB).input.time ∧
      0 < (preparedOwnObservation (B[k]'hkB) i).val.val ∧
      actualDownPositives i ((B).take (k + 1)) =
        actualDownPositives i ((B).take k) ++
          [⟨(B[k]'hkB).input.time, ((B[k]'hkB).input.row.2 (B[k]'hkB).input.time).2 (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩] ∧
      ∀ j : Fin (k + 1), ∃ prior priorMemory,
        (B[j.val]'(by omega)).input.state.followers i = .ordinary prior priorMemory ∧
          prior.lastDown = none := by
  let f := fun n => (actualDownPositives i ((B).take n)).length
  have hstep (n : ℕ) (hn : n < b) : f (n + 1) ≤ f n + 1 := by
    have hnB : n < (B).length := Nat.lt_of_lt_of_le hn hb
    have hsplit := positive_step_length i B n hnB
    have hsingle := positive_singleton_length i B[n]
    dsimp only [f]
    omega
  have hzero : f 0 = 0 := rfl
  obtain ⟨k, hkpos, hkb, hcount, hpriorCount⟩ := first_attainment b q f hzero hstep hq hreach
  have hkB : k < (B).length := Nat.lt_of_lt_of_le hkb hb
  have hsplit := positive_step_length i B k hkB
  have hstrict := hpriorCount k le_rfl
  have hsingle : 0 < (actualDownPositives i [B[k]]).length := by
    change (actualDownPositives i ((B).take (k + 1))).length = q at hcount
    change (actualDownPositives i ((B).take k)).length < q at hstrict
    omega
  obtain ⟨hselected, hpositive, hentry⟩ := positive_singleton_selected i B[k] hsingle
  have hlist : actualDownPositives i ((B).take (k + 1)) =
      actualDownPositives i ((B).take k) ++
        [⟨(B[k]'hkB).input.time, ((B[k]'hkB).input.row.2 (B[k]'hkB).input.time).2 (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩] := by
    rw [List.take_succ_eq_append_getElem hkB, positive_entries_append, hentry]
  have hprior := actual_first_collection_down_old_prefix_inputs
    rate source rewards C_star C_h hcross count hspan hshort b hb hbound i last lastMemory hfinal hnone
  refine ⟨k, hkB, hkpos, hkb, hcount, hpriorCount, hselected, hpositive, hlist, ?_⟩
  intro j
  exact hprior ⟨j.val, by omega⟩


/-- One actual initialized dispatch, its unchanged incoming cutoff banks, and
all original boundaries through its terminal successor. At an OLD boundary,
a reached DOWN threshold has a real first attaining round, strictly positive
index, exact inclusive count, and produced ordinary OLD inputs at every prior
round. The only stage selectors are the displayed local `lastDown = none` and
actual count inequality, after the dispatch and all boundaries are produced. -/
theorem actual_first_collection_down_boundaries_and_attainment :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let P0 := out.payload
      out.window = B ∧ P0.sigma.val = s ∧
      (∀ i, (P0.downRecord i).val.sigma = s + 1 ∧ (P0.downRecord i).val.q = 0) ∧
      ∀ i : Fin (p.m - 1), ∃ hBlen : 0 < (B).length,
      ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
      ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
        (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
        ActiveFollowerLifecycle.localStateDomainValid cutoffState ∧
        ActiveFollowerLifecycle.localBufferValid cutoffState ∧
        ActiveFollowerLifecycle.downDecoderStateValid cutoffState ∧
        ActiveFollowerLifecycle.startRound rate.eta (B[0]'hBlen).input.time cutoffState cutoffMemory =
          .ok ({cutoffState with status := .unoccupied}, cutoffMemory) ∧
        (cutoffState.status = .unoccupied → cutoffState.lastDown = none ∧
          cutoffState.S = 0 ∧ cutoffState.delta = 0 ∧ cutoffState.backlog = 0) ∧
        (cutoffState.status ≠ .unoccupied → cutoffState.lastDown = some (P0.downRecord i)) ∧
        let W0 := cutoffState.downBatch
        let Q := AffineBatchDecoder.quota p
        let q := Q - W0.pending.length + Q
        W0.pending.length < Q ∧ Q < q ∧ q ≤ 2 * Q ∧ 1 < q ∧
        ∀ (b : ℕ) (hb : b ≤ out.ell),
        ∃ hbound : s + (w + b) ≤ p.T,
        ∃ before : ReferencePrelaunchFollower.State p rate.eta,
        ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
          (∀ hlt : b < (B).length,
            (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
              (B[b]'hlt).input.state) ∧
          (∀ hpos : 0 < b,
            (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
              (B[b - 1]'(by have := out.withinWindow; rw [out.windowIsActual] at this; omega)).output.next) ∧
          (b = out.ell →
            (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState =
              d.record.output.next) ∧
          (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
            .ordinary before memory ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          ActiveFollowerLifecycle.localBufferValid before ∧
          ActiveFollowerLifecycle.downDecoderStateValid before ∧
          (b = 0 → before = cutoffState ∧ memory = cutoffMemory ∧
            ∃ r owned base,
              (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.coordinator =
                .live r owned base ∧ P0 = r.payload) ∧
          (0 < b → before.status = .unoccupied ∧
            before.S ≤ p.T * D p ∧ before.delta ≤ D p ∧ before.backlog ≤ p.T * D p ∧
            before.S + before.backlog ≤ w * D p ∧
            (∀ saved ∈ before.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
            (before.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
            (∀ saved ∈ before.buffer, ∃ q : ℕ, q ≤ D p ∧
              saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
            before.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ before.buffer, saved.calendarRound < s + w + b + 1) ∧
            before.downBatch.pending.length < Q ∧
            (∀ batch ∈ before.downBatch.completed, batch.length = Q) ∧
            (before.lastDown = none ∧ before.S = 0 ∧ before.delta = 0 ∧ before.backlog = 0 ∨
              before.lastDown = some (P0.downRecord i)) ∧
            ((actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.coordinator =
              .dagger ∨ ∃ ledger saved,
              (actualPrefix rate source rewards C_star C_h hcross count hspan b hbound).finalState.coordinator =
                .collection P0 ledger saved)) ∧
          (before.lastDown = none → ∀ j : Fin b, ∃ prior priorMemory,
            (B[j.val]'(by have := out.withinWindow; rw [out.windowIsActual] at this; omega)).input.state.followers i =
              .ordinary prior priorMemory ∧ prior.lastDown = none) ∧
          (before.lastDown = none → q ≤ (actualDownPositives i ((B).take b)).length →
            ∃ k : Fin out.ell, ∃ hkB : k.val < (B).length,
              0 < k.val ∧ k.val < b ∧
              (actualDownPositives i ((B).take (k.val + 1))).length = q ∧
              (∀ j : ℕ, j ≤ k.val → (actualDownPositives i ((B).take j)).length < q) ∧
              ActiveFollowerDownAcceptance.downSelected p i (B[k.val]'hkB).input.row (B[k.val]'hkB).input.time ∧
              0 < (preparedOwnObservation (B[k.val]'hkB) i).val.val ∧
              (B[k.val]'hkB).input.time.val = s + w + k.val ∧
              (B[k.val]'hkB).input.rows = source.1.2 ∧
              (B[k.val]'hkB).input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              (B[k.val]'hkB).input.rewards = rewards ∧
              (actualDownPositives i ((B).take (k.val + 1))).Pairwise
                (fun earlier later => earlier.time.val < later.time.val) ∧
              (∀ entry ∈ actualDownPositives i ((B).take (k.val + 1)),
                s + w ≤ entry.time.val ∧ entry.time.val ≤ s + w + k.val) ∧
              (∀ entry ∈ actualDownPositives i ((B).take (k.val + 1)),
                entry.sample = ((source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 entry.time).2
                    (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))) ∧
              (∃ current currentMemory,
                (B[k.val]'hkB).input.state.followers i = .ordinary current currentMemory ∧
                current.lastDown = none ∧
                current.downBatch = foldDownCalls (actualDownCalls i ((B).take k.val)) W0 ∧
                AffineBatchDecoder.collected current.downBatch =
                  AffineBatchDecoder.collected W0 ++ actualDownPositives i ((B).take k.val)) ∧
              actualDownPositives i ((B).take (k.val + 1)) =
                actualDownPositives i ((B).take k.val) ++
                  [⟨(B[k.val]'hkB).input.time,
                    ((B[k.val]'hkB).input.row.2 (B[k.val]'hkB).input.time).2
                      (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩] ∧
              ∀ j : Fin (k.val + 1), ∃ prior priorMemory,
                (B[j.val]'(by omega)).input.state.followers i = .ordinary prior priorMemory ∧
                  prior.lastDown = none) := by
  classical
  obtain ⟨d, hproduced⟩ :=
    ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
      rate source rewards C_star C_h count hcross hspan hshort
  rcases hproduced with ⟨hwindow, hsigma, hrecords, hpure⟩
  have hwindow' : d.stream.window = B := hwindow
  refine ⟨d, hwindow', hsigma, hrecords, ?_⟩
  intro i
  obtain ⟨hBlen, r, owned, base, cutoffState, cutoffMemory, hcoord,
      _hsigmaCut, _hzeroScores, hcut, hunoccupied, hoccupied,
      hdomainCut, hbufferCut, hdecoderCut, hreset⟩ :=
    ReferenceFirstCollectionDownThresholdDetection.actual_first_collection_down_cutoff_seed
      rate source rewards C_star C_h count hcross hspan hshort i
  have hlookup := (ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort ⟨0, hBlen⟩).1
  have hcoordE : ((E).records[w]'(by
      have hcount : (E).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
      omega)).input.state.coordinator = .live r owned base := by
    have hrecord : (E).records[w]'(by
        have hcount : (E).records.length = count :=
          ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
        omega) = B[0] := by
      exact (List.getElem?_eq_some_iff.mp hlookup).2
    rw [hrecord]
    exact hcoord
  have hpayload := stream_payload_eq rate source rewards C_star C_h hcross count hspan
    hshort d r owned base hcoordE
  refine ⟨hBlen, cutoffState, cutoffMemory, hcut, hdomainCut, hbufferCut,
    hdecoderCut, hreset, hunoccupied, ?_, ?_⟩
  · simpa only [hpayload] using hoccupied
  · dsimp only
    let Q := AffineBatchDecoder.quota p
    let q := Q - cutoffState.downBatch.pending.length + Q
    have hQ : 0 < Q := AffineBatchDecoder.quota_pos p
    have hk0 : cutoffState.downBatch.pending.length < Q := hdecoderCut.1
    have hquota : Q < q ∧ q ≤ 2 * Q ∧ 1 < q := by
      dsimp only [q]
      omega
    refine ⟨hk0, hquota.1, hquota.2.1, hquota.2.2, ?_⟩
    intro b hb
    have hbB : b ≤ (B).length := by
      have hwithin := d.stream.withinWindow
      rw [hwindow'] at hwithin
      omega
    by_cases hpos : 0 < b
    · obtain ⟨hbound, hinput, houtput, hcoordinator, hfollowers⟩ :=
        actual_first_collection_down_positive_prefix_boundary
          rate source rewards C_star C_h hcross count hspan hshort d b hbB hpos
      obtain ⟨before, memory, hstate, hstatus, hdomain, hbuffer, hdecoder,
          hS, hdelta, hbacklog, hmass, hcalendar, hnodup, hquantized,
          hpairwise, hchronology, hpending, hcompleted, hlast⟩ := hfollowers i
      refine ⟨hbound, before, memory, hinput, fun _ => houtput, ?_, hstate,
        hdomain, hbuffer, hdecoder, ?_, ?_, ?_, ?_⟩
      · intro hterminal
        have hlast : d.last.val = b - 1 := by have := d.lastIsLast; omega
        have hlastRecord : B[b - 1]'(by omega) = d.record := by
          have hget : (B)[b - 1]? = some d.record := by
            simpa only [hwindow', hlast] using d.recordAt
          exact (List.getElem?_eq_some_iff.mp hget).2
        exact houtput.trans (congrArg (fun record => record.output.next) hlastRecord)
      · intro hzero
        omega
      · intro _
        exact ⟨hstatus, hS, hdelta, hbacklog, hmass, hcalendar, hnodup,
          hquantized, hpairwise, hchronology, hpending, hcompleted, hlast, hcoordinator⟩
      · intro hnone
        exact actual_first_collection_down_old_prefix_inputs
          rate source rewards C_star C_h hcross count hspan hshort b hbB hbound
          i before memory hstate hnone
      · intro hnone hreach
        obtain ⟨k, hkB, hkpos, hkb, hcount, hpriorCount, hselected, hpositive, hentry, hprior⟩ :=
          threshold_at_old_boundary rate source rewards C_star C_h hcross count hspan hshort
            b hbB hbound i before memory hstate hnone q hquota.2.2 hreach
        have hkell : k < d.stream.ell := Nat.lt_of_lt_of_le hkb hb
        have hkOut : k < d.stream.window.length := by rw [hwindow']; exact hkB
        have hdate := (d.stream.alignment ⟨k, hkOut⟩).2
        have horiginal := d.stream.originalInputs ⟨k, hkOut⟩
        have hdate' : (B[k]'hkB).input.time.val = s + w + k := by
          have hdateB : (B[k]'hkB).input.time.val + 1 = s + w + 1 + k := by
            simpa only [hwindow'] using hdate
          omega
        have horiginal' : (B[k]'hkB).input.rows = source.1.2 ∧
            (B[k]'hkB).input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            (B[k]'hkB).input.rewards = rewards := by
          simpa only [hwindow'] using horiginal
        obtain ⟨current, currentMemory, hcurrent, hcurrentNone⟩ := hprior ⟨k, by omega⟩
        have hcurrentOut :
            (d.stream.window[k]'hkOut).input.state.followers i = .ordinary current currentMemory := by
          simpa only [hwindow'] using hcurrent
        obtain ⟨_hreceivers, hBlenPure, cutoffPure, cutoffMemoryPure, hcutPure,
            hbank, _hdiagnostic⟩ := hpure ⟨k, hkell⟩ hkpos i current currentMemory hcurrentOut hcurrentNone
        have hseedEq : cutoffPure = cutoffState :=
          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hcutPure.symm.trans hcut)).1
        subst cutoffPure
        rcases hbank with ⟨hfold, hcollected, _hk0, _holdTimes, _hcalendarCalls,
          hpair, htimes, hsamples, _hcompletedSizes, _hseedPair, _hseedTimes, _hcompletedReplay⟩
        let entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
          ⟨(B[k]'hkB).input.time, ((B[k]'hkB).input.row.2 (B[k]'hkB).input.time).2
            (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p)))⟩
        have hentrySample : entry.sample =
            ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 entry.time).2
              (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p))) := by
          change (((B[k]'hkB).input.rows (B[k]'hkB).input.selected).2
            (B[k]'hkB).input.time).2 _ = _
          rw [horiginal'.1, horiginal'.2.1]
        have hpairInclusive : (actualDownPositives i ((B).take (k + 1))).Pairwise
            (fun earlier later => earlier.time.val < later.time.val) := by
          rw [hentry]
          apply List.pairwise_append.mpr
          refine ⟨hpair, by simp, ?_⟩
          intro earlier hearlier later hlater
          have hlaterEq : later = entry := List.mem_singleton.mp hlater
          subst later
          have htime := (htimes earlier hearlier).2
          change earlier.time.val < (B[k]'hkB).input.time.val
          rw [hdate']
          exact htime
        have htimesInclusive : ∀ e ∈ actualDownPositives i ((B).take (k + 1)),
            s + w ≤ e.time.val ∧ e.time.val ≤ s + w + k := by
          rw [hentry]
          intro e he
          rcases List.mem_append.mp he with hold | hnew
          · obtain ⟨hlo, hhi⟩ := htimes e hold
            exact ⟨hlo, Nat.le_of_lt hhi⟩
          · have heq : e = entry := List.mem_singleton.mp hnew
            subst e
            change s + w ≤ (B[k]'hkB).input.time.val ∧
              (B[k]'hkB).input.time.val ≤ s + w + k
            rw [hdate']
            omega
        have hsamplesInclusive : ∀ e ∈ actualDownPositives i ((B).take (k + 1)),
            e.sample = ((source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 e.time).2
                (0, (⟨i.val, i.isLt⟩ : Fin (ContinuousLearningRows.d p))) := by
          rw [hentry]
          intro e he
          rcases List.mem_append.mp he with hold | hnew
          · exact hsamples e hold
          · have heq : e = entry := List.mem_singleton.mp hnew
            subst e
            exact hentrySample
        exact ⟨⟨k, hkell⟩, hkB, hkpos, hkb, hcount, hpriorCount, hselected,
          hpositive, hdate', horiginal'.1, horiginal'.2.1, horiginal'.2.2,
          hpairInclusive, htimesInclusive, hsamplesInclusive,
          ⟨current, currentMemory, hcurrent, hcurrentNone, hfold, hcollected⟩, hentry, hprior⟩
    · have hbzero : b = 0 := by omega
      subst b
      have hgeometry := window_geometry rate source rewards C_star C_h hcross count hspan hshort
      let hbound : s + (w + 0) ≤ p.T := by omega
      have hendpoints := prefix_endpoints rate source rewards C_star C_h hcross count hspan
        hshort 0 hbB hbound
      have hboundary := hendpoints.1 hBlen
      have hstate : (actualPrefix rate source rewards C_star C_h hcross count hspan 0 hbound).finalState.followers i =
          .ordinary cutoffState cutoffMemory := by rw [hboundary]; exact hcut
      refine ⟨hbound, cutoffState, cutoffMemory, hendpoints.1, hendpoints.2, ?_,
        hstate, hdomainCut, hbufferCut, hdecoderCut, ?_, ?_, ?_, ?_⟩
      · intro hterminal
        have := d.stream.positiveLength
        omega
      · intro _
        refine ⟨rfl, rfl, r, owned, base, ?_, hpayload⟩
        rw [hboundary]
        exact hcoord
      · intro h
        omega
      · intro _ j
        exact Fin.elim0 j
      · intro _ hreach
        have hzero : (actualDownPositives i ((B).take 0)).length = 0 := rfl
        change q ≤ (actualDownPositives i ((B).take 0)).length at hreach
        omega

end Actual

end Bandits.Support.ReferenceFirstCollectionDownThresholdAttainment
