/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
public import Bandits.Support.HandoverStoppedServiceQuota

/-!
# Actual first-live raw DOWN bank prefix

This producer follows the original corrected-source first-live window and its
retained DOWN calls.  Its fold includes the current detecting call and keeps
the inherited pending entries and completed batches from the actual seed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceFirstLiveDownCompletionReadout
open Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
open Bandits.Support.HandoverStoppedDecoderReplay
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceLocalReleaseGateChronology
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverRawPrefix

private theorem collected_length_of_wellFormed {p : ConstructorDimensions.Parameters}
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hstate : ReferenceFollowerDecoderChronology.downBatchWellFormed state) :
    (AffineBatchDecoder.collected state).length =
      state.completed.length * AffineBatchDecoder.quota p + state.pending.length := by
  have hsumFor : ∀ batches : List (List (AffineBatchDecoder.Entry p.T
      (AffineBatchDecoder.width p))),
      (∀ batch ∈ batches, batch.length = AffineBatchDecoder.quota p) →
      (batches.map List.length).sum = batches.length * AffineBatchDecoder.quota p := by
    intro batches
    induction batches with
    | nil => simp
    | cons batch rest ih =>
        intro hbatch
        have hhead := hbatch batch (by simp)
        have htail := ih (by
          intro entry hentry
          exact hbatch entry (by simp [hentry]))
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.succ_mul]
        rw [hhead, htail]
        omega
  have hsum := hsumFor state.completed hstate.2
  simp only [AffineBatchDecoder.collected, List.length_append,
    List.length_flatten, hsum]

private theorem run_records_take_prefix {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n count : ℕ) (hn : n ≤ count) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        ((Nat.add_le_add_left hn start).trans hspan) hmode).records := by
  obtain ⟨suffix, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (count - n) (by omega) hmode
  have hp' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        ((Nat.add_le_add_left hn start).trans hspan) hmode).records ++ suffix := by
    simpa only [Nat.add_sub_of_le hn] using hp
  have hpref : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      ((Nat.add_le_add_left hn start).trans hspan) hmode).records.IsPrefix
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records :=
    ⟨suffix, hp'.symm⟩
  simpa only [ReferenceActivePhysicalHorizon.run_record_count] using
    (List.prefix_iff_eq_take.mp hpref).symm

private theorem pending_completed_counts {p : ConstructorDimensions.Parameters}
    (initial state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (positives : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hinitial : ReferenceFollowerDecoderChronology.downBatchWellFormed initial)
    (hstate : ReferenceFollowerDecoderChronology.downBatchWellFormed state)
    (hcollected : AffineBatchDecoder.collected state =
      AffineBatchDecoder.collected initial ++ positives) :
    state.pending.length =
        (initial.pending.length + positives.length) % AffineBatchDecoder.quota p ∧
      state.completed.length = initial.completed.length +
        (initial.pending.length + positives.length) / AffineBatchDecoder.quota p := by
  let q := AffineBatchDecoder.quota p
  let n := initial.pending.length + positives.length
  let d := state.completed.length - initial.completed.length
  have hq : 0 < q := by exact AffineBatchDecoder.quota_pos p
  have hi : initial.pending.length < q := by simpa [q] using hinitial.1
  have hs : state.pending.length < q := by simpa [q] using hstate.1
  have hlen := collected_length_of_wellFormed initial hinitial
  have hlen' := collected_length_of_wellFormed state hstate
  have htotal : state.completed.length * q + state.pending.length =
      initial.completed.length * q + n := by
    calc
      state.completed.length * q + state.pending.length =
          (AffineBatchDecoder.collected state).length := by simpa [q] using hlen'.symm
      _ = (AffineBatchDecoder.collected initial ++ positives).length :=
        congrArg List.length hcollected
      _ = initial.completed.length * q + initial.pending.length + positives.length := by
        rw [List.length_append, hlen]
      _ = initial.completed.length * q + n := by simp [n, Nat.add_assoc]
  have hle : initial.completed.length ≤ state.completed.length := by
    by_contra hnot
    have hlt : state.completed.length < initial.completed.length := Nat.lt_of_not_ge hnot
    have hleft : state.completed.length * q + state.pending.length <
        (state.completed.length + 1) * q := by
      rw [Nat.add_mul]
      omega
    have hright : (state.completed.length + 1) * q ≤
        initial.completed.length * q + n := by
      have : state.completed.length + 1 ≤ initial.completed.length := by omega
      calc
        (state.completed.length + 1) * q ≤ initial.completed.length * q :=
          Nat.mul_le_mul_right q this
        _ ≤ initial.completed.length * q + n := Nat.le_add_right _ _
    omega
  have hdecomp : state.completed.length = initial.completed.length + d := by
    simp [d, Nat.add_sub_of_le hle]
  have hn : n = state.pending.length + q * d := by
    have hpart : d * q + state.pending.length = n := by
      apply Nat.add_left_cancel (n := initial.completed.length * q)
      calc
        initial.completed.length * q + (d * q + state.pending.length) =
            (initial.completed.length * q + d * q) + state.pending.length := by omega
        _ = (initial.completed.length + d) * q + state.pending.length := by
          rw [← Nat.add_mul]
        _ = state.completed.length * q + state.pending.length := by rw [hdecomp]
        _ = initial.completed.length * q + n := htotal
    calc
      n = d * q + state.pending.length := hpart.symm
      _ = state.pending.length + q * d := by rw [Nat.add_comm, Nat.mul_comm]
  constructor
  · change state.pending.length = n % q
    rw [hn, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt hs).symm
  · change state.completed.length = initial.completed.length + n / q
    rw [hdecomp, hn, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hs]
    simp [d]

private theorem roundRecord_selection_some_iff
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (h : left = right) (selected : ReferenceActivePhysicalStep.Selection right.input) :
    left.output.preparation.coordinator.selection =
        some ((congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate) => record.input) h).symm ▸ selected) ↔
      right.output.preparation.coordinator.selection = some selected := by
  cases h
  rfl

private theorem roundRecord_selection_payload_cast
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (h : left = right) (selected : ReferenceActivePhysicalStep.Selection right.input) :
    ((congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input) h).symm ▸ selected).view.payload =
      selected.view.payload := by
  cases h
  rfl

/-- The raw first-live bank at every retained call, including a call whose
physical recovery subsequently fails.  The inherited decoder state is the
actual corrected-launch seed, and its completed history is preserved. -/
theorem actual_called_prefix_bank_counts_and_raw_false
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed
    let beta := CanonicalRecordingRates.beta p rate.eta.val
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z rewards C_star C_h hc
    let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      ((W.get k).output.followers i).downInput = some logged →
      ((W.get k).output.followers i).down = some cut →
      cut.rawComparison.isSome = true →
      let r := W.get k
      let d0 := (seed.followers i).downBatch
      let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (W.take k.val)
      let A := ReferenceFollowerDownDecoderReplay.replayDownCalls i (W.take k.val) d0
      let tr := ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
      let added := A.pending ++ AffineBatchDecoder.positiveAt p tr r.input.time
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
          rate rewards C_star C_h z = some selected.view.payload ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h r.input.time z = some r ∧
        let M : HandoverStoppedDecoderReplay.Down p beta :=
          selected.view.payload.downRecord i
        r.input.time.val = s + k.val ∧ M.val.sigma = s + 1 ∧
        d0.pending.length < AffineBatchDecoder.quota p ∧
        (∀ e : HandoverStoppedDecoderReplay.DecoderEntry p,
          e ∈ d0.pending → e.time.val < s) ∧
        logged.downBatch = A ∧
        ReferencePrelaunchFollower.acceptedStart logged = 0 ∧
        AffineBatchDecoder.collected A = AffineBatchDecoder.collected d0 ++ P ∧
        A.pending.length =
          (d0.pending.length + P.length) % AffineBatchDecoder.quota p ∧
        A.completed.length = d0.completed.length +
          (d0.pending.length + P.length) / AffineBatchDecoder.quota p ∧
        cut.raw = (AffineBatchDecoder.decodeStep p tr A r.input.time).2 ∧
        (AffineBatchDecoder.decodeStep p tr A r.input.time).1 =
          ReferenceFollowerDownDecoderReplay.replayDownCalls i
            (W.take (k.val + 1)) d0 ∧
        ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i =
          (if AffineBatchDecoder.quota p ≤ added.length then some added else none) ∧
        cut.expectedWord = some (HandoverStoppedDecoderReplay.currentWord p beta M) ∧
        cut.ordinaryParse = HandoverStoppedDecoderReplay.parseOutput p beta cut.raw ∧
        (HandoverStoppedDecoderReplay.falseDecision p beta M 0 r.input.time cut.raw ↔
          ReferenceDownReception.wrongUniqueAccepted cut) := by
  dsimp only
  intro k i logged cut hi hd hraw
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output x).completed
  let beta := CanonicalRecordingRates.beta p rate.eta.val
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z
  let r := W.get k
  let d0 := (seed.followers i).downBatch
  let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (W.take k.val)
  let A := ReferenceFollowerDownDecoderReplay.replayDownCalls i (W.take k.val) d0
  let tr := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
  let added := A.pending ++ AffineBatchDecoder.positiveAt p tr r.input.time
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hc
  let count := p.T - s
  have hs : s ≤ p.T := by
    simpa [s, x, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using
      (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hc
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa [initial, s, x] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hc).2.1
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = s := rfl
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
    hc s count rfl hspan
  let WD := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
  have hcomplete :
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        R.records := by
    have h := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch
    simpa [R, ReferenceLocalReleaseGateChronology.sourceRun, hstart] using h
  have hW : W = WD := by
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) =
      R.records.takeWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
    rw [hcomplete]
  have hlenW : W.length = WD.length := congrArg List.length hW
  have hkWD : k.val < WD.length := by rw [← hlenW]; exact k.isLt
  let kWD : Fin WD.length := ⟨k.val, hkWD⟩
  have hkVal : kWD.val = k.val := rfl
  have hget : W.get k = WD.get kWD := by
    have hgetOpt := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)) => records[k.val]?) hW
    rw [List.getElem?_eq_getElem k.isLt,
      List.getElem?_eq_getElem hkWD] at hgetOpt
    exact Option.some.inj hgetOpt
  have hiR : ((WD.get kWD).output.followers i).downInput = some logged := by
    rw [← hget]
    exact hi
  have hdR : ((WD.get kWD).output.followers i).down = some cut := by
    rw [← hget]
    exact hd
  have hprefix : WD.IsPrefix R.records := List.takeWhile_prefix _
  have hkR : k.val < R.records.length := by
    rw [← hkVal]
    exact kWD.isLt.trans_le hprefix.length_le
  have hkCount : k.val ≤ count := by
    have hlen : R.records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    rw [hlen] at hkR
    exact Nat.le_of_lt hkR
  have htakeRun := run_records_take_prefix initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val count hkCount hspan
    hmode
  have htakePrefix : WD.take k.val = R.records.take k.val := by
    apply (hprefix.take k.val).eq_of_length
    have hkW : k.val ≤ WD.length := by
      rw [← hkVal]
      exact kWD.isLt.le
    have hkRecords : k.val ≤ R.records.length := hkR.le
    simp only [List.length_take, Nat.min_eq_left hkW, Nat.min_eq_left hkRecords]
  have htakeWindow : W.take k.val = R.records.take k.val := by
    rw [hW, htakePrefix]
  have hboundary := ReferenceFirstLiveDownCompletionReadout.actual_first_live_unaccepted_boundary
    rate z rewards C_star C_h count hc hspan kWD i logged hiR
  obtain ⟨hbound, before, memory, hbefore, _, _, hstatus, hlast, hloggedLast, hbank⟩ :=
    hboundary
  obtain ⟨active, hactive, hseedBatch⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
      rate z rewards C_star C_h hc
  have hactiveEq : active = initial :=
    Option.some.inj (hactive.symm.trans hlaunch)
  subst active
  have hseedConfig := hseedBatch i
  obtain ⟨seedState, seedMemory, hseedOrdinary, hseedStatus, hseedWell,
    hseedChronological, hseedStamps⟩ := hseedConfig
  have hseedState : seedState = seed.followers i := by
    have h := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hseedOrdinary.symm.trans (seed.configuration i))
    exact h.1
  have hseedBank : seedState.downBatch = d0 := by simp [d0, hseedState]
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  have hrunReplay := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    initial z.1.2 J rewards s k.val hbound
    hmode hseedBatch i seedState seedMemory
    hseedOrdinary before memory hbefore
  have hrunEndpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial z.1.2 J rewards s k.val hbound
    hmode hseedBatch i before memory hbefore
  have htakeRunEq :
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val hbound
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z rewards C_star C_h hc).activeAtStart).records = R.records.take k.val := by
    simpa [R, ReferenceLocalReleaseGateChronology.sourceRun] using htakeRun.symm
  have hbankEq : logged.downBatch = A := by
    calc
      logged.downBatch = before.downBatch := hbank
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val hbound hmode).records
          seedState.downBatch := hrunReplay.1
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val hbound hmode).records d0 := by
        rw [hseedBank]
      _ = A := by
        simp only [A, ReferenceFollowerDownDecoderReplay.replayDownCalls,
          htakeRunEq, ← htakeWindow]
  have hbeforeA : before.downBatch = A := by
    calc
      before.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val hbound hmode).records
          seedState.downBatch := hrunReplay.1
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val hbound hmode).records d0 := by
        rw [hseedBank]
      _ = A := by
        simp only [A, ReferenceFollowerDownDecoderReplay.replayDownCalls,
          htakeRunEq, ← htakeWindow]
  have hcollected : AffineBatchDecoder.collected A =
      AffineBatchDecoder.collected d0 ++ P := by
    have hpos := hrunReplay.2.1
    rw [hseedBank, htakeRunEq, ← htakeWindow] at hpos
    have hpos' : AffineBatchDecoder.collected before.downBatch =
        AffineBatchDecoder.collected d0 ++ P := by simpa [P] using hpos
    simpa [hbeforeA] using hpos'
  have hstateWF : ReferenceFollowerDecoderChronology.downBatchWellFormed A := by
    simpa [hbeforeA] using hrunEndpoint.1.1
  have hd0WF : ReferenceFollowerDecoderChronology.downBatchWellFormed d0 := by
    simpa [d0, hseedState] using hseedWell
  have hcount := pending_completed_counts d0 A P hd0WF hstateWF hcollected
  have hloggedStart : ReferencePrelaunchFollower.acceptedStart logged = 0 := by
    simp [ReferencePrelaunchFollower.acceptedStart, hloggedLast]
  have htakeCall : W.take (k.val + 1) = W.take k.val ++ [r] := by
    change W.take (k.val + 1) = W.take k.val ++ [W.get k]
    exact List.take_succ_eq_append_getElem k.isLt
  have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
    r i logged cut hi hd hraw
  have hreconstruct := ReferenceFirstLiveDownCompletionReadout.retained_call_reconstructs
    r i logged hi
  let call : ReferenceFollowerDownDecoderReplay.Call p :=
    (r.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
      r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
  have hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call := by
    obtain ⟨code, hcode, hdecode⟩ := hreconstruct
    rw [← ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i r,
      hcode, Option.map_some, hdecode]
  have hpositives :
      ReferenceFollowerDownDecoderReplay.actualDownPositives i (W.take (k.val + 1)) = P ++
        AffineBatchDecoder.positiveAt p tr r.input.time := by
    rw [htakeCall]
    simp only [P, ReferenceFollowerDownDecoderReplay.actualDownPositives,
      ReferenceFollowerDownDecoderReplay.actualDownCalls,
      List.filterMap_append, List.filterMap_cons, hcall,
      List.filterMap_nil, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  have hdecodeState :
      (AffineBatchDecoder.decodeStep p tr A r.input.time).1 =
        ReferenceFollowerDownDecoderReplay.replayDownCalls i (W.take (k.val + 1)) d0 := by
    rw [htakeCall]
    simp only [ReferenceFollowerDownDecoderReplay.replayDownCalls,
      ReferenceFollowerDownDecoderReplay.foldDownCalls,
      ReferenceFollowerDownDecoderReplay.actualDownCalls,
      List.filterMap_append, List.filterMap_cons, hcall,
      List.filterMap_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ReferenceFollowerDownDecoderReplay.replayDownCall,
      ReferenceFollowerDownDecoderReplay.replayDownCalls,
      ReferenceFollowerDownDecoderReplay.foldDownCalls,
      ReferenceFollowerDownDecoderReplay.actualDownCalls] at *
    simp [A, call, tr, ReferenceFollowerDownDecoderReplay.replayDownCalls,
      ReferenceFollowerDownDecoderReplay.foldDownCalls,
      AffineBatchDecoder.decodeStep]
    rfl
  obtain ⟨selected, birth, hselected, hbirth, _, _, hsigma, _, hexpected,
    hsent, hparsed, haccept⟩ :=
      ReferenceFirstLiveDownCompletionReadout.actual_first_live_current_word
        rate z rewards C_star C_h count hc hspan kWD i logged cut hiR hdR hraw
  let selectedW : ReferenceActivePhysicalStep.Selection r.input :=
    (congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input) hget).symm ▸ selected
  have hselectedR : r.output.preparation.coordinator.selection = some selectedW := by
    change (W.get k).output.preparation.coordinator.selection = some selectedW
    exact (roundRecord_selection_some_iff hget selected).mpr hselected
  have hpayloadCast : selectedW.view.payload = selected.view.payload :=
    roundRecord_selection_payload_cast hget selected
  have hsigmaW : selectedW.view.payload.sigma.val = s := by
    rw [hpayloadCast]
    exact hsigma
  have hexpectedW : cut.expectedWord =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selectedW.view.payload i) := by
    rw [hpayloadCast]
    exact hexpected
  have hrecord :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        r.input.time z = some r := by
    exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k).2
  have hrecordTime : r.input.time.val = s + k.val := by
    have hcalendar :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z k
    have hstart' :
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z = s := rfl
    change ((window rate rewards C_star C_h z).get k).input.time.val = s + k.val
    have htime := hcalendar.1
    rw [hstart'] at htime
    exact htime
  have hpayload :
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
        rate rewards C_star C_h z = some selectedW.view.payload := by
    obtain hzero | ⟨hWpos, firstInstalled, firstSelected, hfirstSelected,
      hfirstInstall, hfirstPayload, _, hpayload0, hrows⟩ :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
        rate rewards C_star C_h z hc
    · omega
    · have hrow := hrows k
      obtain ⟨selected', hselected', hsamePayload, _, _, _, _, _, _⟩ := hrow
      have hselectedEq : selected' = selectedW := Option.some.inj
        (hselected'.symm.trans hselectedR)
      have hfirstToSelected' : some firstInstalled.registers.payload =
          some selected'.view.payload :=
        congrArg (fun payload : AssignmentStartPayload.Input p rate.eta => some payload)
          hsamePayload.symm
      have hselected'ToW : some selected'.view.payload = some selectedW.view.payload :=
        congrArg (fun chosen : ReferenceActivePhysicalStep.Selection r.input =>
          some chosen.view.payload) hselectedEq
      exact hpayload0.trans (hfirstToSelected'.trans hselected'ToW)
  let M : HandoverStoppedDecoderReplay.Down p beta := selectedW.view.payload.downRecord i
  have hMstart : M.val.sigma = s + 1 := by
    have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma
      (selectedW.view.payload.downRecord_fields i)
    change (selectedW.view.payload.downRecord i).val.sigma = s + 1
    rw [hfields, hsigmaW]
  have hcurrentWord :
      CoordinatorLocalArmChoice.storedDownFlatWord selectedW.view.payload i =
        HandoverStoppedDecoderReplay.currentWord p beta M := by
    simp only [CoordinatorLocalArmChoice.storedDownFlatWord,
      AssignmentStartPayload.Input.downWord,
      HandoverStoppedDecoderReplay.currentWord,
      ReferencePrelaunchFollower.codecParams]
    rfl
  have hExpected : cut.expectedWord =
      some (HandoverStoppedDecoderReplay.currentWord p beta M) := by
    rw [hexpectedW, hcurrentWord]
    rfl
  rcases hfields with ⟨_, _, _, _, _, hrawEq, hexpectActual,
    hordinaryParse, hordinaryAccept, hcmp⟩
  have hcodec : ReferencePrelaunchFollower.codecParams p rate.eta =
      AffineBatchDecoder.codecParams p beta := by
    rfl
  have hcmpDef := hcmp
  have hparse : cut.ordinaryParse =
      HandoverStoppedDecoderReplay.parseOutput p beta cut.raw := by
    change cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw
    exact hordinaryParse
  have hrawDecode : cut.raw = (AffineBatchDecoder.decodeStep p tr A r.input.time).2 := by
    simpa [ActiveFollowerDownAcceptance.currentDecodeStep, tr, hbankEq,
      hbank] using hrawEq
  have hcompleted :
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i =
        (if AffineBatchDecoder.quota p ≤ added.length then some added else none) := by
    unfold ReferenceFirstLiveDownCompletionReadout.completedDownBatch
    rw [hi, hd]
    simp only [hraw, true_and,
      ReferenceFirstLiveDownCompletionReadout.appendedDownBatch]
    rw [hbankEq]
  refine Exists.intro selectedW ?_
  refine And.intro hselectedR ?_
  refine And.intro hpayload ?_
  refine And.intro hrecord ?_
  constructor
  · simpa [r, s, x] using hrecordTime
  · constructor
    · simpa [s, x] using hMstart
    · constructor
      · exact hd0WF.1
      · constructor
        · intro e he
          have he' : e ∈ seedState.downBatch.pending := by
            simpa [d0, hseedState] using he
          exact hseedStamps e (by
            rw [AffineBatchDecoder.collected]
            exact List.mem_append_right _ he')
        · constructor
          · exact hbankEq
          · constructor
            · exact hloggedStart
            · constructor
              · exact hcollected
              · constructor
                · exact hcount.1
                · constructor
                  · exact hcount.2
                  · constructor
                    · exact hrawDecode
                    · constructor
                      · exact hdecodeState
                      · constructor
                        · exact hcompleted
                        · constructor
                          · exact hExpected
                          · constructor
                            · exact hparse
                            · constructor
                              · rintro ⟨other, hparseOther, hotherNe, hacceptOther⟩
                                have hrawNe : cut.raw ≠ some (HandoverStoppedDecoderReplay.currentWord p beta M) := by
                                  intro heq
                                  have hparsedM := HandoverStoppedDecoderReplay.parseOutput_currentWord p beta M
                                  have hotherEq : other = M := by
                                    apply Option.some.inj
                                    calc
                                      some other = HandoverStoppedDecoderReplay.parseOutput p beta cut.raw :=
                                        hparseOther.symm
                                      _ = HandoverStoppedDecoderReplay.parseOutput p beta
                                          (some (HandoverStoppedDecoderReplay.currentWord p beta M)) := by rw [heq]
                                      _ = some M := hparsedM
                                  exact hotherNe hotherEq
                                have hcmp : cut.rawComparison = some false := by
                                  rw [hcmpDef, hExpected]
                                  by_cases heq : cut.raw =
                                      some (HandoverStoppedDecoderReplay.currentWord p beta M)
                                  · exact (hrawNe heq).elim
                                  · simp [heq]
                                refine ⟨hcmp, ?_, ?_⟩
                                · intro hnone
                                  have hnone' : HandoverStoppedDecoderReplay.parseOutput p beta cut.raw = none := by
                                    simp [HandoverStoppedDecoderReplay.parseOutput,
                                      OrdinaryMessageCodec.parseDown, hnone]
                                  rw [hparseOther] at hnone'
                                  cases hnone'
                                · have hordinaryParsedOther : ReferenceDownReception.ordinaryParse p rate cut.raw = some other := by
                                    exact hordinaryParse.symm.trans (hparse.trans hparseOther)
                                  have hacceptEta : OrdinaryMessageCodec.acceptDown
                                      (ReferencePrelaunchFollower.codecParams p rate.eta) 0
                                      (r.input.time.val + 1) other := by
                                    simpa [ReferencePrelaunchFollower.codecParams,
                                      AffineBatchDecoder.codecParams, beta, r, W,
                                      WaitedWordWindow.sourceRound] using hacceptOther
                                  have htest : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                                      r.input.time logged (ReferenceDownReception.ordinaryParse p rate cut.raw) := by
                                    unfold ReferenceDownReception.ordinaryLocalAcceptanceTest
                                    rw [hordinaryParsedOther]
                                    simpa [ReferencePrelaunchFollower.acceptedStart, hloggedLast,
                                      r, W] using hacceptEta
                                  rw [hordinaryAccept]
                                  exact htest
                              · rintro ⟨hcmp, hrawSome, haccept⟩
                                have hlocal : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                                    r.input.time logged (ReferenceDownReception.ordinaryParse p rate cut.raw) := by
                                  rw [← hordinaryAccept]
                                  exact haccept
                                cases hparsed : ReferenceDownReception.ordinaryParse p rate cut.raw with
                                | none => simp [ReferenceDownReception.ordinaryLocalAcceptanceTest, hparsed] at hlocal
                                | some other =>
                                  have hparseOther : HandoverStoppedDecoderReplay.parseOutput p beta cut.raw = some other := by
                                    exact hparse.symm.trans (hordinaryParse.trans hparsed)
                                  cases hraw : cut.raw with
                                  | none => exact (hrawSome hraw).elim
                                  | some bits =>
                                    rw [hraw] at hparseOther
                                    have hencoded := OrdinaryMessageCodec.parseDown_some_sound
                                      (AffineBatchDecoder.codecParams p beta) (by
                                        change OrdinaryMessageCodec.parseDown
                                          (AffineBatchDecoder.codecParams p beta)
                                          (some ((OrdinaryMessageCodec.wordEquivFlat
                                            (AffineBatchDecoder.codecParams p beta)).symm bits)) = some other
                                        simpa [HandoverStoppedDecoderReplay.parseOutput, hraw] using hparseOther)
                                    have hrawNe : cut.raw ≠
                                        some (HandoverStoppedDecoderReplay.currentWord p beta M) := by
                                      intro heq
                                      have hdec : decide (cut.raw = cut.expectedWord) = false := by
                                        have heq' := hcmpDef.symm.trans hcmp
                                        injection heq' with hdec
                                      rw [heq, hExpected] at hdec
                                      simp at hdec
                                    have hotherNe : other ≠ M := by
                                      intro heq
                                      have hrawEq : cut.raw =
                                          some (HandoverStoppedDecoderReplay.currentWord p beta M) := by
                                        have hflat := congrArg
                                          (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)) hencoded
                                        have hbits : bits = HandoverStoppedDecoderReplay.currentWord p beta M := by
                                          change bits = (OrdinaryMessageCodec.wordEquivFlat
                                            (AffineBatchDecoder.codecParams p beta))
                                            (OrdinaryMessageCodec.encodeDown
                                              (AffineBatchDecoder.codecParams p beta) M)
                                          calc
                                            bits = (OrdinaryMessageCodec.wordEquivFlat
                                                (AffineBatchDecoder.codecParams p beta))
                                                ((OrdinaryMessageCodec.wordEquivFlat
                                                  (AffineBatchDecoder.codecParams p beta)).symm bits) := by simp
                                            _ = (OrdinaryMessageCodec.wordEquivFlat
                                                (AffineBatchDecoder.codecParams p beta))
                                                (OrdinaryMessageCodec.encodeDown
                                                  (AffineBatchDecoder.codecParams p beta) other) := hflat
                                            _ = (OrdinaryMessageCodec.wordEquivFlat
                                                (AffineBatchDecoder.codecParams p beta))
                                                (OrdinaryMessageCodec.encodeDown
                                                  (AffineBatchDecoder.codecParams p beta) M) := by
                                              rw [heq]
                                        rw [hraw]
                                        exact congrArg some hbits
                                      exact (hrawNe hrawEq).elim
                                    have hacceptEta : OrdinaryMessageCodec.acceptDown
                                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                                        (ReferencePrelaunchFollower.acceptedStart logged)
                                        (r.input.time.val + 1) other := by
                                      simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest,
                                        hparsed] using hlocal
                                    have hacceptOther : OrdinaryMessageCodec.acceptDown
                                        (AffineBatchDecoder.codecParams p beta) 0
                                        (WaitedWordWindow.sourceRound r.input.time) other := by
                                      simpa [ReferencePrelaunchFollower.codecParams,
                                        AffineBatchDecoder.codecParams, beta,
                                        hloggedLast, r, W,
                                        WaitedWordWindow.sourceRound,
                                        ReferencePrelaunchFollower.acceptedStart] using hacceptEta
                                    exact ⟨other, hparseOther, hotherNe, hacceptOther⟩

end Bandits.Support.ReferenceFirstLiveHandoverRawPrefix

end
