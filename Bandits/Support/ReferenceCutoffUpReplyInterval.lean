/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCutoffUpOfferConstruction
public import Bandits.Support.ReferenceCollectionUnoccupiedHistory

/-!
# Cutoff UP reply interval

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,164-177,192-209,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module joins the actual adjacent accepted-DOWN cutoff reply seed to the
existing failure-retaining collection-window producers. It retains the same
whole physical run and its payload, collection buffers, decoder state, saved
proposal, and focal follower reply. Conditional UP-word results use only local
actual PREPARE, slot, and sender selectors. They assert no receiver acceptance,
delivery, global queue or score identity, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceCutoffUpReplyInterval

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem foldl_records_extend {initial : State p rate} {α : Type*}
    (step : ReferenceActivePhysicalHorizon.Run initial → α →
      ReferenceActivePhysicalHorizon.Run initial)
    (hstep : ∀ acc entry, ∃ record,
      (step acc entry).records = acc.records ++ [record])
    (entries : List α) (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ suffix, (entries.foldl step acc).records = acc.records ++ suffix := by
  induction entries generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons entry rest ih =>
      obtain ⟨record, hrecord⟩ := hstep acc entry
      obtain ⟨suffix, hsuffix⟩ := ih (step acc entry)
      refine ⟨record :: suffix, ?_⟩
      change (rest.foldl step (step acc entry)).records = acc.records ++ (record :: suffix)
      calc
        (rest.foldl step (step acc entry)).records = (step acc entry).records ++ suffix :=
          hsuffix
        _ = (acc.records ++ [record]) ++ suffix := by rw [hrecord]
        _ = acc.records ++ (record :: suffix) := by simp [List.append_assoc]

private theorem foldCalendar_records_extend {initial : State p rate}
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ suffix,
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows J rewards origin
        intervalStart count horigin hspan active acc).records = acc.records ++ suffix := by
  unfold ReferenceActivePhysicalHorizon.foldCalendar
  apply foldl_records_extend
  intro current entry
  refine ⟨⟨ReferenceActivePhysicalHorizon.roundInputAt initial rows J rewards origin
      active current entry,
    ReferenceActivePhysicalStep.step
      (ReferenceActivePhysicalHorizon.roundInputAt initial rows J rewards origin
        active current entry), rfl⟩, ?_⟩
  rfl

private theorem takeWhile_length_le {α : Type} (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem actualChoice_checkedUpOffer_ne_failure
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (inputState : ReferencePrelaunchFollower.State p rate.eta)
    (inputMemory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary inputState inputMemory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta record.input.time
      inputState inputMemory = .ok (choice, choiceMemory))
    (hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice choiceMemory) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time choice ≠ .failure := by
  have hprepared : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    rfl
  have hlocal : (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (.ordinary inputState inputMemory)).configuration = .ordinary choice choiceMemory := by
    calc
      _ = (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i)).configuration := by rw [hinput]
      _ = (ReferenceFollowerFixedReply.actualChoice record i).configuration :=
        congrArg DeclaredFollowerLocalRound.PreparedRound.configuration hprepared.symm
      _ = .ordinary choice choiceMemory := hchoice
  intro hfailure
  have hfailed := DeclaredFollowerLocalRound.prepare_offer_failure rate i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    inputState choice inputMemory choiceMemory hstart hfailure
  rw [hlocal] at hfailed
  cases hfailed.2

private theorem actualChoice_checkedUpOffer_ne_failure_at_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice choiceMemory) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time choice ≠ .failure := by
  have hprep : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) :=
    record.output.preparation.followers.followers_eq i
  have hspec := ReferenceUpPhysicalHashRule.prepare_arm_spec i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)
  simp only [← hprep, hchoice] at hspec
  intro hfailure
  simp only [hfailure] at hspec

private theorem upOfferFields_eq_of_reply_eq
    {s t : ReferencePrelaunchFollower.State p rate.eta}
    (h : ReferenceFollowerReplyChronology.reply s =
      ReferenceFollowerReplyChronology.reply t) :
    ActiveFollowerQueueOperation.upOfferFields s =
      ActiveFollowerQueueOperation.upOfferFields t := by
  have hparts : s.lastDown = t.lastDown ∧ s.S = t.S ∧
      s.delta = t.delta ∧ s.backlog = t.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using h
  ext
  · exact ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq h
  · exact hparts.2.1
  · exact hparts.2.2.1
  · exact hparts.2.2.2

/-- Literal consumer-facing propositions exposed by U on one original-run
collection interval. The endpoint is included in the prefix and boundary
choice statements; no endpoint record is asserted when the original run ends.
-/
def CollectionWindowProducers
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (_hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.coordinator = .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (_hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.followers i = .ordinary seed seedMemory)
    (_hunoccupied : seed.status = .unoccupied)
    (_hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1) : Prop :=
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
    let W := (R.records.drop b).takeWhile
      fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
    let C := fun (n : ℕ) (hn : n ≤ W.length) =>
      ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n) (by
        have hcount : R.records.length = total := by
          dsimp [R]
          exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start
            total hspan active
        have hdrop : (R.records.drop b).length = total - b := by
          rw [List.length_drop, hcount]
        have htake := takeWhile_length_le
          (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b)
        have hwindow : W.length ≤ total - b := by
          calc
            W.length ≤ (R.records.drop b).length := by
              dsimp [W]
              exact htake
            _ = total - b := hdrop
        omega) active
    (∀ n (hn : n ≤ W.length),
      ((C n hn).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          (C n hn).finalState.coordinator = .collection payload movingLedger movingSaved) ∧
      ((C n hn).finalState.followers i = .dagger ∨
        ∃ state memory,
          (C n hn).finalState.followers i = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed)) ∧
    (∀ n, n < W.length → ∀ (hrecord : b + n < R.records.length), ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown
        (R.records.get ⟨b + n, hrecord⟩) i sigma) ∧
    (∀ n, n ≤ W.length → ∀ (hrecord : b + n < R.records.length),
      (n = W.length →
        ReferenceCollectionPhaseHistory.laterChosen
          (R.records.get ⟨b + n, hrecord⟩).input = true) ∧
      ((ReferenceFollowerFixedReply.actualChoice (R.records.get ⟨b + n, hrecord⟩) i).configuration =
          .dagger ∨
        ∃ state memory,
          (ReferenceFollowerFixedReply.actualChoice (R.records.get ⟨b + n, hrecord⟩) i).configuration =
            .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed))

/-- U's three original-run producers prove the literal window bundle above. -/
theorem collectionWindowProducers_of_boundary
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.coordinator = .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      (by omega) active).finalState.followers i = .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1) :
    CollectionWindowProducers initial rows J rewards start total hspan active b hb payload
      ledger saved hcoord i seed seedMemory hseed hunoccupied hseedStart := by
  dsimp only [CollectionWindowProducers]
  let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
  let W := (R.records.drop b).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  have hprefix := ReferenceCollectionUnoccupiedHistory.run_collection_unoccupied_prefix
    p rate initial rows J rewards start total hspan active b hb payload ledger saved
    hcoord i seed seedMemory hseed hunoccupied hseedStart
  have hnoAppliedDown := ReferenceCollectionUnoccupiedHistory.run_collection_no_appliedDown
    p rate initial rows J rewards start total hspan active b hb payload ledger saved
    hcoord i seed seedMemory hseed hunoccupied hseedStart
  have hboundaryChoice := ReferenceCollectionUnoccupiedHistory.run_collection_boundary_choice_unoccupied
    p rate initial rows J rewards start total hspan active b hb payload ledger saved
    hcoord i seed seedMemory hseed hunoccupied hseedStart
  exact ⟨hprefix, hnoAppliedDown, hboundaryChoice⟩

section Run

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (start count : ℕ) (span : start + count ≤ p.T)
  (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
  (k : ℕ) (hk : k + 1 < count)
  (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))

/-- The S seed is the exact state at the end of the original two-record
boundary. Its moving collection ledger and focal ordinary state are therefore
the actual inputs required by the collection-history consumers.
Sources: `06_interruptions.tex:41-70,164-177,277-284,327-348` and
`05_binary_transport.tex:70-88`. -/
theorem cutoff_after_down_collection_boundary :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let prev := E.records[k]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
    let current := E.records[k + 1]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
    ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload current.input.state.coordinator =
        some payload)
      (_hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
      (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
      (_hf : current.output.next.followers i = .ordinary next nextMemory)
      (_ho : current.output.next.coordinator ≠ .dagger),
      ∃ s memory choice choiceMemory ledger saved,
        current.input.state.followers i = .ordinary s memory ∧
        (ReferenceFollowerFixedReply.actualChoice current i).configuration =
          .ordinary choice choiceMemory ∧
        ActiveFollowerLifecycle.startRound rate.eta current.input.time s memory =
          .ok (choice, choiceMemory) ∧
        s.lastDown = some (payload.downRecord i) ∧
        choice.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply choice =
          ReferenceFollowerReplyChronology.reply s ∧
        next.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply next =
          ReferenceFollowerReplyChronology.reply s ∧
        next.lastDown = some (payload.downRecord i) ∧
        ReferencePrelaunchFollower.acceptedStart next = payload.sigma.val + 1 ∧
        current.output.next.coordinator = .collection payload ledger saved ∧
        let b := k + 2
        let boundaryRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b
          (by omega) active
        boundaryRun.finalState = current.output.next ∧
        boundaryRun.finalState.coordinator = .collection payload ledger saved ∧
        boundaryRun.finalState.followers i = .ordinary next nextMemory ∧
        ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
          (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
          (after : ReferencePrelaunchFollower.State p rate.eta)
          (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
          (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ)
          (lastService : ℕ),
          (prev.output.followers i).downInput = some logged ∧
          (prev.output.followers i).down = some cut ∧
          cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
            logged after raw (payload.downRecord i) scan registers lastService := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  rcases hd with ⟨logged, cut, after, raw, scan, registers, lastService,
    hlogged, hcut, houtcome⟩
  have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i
      (payload.downRecord i) :=
    ⟨logged, cut, after, raw, scan, registers, lastService, hlogged, hcut, houtcome⟩
  obtain ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, hstart,
      hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied, hnextReply,
      hnextDown, hnextStart, hcollection⟩ :=
    ReferenceCutoffUpOfferConstruction.cutoff_after_down_reply_seed
      initial rows J rewards start count span active k hk payload i hp hc hretained
      next nextMemory hf ho
  have hb : k + 2 ≤ count := by omega
  let boundaryRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2)
    (by omega) active
  have hprefixCount : boundaryRun.records.length = k + 2 := by
    dsimp [boundaryRun]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start
      (k + 2) (by omega) active
  have happend : ∃ suffix, E.records = boundaryRun.records ++ suffix := by
    have hsplit := ReferenceActivePhysicalHorizon.run_append initial rows J rewards start
      (k + 2) (count - (k + 2)) (by omega) active
    have hsum : k + 2 + (count - (k + 2)) = count := by omega
    have hsplit' : E = ReferenceActivePhysicalHorizon.foldCalendar initial rows J rewards
        start (start + (k + 2)) (count - (k + 2)) (by omega) (by omega) active
        boundaryRun := by
      simpa only [hsum] using hsplit
    rw [hsplit']
    exact foldCalendar_records_extend rows J rewards start (start + (k + 2))
      (count - (k + 2)) (by omega) (by omega) active boundaryRun
  obtain ⟨suffix, hrecords⟩ := happend
  have hcurrentIndex : k + 1 < E.records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hk
  have hrecordEq : current = boundaryRun.records[k + 1]'(by omega) := by
    change E.records[k + 1]'hcurrentIndex = boundaryRun.records[k + 1]'(by omega)
    have hget : (boundaryRun.records ++ suffix)[k + 1]'(by
        rw [List.length_append, hprefixCount]
        omega) = boundaryRun.records[k + 1]'(by rw [hprefixCount]; omega) :=
      List.getElem_append_left (by rw [hprefixCount]; omega)
    simpa only [hrecords] using hget
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows J rewards
    start (k + 2) (by omega) active
  have hdropEmpty : boundaryRun.records.drop (k + 2) = [] :=
    List.drop_eq_nil_of_le (by rw [hprefixCount])
  have hlastRecord : boundaryRun.finalState =
      (boundaryRun.records[k + 1]'(by omega)).output.next := by
    have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output hconnected
      (k + 1) (by rw [hprefixCount]; omega)
    rw [hdropEmpty] at hdrop
    change boundaryRun.finalState = (boundaryRun.records[k + 1]'(by omega)).output.next at hdrop
    exact hdrop
  have hprefixCurrent : boundaryRun.finalState = current.output.next := by
    rw [hrecordEq]
    exact hlastRecord
  refine ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, hstart,
    hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied, hnextReply,
    hnextDown, hnextStart, hcollection, ?_, ?_, ?_, ?_⟩
  · change boundaryRun.finalState = current.output.next
    exact hprefixCurrent
  · rw [hprefixCurrent]
    exact hcollection
  · rw [hprefixCurrent]
    exact hf
  · exact ⟨logged, cut, after, raw, scan, registers, lastService,
      hlogged, hcut, houtcome⟩

/-- The cutoff's actual ordinary PREPARE checks the literal UP register box
even when this follower is not selected for the UP slot. The accepted DOWN
record supplies the positive one-based start; the full reply preserves the
same four fields at the returned ordinary state. This constructs one checked
word without a cutoff-UP selector premise.
Sources: `06_interruptions.tex:41-70,103-124,164-177` and
`appendix_a_local_protocol.tex:92-109,151-157`. -/
theorem cutoff_fixed_up_word
    :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let prev := E.records[k]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
    let current := E.records[k + 1]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
    ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload
        current.input.state.coordinator = some payload)
      (_hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
      (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
      (_hf : current.output.next.followers i = .ordinary next nextMemory)
      (_ho : current.output.next.coordinator ≠ .dagger),
    ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
      (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
      (ReferenceFollowerFixedReply.actualChoice current i).configuration =
        .ordinary choice choiceMemory ∧
      choice.status = .unoccupied ∧
      ActiveFollowerQueueOperation.stateInputDomain choice ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i current.input.row
        (current.input.state.activations i) current.input.time choice ≠ .failure ∧
      M.val = ActiveFollowerQueueOperation.upOfferFields next ∧
      M.val.sigma = payload.sigma.val + 1 ∧ 0 < M.val.sigma := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  obtain ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, hstart,
      hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied, hnextReply,
      hnextDown, hnextStart, hcollection, _, _, _, _⟩ :=
    cutoff_after_down_collection_boundary initial rows J rewards start count span active
      k hk payload i hp hc hd next nextMemory hf ho
  have hchecked := actualChoice_checkedUpOffer_ne_failure current i s memory choice
    choiceMemory hs hstart hchoice
  have hdomain : ActiveFollowerQueueOperation.stateInputDomain choice := by
    by_contra hbad
    have hfailure : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i current.input.row
        (current.input.state.activations i) current.input.time choice = .failure := by
      simp [ActiveFollowerQueueOperation.checkedUpOffer, hbad]
    exact hchecked hfailure
  have hreply : ReferenceFollowerReplyChronology.reply choice =
      ReferenceFollowerReplyChronology.reply next := hchoiceReply.trans hnextReply.symm
  have hreplyFields : choice.S = next.S ∧ choice.delta = next.delta ∧
      choice.backlog = next.backlog := by
    have hparts := hreply
    simp only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] at hparts
    exact ⟨hparts.2.1, hparts.2.2.1, hparts.2.2.2⟩
  have haccepted : ReferencePrelaunchFollower.acceptedStart choice =
      payload.sigma.val + 1 :=
    (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply).trans hnextStart
  have htargetSigma : (payload.downRecord i).val.sigma = payload.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
  have hdownBound : (payload.downRecord i).val.sigma ≤ p.T := by
    exact (payload.downRecord i).property.2.1
  have hsigmaLe : payload.sigma.val + 1 ≤ p.T := by
    rw [← htargetSigma]
    exact hdownBound
  have hfields : ActiveFollowerQueueOperation.upOfferFields choice =
      ActiveFollowerQueueOperation.upOfferFields next := by
    ext
    · exact haccepted.trans hnextStart.symm
    · exact hreplyFields.1
    · exact hreplyFields.2.1
    · exact hreplyFields.2.2
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields choice) := by
    unfold OrdinaryMessageCodec.upAdmissible
    right
    unfold ActiveFollowerQueueOperation.upOfferFields
    rw [haccepted]
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), hsigmaLe,
      hdomain.1, hdomain.2.1, hdomain.2.2.1⟩
  let M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields choice, hadmissible⟩
  refine ⟨choice, choiceMemory, M, hchoice, hchoiceUnoccupied, hdomain, hchecked, ?_, ?_, ?_⟩
  · simp [M, hfields]
  · change ReferencePrelaunchFollower.acceptedStart choice = payload.sigma.val + 1
    exact haccepted
  · change 0 < ReferencePrelaunchFollower.acceptedStart choice
    rw [haccepted]
    omega

/-- Apply U's original-run collection consumers to the exact state returned
by the two-record cutoff seed. The coordinator and focal follower proofs are
outputs of the boundary endpoint equality, not supplied snapshots. U retains
the moving ledger/saved value, dagger alternatives, and actual window endpoint.
Sources: `06_interruptions.tex:41-70,164-177,277-284,327-348`. -/
theorem cutoff_collection_interval_producers :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let prev := E.records[k]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
    let current := E.records[k + 1]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
    ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload
        current.input.state.coordinator = some payload)
      (_hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
      (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
      (_hf : current.output.next.followers i = .ordinary next nextMemory)
      (_ho : current.output.next.coordinator ≠ .dagger),
    ∃ s memory choice choiceMemory ledger saved,
      current.input.state.followers i = .ordinary s memory ∧
      (ReferenceFollowerFixedReply.actualChoice current i).configuration =
        .ordinary choice choiceMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta current.input.time s memory =
        .ok (choice, choiceMemory) ∧
      s.lastDown = some (payload.downRecord i) ∧
      choice.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply s ∧
      next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply s ∧
      next.lastDown = some (payload.downRecord i) ∧
      ReferencePrelaunchFollower.acceptedStart next = payload.sigma.val + 1 ∧
      current.output.next.coordinator = .collection payload ledger saved ∧
      let b := k + 2
      let boundaryRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b
        (by omega) active
      boundaryRun.finalState = current.output.next ∧
      (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
        (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
        (after : ReferencePrelaunchFollower.State p rate.eta)
        (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
        (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ)
        (lastService : ℕ),
        (prev.output.followers i).downInput = some logged ∧
        (prev.output.followers i).down = some cut ∧
        cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
          logged after raw (payload.downRecord i) scan registers lastService) ∧
      ∃ (hnextUnoccupied : next.status = .unoccupied)
        (hnextStart : ReferencePrelaunchFollower.acceptedStart next = payload.sigma.val + 1),
      ∃ (hcoord : boundaryRun.finalState.coordinator = .collection payload ledger saved)
        (hseed : boundaryRun.finalState.followers i = .ordinary next nextMemory),
        CollectionWindowProducers initial rows J rewards start count span active b (by omega) payload
          ledger saved hcoord i next nextMemory hseed hnextUnoccupied hnextStart := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  obtain ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, hstart,
      hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied, hnextReply,
      hnextDown, hnextStart, hcollection, hboundary, hboundaryCollection,
      hboundaryFollower, hretainedDetails⟩ :=
    cutoff_after_down_collection_boundary initial rows J rewards start count span active
      k hk payload i hp hc hd next nextMemory hf ho
  let boundaryRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2)
    (by omega) active
  have hcoord : boundaryRun.finalState.coordinator = .collection payload ledger saved := by
    rw [hboundary]
    exact hcollection
  have hseed : boundaryRun.finalState.followers i = .ordinary next nextMemory := by
    rw [hboundary]
    exact hf
  refine ⟨s, memory, choice, choiceMemory, ledger, saved, hs, hchoice, hstart,
    hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied, hnextReply,
    hnextDown, hnextStart, hcollection, hboundary, hretainedDetails,
    hnextUnoccupied, hnextStart,
    hcoord, hseed, ?_⟩
  exact collectionWindowProducers_of_boundary initial rows J rewards start count span active (k + 2)
    (by omega) payload ledger saved hcoord i next nextMemory hseed hnextUnoccupied hnextStart

/-- Every actual ordinary focal PREPARE in the U window, when its actual slot
and sender selectors locally choose this follower, offers the same cutoff word.
The slot/sender conditions are conclusions' local query selectors, not global
history assumptions. Positivity is used only after the actual sent word is
constructed. Sources: `05_binary_transport.tex:70-124`,
`06_interruptions.tex:103-124,164-177,277-284`, and
`appendix_a_local_protocol.tex:92-109,151-157`. -/
theorem collection_interval_fixed_up_query :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let prev := E.records[k]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
    let current := E.records[k + 1]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
    ∀ (_hp : ReferenceAssignmentPayloadPersistence.storedPayload
        current.input.state.coordinator = some payload)
      (_hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
      (_hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
      (_hf : current.output.next.followers i = .ordinary next nextMemory)
      (_ho : current.output.next.coordinator ≠ .dagger),
    ∃ (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
      M.val = ActiveFollowerQueueOperation.upOfferFields next ∧ 0 < M.val.sigma ∧
      let b := k + 2
      let W := ((E.records.drop b).takeWhile
        fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      ∀ n, n ≤ W.length → b + n < count →
        ∀ (hrecord : b + n < E.records.length),
        let record := E.records.get ⟨b + n, hrecord⟩
        ∀ (queryState : ReferencePrelaunchFollower.State p rate.eta)
          (queryMemory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice record i).configuration =
            .ordinary queryState queryMemory →
          PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
            PublicDiscreteDraws.upSlot →
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (record.input.row.2 record.input.time).1 = i →
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
            (record.input.state.activations i) record.input.time queryState = .offer M ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            (ReferenceFollowerFixedReply.actualChoice record i).follower
            (ReferenceFollowerFixedReply.actualChoice record i).row
            (ReferenceFollowerFixedReply.actualChoice record i).activation
            (ReferenceFollowerFixedReply.actualChoice record i).time queryState = .offer M ∧
          let w := ActiveFollowerArmChoice.offeredUpWord rate.eta M
          ReferenceActiveAffinePositiveTest.upSent record.input = some w ∧
          ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare record.input) = some w ∧
          (ReferenceActiveAffinePositiveTest.upPositive record.input = true →
            AffineChannelLaw.affineHash ((record.input.row.2 record.input.time).2 (1, i)) w = 1) := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  obtain ⟨seed, seedMemory, seedChoice, seedChoiceMemory, ledger, saved, hseedInput,
      hseedChoice, hseedStartRound, hseedLastDown, hseedChoiceUnoccupied,
      hseedChoiceReply, hnextUnoccupied, hnextReply, hnextLastDown, hnextStart,
      hcollection, hboundary, hboundaryCollection, hboundaryFollower, _⟩ :=
    cutoff_after_down_collection_boundary initial rows J rewards start count span active
      k hk payload i hp hc hd next nextMemory hf ho
  obtain ⟨cutoffChoice, cutoffChoiceMemory, M, hcutoffChoice, hcutoffUnoccupied,
      hcutoffDomain, hcutoffCheck, hMval, hMsigma, hMpositive⟩ :=
    cutoff_fixed_up_word initial rows J rewards start count span active k hk payload i
      hp hc hd next nextMemory hf ho
  let boundaryRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2)
    (by omega) active
  have hcoord : boundaryRun.finalState.coordinator = .collection payload ledger saved := by
    rw [hboundary]
    exact hcollection
  have hseed : boundaryRun.finalState.followers i = .ordinary next nextMemory := by
    rw [hboundary]
    exact hf
  have hwindow := collectionWindowProducers_of_boundary initial rows J rewards start count span
    active (k + 2) (by omega) payload ledger saved hcoord i next nextMemory hseed
    hnextUnoccupied hnextStart
  dsimp only [CollectionWindowProducers] at hwindow
  rcases hwindow with ⟨_, _, hchoiceWindow⟩
  refine ⟨M, hMval, hMpositive, ?_⟩
  intro n hn hround hrecordIndex
  let record := E.records.get ⟨k + 2 + n, hrecordIndex⟩
  intro queryState queryMemory hconfiguration hslot hsender
  have hwindowChoice := hchoiceWindow n hn hrecordIndex
  have hordinary :
      (ReferenceFollowerFixedReply.actualChoice record i).configuration =
        .ordinary queryState queryMemory ∧ queryState.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply queryState =
          ReferenceFollowerReplyChronology.reply next := by
    rcases hwindowChoice.2 with hdagger | ⟨windowState, windowMemory, hwindowConfig,
        hwindowUnoccupied, hwindowReply⟩
    · rw [hconfiguration] at hdagger
      cases hdagger
    · have hstateEq : windowState = queryState := by
        injection hwindowConfig.symm.trans hconfiguration with hstateEq _
      refine ⟨hconfiguration, ?_, ?_⟩
      · rw [← hstateEq]
        exact hwindowUnoccupied
      · rw [← hstateEq]
        exact hwindowReply
  have hnonfailure := actualChoice_checkedUpOffer_ne_failure_at_input record i
    queryState queryMemory hconfiguration
  have hdomain : ActiveFollowerQueueOperation.stateInputDomain queryState := by
    by_contra hbad
    have hfailure : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time queryState = .failure := by
      simp [ActiveFollowerQueueOperation.checkedUpOffer, hbad]
    exact hnonfailure hfailure
  have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time :=
    ⟨record.input.active i, hslot, hsender⟩
  have hselectedStatus : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time ∧
      queryState.status = .unoccupied := ⟨hselectedUp, hordinary.2.1⟩
  have hinputOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time queryState = .offer M := by
    cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time queryState with
    | failure => exact False.elim (hnonfailure hoff)
    | noOffer =>
        unfold ActiveFollowerQueueOperation.checkedUpOffer at hoff
        simp only [dite_eq_left hdomain, dite_eq_left hselectedStatus] at hoff
        split at hoff <;> cases hoff
    | offer offered =>
        have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i
          record.input.row (record.input.state.activations i) record.input.time queryState
          offered hoff
        have hregisters := upOfferFields_eq_of_reply_eq hordinary.2.2
        have hoffered : offered = M := by
          apply Subtype.ext
          calc
            offered.val = ActiveFollowerQueueOperation.upOfferFields queryState := hfields
            _ = ActiveFollowerQueueOperation.upOfferFields next := hregisters
            _ = M.val := hMval.symm
        cases hoffered
        rfl
  have hactualOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time queryState = .offer M := by
    have halign := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
      record.output.preparation i
    change ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time queryState = .offer M
    rw [halign.2.1, halign.1, halign.2.2.2, halign.2.2.1]
    exact hinputOffer
  have hprepConfig :
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary queryState queryMemory := by
    have hchoicePrep : ReferenceFollowerFixedReply.actualChoice record i =
        DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i) :=
      record.output.preparation.followers.followers_eq i
    have hlocalConfig :
        (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i)).configuration =
          .ordinary queryState queryMemory := by
      rw [← hchoicePrep]
      exact hconfiguration
    change (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i)).configuration = .ordinary queryState queryMemory
    exact hlocalConfig
  have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    simpa [record, PublicDiscreteDraws.followerCount] using hsender
  have hsent : ReferenceActiveAffinePositiveTest.upSent record.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration, hsenderIndex]
    simp only [hprepConfig, hinputOffer]
    rfl
  refine ⟨hinputOffer, hactualOffer, hsent, ?_, ?_⟩
  · simpa only [ReferenceActiveAffinePositiveTest.upSent] using hsent
  · intro hpositive
    have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one record.input
      (ActiveFollowerArmChoice.offeredUpWord rate.eta M) hsent hpositive
    rw [hsenderIndex] at hhash
    exact hhash

/-- Two actual selected-UP choice sites carrying the same fixed checked
record have the same sent word. This is the constancy interface for applying
the preceding producer at any pair of local window query sites. -/
theorem actual_query_sites_fixed_word_constancy
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (leftState rightState : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hleftConfiguration :
      (ReferenceFollowerFixedReply.actualChoice left i).configuration =
        .ordinary leftState leftMemory)
    (hrightConfiguration :
      (ReferenceFollowerFixedReply.actualChoice right i).configuration =
        .ordinary rightState rightMemory)
    (hleftSender : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (left.input.row.2 left.input.time).1 = i)
    (hrightSender : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (right.input.row.2 right.input.time).1 = i)
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (hleftReply : ReferenceFollowerReplyChronology.reply leftState =
      ReferenceFollowerReplyChronology.reply seed)
    (hrightReply : ReferenceFollowerReplyChronology.reply rightState =
      ReferenceFollowerReplyChronology.reply seed)
    (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hleftOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice left i).follower
      (ReferenceFollowerFixedReply.actualChoice left i).row
      (ReferenceFollowerFixedReply.actualChoice left i).activation
      (ReferenceFollowerFixedReply.actualChoice left i).time leftState = .offer M)
    (hrightOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice right i).follower
      (ReferenceFollowerFixedReply.actualChoice right i).row
      (ReferenceFollowerFixedReply.actualChoice right i).activation
      (ReferenceFollowerFixedReply.actualChoice right i).time rightState = .offer M) :
    ReferenceFollowerFixedReply.actualUpExpected left =
      ReferenceFollowerFixedReply.actualUpExpected right := by
  have hleftSelected : ReferenceActivePhysicalStep.upSenderIndex left.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    simpa [PublicDiscreteDraws.followerCount] using hleftSender
  have hrightSelected : ReferenceActivePhysicalStep.upSenderIndex right.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    simpa [PublicDiscreteDraws.followerCount] using hrightSender
  have hreply : ReferenceFollowerReplyChronology.reply leftState =
      ReferenceFollowerReplyChronology.reply rightState := hleftReply.trans hrightReply.symm
  have hparts : leftState.lastDown = rightState.lastDown ∧
      leftState.S = rightState.S ∧ leftState.delta = rightState.delta ∧
      leftState.backlog = rightState.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply
  have hregisters : ReferencePrelaunchFollower.acceptedStart leftState =
        ReferencePrelaunchFollower.acceptedStart rightState ∧
      leftState.S = rightState.S ∧ leftState.delta = rightState.delta ∧
      leftState.backlog = rightState.backlog := by
    refine ⟨?_, hparts.2.1, hparts.2.2.1, hparts.2.2.2⟩
    exact ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  exact (ReferenceFollowerFixedReply.actualUpExpected_eq_of_same_reply_registers
    left right i hleftSelected hrightSelected leftState rightState leftMemory rightMemory
    hleftConfiguration hrightConfiguration hregisters M M hleftOffer hrightOffer).2

end Run

end Bandits.Support.ReferenceCutoffUpReplyInterval

end
