/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionUnoccupiedHistory
public import Bandits.Support.ReferenceAcceptedUpFollowerHistory
public import Bandits.Support.ReferenceCollectionPriorDownHistory

/-!
# Unoccupied prepared choices at actual later assignment starts

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,100-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295,324,340-344`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:54-64,100-108`.

This module concerns follower status on the original physical run. Ordinary
endpoints are explicit branch selectors; failure paths are retained. No numeric
reply identity, collision freedom, safety law, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceLaterStartUnoccupiedChoice


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_record_eq
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (span : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start total span active).records[n]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hn) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start n (by omega) active := by
  have he : total = (n + 1) + (total - (n + 1)) := by omega
  obtain ⟨suffix, hsuffix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J rewards start
    (n + 1) (total - (n + 1)) (by omega) active
  simp only [← he] at hsuffix
  simp only [hsuffix, ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start n (by omega) active
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_singleton, hlen]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero]

private theorem run_output_eq
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (span : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start (n + 1) (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start total span active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hn)).output.next := by
  rw [run_record_eq initial rows J rewards start total span active n hn]
  exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt initial rows J rewards start n
    (by omega) active

private theorem executedTail_equations
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (tail : ReferenceCollectionPhaseHistory.Tail x)
    (ht : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      (ReferenceActivePhysicalStep.step x).next.coordinator =
        (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
          tail.started tail.weights).configuration := by
  classical
  have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    intro hnone
    simp only [ReferenceCollectionPhaseHistory.executedTail, hnone, ite_true] at ht
    cases ht
  unfold ReferenceCollectionPhaseHistory.executedTail at ht
  rw [ite_eq_right hselection] at ht
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r owned base outcome =>
      cases outcome <;> simp only [he] at ht <;> try contradiction
      rename_i dispatched hstart ledger hinitialization hcandidate hdomains
        hclock hpending hnone selected
      cases ht
      constructor
      · rw [(ReferenceActivePhysicalStep.sharedLedger_fields ledger).2.1, hcandidate]
        exact (CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time) (ReferenceActivePhysicalStep.liveOwnedAt r owned x.time) base
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time).2.1
      · have ho := ReferenceActivePhysicalStep.observeCoordinator_live_equation (ReferenceActivePhysicalStep.prepare x) r owned base _ he
        have hsel : (ReferenceActivePhysicalStep.DispatchCut.live r owned base
            (.cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
              hclock hpending hnone selected)).selection ≠ none := by
          simpa only [he] using hselection
        rw [ite_eq_right hsel] at ho
        exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration ho
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [he] at ht <;> try contradiction
      rename_i core snapshot boundary scores
      cases ht
      constructor
      · exact core.ledger_sigma_eq
      · have ho := ReferenceActivePhysicalStep.observeCoordinator_collection_equation (ReferenceActivePhysicalStep.prepare x)
          payload ledger clock cutoff (.continuing core snapshot boundary scores) he
        have hsel : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
            (.continuing core snapshot boundary scores)).selection ≠ none := by
          simpa only [he] using hselection
        rw [ite_eq_right hsel] at ho
        exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration ho
  | first outcome => cases outcome <;> simp only [he] at ht <;> contradiction
  | invalidCollectionCutoff => simp only [he] at ht; contradiction
  | dagger => simp only [he] at ht; contradiction

/-- A successfully retained collection output has the literal payload/ledger
start identity. The hypotheses select an actual executed tail and actual
collection output, including all possible failures before that output. -/
theorem executedTail_collection_output
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (tail : ReferenceCollectionPhaseHistory.Tail record.input) (ht : ReferenceCollectionPhaseHistory.executedTail record.input = some tail)
    (hnot : record.output.next.coordinator ≠ .dagger) :
    ∃ payload ledger saved,
      record.output.next.coordinator = .collection payload ledger saved ∧
      ledger.sigma = payload.sigma.val + 1 := by
  have he := executedTail_equations record.input tail ht
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation (ReferenceActivePhysicalStep.prepare record.input)
    tail.payload tail.ledger tail.started tail.weights
  have hpayload := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare record.input) tail.payload tail.ledger tail.started tail.weights
  have houtput : record.output.next.coordinator =
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare record.input) tail.payload tail.ledger
        tail.started tail.weights).configuration := by
    rw [record.output_eq]
    exact he.2
  rcases hphase with hd | ⟨payload, ledger, saved, hcollection⟩
  · exact (hnot (houtput.trans hd)).elim
  · have hcoord := houtput.trans hcollection
    have hsame : payload = tail.payload := by
      rw [hcollection] at hpayload
      simpa [ReferenceAssignmentPayloadPersistence.storedPayload] using hpayload
    have hf := ReferenceCollectionPhaseHistory.step_collection_frame record.input payload ledger saved (by
      rw [← record.output_eq]; exact hcoord)
    obtain ⟨tail', ht', _, hsigma⟩ := hf
    have htail : tail' = tail := Option.some.inj (ht'.symm.trans ht)
    subst tail'
    exact ⟨payload, ledger, saved, hcoord, hsigma.trans (he.1.trans (by rw [hsame]))⟩

private theorem window_during_no_later
    (before : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cutoff : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (during : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (last : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hw : ReferenceCollectionPhaseHistory.collectionWindow
      ((before ++ cutoff :: during) ++ [last]) before.length = cutoff :: during) :
    ∀ r ∈ during, ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
  have hdrop : (((before ++ cutoff :: during) ++ [last]).drop
      (before.length + 1)) = during ++ [last] := by
    rw [List.append_assoc, List.drop_append]
    simp only [List.drop_eq_nil_of_le (by omega : before.length ≤ before.length + 1),
      List.nil_append, Nat.add_sub_cancel_left, List.cons_append, List.drop_succ_cons,
      List.drop_zero]
  have hhead : (((before ++ cutoff :: during) ++ [last]).drop
      before.length).take 1 = [cutoff] := by
    rw [List.append_assoc, List.drop_append]
    simp only [List.drop_length, Nat.sub_self, List.nil_append, List.drop_zero,
      List.cons_append, List.take_succ_cons, List.take_zero]
  have ht : (during ++ [last]).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) = during := by
    rw [ReferenceCollectionPhaseHistory.collectionWindow, hdrop, hhead] at hw
    exact List.cons.inj hw |>.2
  intro r hr
  have hm : r ∈ (during ++ [last]).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by rw [ht]; exact hr
  have hp := List.all_eq_true.mp (List.all_takeWhile (p := fun r =>
    !ReferenceCollectionPhaseHistory.laterChosen r.input) (l := during ++ [last])) r hm
  simpa using hp

/-- The actual carried ordinary endpoint and its prepared choice, before the
replacement round's logging and DOWN effects. -/
private theorem run_laterChosen_ordinary_boundary_unoccupied
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + (count + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active) = true)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active).state.followers i =
      .ordinary s memory) :
    s.status = .unoccupied ∧
      (((ReferenceActivePhysicalStep.prepare
        (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active)).followers.followers i).configuration = .dagger ∨
        ∃ choice choiceMemory,
          ((ReferenceActivePhysicalStep.prepare
            (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active)).followers.followers i).configuration =
            .ordinary choice choiceMemory ∧ choice.status = .unoccupied) := by
  let x := ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active
  let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count (by omega) active
  let whole := ReferenceActivePhysicalHorizon.run initial rows J rewards start (count + 1) span active
  let last := ReferenceAssignmentPayloadChronology.actualStepRecord x
  have hwhole : whole.records = R.records ++ [last] := by
    exact ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt initial rows J
      rewards start count span active
  have hlast : whole.records[count]'(by
      dsimp [whole]; rw [ReferenceActivePhysicalHorizon.run_record_count]; omega) = last := by
    simp only [hwhole]
    rw [List.getElem_append_right (by
      dsimp [R]; rw [ReferenceActivePhysicalHorizon.run_record_count])]
    have hlen : R.records.length = count := ReferenceActivePhysicalHorizon.run_record_count
      initial rows J rewards start count (by omega) active
    simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
  obtain ⟨before, cutoff, during, finalPayload, old, proposal, hrecords,
      hcutoff, hfinal, hempty, hwindow, heach⟩ :=
    ReferenceCollectionPhaseHistory.run_laterStart_all_up_accepted initial rows J rewards
      start count span active hfirst hlater
  have hnoDuring := window_during_no_later before cutoff during last (by
    change ReferenceCollectionPhaseHistory.collectionWindow (R.records ++ [last])
      before.length = cutoff :: during at hwindow
    rw [hrecords] at hwindow
    exact hwindow)
  obtain ⟨k, record, message, hbefore, hkcount, hget, haccepted, hmessageSigma⟩ := heach i
  have hRlen : R.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count (by omega) active
  have hkR : k < R.records.length := by rw [hRlen]; exact hkcount
  have hrecord : R.records[k] = record := by
    exact Option.some.inj ((List.getElem?_eq_getElem hkR).symm.trans hget)
  have houtput : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
      (by omega) active).finalState = record.output.next := by
    have he := run_output_eq initial rows J rewards start count (by omega) active k hkcount
    change _ = R.records[k].output.next at he
    rw [hrecord] at he
    exact he
  have hincomingR : R.finalState.followers i = .ordinary s memory := hc
  have chain := ReferenceActivePhysicalHorizon.run_connected initial rows J rewards start count
    (by omega) active
  obtain ⟨seed, seedMemory, hseedOutput, _⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology chain i s memory
      hincomingR k hkR
  rw [hrecord] at hseedOutput
  obtain ⟨choice, choiceMemory, hchoice, _, hunoccupied, hreply⟩ :=
    ReferenceAcceptedUpFollowerHistory.record_acceptedUp_output_frame haccepted hseedOutput
  obtain ⟨sender, offered, offeredMemory, hsender, hindex, hsenderConfig, _, _, hstart,
      _⟩ := ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  have hsenderChoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary offered offeredMemory := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
    rw [hindex, ← hsender]
    exact hsenderConfig
  have hoff : choice = offered := LocalConfiguration.ordinary.inj
    (hchoice.symm.trans hsenderChoice) |>.1
  have hseedStart : ReferencePrelaunchFollower.acceptedStart seed = old.sigma := by
    calc
      ReferencePrelaunchFollower.acceptedStart seed =
          ReferencePrelaunchFollower.acceptedStart choice :=
        ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
      _ = message.val.sigma := by rw [hoff]; exact hstart.symm
      _ = old.sigma := hmessageSigma
  have hsuffix := ReferenceFollowerReplyChronology.connected_drop_from_output chain k hkR
  rw [hrecord] at hsuffix
  have hnot : record.output.next.coordinator ≠ .dagger := by
    intro hd
    have hterminal := hsuffix.coordinator_dagger hd |>.1
    have hf : R.finalState.coordinator = .collection finalPayload old proposal := hfinal
    rw [hf] at hterminal
    cases hterminal
  obtain ⟨tail, recording, started, decoded, bank, ht, _⟩ := haccepted
  obtain ⟨payload, ledger, saved, hcoordOutput, hledgerSigma⟩ :=
    executedTail_collection_output record tail ht hnot
  have hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
      (by omega) active).finalState.coordinator = .collection payload ledger saved := by
    rw [houtput]; exact hcoordOutput
  have hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
      (by omega) active).finalState.followers i = .ordinary seed seedMemory := by
    rw [houtput]; exact hseedOutput
  have hnoSuffix : ∀ r ∈ R.records.drop (k + 1),
      ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
    intro r hr
    have hdrop : R.records.drop (k + 1) = during.drop (k - before.length) := by
      change (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
        (by omega) active).records.drop (k + 1) = _
      rw [hrecords, List.drop_append]
      rw [List.drop_eq_nil_of_le (by omega : before.length ≤ k + 1)]
      simp only [List.nil_append]
      have he : k + 1 - before.length = (k - before.length) + 1 := by omega
      rw [he, List.drop_succ_cons]
    rw [hdrop] at hr
    exact hnoDuring r (List.mem_of_mem_drop hr)
  have hnested := ReferenceCollectionPhaseHistory.run_collection_pending_nested initial rows J
    rewards start (k + 1) (count - (k + 1)) (by omega) active payload ledger saved
    finalPayload old proposal hcoord (by
      simpa only [Nat.add_sub_cancel' (by omega : k + 1 ≤ count)] using (show R.finalState.coordinator = .collection finalPayload old proposal from hfinal))
    (by simpa only [Nat.add_sub_cancel' (by omega : k + 1 ≤ count)] using hnoSuffix)
  have hseedSigma : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1 :=
    hseedStart.trans (hnested.2.trans hledgerSigma)
  have hW : ((whole.records.drop (k + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length = count - (k + 1) := by
    rw [hwhole, List.drop_append]
    have hdropLast : [last].drop (k + 1 - R.records.length) = [last] := by
      rw [hRlen, Nat.sub_eq_zero_of_le (by omega), List.drop_zero]
    rw [hdropLast, List.takeWhile_append_of_pos (by
      intro r hr; simp only [hnoSuffix r hr, Bool.not_false])]
    have htag : ReferenceCollectionPhaseHistory.laterChosen last.input = true := hlater
    simp only [List.takeWhile_cons, htag, Bool.not_true, Bool.false_eq_true,
      ite_false, List.append_nil, List.length_drop, hRlen]
  have hboundary := ReferenceCollectionUnoccupiedHistory.run_collection_boundary_choice_unoccupied
    p rate initial rows J rewards start (count + 1) span active (k + 1) (by omega)
    payload ledger saved hcoord i seed seedMemory hseed hunoccupied hseedSigma
    (count - (k + 1)) (by rw [hW]) (by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  have hgetLast : whole.records.get ⟨k + 1 + (count - (k + 1)), by
      dsimp [whole]; rw [ReferenceActivePhysicalHorizon.run_record_count]; omega⟩ = last := by
    simpa only [List.get_eq_getElem, Nat.add_sub_cancel' (by omega : k + 1 ≤ count)] using hlast
  change _ ∧ ((ReferenceFollowerFixedReply.actualChoice
    (whole.records.get _) i).configuration = .dagger ∨ _) at hboundary
  rw [hgetLast] at hboundary
  have hprefix := ReferenceCollectionUnoccupiedHistory.run_collection_unoccupied_prefix
    p rate initial rows J rewards start (count + 1) span active (k + 1) (by omega)
    payload ledger saved hcoord i seed seedMemory hseed hunoccupied hseedSigma
    (count - (k + 1)) (by rw [hW])
  dsimp only at hprefix
  have hinput : (ReferenceActivePhysicalHorizon.run initial rows J rewards start
      (k + 1 + (count - (k + 1))) (by omega) active).finalState.followers i =
      .ordinary s memory := by
    simpa only [Nat.add_sub_cancel' (by omega : k + 1 ≤ count)] using hincomingR
  have huInput : s.status = .unoccupied := by
    rcases hprefix.2 with hd | ⟨out, outMemory, hout, hu, _⟩
    · rw [hinput] at hd; cases hd
    · have hs : out = s := LocalConfiguration.ordinary.inj (hout.symm.trans hinput) |>.1
      rw [← hs]; exact hu
  refine ⟨huInput, ?_⟩
  change (ReferenceFollowerFixedReply.actualChoice last i).configuration = .dagger ∨
    ∃ choice choiceMemory,
      (ReferenceFollowerFixedReply.actualChoice last i).configuration =
        .ordinary choice choiceMemory ∧ choice.status = .unoccupied
  rcases hboundary.2 with hd | ⟨out, outMemory, hout, hu, _⟩
  · exact Or.inl hd
  · exact Or.inr ⟨out, outMemory, hout, hu⟩

/-- An actual ordinary incoming follower at a later assignment boundary is
unoccupied, before PREPARE as well as before the new word's possible effects. -/
theorem run_laterChosen_ordinary_input_unoccupied
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + (count + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active) = true)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active).state.followers i =
      .ordinary s memory) : s.status = .unoccupied :=
  (run_laterChosen_ordinary_boundary_unoccupied initial rows J rewards start count span active
    hfirst hlater i s memory hc).1

/-- Every ordinary prepared follower at the actual later-choice boundary is
unoccupied. All collection seed inputs are produced from the original run;
neither initial follower status nor initial last-DOWN restrictions are needed. -/
theorem run_laterChosen_ordinary_choice_unoccupied
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + (count + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active) = true)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((ReferenceActivePhysicalStep.prepare
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active)).followers.followers i).configuration =
        .ordinary s memory) : s.status = .unoccupied := by
  let x := ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active
  let record := ReferenceAssignmentPayloadChronology.actualStepRecord x
  have hcRecord : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary s memory := hc
  obtain ⟨incoming, incomingMemory, hi, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice record i s memory hcRecord
  have hboundary := run_laterChosen_ordinary_boundary_unoccupied initial rows J rewards start count
    span active hfirst hlater i incoming incomingMemory hi
  rcases hboundary.2 with hd | ⟨out, outMemory, hout, hu⟩
  · rw [hc] at hd; cases hd
  · have hs : out = s := LocalConfiguration.ordinary.inj (hout.symm.trans hc) |>.1
    rw [← hs]; exact hu

private theorem laterChosen_selected_birth
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen x = true)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) selected.view.payload := by
  classical
  let record := ReferenceAssignmentPayloadChronology.actualStepRecord x
  have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare x := rfl
  rw [hprep] at hbirth
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen, he,
        Bool.false_eq_true] at hlater
      rename_i core consistent started hstart instruction hinstruction output hlocal
        clockData installed selection
      have hsel : ReferenceActivePhysicalStep.selectionAt x installed.registers.payload started
          instruction.time installed.registers.complementWeights selection = some selected := by
        simpa only [he, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
      have hselectedPayload : selected.view.payload = installed.registers.payload := by
        unfold ReferenceActivePhysicalStep.selectionAt at hsel
        split at hsel
        · exact congrArg (fun s : ReferenceActivePhysicalStep.Selection x => s.view.payload)
            (Option.some.inj hsel).symm
        · cases hsel
      rw [he] at hbirth
      simpa only [hselectedPayload] using hbirth
  | first outcome => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at hlater
  | live registers owned base outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at hlater
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at hlater
  | dagger => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at hlater

/-- The exact structural input consumed by `step_occupied_fields`, and that
consumer's result for the very same actual selected payload. This allows
dagger followers and makes no assertion that every follower is ordinary.
Literal dispatch inversion identifies this payload as the newly installed
one, even when that round's later coordinator tail fails. -/
theorem run_laterChosen_step_occupied_fields
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + (count + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active) = true)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active))
    (hselected : (ReferenceActivePhysicalStep.prepare
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active)).coordinator.selection =
        some selected) :
    let x := ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start count span active
    ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) selected.view.payload ∧
      ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload x.state ∧
      ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload
        (ReferenceActivePhysicalStep.step x).next := by
  intro x
  have hfields : ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload x.state := by
    intro i
    cases hi : x.state.followers i with
    | dagger => trivial
    | ordinary s memory =>
        have hu := run_laterChosen_ordinary_input_unoccupied initial rows J rewards start count
          span active hfirst hlater i s memory hi
        change s.status ≠ .unoccupied → _
        intro hoccupied
        exact (hoccupied hu).elim
  exact ⟨laterChosen_selected_birth x hlater selected hselected, hfields,
    ReferenceActiveDataOwnership.step_occupied_fields x selected hselected hfields⟩

/-- Actual-launch specialization on the original source arrays, including
their original selected private row. Initial ordinary states, no-DOWN fields,
and unoccupied statuses are produced by the launch replay API. The relation,
generated-DOWN, clean-prefix, forced, and actual launch conditions remain
explicit; no replacement initial state is supplied. The next physical round
is formed only under the displayed `blockStop + (count + 1) ≤ T` bound. -/
theorem ofActualLaunchedBoundary_laterChosen_ordinary_choice_unoccupied
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + (count + 1) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun player => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched player
    let x := ReferenceCollectionPhaseHistory.nextInput initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
    initial.coordinator = .first ∧
      (∀ i : Fin (p.m - 1), ∃ first firstMemory,
        initial.followers i = .ordinary first firstMemory ∧
        first = ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.finishBlock
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            b h) (ActualReferenceInitializationBlock.refFollower i) ∧
        first.lastDown = none ∧ first.status = .unoccupied) ∧
      ∀ (_hlater : ReferenceCollectionPhaseHistory.laterChosen x = true)
        (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (_hc : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
          .ordinary s memory), s.status = .unoccupied := by
  intro initial start active x
  have hfirst : initial.coordinator = .first :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  refine ⟨hfirst, ?_, ?_⟩
  · intro i
    obtain ⟨first, firstMemory, hconfiguration, hstate, hlast, _, _, _, _, hstatus, _⟩ :=
      ReferenceFollowerFixedReply.ofActualLaunchedBoundary_replaySeed source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    exact ⟨first, firstMemory, hconfiguration, hstate, hlast, hstatus⟩
  · intro hlater i s memory hc
    exact run_laterChosen_ordinary_choice_unoccupied initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
      hfirst hlater i s memory hc

end Bandits.Support.ReferenceLaterStartUnoccupiedChoice

end
