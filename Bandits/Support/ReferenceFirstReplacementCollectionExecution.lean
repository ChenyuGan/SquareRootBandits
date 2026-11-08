/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation
public import Bandits.Support.ReferenceGeneratedFirstCollectionFollowerPrefix
import Lean.Elab.Tactic.Omega

/-!
# The first reached replacement's collection execution

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,123-233,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The collection window is the existing raw chronological window. A reached
replacement excludes earlier coordinator failure by absorption. No numerical
queue truth, replacement existence, probability law, or regret result is claimed.

The local inputs to the composition are produced as follows. The actual
corrected launch supplies the original seed, active mode, and first coordinator.
The reached replacement supplies a non-dagger incoming coordinator, so the
follower-prefix theorem's coordinator alternatives give collection states at
every earlier boundary. Inverting each actual physical successor supplies its
selection guard and completed collection extraction. These facts identify the
whole raw window with the initialized segment. Actual adjacency then identifies
the segment endpoint with the incoming carried ledger of the replacement.

The replacement record itself is excluded from this execution; its post-choice
tail may fail. Checked execution uses `rate.eta.val` and `rate.n` throughout.
It does not use elapsed time as the integer rate scale. The prefix corollary
includes the empty prefix and retains the same segment and preledger.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionExecution

open ConstructorDimensions
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_at
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (index : ℕ) (hi : index < count) :
    (run initial rows J rewards start count span active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hlen := run_record_count initial rows J rewards start count (by omega) active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start count span active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa only [hlen] using hlt)]
        exact ih (by omega) index hlt
      · have heq : index = count := by omega
        subst index
        simp [hlen]

/-- Inversion uses the actual successful physical successor, including the
selection guard and all post-choice checked operations. -/
private theorem completed_of_collection
    (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hnext : record.output.next.coordinator = .collection payload ledger saved) :
    ∃ completed, ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
  have hs := hnext
  rw [record.output_eq] at hs
  obtain ⟨tail, ht, _, _⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
    record.input payload ledger saved hs
  have hc : ∃ c, ReferenceCollectionSegmentExtraction.choice record.input = some c := by
    unfold ReferenceCollectionPhaseHistory.executedTail at ht
    dsimp only at ht
    split at ht
    · contradiction
    next hguard =>
      unfold ReferenceCollectionSegmentExtraction.choice
      rw [ite_eq_right hguard]
      cases he : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
      | first outcome => cases outcome <;> simp only [he] at ht <;> contradiction
      | live r q base outcome =>
          cases outcome <;> simp only [he] at ht <;> try contradiction
          exact ⟨_, rfl⟩
      | collection old incoming clock cutoff outcome =>
          cases outcome <;> simp only [he] at ht <;> try contradiction
          exact ⟨_, rfl⟩
      | invalidCollectionCutoff => simp only [he] at ht; contradiction
      | dagger => simp only [he] at ht; contradiction
  obtain ⟨c, hc⟩ := hc
  exact ReferenceCollectionSegmentExtraction.actual_collection_round_complete
    record c payload ledger saved hc hnext

/-- Conditional on the actual incoming and outgoing collection constructors.
The launched proof below produces both from adjacent original-run boundaries. -/
private theorem continuing_of_collection
    (record : RoundRecord (p := p) (rate := rate))
    (old payload : ReferenceActivePhysicalStep.Payload rate)
    (incoming ledger : ReferenceActivePhysicalStep.Ledger rate)
    (before after : Option (Fin p.T × Bool))
    (hpre : record.input.state.coordinator = .collection old incoming before)
    (hnext : record.output.next.coordinator = .collection payload ledger after) :
    ReferenceCollectionSegmentExtraction.continuing record = true := by
  obtain ⟨completed, he⟩ := completed_of_collection record payload ledger after hnext
  have hc := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed he).1
  have hi := (ReferenceCollectionSegmentExtraction.choice_collection_pre
    record.input old incoming before completed.context hpre hc).2
  simp only [ReferenceCollectionSegmentExtraction.continuing, he, hi, Option.isNone_none]

private theorem record_fields
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (index : ℕ) (hi : index < count) :
    let record := (run initial rows J rewards start count span active).records[index]'(by
      rw [run_record_count]; exact hi)
    record.input.state = (run initial rows J rewards start index (by omega) active).finalState ∧
    record.output.next = (run initial rows J rewards start (index + 1) (by omega) active).finalState ∧
    record.input.time.val = start + index := by
  dsimp only
  have he := record_at initial rows J rewards start count span active index hi
  rw [List.getElem?_eq_getElem (by rw [run_record_count]; exact hi)] at he
  have heq := Option.some.inj he
  rw [heq]
  exact ⟨rfl, (ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    initial rows J rewards start index (by omega) active).symm, rfl⟩

private theorem endpoint_of_connected
    (initial final : State p rate)
    (records : List (RoundRecord (p := p) (rate := rate)))
    (chain : Connected initial records final) :
    ReferenceCollectionSegmentExtraction.endpointState initial records = final := by
  induction records generalizing initial with
  | nil => exact chain.symm
  | cons record rest ih =>
      exact ih record.output.next chain.2

private theorem collection_dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match (ReferenceActivePhysicalStep.prepare x).coordinator with
    | .collection payload ledger _ _ _ =>
        ∃ saved, x.state.coordinator = .collection payload ledger saved
    | _ => True := by
  change match ReferenceActivePhysicalStep.dispatch x with
    | .collection payload ledger _ _ _ =>
        ∃ saved, x.state.coordinator = .collection payload ledger saved
    | _ => True
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; trivial
  | live r q base => simp only [CoordinatorRoundDispatch.dispatch]; trivial
  | collection payload ledger saved =>
      simp only [CoordinatorRoundDispatch.dispatch]
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcut]
        exact ⟨saved, rfl⟩
      · simp only [dite_eq_right hcut]
  | dagger => trivial

private theorem cutoff_choice_initializer
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    c.initializer.isSome = true := by
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · contradiction
  next =>
    cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | live r q base outcome =>
        cases outcome <;>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen, he, Bool.false_eq_true] at hcut
        simp only [he, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        cases Option.some.inj hc
        rfl
    | first outcome => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, he, Bool.false_eq_true] at hcut
    | collection payload ledger clock cutoff outcome =>
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, he, Bool.false_eq_true] at hcut
    | invalidCollectionCutoff => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, he, Bool.false_eq_true] at hcut
    | dagger => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, he, Bool.false_eq_true] at hcut

/-- Conditional on a non-dagger endpoint of this same run. Absorption rules out
dagger at every earlier prefix; no coordinator survival is assumed at source. -/
private theorem prefix_ne_dagger
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfinal : (run initial rows J rewards start count span active).finalState.coordinator ≠ .dagger)
    (k : ℕ) (hk : k ≤ count) :
    (run initial rows J rewards start k (by omega) active).finalState.coordinator ≠ .dagger := by
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards start k (count - k) (by omega) active
  have hcount : k + (count - k) = count := by omega
  simp only [hcount] at he
  have htake : (run initial rows J rewards start count span active).records.take k =
      (run initial rows J rewards start k (by omega) active).records := by
    rw [he]
    exact List.take_left' (run_record_count initial rows J rewards start k (by omega) active)
  have hchain := ReferenceCollectionSegmentExtraction.connected_drop
    (run initial rows J rewards start count span active).records initial
    (run initial rows J rewards start count span active).finalState k
    (run_connected initial rows J rewards start count span active)
  rw [htake, endpoint_of_connected initial _ _
    (run_connected initial rows J rewards start k (by omega) active)] at hchain
  intro hd
  exact hfinal (hchain.coordinator_dagger hd).1

/-- Conditional on the actual initialization crossing, its elapsed start, and
a prefix length within the horizon. The complete-source theorem below produces
the crossing and elapsed equality and chooses `count = p.T - s`. All successful
collection operations and the endpoint ledger equality are proved here. -/
private theorem launched_execution
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (span : s + count ≤ p.T) :
    let R := (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hc s hsElapsed count span).records
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let C := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + C.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection old ledger _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
          w < R.length ∧ old.sigma.val = s ∧ record.input.time.val = s + v ∧
          ∃ (seg : ReferenceCollectionSegmentExtraction.Segment rate)
            (a : ReferenceCollectionSegmentExtraction.Initializer p),
            ReferenceCollectionSegmentExtraction.segmentAt R w = some seg ∧
            seg.records = C ∧ seg.remaining = R.drop v ∧
            seg.context.initializer = some a ∧ seg.final = ledger ∧ ledger.pending = ∅ ∧
            (∀ c ∈ C, (ReferenceCollectionSegmentExtraction.extractRound c).isSome = true) ∧
            seg.inputs.length = C.length ∧
            seg.inputs.map (fun input => input.round.val) = C.map (fun r => r.input.time.val) ∧
            CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
              (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
              a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside seg.inputs =
                .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
            (∀ k, k ≤ C.length → ∃ accepted,
              CollectionCheckedExecution.checkedRounds seg.context.preLedger (seg.inputs.take k) =
                some (accepted, ReferenceCollectionSegmentExtraction.endpointLedger
                  seg.context.preLedger (C.take k)))
      | _ => True := by
  classical
  dsimp only
  set R := (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hc s hsElapsed count span).records
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set C := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + C.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    dsimp only
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection old ledger clock cutoff outcome =>
      cases outcome <;> dsimp only
      rename_i core consistent started hs instruction hi output hl clockData installed selected
      have hcanonical : record.output.preparation.coordinator =
          (ReferenceActivePhysicalStep.prepare record.input).coordinator := by
        rw [record.output_eq]; rfl
      rw [hcanonical] at hcut
      obtain ⟨hvR, hrecord⟩ := List.getElem?_eq_some_iff.mp hget
      have hwR : w < R.length := by dsimp only [v] at hvR; omega
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have active : allActiveAtStart initial s := by
        simpa only [hsElapsed] using seed.activeAtStart
      let J := ActualInitializationPhysicalStep.selectedRowIndex p source
      have hrun : R = (run initial source.1.2 J rewards s count span active).records := rfl
      have hcount : R.length = count := by
        rw [hrun, run_record_count]
      have hv : v < count := by omega
      have hw : w < count := by omega
      have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
            rate source rewards C_star C_h hc s hsElapsed count span).records).length < count := hw
      have hfields := record_fields initial source.1.2 J rewards s count span active v hv
      change (R[v]'hvR).input.state = _ ∧ (R[v]'hvR).output.next = _ ∧
        (R[v]'hvR).input.time.val = s + v at hfields
      rw [hrecord] at hfields
      have horigin := collection_dispatch_origin record.input
      rw [hcut] at horigin
      obtain ⟨saved, hincoming⟩ := horigin
      have hend : (run initial source.1.2 J rewards s v (by omega) active).finalState.coordinator =
          .collection old ledger saved := by
        rw [← hfields.1]; exact hincoming
      -- Only the incoming state is used; the new assignment's tail may fail.
      have hne : (run initial source.1.2 J rewards s v (by omega) active).finalState.coordinator ≠ .dagger := by
        rw [hend]
        intro h
        cases h
      have hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
        simp only [ReferenceCollectionPhaseHistory.laterChosen, hcut]
      obtain ⟨other, incoming, proposal, hstate, hempty⟩ :=
        ReferenceCollectionPhaseHistory.laterChosen_pending_empty record.input hlater
      rw [hincoming] at hstate
      have hledgerEq := (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hstate).2.1
      have hpending : ledger.pending = ∅ := hledgerEq ▸ hempty
      let b := w + 1
      let W := (R.drop b).takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let cut := R[w]'hwR
      have hdrop : R.drop w = cut :: R.drop b := List.drop_eq_getElem_cons hwR
      have hC : C = cut :: W := by
        dsimp only [C, ReferenceCollectionPhaseHistory.collectionWindow]
        rw [hdrop]
        rfl
      have hvEq : v = b + W.length := by
        dsimp only [v, b]
        rw [hC, List.length_cons]
        omega
      have htail : b + W.length < count := by omega
      -- F supplies the original cutoff and every actual prefix alternative.
      -- Its dagger alternatives are excluded using the reached incoming state.
      have hF := ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
        rate source rewards C_star C_h hc s hsElapsed count span hshort
      obtain ⟨r0, q0, base, hpre, hsigma, _hzero, dispatched, hstart,
        initialLedger, hinit, hledger, hdomain, hclock, hallPending, hnoAssignment,
        chosen, hcutoff, _hu, _huT, _huGrid, _hlSigma, _hlCut, _hscan,
        _hsuccessor, _hpostCut, hboundaries, _hsteps⟩ := hF
      have hcollection (j : ℕ) (hj : j ≤ W.length) :
          ∃ moving movingSaved,
            (run initial source.1.2 J rewards s (b + j) (by omega) active).finalState.coordinator =
              .collection r0.payload moving movingSaved := by
        rcases (hboundaries j hj).1 with hdagger | hcollection
        · exact False.elim (prefix_ne_dagger initial source.1.2 J rewards s v (by omega)
            active hne (b + j) (by omega) hdagger)
        · exact hcollection
      obtain ⟨lastLedger, lastSaved, hlast⟩ := hcollection W.length le_rfl
      have hend' : (run initial source.1.2 J rewards s (b + W.length) (by omega) active).finalState.coordinator =
          .collection old ledger saved := by
        simpa only [hvEq] using hend
      have hsame := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
        (hlast.symm.trans hend')
      have holdSigma : old.sigma.val = s := by rw [← hsame.1]; exact hsigma
      have hcutFields := record_fields initial source.1.2 J rewards s count span active w hw
      change cut.input.state = _ ∧ cut.output.next = _ ∧ cut.input.time.val = s + w at hcutFields
      obtain ⟨cutLedger, cutSaved, hcutNext⟩ := hcollection 0 (Nat.zero_le _)
      have hcutNext' : cut.output.next.coordinator = .collection r0.payload cutLedger cutSaved := by
        rw [hcutFields.2.1]
        exact hcutNext
      obtain ⟨completedCut, hcompletedCut⟩ := completed_of_collection cut r0.payload cutLedger cutSaved hcutNext'
      have hchoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked cut completedCut hcompletedCut).1
      have hcutChosen : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
        change cut.output.preparation.coordinator = _ at hcutoff
        have hprep : cut.output.preparation.coordinator =
            (ReferenceActivePhysicalStep.prepare cut.input).coordinator := by rw [cut.output_eq]; rfl
        rw [hprep] at hcutoff
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hcutoff]
      have hinitializer := cutoff_choice_initializer cut.input completedCut.context hchoice hcutChosen
      have hWprefix : W <+: R.drop b := List.takeWhile_prefix _
      have hWtake : W = (R.drop b).take W.length := List.prefix_iff_eq_take.mp hWprefix
      -- Successful extraction is produced from each actual next collection state.
      have hcontinuing : ∀ c ∈ W, ReferenceCollectionSegmentExtraction.continuing c = true := by
        intro c hcW
        obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hcW
        have he' := (hWprefix.getElem hj).symm.trans he
        simp only [List.getElem_drop] at he'
        have hjcount : b + j < count := by omega
        have hf := record_fields initial source.1.2 J rewards s count span active (b + j) hjcount
        change (R[b + j]'(by omega)).input.state = _ ∧
          (R[b + j]'(by omega)).output.next = _ ∧ _ at hf
        rw [he'] at hf
        obtain ⟨preLedger, preSaved, hpreCollection⟩ := hcollection j (by omega)
        obtain ⟨nextLedger, nextSaved, hnextCollection⟩ := hcollection (j + 1) (by omega)
        apply continuing_of_collection c r0.payload r0.payload preLedger nextLedger preSaved nextSaved
        · rw [hf.1]; exact hpreCollection
        · rw [hf.2.1]
          convert hnextCollection using 1
      -- Identify the entire raw window, rather than a filtered input count.
      have htailSplit : R.drop b = W ++ R.drop v := by
        have ht := (List.take_append_drop W.length (R.drop b)).symm
        rw [← hWtake, List.drop_drop] at ht
        simpa only [← hvEq] using ht
      have hdropV : R.drop v = record :: R.drop (v + 1) := by
        rw [List.drop_eq_getElem_cons hvR, hrecord]
      have hstopChoice : ReferenceCollectionSegmentExtraction.choice record.input = none := by
        unfold ReferenceCollectionSegmentExtraction.choice
        split
        · rfl
        · rw [hcut]; rfl
      have hstop : ReferenceCollectionSegmentExtraction.continuing record = false := by
        simp only [ReferenceCollectionSegmentExtraction.continuing,
          ReferenceCollectionSegmentExtraction.extractRound, hstopChoice, Option.bind_none]
      have htake : (R.drop b).takeWhile ReferenceCollectionSegmentExtraction.continuing = W := by
        rw [htailSplit, hdropV, List.takeWhile_append_of_pos hcontinuing]
        simp only [List.takeWhile_cons, hstop, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      have hrest : (R.drop b).dropWhile ReferenceCollectionSegmentExtraction.continuing = R.drop v := by
        rw [htailSplit, hdropV, List.dropWhile_append_of_pos hcontinuing]
        simp only [List.dropWhile_cons, hstop, Bool.false_eq_true, ↓reduceIte]
      let seg : ReferenceCollectionSegmentExtraction.Segment rate :=
        ⟨cut, completedCut.context, C, R.drop v⟩
      have hsegment : ReferenceCollectionSegmentExtraction.segment (R.drop w) = some seg := by
        rw [hdrop]
        simp only [ReferenceCollectionSegmentExtraction.segment, hchoice, Option.map_some,
          hcompletedCut, Option.isSome_some, ↓reduceIte, htake, hrest]
        rw [← hC]
      have hsegmentAt : ReferenceCollectionSegmentExtraction.segmentAt R w = some seg := by
        simp only [ReferenceCollectionSegmentExtraction.segmentAt, hsegment, Option.bind_some]
        exact ite_eq_left (Or.inr hinitializer)
      obtain ⟨a, ha, hchecked⟩ := ReferenceCollectionSegmentExtraction.run_collection_initialized_segment_at
        initial source.1.2 J rewards s count span active seed.coordinatorFirst w seg hsegmentAt
      have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed (R.drop w) seg hsegment
      have hcountInputs := ReferenceCollectionSegmentExtraction.segment_input_count (R.drop w) seg hsegment
      have hcalendar := ReferenceCollectionSegmentExtraction.inputs_calendar C hgood
      have hpartition : R.drop w = C ++ R.drop v := by
        rw [hdrop, htailSplit, hC, List.cons_append]
      have hchain := ReferenceFollowerReplyChronology.connected_drop_from_input
        (run_connected initial source.1.2 J rewards s count span active) w
        (by rw [← hrun]; exact hwR)
      change Connected cut.input.state (R.drop w) _ at hchain
      have hindex : C.length < (R.drop w).length := by
        simp only [List.length_drop]
        dsimp only [v] at hvR
        omega
      have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hchain C.length hindex
      have hnextRecord : (R.drop w)[C.length]'hindex = record := by
        simpa only [List.getElem_drop] using hrecord
      rw [hnextRecord, hpartition, List.take_left] at hprefix
      -- This boundary is before the replacement record's new assignment.
      have hendpoint := endpoint_of_connected cut.input.state record.input.state C hprefix
      obtain ⟨endpointPayload, endpointSaved, hendpointCollection⟩ :=
        ReferenceCollectionSegmentExtraction.segmentAt_actual_endpoint R w seg hsegmentAt
          (by change C ≠ []; rw [hC]; exact List.cons_ne_nil _ _)
      change (ReferenceCollectionSegmentExtraction.endpointState cut.input.state C).coordinator =
        .collection endpointPayload seg.final endpointSaved at hendpointCollection
      rw [hendpoint, hincoming] at hendpointCollection
      have hfinal : seg.final = ledger :=
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hendpointCollection).2.1.symm
      refine ⟨hwR, holdSigma, hfields.2.2, seg, a, hsegmentAt, rfl, rfl, ha,
        hfinal, hpending, hgood, hcountInputs, hcalendar, hchecked, ?_⟩
      intro k hk
      exact ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
        initial source.1.2 J rewards s count span active w seg hsegmentAt k hk


/-- On the complete original source, a first reached replacement has the full
checked raw collection execution and the actual incoming carried ledger.
The final conjunct also exposes every checked prefix of this same segment.
No success, crossing, message, numerical law, or survival premise is supplied.
The dependent `laterChosen` fields are those of the actual record; no success
of that record's new-assignment tail is needed. -/
theorem complete_first_replacement_collection_execution
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let C := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + C.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection old ledger _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
          w < R.length ∧ old.sigma.val = s ∧ record.input.time.val = s + v ∧
          ∃ (seg : ReferenceCollectionSegmentExtraction.Segment rate)
            (a : ReferenceCollectionSegmentExtraction.Initializer p),
            ReferenceCollectionSegmentExtraction.segmentAt R w = some seg ∧
            seg.records = C ∧ seg.remaining = R.drop v ∧
            seg.context.initializer = some a ∧ seg.final = ledger ∧ ledger.pending = ∅ ∧
            (∀ c ∈ C, (ReferenceCollectionSegmentExtraction.extractRound c).isSome = true) ∧
            seg.inputs.length = C.length ∧
            seg.inputs.map (fun input => input.round.val) = C.map (fun r => r.input.time.val) ∧
            CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
              (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
              a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside seg.inputs =
                .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
            (∀ k, k ≤ C.length → ∃ accepted,
              CollectionCheckedExecution.checkedRounds seg.context.preLedger (seg.inputs.take k) =
                some (accepted, ReferenceCollectionSegmentExtraction.endpointLedger
                  seg.context.preLedger (C.take k)))
      | _ => True := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch, ↓reduceDIte,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, List.takeWhile_nil,
        List.length_nil, ReferenceCollectionPhaseHistory.collectionWindow,
        List.drop_nil, List.take_nil, List.nil_append, Nat.zero_add, List.getElem?_nil]
  | some initial =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      have hactual := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) hactual
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
      have result := launched_execution rate source rewards C_star C_h hc
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) rfl
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) (by omega)
      simp only [ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun, ← hrecords] at result
      dsimp only at result ⊢
      generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = R at result ⊢
      generalize hw : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length = w at result ⊢
      generalize hC : ReferenceCollectionPhaseHistory.collectionWindow R w = C at result ⊢
      cases hget : R[w + C.length]? with
      | none => trivial
      | some record =>
          simp only [hget] at result
          dsimp only
          cases hcut : record.output.preparation.coordinator with
          | first outcome => trivial
          | live registers owned base outcome => trivial
          | invalidCollectionCutoff => trivial
          | dagger => trivial
          | collection old ledger clock cutoff outcome =>
              rw [hcut] at result
              cases outcome <;> exact result


/-- Every prefix uses the same actual segment and its actual retained ledger
at that prefix boundary. The zero prefix is included. -/
theorem complete_first_replacement_collection_prefix_checked
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let C := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + C.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection _ ledger _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
          ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
            ReferenceCollectionSegmentExtraction.segmentAt R w = some seg ∧
            seg.records = C ∧ seg.final = ledger ∧
            ∀ k, k ≤ C.length → ∃ accepted,
              CollectionCheckedExecution.checkedRounds seg.context.preLedger (seg.inputs.take k) =
                some (accepted, ReferenceCollectionSegmentExtraction.endpointLedger
                  seg.context.preLedger (C.take k))
      | _ => True := by
  have result := complete_first_replacement_collection_execution rate source rewards C_star C_h
  dsimp only at result ⊢
  generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h = R at result ⊢
  generalize hw : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length = w at result ⊢
  generalize hC : ReferenceCollectionPhaseHistory.collectionWindow R w = C at result ⊢
  cases hget : R[w + C.length]? with
  | none => trivial
  | some record =>
      simp only [hget] at result
      dsimp only
      cases hcut : record.output.preparation.coordinator with
      | first outcome => trivial
      | live registers owned base outcome => trivial
      | invalidCollectionCutoff => trivial
      | dagger => trivial
      | collection old ledger clock cutoff outcome =>
          rw [hcut] at result
          cases outcome <;> dsimp only at result ⊢
          obtain ⟨_, _, _, seg, _, hseg, hrec, _, _, hfinal, _, _, _, _, _, hprefix⟩ := result
          exact ⟨seg, hseg, hrec, hfinal, hprefix⟩

end Bandits.Support.ReferenceFirstReplacementCollectionExecution
end
