/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionCurrentNumericalFields

/-!
# First replacement collection: pending sets and actual UP receivers

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,110-177,193-233,246-299`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

These internal execution identities retain old and placeholder offers, checked
receiver failures, and the incoming boundary before a later assignment choice.
Local acceptance is separate from successful checked replay.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionUpReceiverProvenance

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem tail_observation
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {tail : ReferenceCollectionPhaseHistory.Tail x}
    (ht : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
        tail.started tail.weights := by
  classical
  unfold ReferenceCollectionPhaseHistory.executedTail at ht
  dsimp only at ht
  split at ht
  · contradiction
  next hguard =>
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    rw [dite_eq_right hguard]
    cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => cases outcome <;> simp only [hc] at ht <;> contradiction
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc] at ht <;> try contradiction
      cases Option.some.inj ht
      rfl
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc] at ht <;> try contradiction
      cases Option.some.inj ht
      rfl
    | invalidCollectionCutoff => simp only [hc] at ht; contradiction
    | dagger => simp only [hc] at ht; contradiction

private theorem finish_up
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (clock : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (received : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x)
      payload clock recording received).up = received.diagnostic := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases received.result with
  | invalid => rfl
  | success pair | rejected pair =>
    dsimp only
    split <;> try rfl
    split <;> rfl

/-- The same recorder and stage-one call produce the actual retained UP cut,
even when a subsequent receiver, ledger finish, or clock finish fails. -/
theorem executed_reception_provenance
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (started : ReferenceActivePhysicalStep.Ledger rate)
    (received : ReferenceActivePhysicalStep.UpCut p rate)
    (ht : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hr : tail.reception = some (started, received)) :
    ∃ recording : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input)
          tail.payload tail.started tail.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      received = ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) started ∧
      r.output.coordinator.up = received.diagnostic := by
  classical
  unfold ReferenceCollectionPhaseHistory.Tail.reception at hr
  split at hr
  · contradiction
  next recording hrecord =>
    split at hr <;> try contradiction
    rename_i out hstart
    cases Option.some.inj hr
    refine ⟨recording, hrecord, hstart, rfl, ?_⟩
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up = _
    rw [tail_observation ht,
      ReferenceActivePhysicalStep.collectionPostChoice_after_start _ _ _ _ _
        recording started hrecord hstart]
    exact finish_up _ _ _ _

private theorem start_fields
    (ledger started : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (raw : Option (Fin p.K × ℕ))
    (h : CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger time) raw = .success started) :
    started.sigma = ledger.sigma ∧ started.cutoff = ledger.cutoff ∧
      started.pending = ledger.pending ∧ started.cursor = time.val + 1 := by
  rw [ReferenceActivePhysicalStep.collection_started_candidate ledger started time raw h]
  exact ⟨rfl, rfl, rfl, rfl⟩

open CoordinatorCollectionLedger in
private theorem decode_cutoff
    (l : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (ReferenceCollectionPhaseHistory.UpRecord p rate)) :
    match decodeUp l i parsed with
    | .invalid => True
    | .success out | .rejected out => out.cutoff = l.cutoff := by
  classical
  cases parsed with
  | none =>
    by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
        1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
    · let next : ReferenceActivePhysicalStep.Ledger rate := { l with phase := .decoded }
      by_cases hvalid : validLedgerCheck next = true <;>
        simp [decodeUp, hinput, next, hvalid]
    · simp [decodeUp, hinput]
  | some M =>
    by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
        1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
    · by_cases haccept : acceptUpCheck l i M = true
      · by_cases hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
            l.cutoffRegisters (l.assignment.arm i) = none
        · let prefixIndices := calendarIndices p.T (l.cutoff - 1)
            (l.cursor - l.cutoff) (by omega)
          let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
          cases hpast : replayRecords? l (l.assignment.arm i) prefixIndices with
          | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices, hpast]
          | some past =>
            cases hlast : replayRecords? l (l.assignment.arm i) [lastIndex] with
            | none => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                lastIndex, hpast, hlast]
            | some records =>
              cases records with
              | nil => simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                  lastIndex, hpast, hlast]
              | cons record tail =>
                cases tail with
                | nil =>
                  by_cases hdomain : replayOutputDomainsCheck (p := p)
                      (4 * rate.n) M.val.q (past ++ [record]) = true
                  · by_cases hvalid : validLedgerCheck
                        (acceptUpCandidate l i M past record) = true
                    · simp only [decodeUp, hinput, haccept, hunknown, prefixIndices,
                        lastIndex, hpast, hlast, hdomain, hvalid]
                      rfl
                    · simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                        lastIndex, hpast, hlast, hdomain, hvalid]
                  · simp [decodeUp, hinput, haccept, hunknown, prefixIndices,
                      lastIndex, hpast, hlast, hdomain]
                | cons _ _ => simp [decodeUp, hinput, haccept, hunknown,
                    prefixIndices, lastIndex, hpast, hlast]
        · simp [decodeUp, hinput, haccept, hunknown]
      · let next : ReferenceActivePhysicalStep.Ledger rate := { l with phase := .decoded }
        by_cases hvalid : validLedgerCheck next = true <;>
          simp [decodeUp, hinput, haccept, next, hvalid]
    · simp [decodeUp, hinput]

private theorem receive_cutoff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    match (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) ledger).result with
    | .invalid => True
    | .success pair | .rejected pair => pair.1.cutoff = ledger.cutoff := by
  have hd := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x ledger
  have hc := decode_cutoff ledger (ReferenceActivePhysicalStep.upSenderIndex x)
    (ReferenceCollectionSegmentExtraction.effectiveParse x ledger)
  cases hr : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) ledger).result with
  | invalid => trivial
  | success pair | rejected pair =>
    rw [hr] at hd
    rw [hd] at hc
    exact hc

private theorem finish_cutoff
    (ledger out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.finishRound ledger = .success out) :
    out.cutoff = ledger.cutoff := by
  unfold CoordinatorCollectionLedger.finishRound at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h
  rfl

private theorem post_choice_cutoff
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
      tail.started tail.weights).configuration = .collection payload out saved) :
    out.cutoff = tail.ledger.cutoff := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  split at h <;> try contradiction
  rename_i recording hrecord
  dsimp only at h
  split at h <;> try contradiction
  rename_i started hstart
  have hs := (start_fields tail.ledger started x.time _ hstart).2.1
  have hr := receive_cutoff x started
  unfold ReferenceActivePhysicalStep.collectionFinish at h
  cases hc : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).result <;> rw [hc] at h hr
  · dsimp only at h hr
    split at h <;> try contradiction
    rename_i finished hf
    split at h <;> try contradiction
    cases h
    exact (finish_cutoff _ out hf).trans (hr.trans hs)
  · dsimp only at h hr
    split at h <;> try contradiction
    rename_i finished hf
    split at h <;> try contradiction
    cases h
    exact (finish_cutoff _ out hf).trans (hr.trans hs)
  · contradiction

/-- Cutoff is retained along the actual successful collection output. -/
theorem step_collection_cutoff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (h : (ReferenceActivePhysicalStep.step x).next.coordinator =
      .collection payload out saved) :
    ∃ tail : ReferenceCollectionPhaseHistory.Tail x,
      ReferenceCollectionPhaseHistory.executedTail x = some tail ∧
      out.cutoff = tail.ledger.cutoff := by
  obtain ⟨tail, ht, _⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
    x payload out saved h
  refine ⟨tail, ht, post_choice_cutoff tail payload out saved ?_⟩
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = _ at h
  rw [tail_observation ht] at h
  exact h

private theorem tail_of_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (ht : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.payload = payload ∧ tail.ledger = ledger := by
  classical
  have hdispatch : (ReferenceActivePhysicalStep.prepare x).coordinator =
      ReferenceActivePhysicalStep.dispatch x := rfl
  unfold ReferenceActivePhysicalStep.dispatch at hdispatch
  rw [hstate] at hdispatch
  dsimp only at hdispatch
  split at hdispatch
  · rename_i hcut
    cases hd : CoordinatorRoundDispatch.dispatch (.collection
        (ReferenceActivePhysicalStep.collectionInput x payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved
            ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩)) with
    | collection outcome =>
      rw [hd] at hdispatch
      unfold ReferenceCollectionPhaseHistory.executedTail at ht
      dsimp only at ht
      split at ht <;> try contradiction
      rw [hdispatch] at ht
      cases outcome <;> try contradiction
      cases Option.some.inj ht
      exact ⟨rfl, rfl⟩
  · simp only [ReferenceCollectionPhaseHistory.executedTail, hdispatch] at ht
    split at ht <;> contradiction

/-- The unfiltered diagnostic belongs to the same actual receiver call.
An absent diagnostic is a failed input check and an invalid receiver result. -/
theorem executed_reception_diagnostic
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (started : ReferenceActivePhysicalStep.Ledger rate)
    (received : ReferenceActivePhysicalStep.UpCut p rate)
    (ht : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hr : tail.reception = some (started, received)) :
    let rin := ReferenceUpReception.receptionInputAtRow rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time
    match received.diagnostic with
    | none => CoordinatorUpReception.receptionInputCheck rin = false ∧
        received.result = .invalid ∧ r.output.coordinator.up = none
    | some d => d.input = rin ∧
        d.expected = ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) ∧
        d.raw = (CoordinatorUpReception.decoderTransition rin).2 ∧
        d.parsed = ReferenceUpReception.rawParsedOutput rate rin ∧
        r.output.coordinator.up = some d := by
  classical
  obtain ⟨recording, hrecord, hstart, heq, hup⟩ :=
    executed_reception_provenance r tail started received ht hr
  subst received
  dsimp only
  cases hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time) with
  | false =>
    have hnone : (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) started).diagnostic = none := by
      simp only [ReferenceActivePhysicalStep.receiveUp, hcheck, Bool.false_eq_true,
        ite_false]
    rw [hnone]
    refine ⟨rfl, ?_, hup.trans hnone⟩
    simp only [ReferenceActivePhysicalStep.receiveUp,
      ReferenceUpReception.receiveUpFilteredAtRow, hcheck, Bool.false_eq_true, ite_false]
  | true =>
    simp only [ReferenceActivePhysicalStep.receiveUp, hcheck, ite_true] at hup ⊢
    simpa only [true_and] using hup

private theorem erase_labels
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) :
    ReferenceCollectionPhaseHistory.eraseEvent
      (Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels records).toFinset)
      (ReferenceCollectionPhaseHistory.acceptedLabel r.input) =
      Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (records ++ [r])).toFinset := by
  classical
  cases he : ReferenceCollectionPhaseHistory.acceptedLabel r.input with
  | none => simp only [ReferenceCollectionPhaseHistory.acceptedLabels,
      List.filterMap_append, List.filterMap_cons, he, List.filterMap_nil,
      List.append_nil, ReferenceCollectionPhaseHistory.eraseEvent]
  | some i =>
    simp only [ReferenceCollectionPhaseHistory.acceptedLabels,
      List.filterMap_append, List.filterMap_cons, he, List.filterMap_nil,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      ReferenceCollectionPhaseHistory.eraseEvent, Finset.union_insert, Finset.union_empty]
    rw [Finset.sdiff_insert]


private theorem offer_of_prepared
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (r.output.preparation.followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex r.input)).configuration =
        .ordinary state memory)
    (hstatus : state.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state))
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot) :
    ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceActivePhysicalStep.upSenderIndex r.input) r.input.row
        (r.input.state.activations (ReferenceActivePhysicalStep.upSenderIndex r.input))
        r.input.time state = .offer U ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  classical
  let i := ReferenceActivePhysicalStep.upSenderIndex r.input
  have hselected : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
      (r.input.state.activations i) r.input.time :=
    ⟨r.input.active i, hslot,
      (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw _).symm⟩
  have hinput : ActiveFollowerQueueOperation.stateInputDomain state := by
    rcases hdomain with ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _⟩
    exact ⟨hS, hdelta, hbacklog,
      ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer,
      ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer⟩
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time state = .offer U := by
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dite_eq_left hinput, dite_eq_left ⟨hselected, hstatus⟩,
      dite_eq_left hadmissible]
  have halign := r.output.preparation.follower_alignment i
  have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice r i).follower
      (ReferenceFollowerFixedReply.actualChoice r i).row
      (ReferenceFollowerFixedReply.actualChoice r i).activation
      (ReferenceFollowerFixedReply.actualChoice r i).time state = .offer U := by
    change ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (r.output.preparation.followers.followers i).follower
      (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).activation
      (r.output.preparation.followers.followers i).time state = .offer U
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    exact hoff
  have hword := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
    r i rfl state memory hconfiguration U hoff'
  refine ⟨U, hoff, rfl, ?_⟩
  unfold ReferenceFollowerFixedReply.actualUpExpected at hword
  rw [r.output_eq] at hword
  exact hword

private theorem collection_endpoint_fields
    (cut : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (W : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hcut : ∀ tail : ReferenceCollectionPhaseHistory.Tail cut.input,
      ReferenceCollectionPhaseHistory.executedTail cut.input = some tail →
        tail.ledger.sigma = payload.sigma.val + 1 ∧
        tail.ledger.cutoff = cut.input.time.val + 1 ∧ tail.ledger.pending = Finset.univ)
    (hzero : cut.output.next.coordinator = .dagger ∨
      ∃ ledger saved, cut.output.next.coordinator = .collection payload ledger saved)
    (hphase : ∀ j : Fin W.length,
      (W.get j).output.next.coordinator = .dagger ∨
        ∃ ledger saved, (W.get j).output.next.coordinator = .collection payload ledger saved)
    (hadjacent : ∀ j : Fin W.length,
      (W.get j).input.state = ReferenceCollectionSegmentExtraction.endpointState
          cut.output.next (W.take j.val) ∧
      ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take (j.val + 1)) =
        (W.get j).output.next) :
    ∀ j : ℕ, j ≤ W.length →
      let E := ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j)
      E.coordinator = .dagger ∨ ∃ ledger saved,
        E.coordinator = .collection payload ledger saved ∧
        ledger.sigma = payload.sigma.val + 1 ∧
        ledger.cutoff = cut.input.time.val + 1 ∧
        ledger.pending = Finset.univ \
          (ReferenceCollectionPhaseHistory.acceptedLabels (cut :: W.take j)).toFinset := by
  classical
  intro j
  induction j with
  | zero =>
    intro _
    dsimp only
    simp only [List.take_zero, ReferenceCollectionSegmentExtraction.endpointState]
    rcases hzero with hdagger | ⟨ledger, saved, hcoord⟩
    · exact Or.inl hdagger
    · right
      have hs : (ReferenceActivePhysicalStep.step cut.input).next.coordinator =
          .collection payload ledger saved := by
        rw [← cut.output_eq]
        exact hcoord
      obtain ⟨tail, ht, hpending, hsigma⟩ :=
        ReferenceCollectionPhaseHistory.step_collection_frame cut.input payload ledger saved hs
      obtain ⟨hsigma0, hcutoff0, hfull⟩ := hcut tail ht
      have hpost := hs
      change (ReferenceActivePhysicalStep.prepare cut.input).observeCoordinator.configuration = _
        at hpost
      rw [tail_observation ht] at hpost
      refine ⟨ledger, saved, hcoord, hsigma.trans hsigma0,
        (post_choice_cutoff tail payload ledger saved hpost).trans hcutoff0, ?_⟩
      calc
        ledger.pending = ReferenceCollectionPhaseHistory.eraseEvent
            (Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels []).toFinset)
            (ReferenceCollectionPhaseHistory.acceptedLabel cut.input) := by
          rw [hpending, hfull]
          rfl
        _ = _ := erase_labels [] cut
  | succ j ih =>
    intro hj
    have hjlt : j < W.length := by omega
    let idx : Fin W.length := ⟨j, hjlt⟩
    let r := W.get idx
    obtain ⟨hinput, hnext⟩ := hadjacent idx
    dsimp only
    rw [hnext]
    rcases hphase idx with hdagger | ⟨ledger, saved, hcoord⟩
    · exact Or.inl hdagger
    · right
      have hs : (ReferenceActivePhysicalStep.step r.input).next.coordinator =
          .collection payload ledger saved := by
        rw [← r.output_eq]
        exact hcoord
      obtain ⟨tail, ht, hpending, hsigma⟩ :=
        ReferenceCollectionPhaseHistory.step_collection_frame r.input payload ledger saved hs
      rcases ih (Nat.le_of_lt hjlt) with hdagger | ⟨before, proposal, hbefore, hsig, hcutoff, hpend⟩
      · have hin : r.input.state.coordinator = .dagger := by rw [hinput]; exact hdagger
        have hout := (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hin).1
        rw [hs] at hout
        contradiction
      · have hin : r.input.state.coordinator = .collection payload before proposal := by
          rw [hinput]
          exact hbefore
        have htail := (tail_of_collection r.input payload before proposal tail hin ht).2
        have hpost := hs
        change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration = _
          at hpost
        rw [tail_observation ht] at hpost
        refine ⟨ledger, saved, hcoord, hsigma.trans (htail ▸ hsig),
          (post_choice_cutoff tail payload ledger saved hpost).trans (htail ▸ hcutoff), ?_⟩
        calc
          ledger.pending = ReferenceCollectionPhaseHistory.eraseEvent
              (Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                (cut :: W.take j)).toFinset)
              (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
            rw [hpending, htail, hpend]
          _ = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
              ((cut :: W.take j) ++ [r])).toFinset := erase_labels (cut :: W.take j) r
          _ = _ := by
            rw [List.take_succ_eq_append_getElem hjlt]
            rfl

private theorem reception_none_failure
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (tail : ReferenceCollectionPhaseHistory.Tail x) (h : tail.reception = none) :
    CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
        tail.payload tail.started tail.weights) = none ∨
    ∃ recording : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
          tail.payload tail.started tail.weights) = some recording ∧
      (CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .invalid ∨
        ∃ rejected, CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .rejected rejected) := by
  unfold ReferenceCollectionPhaseHistory.Tail.reception at h
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
        tail.payload tail.started tail.weights) with
  | none => exact Or.inl rfl
  | some recording =>
    rw [hrecord] at h
    dsimp only at h
    cases hstart : CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
    | invalid => exact Or.inr ⟨recording, rfl, Or.inl hstart⟩
    | rejected out => exact Or.inr ⟨recording, rfl, Or.inr ⟨out, hstart⟩⟩
    | success out => rw [hstart] at h; contradiction


private theorem offer_origin
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hfields : U.val = ActiveFollowerQueueOperation.upOfferFields state)
    (hsigma : ledger.sigma = M.val.sigma) (hcutoff : ledger.cutoff ≤ ledger.cursor)
    (horigin : ReferencePrelaunchFollower.acceptedStart state < M.val.sigma ∨
      state.lastDown = some M) :
    (ReferencePrelaunchFollower.acceptedStart state < M.val.sigma ∧
      U.val.sigma < M.val.sigma ∧ CoordinatorCollectionLedger.acceptUpCheck ledger i U = false) ∨
    (state.lastDown = some M ∧ U.val.sigma = M.val.sigma ∧
      (CoordinatorCollectionLedger.acceptUpCheck ledger i U = true ↔ i ∈ ledger.pending)) := by
  have hstart : U.val.sigma = ReferencePrelaunchFollower.acceptedStart state := by
    rw [hfields]
    rfl
  rcases horigin with hold | hcurrent
  · left
    have hne : U.val.sigma ≠ ledger.sigma := by omega
    exact ⟨hold, hstart ▸ hold, by simp [CoordinatorCollectionLedger.acceptUpCheck, hne]⟩
  · right
    have hcurrentStart : U.val.sigma = M.val.sigma := by
      rw [hstart]
      simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
    refine ⟨hcurrent, hcurrentStart, ?_⟩
    simp only [CoordinatorCollectionLedger.acceptUpCheck, hcutoff, decide_true,
      Bool.true_and, hcurrentStart, hsigma, Bool.and_true, decide_eq_true_eq]

/-- The actual first replacement collection's coordinator and receiver
provenance. No current-word, successful-decoder, or surviving-tail premise is
required. This does not assert that a pure completed UP window exists. -/
theorem complete_first_replacement_collection_up_receiver_provenance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        C.length = L ∧ X = birth :: tail ∧
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let M := fun i => payload.downRecord i
            (∀ j : ℕ, j ≤ W.length →
              (E j).coordinator = .dagger ∨ ∃ ledger saved,
                (E j).coordinator = .collection payload ledger saved ∧
                ledger.sigma = payload.sigma.val + 1 ∧ ledger.cutoff = u ∧
                ledger.pending = Finset.univ \
                  (ReferenceCollectionPhaseHistory.acceptedLabels (cut :: W.take j)).toFinset) ∧
            (∀ k : Fin K.length,
              let r := K.get k
              match ReferenceCollectionPhaseHistory.executedTail r.input with
              | none => ReferenceCollectionPhaseHistory.executedTail r.input = none
              | some t =>
                match t.reception with
                | none =>
                  CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.collectionRecordingInput
                      (ReferenceActivePhysicalStep.prepare r.input)
                      t.payload t.started t.weights) = none ∨
                  ∃ recording : CoordinatorRecordingOperation.Output p,
                    CoordinatorRecorderComplementBridge.run
                      (ReferenceActivePhysicalStep.collectionRecordingInput
                        (ReferenceActivePhysicalStep.prepare r.input)
                        t.payload t.started t.weights) = some recording ∧
                    (CoordinatorCollectionLedger.startRound t.ledger (r.input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled t.ledger r.input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .invalid ∨
                      ∃ rejected, CoordinatorCollectionLedger.startRound t.ledger
                        (r.input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled t.ledger r.input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .rejected rejected)
                | some (started, received) =>
                  let rin := ReferenceUpReception.receptionInputAtRow rate r.input.row
                    (ReferenceActivePhysicalStep.upInputs
                      (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time
                  let i := ReferenceActivePhysicalStep.upSenderIndex r.input
                  started.sigma = payload.sigma.val + 1 ∧ started.cutoff = u ∧
                  started.cursor = r.input.time.val + 1 ∧
                  started.pending = Finset.univ \
                    (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset ∧
                  (CoordinatorUpReception.receptionGate rin ↔
                    PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                        PublicDiscreteDraws.upSlot ∧
                      i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset) ∧
                  (PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                      PublicDiscreteDraws.upSlot →
                    ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                      (memory : ActiveFollowerLifecycle.LocalMemory p)
                      (U : OrdinaryMessageCodec.UpRecord
                        (ReferencePrelaunchFollower.codecParams p rate.eta)),
                      (r.output.preparation.followers.followers i).configuration =
                        .ordinary state memory ∧
                      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                        (r.input.state.activations i) r.input.time state = .offer U ∧
                      U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                      ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare r.input) =
                          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                      ((ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                        U.val.sigma < (M i).val.sigma ∧
                        CoordinatorCollectionLedger.acceptUpCheck started i U = false) ∨
                      (state.lastDown = some (M i) ∧ U.val.sigma = (M i).val.sigma ∧
                        (CoordinatorCollectionLedger.acceptUpCheck started i U = true ↔
                          i ∈ started.pending)))) ∧
                  match received.diagnostic with
                  | none => CoordinatorUpReception.receptionInputCheck rin = false ∧
                      received.result = .invalid ∧ r.output.coordinator.up = none
                  | some d => d.input = rin ∧
                      d.expected = ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare r.input) ∧
                      d.raw = (CoordinatorUpReception.decoderTransition rin).2 ∧
                      d.parsed = ReferenceUpReception.rawParsedOutput rate rin ∧
                      r.output.coordinator.up = some d) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState
                  rate source rewards C_star C_h = some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved,
                  (E W.length).coordinator = .collection payload ledger saved ∧
                  next.input.state.coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K,
                    ∃ U, ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hN :=
    ReferenceFirstReplacementCollectionCurrentNumericalFields.complete_first_replacement_collection_current_numerical_fields
      rate source rewards C_star C_h
  have hO :=
    ReferenceFirstReplacementCollectionDispatchOrigin.complete_first_replacement_collection_dispatch_origin
      rate source rewards C_star C_h
  have hB :=
    ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
      rate source rewards C_star C_h
  have hK :=
    ReferenceFirstReplacementCutoffCurrentNumericalOutputs.complete_first_replacement_cutoff_current_numerical_outputs
      rate source rewards C_star C_h
  dsimp only at hN hO hB hK ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hN hO hB hK ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hN hO hB hK ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hN hO hB hK ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      let L := X.length
      rcases hN with ⟨hCL, hX, hN⟩
      refine ⟨hCL, hX, ?_⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hN hO hB hK ⊢
        rcases hB with ⟨_, hB⟩
        rcases hK with ⟨_, _, _, _, hK⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hN hO hB hK ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hN hO hB hK ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let M := fun i => payload.downRecord i
          rcases hN with ⟨_, _, hEzero, hgeometry, hfollowers⟩
          rcases hO with ⟨hphase0, hphases⟩
          rcases hB with ⟨hpayload, _, _, _, _, _, _, _, _, _, _,
            selectedB, hselectedB, _, _, _, hboundary⟩
          rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, _,
            selectedK, hselectedK, _, _, _, hcutFollowers⟩
          have hactualCut : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
              .live registers owned base
                (.cutoffChosen dispatched hs ledger hi hledger hdata hclock hpending hnone
                  selectedCut) := by
            have he := hcut
            rw [cut.output_eq] at he
            exact he
          have hcutFields : ∀ t : ReferenceCollectionPhaseHistory.Tail cut.input,
              ReferenceCollectionPhaseHistory.executedTail cut.input = some t →
              t.ledger.sigma = payload.sigma.val + 1 ∧ t.ledger.cutoff = u ∧
                t.ledger.pending = Finset.univ := by
            intro t ht
            unfold ReferenceCollectionPhaseHistory.executedTail at ht
            dsimp only at ht
            split at ht <;> try contradiction
            rw [hactualCut] at ht
            cases Option.some.inj ht
            rw [hledger]
            exact ⟨by simpa only [ReferenceActivePhysicalStep.sharedLedger,
              CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
              ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt]
              using congrArg (fun q : ReferenceActivePhysicalStep.Payload rate =>
                q.sigma.val + 1) hpayload, rfl, rfl⟩
          have hadjacent : ∀ j : Fin W.length,
              (W.get j).input.state = E j.val ∧ E (j.val + 1) = (W.get j).output.next := by
            intro j
            rcases hfollowers ⟨0, by have := p.two_le_m; omega⟩ with
              ⟨old, initial, memory, _, _, _, _, _, hsteps, _⟩
            have hstep := hsteps j.val j.isLt
            obtain ⟨state, logged, post, hget, hinput, _⟩ := hstep
            have hgeo := hgeometry j.val (Nat.le_of_lt j.isLt)
            rw [hget] at hgeo
            exact ⟨hinput, (hgeo.2.2.2.2.2.1 j.isLt).2⟩
          have hendpoints := collection_endpoint_fields cut W payload hcutFields hphase0
            (fun j => (hphases j).2.1) hadjacent
          refine ⟨hendpoints, ?_, ?_⟩
          · have hrecords : ∀ k : Fin K.length,
                let r := K.get k
                (∀ t : ReferenceCollectionPhaseHistory.Tail r.input,
                  ReferenceCollectionPhaseHistory.executedTail r.input = some t →
                  t.ledger.sigma = payload.sigma.val + 1 ∧ t.ledger.cutoff = u ∧
                  t.ledger.pending = Finset.univ \
                    (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset) ∧
                u ≤ r.input.time.val + 1 ∧
                ∀ i : Fin (p.m - 1),
                  ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                    (memory : ActiveFollowerLifecycle.LocalMemory p),
                    (r.output.preparation.followers.followers i).configuration =
                      .ordinary state memory ∧ state.status = .unoccupied ∧
                    ActiveFollowerLifecycle.localStateDomainValid state ∧
                    OrdinaryMessageCodec.upAdmissible
                      (ReferencePrelaunchFollower.codecParams p rate.eta)
                      (ActiveFollowerQueueOperation.upOfferFields state) ∧
                    (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                      state.lastDown = some (M i)) := by
              intro ⟨k, hk⟩
              cases k with
              | zero =>
                refine ⟨?_, Nat.le_refl u, ?_⟩
                · intro t ht
                  simpa only [List.take_zero, ReferenceCollectionPhaseHistory.acceptedLabels,
                    List.filterMap_nil, List.toFinset_nil, Finset.sdiff_empty] using hcutFields t ht
                · intro i
                  rcases hboundary i with
                    ⟨old, memory, hinput, _, _, _, hold, hcurrent, _, _, _,
                      hdomain, _, _, _, hadmissible, _⟩
                  rcases hcutFollowers i with
                    ⟨oldK, memoryK, hinputK, hconfiguration, _⟩
                  obtain ⟨rfl, rfl⟩ :=
                    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                      (hinput.symm.trans hinputK)
                  refine ⟨{ old with status := .unoccupied }, memory,
                    hconfiguration, rfl, hdomain, hadmissible, ?_⟩
                  by_cases hstatus : old.status = .unoccupied
                  · exact Or.inl (hold hstatus)
                  · exact Or.inr (hcurrent hstatus).1
              | succ j =>
                have hj : j < W.length := by
                  have hk' : j + 1 < W.length + 1 := hk
                  omega
                let idx : Fin W.length := ⟨j, hj⟩
                let r := W.get idx
                have hin := (hadjacent idx).1
                change (∀ t : ReferenceCollectionPhaseHistory.Tail r.input, _) ∧
                  u ≤ r.input.time.val + 1 ∧ _
                refine ⟨?_, ?_, ?_⟩
                · intro t ht
                  change ReferenceCollectionPhaseHistory.executedTail r.input = some t at ht
                  rcases hendpoints j (Nat.le_of_lt hj) with
                    hdagger | ⟨before, proposal, hcoord, hsig, hcutoff, hpend⟩
                  · have hd : r.input.state.coordinator = .dagger := by rw [hin]; exact hdagger
                    have hdispatch := ReferenceActivePhysicalStep.dispatch_dagger r.input hd
                    simp only [ReferenceCollectionPhaseHistory.executedTail,
                      ReferenceActivePhysicalStep.prepare, hdispatch,
                      ReferenceActivePhysicalStep.DispatchCut.selection, ite_true] at ht
                    contradiction
                  · have hcoord' : r.input.state.coordinator =
                        .collection payload before proposal := by rw [hin]; exact hcoord
                    have heq := (tail_of_collection r.input payload before proposal t
                      hcoord' ht).2
                    exact ⟨heq ▸ hsig, heq ▸ hcutoff, heq ▸ hpend⟩
                · rcases hfollowers ⟨0, by have := p.two_le_m; omega⟩ with
                    ⟨old, initial, memory, _, _, _, _, _, hsteps, _⟩
                  rcases hsteps j hj with ⟨state, logged, post, hget, _⟩
                  have hgeo := hgeometry j (Nat.le_of_lt hj)
                  rw [hget] at hgeo
                  have htime : r.input.time.val = u + j := hgeo.2.1
                  omega
                · intro i
                  rcases hfollowers i with
                    ⟨old, initial, memory, _, _, _, _, _, hsteps, _⟩
                  rcases hsteps j hj with
                    ⟨state, logged, post, _, _, _, _, hstatus, hdomain, horigin,
                      _, _, hconfiguration, hadmissible, _⟩
                  exact ⟨state, memory, hconfiguration, hstatus, hdomain, hadmissible, horigin⟩
            intro k
            let r := K.get k
            obtain ⟨hpre, htime, hprepared⟩ := hrecords k
            cases ht : ReferenceCollectionPhaseHistory.executedTail r.input with
            | none =>
              simp only
            | some t =>
              simp only
              cases hr : t.reception with
              | none => exact reception_none_failure t hr
              | some pair =>
                rcases pair with ⟨started, received⟩
                dsimp only
                obtain ⟨recording, hrecord, hstart, _, _⟩ :=
                  executed_reception_provenance r t started received ht hr
                obtain ⟨hsigma, hcutoff, hpending⟩ := hpre t ht
                obtain ⟨hsig, hcut, hpend, hcursor⟩ :=
                  start_fields t.ledger started r.input.time _ hstart
                have hsig' := hsig.trans hsigma
                have hcut' := hcut.trans hcutoff
                have hpend' := hpend.trans hpending
                have htime' : u ≤ r.input.time.val + 1 := htime
                have hcutCursor : started.cutoff ≤ started.cursor := by omega
                refine ⟨hsig', hcut', hcursor, hpend', ?_, ?_,
                  executed_reception_diagnostic r t started received ht hr⟩
                · change started.cutoff ≤ r.input.time.val + 1 ∧
                    PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                      PublicDiscreteDraws.upSlot ∧
                    ReferenceActivePhysicalStep.upSenderIndex r.input ∈ started.pending ↔ _
                  rw [hpend']
                  simp only [hcut', htime', true_and, Finset.mem_sdiff, Finset.mem_univ]
                  rfl
                · intro hslot
                  let i := ReferenceActivePhysicalStep.upSenderIndex r.input
                  obtain ⟨state, memory, hconfiguration, hstatus, hdomain, hadmissible, horigin⟩ :=
                    hprepared i
                  obtain ⟨U, hoff, hfields, hword⟩ := offer_of_prepared r state memory
                    hconfiguration hstatus hdomain hadmissible hslot
                  exact ⟨state, memory, U, hconfiguration, hoff, hfields, hword,
                    offer_origin state started i (M i) U hfields hsig' hcutCursor horigin⟩
          · have hgeo := hgeometry W.length (Nat.le_refl _)
            cases hn : R[c + 1 + W.length]? with
            | none =>
              simp only
              rw [hn] at hgeo
              exact hgeo.2
            | some next =>
              simp only
              rw [hn] at hgeo
              have hin : next.input.state = E W.length := hgeo.1
              have hlater := hgeo.2.2.2.2.2.2 rfl
              obtain ⟨nextPayload, nextLedger, nextSaved, hcoordNext, hempty⟩ :=
                ReferenceCollectionPhaseHistory.laterChosen_pending_empty next.input hlater
              rcases hendpoints W.length (Nat.le_refl _) with
                hdagger | ⟨final, saved, hcoord, hsig, hcutoff, hpend⟩
              · rw [hin, hdagger] at hcoordNext
                contradiction
              · have heq : ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
                    payload final saved = .collection nextPayload nextLedger nextSaved := by
                  calc
                    _ = (E W.length).coordinator := hcoord.symm
                    _ = next.input.state.coordinator := congrArg
                      ReferenceActivePhysicalStep.State.coordinator hin.symm
                    _ = _ := hcoordNext
                obtain ⟨rfl, rfl, rfl⟩ :=
                  ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj heq
                refine ⟨hin, hlater, final, saved, hcoord, hcoordNext, hempty, ?_⟩
                intro i
                have hmember : i ∈ (ReferenceCollectionPhaseHistory.acceptedLabels K).toFinset := by
                  have hall : Finset.univ \
                      (ReferenceCollectionPhaseHistory.acceptedLabels K).toFinset = ∅ := by
                    simpa only [List.take_length] using hpend.symm.trans hempty
                  exact Finset.mem_of_subset (Finset.sdiff_eq_empty_iff_subset.mp hall)
                    (Finset.mem_univ i)
                have hlabel : i ∈ ReferenceCollectionPhaseHistory.acceptedLabels K :=
                  List.mem_toFinset.mp hmember
                obtain ⟨r, hr, hevent⟩ := List.mem_filterMap.mp hlabel
                obtain ⟨U, hwitness⟩ := ReferenceCollectionPhaseHistory.acceptedLabel_witness hevent
                exact ⟨r, hr, U, hwitness⟩

end Bandits.Support.ReferenceFirstReplacementCollectionUpReceiverProvenance
