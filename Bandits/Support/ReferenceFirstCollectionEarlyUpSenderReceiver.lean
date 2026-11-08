/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEarlyDownReplyHistory
public import Bandits.Support.ReferenceCutoffUpReceiverLocal

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection UP sender and receiver after an earlier DOWN

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,164-177,246-295,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The root retains the actual early-DOWN boundaries and strengthens its offered
word conclusions to equality with one typed record, including the original
pairwise codec equality. The seed query
constructs one admissible ordinary UP record from that result's actual local
registers and checks the actual cutoff sender when the same row selects this
follower for UP. No receiver observation or successful outgoing premise is
used to create the record.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.OrdinaryMessageCodec

namespace Bandits.Support.ReferenceFirstCollectionEarlyUpSenderReceiver

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem stateInputDomain_of_localDomain
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases hvalid with ⟨hservice, hbuffer, _⟩
  rcases hservice with ⟨hS, hdelta, hbacklog⟩
  refine ⟨hS, hdelta, hbacklog, hbuffer.1, ?_⟩
  change (state.buffer.map (fun record => (record.calendarRound, record.pilot))).Nodup
  exact hbuffer.2.1

private theorem seed_up_record
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (s : ℕ)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid before)
    (hMstart : M.val.sigma = s + 1) :
    ∃ U : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = OrdinaryMessageCodec.UpFields.mk (s + 1)
        before.S before.delta before.backlog ∧
      0 < U.val.sigma := by
  have hMproperty := M.property
  simp only [OrdinaryMessageCodec.downAdmissible] at hMproperty
  have hsigmaLower : 1 ≤ s + 1 := by omega
  have hsigmaUpper : s + 1 ≤ p.T := by rw [← hMstart]; exact hMproperty.2.1
  have hregisters := hvalid.1
  have hfieldsAdmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (OrdinaryMessageCodec.UpFields.mk (s + 1)
        before.S before.delta before.backlog) := by
    apply Or.inr
    refine ⟨hsigmaLower, hsigmaUpper, ?_, ?_, ?_⟩
    · simpa only [ReferencePrelaunchFollower.codecParams] using hregisters.1
    · simpa only [ReferencePrelaunchFollower.codecParams] using hregisters.2.1
    · simpa only [ReferencePrelaunchFollower.codecParams] using hregisters.2.2
  let U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨OrdinaryMessageCodec.UpFields.mk (s + 1)
      before.S before.delta before.backlog, hfieldsAdmissible⟩
  refine ⟨U, rfl, ?_⟩
  exact hsigmaLower

private theorem receiver_awaited_gates
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (A : List (ReferenceCollectionPhaseHistory.Label p))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1)) (s : ℕ)
    (hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true)
    (hinput : d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L)
    (hpending : L.pending = Finset.univ \ A.toFinset)
    (hsigma : L.sigma = s + 1) (hU : U.val.sigma = s + 1)
    (hdecoder : d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1)
    (hraw : d.raw = (CoordinatorUpReception.decoderTransition d.input).2) :
    ∀ (_hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
      (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i),
      (i ∉ A.toFinset →
        d.input.selectedFollower = i ∧ CoordinatorUpReception.receptionGate d.input ∧
        (CoordinatorUpReception.roundInput d.input).selected = true ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
        (d.input.ownObservation.val = 0 →
          d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none)) ∧
      (i ∈ A.toFinset →
        d.input.selectedFollower = i ∧ ¬ CoordinatorUpReception.receptionGate d.input ∧
        (CoordinatorUpReception.roundInput d.input).selected = false ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none) := by
  intro hslot hselected
  have hdomain : CoordinatorUpReception.receptionInputDomain d.input := by
    apply (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp
    rw [hinput]
    exact hcheck
  obtain ⟨_, _, _, _, hcutoffCursor, _, hcursorSource, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdomain
  have hinputLedger : d.input.ledger = L := by
    rw [hinput]
    rfl
  have hinputFollower : d.input.selectedFollower = i := by
    rw [hinput]
    simp only [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl_selectedFollower]
    exact hselected
  have hinputSlot : d.input.slot = PublicDiscreteDraws.upSlot := by
    simpa [hinput, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl_slot] using hslot
  have hcutoffBound : L.cutoff ≤ L.cursor := by
    simpa [hinputLedger] using hcutoffCursor
  have hcutoffSource : L.cutoff ≤ CoordinatorCollectionLedger.sourceRound d.input.time := by
    calc
      L.cutoff ≤ L.cursor := hcutoffBound
      _ = CoordinatorCollectionLedger.sourceRound d.input.time := by
        simpa [hinputLedger] using hcursorSource
  have henabled : (CoordinatorUpReception.roundInput d.input).receiverEnabled = true := by
    simp only [CoordinatorUpReception.roundInput]
  have hunchanged (hineligible :
      ¬ AffineBatchDecoder.eligible ((CoordinatorUpReception.traceAt d.input) d.input.time)) :
      d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none := by
    have htransition := CoordinatorUpReception.decoderTransition_ineligible d.input hdomain hineligible
    rw [hdecoder, hraw, htransition]
    exact ⟨rfl, rfl⟩
  constructor
  · intro hnotAccepted
    have hiPending : i ∈ L.pending := by
      rw [hpending]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnotAccepted⟩
    have hgate : CoordinatorUpReception.receptionGate d.input := by
      unfold CoordinatorUpReception.receptionGate
      rw [hinputLedger, hinputFollower]
      exact ⟨hcutoffSource, hinputSlot, hiPending⟩
    have hselect := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).2 hgate
    have haccept : CoordinatorCollectionLedger.acceptUpCheck L i U = true := by
      simp only [CoordinatorCollectionLedger.acceptUpCheck, hcutoffBound, hiPending, hsigma, hU,
        Bool.and_self, decide_true]
    refine ⟨hinputFollower, hgate, hselect, henabled, haccept, ?_⟩
    intro hzero
    apply hunchanged
    intro heligible
    have hpositive := heligible.2.2
    change 0 < CoordinatorUpReception.roundedObservationValue p d.input.ownObservation at hpositive
    rw [CoordinatorUpReception.roundedObservationValue_zero p d.input.ownObservation hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  · intro haccepted
    have hiNotPending : i ∉ L.pending := by
      rw [hpending]
      intro hi
      exact (Finset.mem_sdiff.mp hi).2 haccepted
    have hgate : ¬ CoordinatorUpReception.receptionGate d.input := by
      intro hgate
      have hi := hgate.2.2
      rw [hinputLedger, hinputFollower] at hi
      exact hiNotPending hi
    have hselect : (CoordinatorUpReception.roundInput d.input).selected = false := by
      cases hsel : (CoordinatorUpReception.roundInput d.input).selected with
      | false => rfl
      | true => exact (hgate ((CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp hsel)).elim
    refine ⟨hinputFollower, hgate, hselect, henabled, hunchanged ?_⟩
    intro heligible
    have hselectedTrue := heligible.1
    change (CoordinatorUpReception.roundInput d.input).selected = true at hselectedTrue
    rw [hselect] at hselectedTrue
    cases hselectedTrue

private theorem connected_endpoint_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final₁ final₂ : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h₁ : ReferenceActivePhysicalHorizon.Connected initial records final₁)
    (h₂ : ReferenceActivePhysicalHorizon.Connected initial records final₂) :
    final₁ = final₂ := by
  induction records generalizing initial final₁ final₂ with
  | nil =>
      change final₁ = initial at h₁
      change final₂ = initial at h₂
      exact h₁.trans h₂.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact ih h₁.2 h₂.2

private theorem run_prefix_records
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records.take k =
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
      (by omega) active).records := by
  obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows
    selected rewards start k (count - k) (by omega) active
  have hcount : k + (count - k) = count := Nat.add_sub_of_le hk
  simp only [hcount] at heq
  rw [heq, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem run_prefix_endpoints
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
    (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
    (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards
    start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n
    (by omega)
  have hprefixEq : full.records.take n = prefixRun.records := by
    simpa [full, prefixRun] using hprefix
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefixEq]
    exact htake)
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] htake rfl
  have hprefixNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hprefixNextEq : full.records.take (n + 1) = nextPrefix.records := by
    simpa [full, nextPrefix] using hprefixNext
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hprefixNextEq]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem run_records_chronological
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
  have hvalues := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan active
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar start count).Pairwise
      (fun earlier later => earlier < later) := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.pairwise_lt_range' (s := start) (n := count) (step := 1)
        (by decide : 0 < 1))
  have htimeValues :
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.map
        (fun record => record.input.time.val)).Pairwise (fun earlier later => earlier < later) := by
    rw [hvalues]
    exact hcalendar
  exact List.pairwise_map.mp htimeValues

private theorem acceptedLabels_take_succ
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : ℕ) (hn : n < xs.length) :
    ReferenceCollectionPhaseHistory.acceptedLabels (xs.take (n + 1)) =
      ReferenceCollectionPhaseHistory.acceptedLabels (xs.take n) ++
        (ReferenceCollectionPhaseHistory.acceptedLabel xs[n].input).toList := by
  have htake : xs.take (n + 1) = xs.take n ++ [xs[n]] := by
    rw [List.take_add_one]
    simp [hn]
  unfold ReferenceCollectionPhaseHistory.acceptedLabels
  rw [htake, List.filterMap_append]
  rfl

private theorem eraseEvent_relative
    (base : Finset (ReferenceCollectionPhaseHistory.Label p))
    (seen : List (ReferenceCollectionPhaseHistory.Label p))
    (event : Option (ReferenceCollectionPhaseHistory.Label p)) :
    ReferenceCollectionPhaseHistory.eraseEvent
        (base \ seen.toFinset) event =
      base \ (seen ++ event.toList).toFinset := by
  cases event with
  | none => simp [ReferenceCollectionPhaseHistory.eraseEvent]
  | some i =>
      ext x
      simp [ReferenceCollectionPhaseHistory.eraseEvent, Finset.mem_sdiff,
        Finset.mem_erase, and_left_comm]

private theorem cutoffChosen_false_of_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hstate : x.state.coordinator = .collection payload ledger saved) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  simp only [ReferenceActivePhysicalStep.prepare]
  change (match ReferenceActivePhysicalStep.dispatch x with
    | .live _ _ _ (.cutoffChosen ..) => true
    | _ => false) = false
  unfold ReferenceActivePhysicalStep.dispatch
  rw [hstate]
  by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · simp only [dite_eq_left hcut]
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    cases CoordinatorRoundDispatch.dispatch
        (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
    | collection outcome => rfl
  · simp [hcut]

private theorem actual_record_output_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hnext : r.output.next.coordinator = .collection payload ledger saved)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (hpost : r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger tail.started tail.weights) :
    tail.payload = payload := by
  have hnextConfig : r.output.coordinator.configuration =
      .collection payload ledger saved := by
    calc
      r.output.coordinator.configuration = (ReferenceActivePhysicalStep.step r.input).coordinator.configuration := by
        rw [r.output_eq]
      _ = (ReferenceActivePhysicalStep.step r.input).next.coordinator := rfl
      _ = r.output.next.coordinator := by rw [r.output_eq]
      _ = .collection payload ledger saved := hnext
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      r.output.coordinator.configuration = some payload := by
    rw [hnextConfig]
    rfl
  have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (x := r.input) (ReferenceActivePhysicalStep.prepare r.input)
    tail.payload tail.ledger tail.started tail.weights
  rw [hpost] at hstored
  rcases hframe with hnone | hsome
  · rw [hnone] at hstored
    cases hstored
  · exact Option.some.inj (hsome.symm.trans hstored)

private theorem actual_query_sender_word
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (out : ReferencePrelaunchFollower.State p rate.eta)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hreply : ReferenceFollowerReplyChronology.reply state =
      ReferenceFollowerReplyChronology.reply out)
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hUfields : U.val = ActiveFollowerQueueOperation.upOfferFields out)
    (hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state = .offer U ∧
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time state = .offer U ∧
    ReferenceActiveAffinePositiveTest.upSent record.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare record.input) =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  have hprep : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) :=
    record.output.preparation.followers.followers_eq i
  have haligned := record.output.preparation.follower_alignment i
  have hspec := ReferenceUpPhysicalHashRule.prepare_arm_spec i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)
  simp only [← hprep, hconfiguration] at hspec
  have hnotFailure : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      record.input.row (record.input.state.activations i) record.input.time state ≠ .failure := by
    intro hfailure
    simp only [hfailure] at hspec
  have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time ∧ state.status = .unoccupied :=
    ⟨⟨record.input.active i, hslot, hselected⟩, hunoccupied⟩
  have hdomain : ActiveFollowerQueueOperation.stateInputDomain state := by
    by_contra hbad
    apply hnotFailure
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hbad]
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    by_contra hbad
    apply hnotFailure
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselectedUp, hbad]
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state = .offer offered := by
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselectedUp, hadmissible, offered]
  have hoffFields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i
    record.input.row (record.input.state.activations i) record.input.time state offered hoff
  have hreplyParts : state.lastDown = out.lastDown ∧ state.S = out.S ∧
      state.delta = out.delta ∧ state.backlog = out.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply
  have hstartEq := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hfields : ActiveFollowerQueueOperation.upOfferFields state =
      ActiveFollowerQueueOperation.upOfferFields out := by
    apply OrdinaryMessageCodec.UpFields.ext
    · exact hstartEq
    · exact hreplyParts.2.1
    · exact hreplyParts.2.2.1
    · exact hreplyParts.2.2.2
  have hval : offered.val = U.val := by
    calc
      offered.val = ActiveFollowerQueueOperation.upOfferFields state := hoffFields
      _ = ActiveFollowerQueueOperation.upOfferFields out := hfields
      _ = U.val := hUfields.symm
  have hoffU : offered = U := Subtype.ext hval
  have hcheckedOriginal : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      record.input.row (record.input.state.activations i) record.input.time state = .offer U := by
    rw [hoffU] at hoff
    exact hoff
  have hcheckedPrepared : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time state = .offer U := by
    have hargs : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice record i).follower
        (ReferenceFollowerFixedReply.actualChoice record i).row
        (ReferenceFollowerFixedReply.actualChoice record i).activation
        (ReferenceFollowerFixedReply.actualChoice record i).time state =
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
            (record.input.state.activations i) record.input.time state := by
      dsimp only [ReferenceFollowerFixedReply.actualChoice]
      rw [haligned.2.1, haligned.1, haligned.2.2.2, haligned.2.2.1]
    rw [hargs]
    exact hcheckedOriginal
  have hselectedIndex : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hselected]
  have hExpectedFlat := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
    record i hselectedIndex state memory hconfiguration U hcheckedPrepared
  have hprepOutput : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcodec : CoordinatorCollectionLedger.codecParams p rate.eta.val =
      ReferencePrelaunchFollower.codecParams p rate.eta := rfl
  cases hcodec
  rw [ReferenceFollowerFixedReply.actualUpExpected, hprepOutput] at hExpectedFlat
  have hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := hExpectedFlat
  have hsent : ReferenceActiveAffinePositiveTest.upSent record.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    simpa only [ReferenceActiveAffinePositiveTest.upSent] using hexpected
  exact ⟨hcheckedOriginal, hcheckedPrepared, hsent, hexpected⟩

private theorem actual_offer_matches_seed
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (hchoice : (actualChoice r i).configuration = .ordinary choice memory)
    (hreply : ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply before)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hU : U.val = ActiveFollowerQueueOperation.upOfferFields before)
    (offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice r i).follower (actualChoice r i).row
      (actualChoice r i).activation (actualChoice r i).time choice = .offer offered) :
    offered = U ∧ ReferenceUpReception.currentOfferWord rate r.input.row i r.input.time
      (actualChoice r i) (actualChoice_alignment r i).1
      (actualChoice_alignment r i).2.1 (actualChoice_alignment r i).2.2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta
    (actualChoice r i).follower (actualChoice r i).row
    (actualChoice r i).activation (actualChoice r i).time choice offered hoff
  have hparts : choice.lastDown = before.lastDown ∧ choice.S = before.S ∧
      choice.delta = before.delta ∧ choice.backlog = before.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply
  have hsame : offered = U := by
    apply Subtype.ext
    rw [hfields, hU]
    apply OrdinaryMessageCodec.UpFields.ext
    · exact ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
    · exact hparts.2.1
    · exact hparts.2.2.1
    · exact hparts.2.2.2
  refine ⟨hsame, ?_⟩
  subst offered
  exact ReferenceUpReception.currentOfferWord_eq_encoded_offer rate r.input.row i
    r.input.time (actualChoice r i) (actualChoice_alignment r i).1
    (actualChoice_alignment r i).2.1 (actualChoice_alignment r i).2.2 choice memory hchoice U hoff

private theorem cutoff_selected_sender
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hfields : U.val = ActiveFollowerQueueOperation.upOfferFields before)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid before)
    (hbefore : r.input.state.followers i = .ordinary before memory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time before memory =
      .ok ({before with status := .unoccupied}, memory))
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i) :
    (actualChoice r i).configuration = .ordinary {before with status := .unoccupied} memory ∧
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time {before with status := .unoccupied} = .offer U ∧
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice r i).follower (actualChoice r i).row
      (actualChoice r i).activation (actualChoice r i).time
        {before with status := .unoccupied} = .offer U ∧
    ReferenceActiveAffinePositiveTest.upSent r.input = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  let choice := {before with status := ActiveRoundActions.FollowerStatus.unoccupied}
  have hdomain : ActiveFollowerQueueOperation.stateInputDomain choice :=
    stateInputDomain_of_localDomain before hvalid
  have hchoiceFields : ActiveFollowerQueueOperation.upOfferFields choice = U.val := hfields.symm
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields choice) := by
    rw [hchoiceFields]
    exact U.property
  have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
      (r.input.state.activations i) r.input.time ∧ choice.status = .unoccupied :=
    ⟨⟨r.input.active i, hslot, hselected⟩, rfl⟩
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time choice = .offer U := by
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dite_eq_left hdomain, dite_eq_left hselectedUp, dite_eq_left hadmissible]
    exact congrArg ActiveFollowerQueueOperation.UpOfferResult.offer (Subtype.ext hchoiceFields)
  have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
    choice (r.input.row.2 r.input.time) i U rfl hslot hselected
    ⟨⟨hdomain.1, hdomain.2.1, hdomain.2.2.1⟩,
      congrArg OrdinaryMessageCodec.UpFields.sigma hfields,
      congrArg OrdinaryMessageCodec.UpFields.S hfields,
      congrArg OrdinaryMessageCodec.UpFields.delta hfields,
      congrArg OrdinaryMessageCodec.UpFields.q hfields⟩
  obtain ⟨arm, harm⟩ : ∃ arm, ActiveFollowerArmChoice.followerArmChoice choice
      r.input.row r.input.time i (some U) = some arm := by
    let arm := ActiveRoundActions.sendArm
      (ActiveFollowerArmChoice.offeredUpBit rate.eta (r.input.row.2 r.input.time) i U)
      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
        (ActiveRoundActions.coordinator p.two_le_m))
    refine ⟨arm, ?_⟩
    rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
    exact hcore
  have hprepare := DeclaredFollowerLocalRound.prepare_offer_arm_equation rate i
    r.input.row (r.input.state.activations i) r.input.time (r.input.active i)
    before choice memory memory hstart U hoff
  have hconfig : (actualChoice r i).configuration = .ordinary choice memory := by
    rw [show actualChoice r i = DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (r.input.state.followers i) from r.output.preparation.followers.followers_eq i,
      hbefore]
    exact (hprepare.2 arm harm).2
  exact ⟨hconfig, actual_query_sender_word r i choice memory choice hconfig rfl rfl U
    hfields hslot hselected⟩

private theorem receiver_start_fields
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (recording : CoordinatorRecordingOperation.Output p)
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (seen : List (ReferenceCollectionPhaseHistory.Label p)) (s : ℕ)
    (hpending : tail.ledger.pending = Finset.univ \ seen.toFinset)
    (hsigma : tail.ledger.sigma = s + 1)
    (hstart : CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L)
    (hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true) :
    L.pending = Finset.univ \ seen.toFinset ∧ L.sigma = s + 1 ∧
    L.cutoff ≤ L.cursor ∧ L.cursor = r.input.time.val + 1 := by
  have hcandidate := ReferenceActivePhysicalStep.collection_started_candidate
    tail.ledger L r.input.time
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff _).mp hcheck
  obtain ⟨_, _, _, _, hcutoff, _, hcursor, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts _ hdomain
  refine ⟨?_, ?_, hcutoff, ?_⟩
  · rw [hcandidate]
    exact hpending
  · rw [hcandidate]
    exact hsigma
  · exact hcursor

private theorem receiver_of_origin
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (s : ℕ) (hsigma : P0.sigma.val = s)
    (seen : List (ReferenceCollectionPhaseHistory.Label p))
    (hpre : (ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧ seen = []) ∨
      r.input.state.coordinator = .dagger ∨
      ∃ pre preSaved, r.input.state.coordinator = .collection P0 pre preSaved ∧
        pre.sigma = s + 1 ∧ pre.pending = Finset.univ \ seen.toFinset)
    (hpost : r.output.next.coordinator = .dagger ∨
      ∃ next saved, r.output.next.coordinator = .collection P0 next saved)
    (hordinary : r.output.next.coordinator ≠ .dagger)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1)) (hU : U.val.sigma = s + 1) :
    ∃ (tail : ReferenceCollectionPhaseHistory.Tail r.input)
      (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (finished : ReferenceActivePhysicalStep.Ledger rate)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      tail.ledger.pending = Finset.univ \ seen.toFinset ∧
      tail.ledger.sigma = s + 1 ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
        some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      r.output.coordinator.up = some d ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
      ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result =
            .success (receivedLedger, bank) ∨
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result =
            .rejected (receivedLedger, bank)) ∧
      CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time tail.started.clock
        finished.pending r.input.row = .ok clockFinished ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.rawMatches = decide (d.raw = d.expected) ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      d.input.affineSample =
        ((r.input.rows r.input.selected).2 r.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time)) ∧
      d.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input))
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl ∧
      L.pending = Finset.univ \ seen.toFinset ∧ L.sigma = s + 1 ∧
      L.cutoff ≤ L.cursor ∧ L.cursor = r.input.time.val + 1 ∧
      (ReferenceCollectionPhaseHistory.cutoffChosen r.input = true →
        r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger tail.started tail.weights ∧
        tail.ledger.pending = Finset.univ ∧ tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
        tail.ledger.cutoff = r.input.time.val + 1 ∧ tail.ledger.cursor = r.input.time.val + 1 ∧
        tail.ledger.phase = .ready ∧ tail.started.pending = Finset.univ ∧
        L.pending = Finset.univ ∧ L.sigma = tail.payload.sigma.val + 1 ∧
        L.cutoff = r.input.time.val + 1) ∧
    ∀ (_hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
      (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i),
      (i ∉ seen.toFinset →
        d.input.selectedFollower = i ∧ CoordinatorUpReception.receptionGate d.input ∧
        (CoordinatorUpReception.roundInput d.input).selected = true ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
        (d.input.ownObservation.val = 0 →
          d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none)) ∧
      (i ∈ seen.toFinset →
        d.input.selectedFollower = i ∧ ¬ CoordinatorUpReception.receptionGate d.input ∧
        (CoordinatorUpReception.roundInput d.input).selected = false ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none) := by
  obtain ⟨next, saved, hnext⟩ := hpost.resolve_left hordinary
  have horigin : (ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧ seen = []) ∨
      ∃ pre preSaved, r.input.state.coordinator = .collection P0 pre preSaved ∧
        pre.pending = Finset.univ \ seen.toFinset ∧ pre.sigma = s + 1 := by
    rcases hpre with hcut | hdagger | ⟨pre, preSaved, hstate, hsig, hpend⟩
    · exact Or.inl hcut
    · apply False.elim
      apply hordinary
      rw [r.output_eq]
      exact (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hdagger).1
    · exact Or.inr ⟨pre, preSaved, hstate, hpend, hsig⟩
  rcases horigin with ⟨hcut, hseen⟩ | ⟨pre, preSaved, hstate, hprePending, hpreSigma⟩
  · obtain ⟨tail, recording, L, d, received, bank, finished, clock,
      htail, hpost, hsite, htailPending, htailSigma, htailCutoff, htailCursor,
      htailPhase, hstartedPending, hrecording, hstart, hLpending, hLsigma,
      hLcutoff, _, hcheck, hinput, houtput,
      hreception, hnoninvalid, hresult, hfinish, hclock, hdecoder, hraw,
      hparsed, hlocal, hexpected, hmatches, hbank, htime, hsample,
      hobservation, hwrong⟩ :=
        ReferenceCutoffUpReceiverLocal.actual_ordinary_cutoff_up_receiver r hcut hordinary
    have hpayload := actual_record_output_payload r P0 next saved hnext tail hpost
    have hpending : tail.ledger.pending = Finset.univ \ seen.toFinset := by
      simpa only [hseen, List.toFinset_nil, Finset.sdiff_empty] using htailPending
    have hsig : tail.ledger.sigma = s + 1 := by rw [htailSigma, hpayload, hsigma]
    have hfields := receiver_start_fields r tail recording L seen s hpending hsig hstart hcheck
    exact ⟨tail, recording, L, d, received, bank, finished, clock,
      htail, hpending, hsig, hsite, hrecording, hstart, hcheck, hinput, houtput,
      hreception, hnoninvalid, hresult, hfinish, hclock, hdecoder, hraw,
      hparsed, hlocal, hexpected, hmatches, hbank, htime, hsample,
      hobservation, hwrong, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2,
      (fun _ => ⟨hpost, htailPending, htailSigma, htailCutoff, htailCursor,
        htailPhase, hstartedPending, hLpending, hLsigma, hLcutoff⟩),
      receiver_awaited_gates r L d seen U i s hcheck hinput hfields.1 hfields.2.1 hU hdecoder hraw⟩
  · obtain ⟨tail, htail, _, _⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
      r.input P0 next saved (by rw [← r.output_eq]; exact hnext)
    have hcut := cutoffChosen_false_of_collection r.input P0 pre preSaved hstate
    obtain ⟨_, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin htail
    have hledger : tail.ledger = pre := by
      rcases horigin with ⟨hbad, _⟩ | ⟨_, op, ol, os, hsource, heq⟩
      · rw [hcut] at hbad
        cases hbad
      · rw [hstate] at hsource
        cases hsource
        exact heq
    obtain ⟨recording, L, d, hrecording, hstart, hsite, hcheck, houtput,
      hinput, hreception, hnoninvalid, received, bank, finished, clock,
      hresult, hfinish, hclock, hdecoder, hraw, hparsed, hlocal, hexpected,
      hmatches, hbank, htime, hsample, hobservation, hwrong⟩ :=
        ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver
          r P0 pre preSaved tail hstate htail hordinary
    have hpending : tail.ledger.pending = Finset.univ \ seen.toFinset := hledger ▸ hprePending
    have hsig : tail.ledger.sigma = s + 1 := hledger ▸ hpreSigma
    have hfields := receiver_start_fields r tail recording L seen s hpending hsig hstart hcheck
    exact ⟨tail, recording, L, d, received, bank, finished, clock,
      htail, hpending, hsig, hsite, hrecording, hstart, hcheck, hinput, houtput,
      hreception, hnoninvalid, hresult, hfinish, hclock, hdecoder, hraw,
      hparsed, hlocal, hexpected, hmatches, hbank, htime, hsample,
      hobservation, hwrong, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2,
      (by intro hflag; rw [hcut] at hflag; cases hflag),
      receiver_awaited_gates r L d seen U i s hcheck hinput hfields.1 hfields.2.1 hU hdecoder hraw⟩

private theorem collection_bounds
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w count : ℕ) (hrecords : records.length = count) (hshort : w < count) :
    w + 1 + ((records.drop (w + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length ≤ count ∧
    w + (ReferenceCollectionPhaseHistory.collectionWindow records w).length ≤ count := by
  have htail : ((records.drop (w + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length ≤
        (records.drop (w + 1)).length := (List.takeWhile_prefix _).length_le
  rw [List.length_drop, hrecords] at htail
  have hfirst : ((records.drop w).take 1).length ≤ 1 := List.length_take_le _ _
  constructor
  · omega
  · have hlen : (ReferenceCollectionPhaseHistory.collectionWindow records w).length ≤
        1 + (count - (w + 1)) := by
      unfold ReferenceCollectionPhaseHistory.collectionWindow
      rw [List.length_append]
      exact Nat.add_le_add hfirst htail
    omega

private theorem collection_cutoff_pending
    (I : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s w count : ℕ) (hspan : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart I s)
    (B Wearly : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hBsplit : B = cut :: Wearly) (hbound : w + B.length ≤ count)
    (hwindow : ∀ n : Fin B.length,
      (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records[
        w + n.val]? = some B[n.val])
    (P0 : ReferenceActivePhysicalStep.Payload rate) (hsigma : P0.sigma.val = s)
    (l0 : ReferenceActivePhysicalStep.Ledger rate) (saved0 : Option (Fin p.T × Bool))
    (hcollection : cut.output.next.coordinator = .collection P0 l0 saved0)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true) :
    let C := fun (k : ℕ) (hk : k ≤ Wearly.length) =>
      ReferenceActivePhysicalHorizon.run I rows J rewards s (w + 1 + k) (by
        have hlen := congrArg List.length hBsplit
        simp only [List.length_cons] at hlen
        omega) active
    let D := fun (n : ℕ) (hn : n ≤ B.length) =>
      ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) (by omega) active
    ∀ (_hprefix : ∀ k (hk : k ≤ Wearly.length),
      (C k hk).finalState.coordinator = .dagger ∨
        ∃ moving saved, (C k hk).finalState.coordinator = .collection P0 moving saved),
    (∀ n : Fin B.length,
      (D n.val (Nat.le_of_lt n.isLt)).finalState = B[n.val].input.state ∧
      (D (n.val + 1) n.isLt).finalState = B[n.val].output.next) ∧
    l0.sigma = s + 1 ∧
    l0.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take 1)).toFinset ∧
    (∀ n (hn : n ≤ B.length), 1 ≤ n →
      (D n hn).finalState.coordinator = .dagger ∨
        ∃ moving saved, (D n hn).finalState.coordinator = .collection P0 moving saved ∧
          moving.sigma = s + 1 ∧ moving.pending = Finset.univ \
            (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset) := by
  intro C D hprefix
  let b := w + 1
  have hBlen : B.length = Wearly.length + 1 := by rw [hBsplit]; simp
  have hBzero : B[0]'(by omega) = cut := by simp only [hBsplit, List.getElem_cons_zero]
  have hends : ∀ n : Fin B.length,
      (D n.val (Nat.le_of_lt n.isLt)).finalState = B[n.val].input.state ∧
      (D (n.val + 1) n.isLt).finalState = B[n.val].output.next := by
    intro n
    have hlookup := hwindow n
    obtain ⟨hidx, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
    have hidxCount : w + n.val < count := by
      simpa only [ReferenceActivePhysicalHorizon.run_record_count] using hidx
    have hboundaries := run_prefix_endpoints I rows J rewards s count hspan active
      (w + n.val) hidxCount
    change (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records[
      w + n.val]'(by simpa only [ReferenceActivePhysicalHorizon.run_record_count] using hidxCount) =
        B[n.val] at heq
    constructor
    · exact hboundaries.1.trans (congrArg (fun record => record.input.state) heq)
    · have hout := hboundaries.2.trans (congrArg (fun record => record.output.next) heq)
      simpa only [D, Nat.add_assoc] using hout
  obtain ⟨cutTail, hcutTail, hcutPost, _, hcutPending, hcutSigma, _, _, _, _⟩ :=
    ReferenceCutoffUpReceiverLocal.actual_cutoff_up_receiver cut hcutoff
  have hcutPayload := actual_record_output_payload cut P0 l0 saved0
    hcollection cutTail hcutPost
  obtain ⟨frameTail, hframeTail, hframePending, hframeSigma⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame cut.input P0 l0 saved0
      (by rw [← cut.output_eq]; exact hcollection)
  have hframeEq : frameTail = cutTail := Option.some.inj (hframeTail.symm.trans hcutTail)
  have hl0Sigma : l0.sigma = s + 1 := by
    rw [hframeSigma, hframeEq, hcutSigma, hcutPayload, hsigma]
  have hlabelsOne : ReferenceCollectionPhaseHistory.acceptedLabels (B.take 1) =
      (ReferenceCollectionPhaseHistory.acceptedLabel cut.input).toList := by
    simp only [hBsplit, List.take_succ_cons, List.take_zero,
      ReferenceCollectionPhaseHistory.acceptedLabels, List.filterMap_cons, List.filterMap_nil]
    cases ReferenceCollectionPhaseHistory.acceptedLabel cut.input <;> rfl
  have hl0Pending : l0.pending = Finset.univ \
      (ReferenceCollectionPhaseHistory.acceptedLabels (B.take 1)).toFinset := by
    rw [hframePending, hframeEq, hcutPending, hlabelsOne]
    simpa using eraseEvent_relative (Finset.univ : Finset (ReferenceCollectionPhaseHistory.Label p))
      [] (ReferenceCollectionPhaseHistory.acceptedLabel cut.input)
  have hshape : ∀ n (hn : n ≤ B.length), 1 ≤ n →
      (D n hn).finalState.coordinator = .dagger ∨
        ∃ moving saved, (D n hn).finalState.coordinator = .collection P0 moving saved := by
    intro n hn hpos
    have hk : n - 1 ≤ Wearly.length := by omega
    have hCD : C (n - 1) hk = D n hn := by
      dsimp only [C, D]
      congr 1
      omega
    have hcurrent := hprefix (n - 1) hk
    rw [hCD] at hcurrent
    exact hcurrent
  have hbase : (D 1 (by omega)).finalState.coordinator = .collection P0 l0 saved0 := by
    have hend := (hends ⟨0, by omega⟩).2
    rw [hBzero] at hend
    exact (congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
      state.coordinator) hend).trans hcollection
  refine ⟨hends, hl0Sigma, hl0Pending, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hpos
    rcases hshape n hn hpos with hdagger | ⟨moving, saved, hcurrent⟩
    · exact Or.inl hdagger
    · right
      refine ⟨moving, saved, hcurrent, ?_⟩
      by_cases hfirst : n = 1
      · subst n
        have hledger := (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
          (hcurrent.symm.trans hbase)).2.1
        simpa only [hledger] using And.intro hl0Sigma hl0Pending
      · let k := n - 1
        have hk : k < B.length := by dsimp [k]; omega
        have hnEq : k + 1 = n := by dsimp [k]; omega
        have hend := hends ⟨k, hk⟩
        let r := B[k]
        have hnext : r.output.next.coordinator = .collection P0 moving saved := by
          have heq := congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
            state.coordinator) hend.2.symm
          have hcurrent' : (D (k + 1) (by omega)).finalState.coordinator =
              .collection P0 moving saved := by simpa only [hnEq] using hcurrent
          exact heq.trans hcurrent'
        rcases ih k (by dsimp [k]; omega) (by omega) (by dsimp [k]; omega) with
          hdagger | ⟨pre, preSaved, hpre, hpreSigma, hprePending⟩
        · have hinput : r.input.state.coordinator = .dagger :=
            (congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
              state.coordinator) hend.1.symm).trans hdagger
          have hbad : r.output.next.coordinator = .dagger := by
            rw [r.output_eq]
            exact (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hinput).1
          rw [hnext] at hbad
          cases hbad
        · have hinput : r.input.state.coordinator = .collection P0 pre preSaved :=
            (congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
              state.coordinator) hend.1.symm).trans hpre
          obtain ⟨tail, htail, hpending, hsig⟩ :=
            ReferenceCollectionPhaseHistory.step_collection_frame r.input P0 moving saved
              (by rw [← r.output_eq]; exact hnext)
          have hcutFalse := cutoffChosen_false_of_collection r.input P0 pre preSaved hinput
          obtain ⟨_, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin htail
          have hledger : tail.ledger = pre := by
            rcases horigin with ⟨hbad, _⟩ | ⟨_, op, ol, os, hsource, heq⟩
            · rw [hcutFalse] at hbad
              cases hbad
            · rw [hinput] at hsource
              cases hsource
              exact heq
          constructor
          · exact hsig.trans (congrArg (fun L => L.sigma) hledger |>.trans hpreSigma)
          · rw [hpending, hledger, hprePending, eraseEvent_relative,
              ← acceptedLabels_take_succ B k hk, hnEq]


/-- An actual early retained-DOWN query produces one typed reply before all
collection-round queries. The original cutoff, seed, boundaries and failures
are retained. Ordinary coordinator queries produce their actual receiver,
with relative erasure counting every successful received follower label.
This is an internal operational join; service and decoding probability remain
separate obligations. -/
theorem actual_first_collection_early_up_sender_receiver
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
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    let b := w + 1
    let Wearly := (Erun.records.drop b).takeWhile
      fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let C := fun (k : ℕ) (hk : k ≤ Wearly.length) =>
      ReferenceActivePhysicalHorizon.run I rows J rewards s (b + k) (by
        have hlen : Erun.records.length = count :=
          ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s count hspan active
        have hbound := (collection_bounds Erun.records w count hlen hshort).1
        change b + Wearly.length ≤ count at hbound
        have hspan' : s + count ≤ p.T := hspan
        omega) active
    let D := fun (n : ℕ) (hn : n ≤ B.length) =>
      ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) (by
        have hlen : Erun.records.length = count :=
          ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s count hspan active
        have hbound := (collection_bounds Erun.records w count hlen hshort).2
        change w + B.length ≤ count at hbound
        have hspan' : s + count ≤ p.T := hspan
        omega) active
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      Erun.records = W ++ cut :: suffix ∧
      ReferenceActivePhysicalHorizon.Connected I W cut.input.state ∧
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) ∧
      cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      Erun.records.length = count ∧ b ≤ count ∧
      B = cut :: Wearly ∧
      w + B.length = b + Wearly.length ∧
      b + Wearly.length ≤ count ∧
      s + b + Wearly.length ≤ p.T ∧
      (s + b + Wearly.length = p.T →
        ∀ time : Fin p.T, time.val < s + b + Wearly.length) ∧
      (∀ k : Fin Wearly.length,
        Erun.records[b + k.val]? = some Wearly[k.val] ∧
          Wearly[k.val].input.time.val = u + k.val) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (let callInput := ReferenceActivePhysicalStep.liveInput cut.input registers owned base
       ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          callInput.registers callInput.ownedRegisters base),
        ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val callInput.registers.time
          callInput.registers.priorClock callInput.registers.clockPending = .ok dispatched.startResult),
        ∃ (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers),
        ∃ (hinit : dispatched.collectionInitialization = .success (some ledger)),
        ∃ (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hclock : dispatched.startResult.clock =
          { callInput.registers.priorClock with u := some callInput.registers.time }),
        ∃ (hpending : dispatched.startResult.pending = Finset.univ),
        ∃ (hnoAssignment : dispatched.startResult.assignmentStart = none),
        ∃ (selected : CoordinatorRoundDispatch.ArmSelection
          callInput.registers.payload dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights callInput.row),
        cut.output.preparation.coordinator = .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
        cut.output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation registers.payload
            (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
            callInput.registers.complementWeights) ∧
      (cut.output.next.coordinator = .dagger ∨
        ∃ nextLedger saved, cut.output.next.coordinator = .collection P0 nextLedger saved) ∧
      (∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (token : ActiveFollowerLifecycle.ProposalRead p)
          (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
          cut.input.state.followers i = .ordinary before memory ∧
          before.lastDown = some M ∧ M = P0.downRecord i ∧
          before.status ≠ .unoccupied ∧
          ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
          M.val.sigma = s + 1 ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp ∧
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
            .ok ({before with status := .unoccupied}, memory) ∧
          ((actualChoice cut i).configuration = .dagger ∨
            (actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ∀ arrival,
              ActiveFollowerQueueOperation.serviceOutput rate.n
                {before with status := .unoccupied} arrival =
                  {before with status := .unoccupied}) ∧
          U.val = OrdinaryMessageCodec.UpFields.mk (s + 1) before.S before.delta before.backlog ∧
          0 < U.val.sigma ∧
          (∀ (_hslot : PublicDiscreteDraws.slotDraw
              (cut.input.row.2 cut.input.time).1 = PublicDiscreteDraws.upSlot)
            (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1 = i),
            (actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i cut.input.row
              (cut.input.state.activations i) cut.input.time
                {before with status := .unoccupied} = .offer U ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              (actualChoice cut i).follower (actualChoice cut i).row
              (actualChoice cut i).activation (actualChoice cut i).time
                {before with status := .unoccupied} = .offer U ∧
            ReferenceActiveAffinePositiveTest.upSent cut.input =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare cut.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
          (cut.output.next.followers i = .dagger ∨
            ∃ out outMemory,
              cut.output.next.followers i = .ordinary out outMemory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply before ∧
              out.lastDown = some M ∧
              ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
          (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) ∧
          (cut.output.next.coordinator = .dagger ∨
            ∃ nextLedger saved,
              cut.output.next.coordinator = .collection P0 nextLedger saved ∧
              (cut.output.next.followers i = .dagger ∨
                ∃ out outMemory,
                  cut.output.next.followers i = .ordinary out outMemory ∧
                  out.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply out =
                    ReferenceFollowerReplyChronology.reply before ∧
                  out.lastDown = some M ∧
                  ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1 ∧
                  ((∃ _hfinal : (C 0 (by omega)).finalState = cut.output.next,
                    ∃ _hcoord : (C 0 (by omega)).finalState.coordinator =
                      .collection P0 nextLedger saved,
                      ∃ _hseed : (C 0 (by omega)).finalState.followers i =
                        .ordinary out outMemory,
                        ∃ _hseedStart : ReferencePrelaunchFollower.acceptedStart out =
                          P0.sigma.val + 1,
                          (∀ (k : ℕ) (hk : k ≤ Wearly.length),
                            ((C k hk).finalState.coordinator = .dagger ∨
                              ∃ movingLedger movingSaved,
                                (C k hk).finalState.coordinator =
                                  .collection P0 movingLedger movingSaved) ∧
                            ((C k hk).finalState.followers i = .dagger ∨
                              ∃ state stateMemory,
                                (C k hk).finalState.followers i =
                                  .ordinary state stateMemory ∧
                                state.status = .unoccupied ∧
                                ReferenceFollowerReplyChronology.reply state =
                                  ReferenceFollowerReplyChronology.reply before ∧
                                  state.lastDown = some M))) ∧
                          (∀ (k : ℕ), k < Wearly.length →
                            ∀ hrecord : b + k < Erun.records.length, ∀ sigma,
                              ¬ ReferenceFollowerReplyChronology.appliedDown
                                (Erun.records.get ⟨b + k, hrecord⟩) i sigma) ∧
                          (∀ (k : ℕ) (_hk : k ≤ Wearly.length)
                            (hrecord : b + k < Erun.records.length),
                            (Erun.records.get ⟨b + k, hrecord⟩).input.time.val = s + b + k ∧
                            (k = Wearly.length →
                              ReferenceCollectionPhaseHistory.laterChosen
                                (Erun.records.get ⟨b + k, hrecord⟩).input = true) ∧
                            ((actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                                .dagger ∨
                              ∃ state stateMemory,
                                (actualChoice (Erun.records.get ⟨b + k, hrecord⟩) i).configuration =
                                  .ordinary state stateMemory ∧
                                state.status = .unoccupied ∧
                                ReferenceFollowerReplyChronology.reply state =
                                  ReferenceFollowerReplyChronology.reply before ∧
                                  state.lastDown = some M)) ∧
                          ((b + Wearly.length = count ∧
                              Erun.records[b + Wearly.length]? = none) ∨
                            ∃ endpoint,
                              Erun.records[b + Wearly.length]? = some endpoint ∧
                              endpoint.input.time.val = s + b + Wearly.length ∧
                              ReferenceCollectionPhaseHistory.laterChosen endpoint.input = true) ) ∧
                  nextLedger.sigma = s + 1 ∧
                  nextLedger.pending = Finset.univ \
                    (ReferenceCollectionPhaseHistory.acceptedLabels (B.take 1)).toFinset ∧
                  (∀ n (hn : n ≤ B.length), 1 ≤ n →
                    (D n hn).finalState.coordinator = .dagger ∨
                      ∃ moving movingSaved,
                        (D n hn).finalState.coordinator = .collection P0 moving movingSaved ∧
                        moving.sigma = s + 1 ∧ moving.pending = Finset.univ \
                          (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset) ∧
                  (∀ n : Fin B.length,
                    let r := B[n.val]
                    ((actualChoice r i).configuration = .dagger ∨
                      ∃ choice choiceMemory,
                        (actualChoice r i).configuration = .ordinary choice choiceMemory ∧
                        choice.status = .unoccupied ∧
                        ReferenceFollowerReplyChronology.reply choice =
                          ReferenceFollowerReplyChronology.reply before ∧
                        (∀ offered : OrdinaryMessageCodec.UpRecord
                            (ReferencePrelaunchFollower.codecParams p rate.eta),
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                            (actualChoice r i).follower (actualChoice r i).row
                            (actualChoice r i).activation (actualChoice r i).time choice = .offer offered →
                          offered = U ∧ ReferenceUpReception.currentOfferWord rate r.input.row i r.input.time
                            (actualChoice r i) (actualChoice_alignment r i).1
                            (actualChoice_alignment r i).2.1 (actualChoice_alignment r i).2.2 =
                              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                        ∀ (_hslot : PublicDiscreteDraws.slotDraw
                            (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
                          (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                            (r.input.row.2 r.input.time).1 = i),
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                            (r.input.state.activations i) r.input.time choice = .offer U ∧
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                            (actualChoice r i).follower (actualChoice r i).row
                            (actualChoice r i).activation (actualChoice r i).time choice = .offer U ∧
                          ReferenceActiveAffinePositiveTest.upSent r.input =
                            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
                            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                    (r.output.next.coordinator ≠ .dagger →
                      ∃ (tail : ReferenceCollectionPhaseHistory.Tail r.input)
                        (recording : CoordinatorRecordingOperation.Output p)
                        (L : ReferenceActivePhysicalStep.Ledger rate)
                        (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                        (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
                        (bank : CoordinatorUpReception.UpDecoderBank p)
                        (finished : ReferenceActivePhysicalStep.Ledger rate)
                        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                        tail.ledger.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)).toFinset ∧
                        tail.ledger.sigma = s + 1 ∧
                        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                        CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
                          some recording ∧
                        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
                          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
                        CoordinatorUpReception.receptionInputCheck
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
                        d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                        r.output.coordinator.up = some d ∧
                        tail.reception = some (L,
                          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                        ((ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L).result =
                              .success (receivedLedger, bank) ∨
                          (ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L).result =
                              .rejected (receivedLedger, bank)) ∧
                        CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
                        CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time tail.started.clock
                          finished.pending r.input.row = .ok clockFinished ∧
                        d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
                        d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
                        d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
                        d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
                        d.expected = ReferenceActivePhysicalStep.upExpected
                          (ReferenceActivePhysicalStep.prepare r.input) ∧
                        d.rawMatches = decide (d.raw = d.expected) ∧
                        d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                        d.input.time = r.input.time ∧
                        d.input.affineSample =
                          ((r.input.rows r.input.selected).2 r.input.time).2
                            (1, CoordinatorUpMeasurability.selectedChannelFollower
                              ((r.input.rows r.input.selected).2 r.input.time)) ∧
                        d.input.ownObservation =
                          (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                            (ActiveRoundActions.coordinator p.two_le_m) ∧
                        d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                          rate r.input.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
                          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
                            (ReferenceActivePhysicalStep.upSenderIndex r.input))
                          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
                          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
                          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl ∧
                        L.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)).toFinset ∧ L.sigma = s + 1 ∧
                        L.cutoff ≤ L.cursor ∧ L.cursor = r.input.time.val + 1 ∧
                        (ReferenceCollectionPhaseHistory.cutoffChosen r.input = true →
                          r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
                            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger tail.started tail.weights ∧
                          tail.ledger.pending = Finset.univ ∧ tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
                          tail.ledger.cutoff = r.input.time.val + 1 ∧ tail.ledger.cursor = r.input.time.val + 1 ∧
                          tail.ledger.phase = .ready ∧ tail.started.pending = Finset.univ ∧
                          L.pending = Finset.univ ∧ L.sigma = tail.payload.sigma.val + 1 ∧
                          L.cutoff = r.input.time.val + 1) ∧
                        (∀ (_hslot : PublicDiscreteDraws.slotDraw
                            (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
                          (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                            (r.input.row.2 r.input.time).1 = i),
                          (i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)).toFinset →
                            d.input.selectedFollower = i ∧ CoordinatorUpReception.receptionGate d.input ∧
                            (CoordinatorUpReception.roundInput d.input).selected = true ∧
                            (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                            CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                            (d.input.ownObservation.val = 0 →
                              d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none)) ∧
                          (i ∈ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)).toFinset →
                            d.input.selectedFollower = i ∧ ¬ CoordinatorUpReception.receptionGate d.input ∧
                            (CoordinatorUpReception.roundInput d.input).selected = false ∧
                            (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                            d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none))) ∧
                                      ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace Erun.records i r.input.time =
                                        ReferenceCoordinatorUpIntervalWindow.recordFocalInput r i)))) := by
  classical
  intro x0 b0 s I Erun W w B u b Wearly rows J active C D
  have hE := ReferenceFirstCollectionEarlyDownReplyHistory.actual_first_collection_early_down_reply_history
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hE with ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecords, hb, hBsplit, hwindowEnd, hWearlyBound,
    hphysicalEnd, hterminal, hEarly, hwindow, hdispatch, hcoordNext, hqueries⟩
  change B = cut :: Wearly at hBsplit
  change Erun.records.length = count at hrecords
  change ∀ n : Fin B.length, Erun.records[w + n.val]? = some B[n.val] ∧
    B[n.val].input.time.val + 1 = u + n.val at hwindow
  have hchron : Erun.records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) :=
    run_records_chronological I rows J rewards s count hspan active
  have htrace (i : Fin (p.m - 1)) (n : Fin B.length) :
      ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace Erun.records i B[n.val].input.time =
        ReferenceCoordinatorUpIntervalWindow.recordFocalInput B[n.val] i :=
    ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record Erun.records i hchron B[n.val]
      (List.mem_of_getElem? (hwindow n).1)
  refine ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecords, hb, hBsplit, hwindowEnd, hWearlyBound,
    hphysicalEnd, hterminal, hEarly, hwindow, hdispatch, hcoordNext, ?_⟩
  intro i j M hj hretained
  obtain ⟨before, memory, token, hbefore, hlast, hMpayload, hoccupied,
    hstart, hMstart, hdomain, htoken, htokenTime, htokenBit,
    hstartRound, hcutChoice, hcutFollower, hcutNoDown, hcutCollection⟩ :=
      hqueries i j M hj hretained
  obtain ⟨U, hUfields, hUpositive⟩ := seed_up_record before M s hdomain hMstart
  have hUoffer : U.val = ActiveFollowerQueueOperation.upOfferFields before := by
    rw [hUfields]
    apply OrdinaryMessageCodec.UpFields.ext
    · exact hstart.symm
    · rfl
    · rfl
    · rfl
  refine ⟨before, memory, token, U, hbefore, hlast, hMpayload, hoccupied,
    hstart, hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound,
    hcutChoice, hUfields, hUpositive, ?_, hcutFollower, hcutNoDown, ?_⟩
  · intro hslot hselected
    exact cutoff_selected_sender cut i before memory U hUoffer hdomain hbefore
      hstartRound hslot hselected
  · rcases hcutCollection with hdagger | ⟨l0, saved0, hcollection, hfollower⟩
    · exact Or.inl hdagger
    · right
      refine ⟨l0, saved0, hcollection, ?_⟩
      rcases hfollower with hdagger | ⟨out, outMemory, hout, hstatus, hreply,
        hlastOut, hstartOut, hprefix⟩
      · exact Or.inl hdagger
      · right
        obtain ⟨hprefixStart, hnoDown, htimeChoices, hendpoint, hoffers, hconsistent⟩ := hprefix
        refine ⟨out, outMemory, hout, hstatus, hreply, hlastOut, hstartOut,
          ⟨hprefixStart, hnoDown, htimeChoices, hendpoint⟩, ?_⟩
        obtain ⟨hfinal, hcoord, hseed, hseedStart, hprefixFacts⟩ := hprefixStart
        have hbound : w + B.length ≤ count := hwindowEnd.le.trans hWearlyBound
        obtain ⟨hends, hl0Sigma, hl0Pending, hmovement⟩ :=
          collection_cutoff_pending I rows J rewards s w count hspan active B Wearly cut
            hBsplit hbound (fun n => (hwindow n).1) P0 hsigma l0 saved0 hcollection hcutoff
            (fun k hk => (hprefixFacts k hk).1)
        refine ⟨hl0Sigma, hl0Pending, hmovement, ?_⟩
        intro n r
        refine ⟨?_, ?_, ?_⟩
        · rcases hoffers n with hdagger | ⟨choice, choiceMemory, hchoice, hstatus, hreply, _⟩
          · exact Or.inl hdagger
          · right
            refine ⟨choice, choiceMemory, hchoice, hstatus, hreply, ?_,
              fun hslot hselected => actual_query_sender_word r i choice choiceMemory before
                hchoice hstatus hreply U hUoffer hslot hselected⟩
            intro offered hoff
            exact actual_offer_matches_seed r i choice choiceMemory before hchoice hreply U hUoffer offered hoff
        · intro hordinary
          have hend := hends n
          have hpost : r.output.next.coordinator = .dagger ∨
              ∃ next saved, r.output.next.coordinator = .collection P0 next saved := by
            have hnext := hmovement (n.val + 1) n.isLt (by omega)
            rw [hend.2] at hnext
            rcases hnext with hdagger | ⟨next, saved, hnext, _, _⟩
            · exact Or.inl hdagger
            · exact Or.inr ⟨next, saved, hnext⟩
          have hpre :
              (ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
                ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val) = []) ∨
              r.input.state.coordinator = .dagger ∨
              ∃ pre preSaved, r.input.state.coordinator = .collection P0 pre preSaved ∧
                pre.sigma = s + 1 ∧ pre.pending = Finset.univ \
                  (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)).toFinset := by
            by_cases hzero : n.val = 0
            · have hr : r = cut := by
                dsimp only [r]
                simp only [hzero, hBsplit, List.getElem_cons_zero]
              exact Or.inl ⟨by rw [hr]; exact hcutoff, by simp only [hzero, List.take_zero,
                ReferenceCollectionPhaseHistory.acceptedLabels, List.filterMap_nil]⟩
            · have hcurrent := hmovement n.val (Nat.le_of_lt n.isLt) (by omega)
              rw [hend.1] at hcurrent
              exact Or.inr hcurrent
          exact receiver_of_origin r P0 s hsigma
            (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n.val)) hpre hpost hordinary U i
            (by rw [hUfields])
        · exact htrace i n

end Bandits.Support.ReferenceFirstCollectionEarlyUpSenderReceiver

end
