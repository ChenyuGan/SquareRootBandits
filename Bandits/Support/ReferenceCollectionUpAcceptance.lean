/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionUpPendingInterval
public import Bandits.Support.ReferenceCollectionUpReceiverLocal
public import Bandits.Support.ReferenceFixedUpCompletedWindowTruth

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Range

/-!
# Actual collection UP queries and second-window acceptance

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-88,105-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,164-177,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module composes the actual pending-set trajectory, a same-record local
receiver call, and the computed second positive window. It keeps the local
ordinary-choice and acceptance conditions explicit and retains the final
follower's computed dagger alternative.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionUpAcceptance

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem takeWhile_length_le {α : Type} (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem run_record_endpoints
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.get
      ⟨j, by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj⟩).input.state =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j (by omega) active).finalState ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1) (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.get
        ⟨j, by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj⟩).output.next := by
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
    start j (by omega) active
  have hsuccessorRecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  have hsuccessorFinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (j + 1) (count - (j + 1)) (by omega) active
  have hprefixCount :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
          (by omega) active).records ++ suffix := by
    simpa [Nat.add_sub_of_le (by omega : j + 1 ≤ count)] using hprefix
  have hjFull : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjSuccessor : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (j + 1) (by omega) active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hprefixAt := List.getElem_of_eq hprefixCount hjFull
  have hsuccessorAt := List.getElem_of_eq hsuccessorRecords hjSuccessor
  have hprefixAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.get
        ⟨j, hjFull⟩ =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ := by
    simpa [List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using hprefixAt
  have hsuccessorAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ = record := by
    simpa [record, List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using
      hsuccessorAt
  have hactual :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.get
        ⟨j, hjFull⟩ = record := hprefixAt'.trans hsuccessorAt'
  constructor
  · rw [hactual]
    rfl
  · rw [hactual]
    exact hsuccessorFinal

private theorem run_record_time
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records[j]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).input.time.val = start + j := by
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan active
  have hjtimes : j < ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).records.map (fun record => record.input.time.val)).length := by
    simp [ReferenceActivePhysicalHorizon.run_record_count, hj]
  have hjcalendar : j < (ReferenceActivePhysicalHorizon.calendar start count).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hj
  have hmap := List.getElem_of_eq htimes hjtimes
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem_map,
    List.getElem_range'_1] using hmap

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (start count : ℕ) (span : start + count ≤ p.T)
  (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
  (k : ℕ) (hk : k + 1 < count)
  (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))

/-- At every actual, non-dagger receiver query in the continuing cutoff
collection window, the executed local receiver and its ledger are obtained
from the same physical record. Pending, sigma, cutoff and cursor are the
actual moving fields. The local slot, sender, nonacceptance and ordinary-choice
selectors remain explicit. Sources: `05_binary_transport.tex:36-53,70-88,105-124`,
`06_interruptions.tex:41-70,164-177,277-284,327-348`, and
`appendix_a_local_protocol.tex:92-109,151-157`. -/
theorem run_cutoff_collection_receiver_query :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let prev := E.records[k]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
    let current := E.records[k + 1]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
    ∀ (hp : ReferenceAssignmentPayloadPersistence.storedPayload
        current.input.state.coordinator = some payload)
      (hc : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true)
      (hd : ReferenceAcceptedUpFollowerHistory.RetainedDown prev i (payload.downRecord i))
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
      (hf : current.output.next.followers i = .ordinary next nextMemory)
      (ho : current.output.next.coordinator ≠ .dagger),
      ∃ (M : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta)),
        M.val = ActiveFollowerQueueOperation.upOfferFields next ∧
        M.val.sigma = payload.sigma.val + 1 ∧ 0 < M.val.sigma ∧
        let b := k + 2
        let W := (E.records.drop b).takeWhile
          fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
        ∀ n (hn : n < W.length),
          let record := E.records[b + n]'(by
            have htake : ((E.records.drop b).takeWhile
                (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length ≤
                (E.records.drop b).length := takeWhile_length_le _ _
            have hnDrop : n < (E.records.drop b).length := lt_of_lt_of_le hn htake
            rw [List.length_drop] at hnDrop
            omega)
          ∀ (hordinary : record.output.next.coordinator ≠ .dagger),
            ∃ (tail : ReferenceCollectionPhaseHistory.Tail record.input)
              (recording : CoordinatorRecordingOperation.Output p)
              (L : ReferenceActivePhysicalStep.Ledger rate)
              (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
              ReferenceCollectionPhaseHistory.executedTail record.input = some tail ∧
              CoordinatorRecorderComplementBridge.run
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  (ReferenceActivePhysicalStep.prepare record.input)
                  tail.payload tail.started tail.weights) = some recording ∧
              CoordinatorCollectionLedger.startRound tail.ledger
                (record.input.time.val + 1)
                (ReferenceActivePhysicalStep.collectionEnabled tail.ledger record.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                  .success L ∧
              ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some L ∧
              CoordinatorUpReception.receptionInputCheck
                (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L) = true ∧
              record.output.coordinator.up = some d ∧
              d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L ∧
              tail.reception = some (L,
                ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare record.input) L) ∧
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) L).result ≠ .invalid ∧
              (∃ (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
                (bank : CoordinatorUpReception.UpDecoderBank p)
                (finished : ReferenceActivePhysicalStep.Ledger rate)
                (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                ((ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare record.input) L).result =
                      .success (receivedLedger, bank) ∨
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare record.input) L).result =
                      .rejected (receivedLedger, bank)) ∧
                CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
                  (tail.started.clock) finished.pending record.input.row = .ok clockFinished) ∧
              L.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                (current :: W.take n)).toFinset ∧
              L.sigma = payload.sigma.val + 1 ∧
              L.cutoff = current.input.time.val + 1 ∧
              L.cursor = record.input.time.val + 1 ∧
              d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
              d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
              d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
              d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
              d.expected = ReferenceActivePhysicalStep.upExpected
                (ReferenceActivePhysicalStep.prepare record.input) ∧
              d.rawMatches = decide (d.raw = d.expected) ∧
              d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                rate record.input.row
                (ReferenceActivePhysicalStep.upInputs
                  (ReferenceActivePhysicalStep.prepare record.input) L) record.input.time
                ((ReferenceActivePhysicalStep.prepare record.input).followers.followers
                  (ReferenceActivePhysicalStep.upSenderIndex record.input))
                ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).1
                ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).2.1
                ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).2.2.1 rfl ∧
              d.input.upDecoderBank = record.input.state.upDecoderBank ∧
              d.input.time = record.input.time ∧
              d.input.affineSample =
                (record.input.row.2 record.input.time).2
                  (1, CoordinatorUpMeasurability.selectedChannelFollower
                    (record.input.row.2 record.input.time)) ∧
              d.input.ownObservation =
                (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
                  (ActiveRoundActions.coordinator p.two_le_m) ∧
              (∀ (hslot : PublicDiscreteDraws.slotDraw
                  (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot)
                (hselected : ReferenceActivePhysicalStep.upSenderIndex record.input = i)
                (hunaccepted : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
                  (current :: W.take n)).toFinset),
                d.input.slot = PublicDiscreteDraws.upSlot ∧
                d.input.selectedFollower = i ∧
                CoordinatorUpReception.receptionGate d.input ∧
                (CoordinatorUpReception.roundInput d.input).selected = true ∧
                (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                CoordinatorCollectionLedger.acceptUpCheck L i M = true) ∧
              (∀ (hslot : PublicDiscreteDraws.slotDraw
                  (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot)
                (hselected : ReferenceActivePhysicalStep.upSenderIndex record.input = i)
                (s : ReferencePrelaunchFollower.State p rate.eta)
                (mem : ActiveFollowerLifecycle.LocalMemory p),
                (ReferenceFollowerFixedReply.actualChoice record i).configuration =
                  .ordinary s mem →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                  (record.input.state.activations i) record.input.time s = .offer M ∧
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  (ReferenceFollowerFixedReply.actualChoice record i).follower
                  (ReferenceFollowerFixedReply.actualChoice record i).row
                  (ReferenceFollowerFixedReply.actualChoice record i).activation
                  (ReferenceFollowerFixedReply.actualChoice record i).time s = .offer M ∧
                ReferenceActiveAffinePositiveTest.upSent record.input =
                    some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
                  ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare record.input) =
                      some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
                  (ReferenceActiveAffinePositiveTest.upPositive record.input = true →
                    AffineChannelLaw.affineHash
                      ((record.input.row.2 record.input.time).2 (1, i))
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta M) = 1)) ∧
              (∀ (hselected : ReferenceActivePhysicalStep.upSenderIndex record.input = i),
                d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) →
                d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) →
                CoordinatorCollectionLedger.acceptUpCheck L i M = true →
                ReferenceCollectionPhaseHistory.filteredParsed record.input L = some M ∧
                d.parsed = some M ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
                d.wrongUniqueAccepted = false ∧
                ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                  (bank : CoordinatorUpReception.UpDecoderBank p),
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare record.input) L).result =
                      .success (decoded, bank) ∧
                  ReferenceCollectionPhaseHistory.AcceptedUp record.input i M) := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  obtain ⟨trajectoryM, hTrajectoryM, hTrajectorySigma, _,
      htrajectory⟩ :=
    ReferenceCollectionUpPendingInterval.run_cutoff_collection_pending_exact
      initial rows J rewards start count span active k hk payload i hp hc hd
      next nextMemory hf ho
  obtain ⟨M, hMval, hMpositive, hfixedQuery⟩ :=
    ReferenceCutoffUpReplyInterval.collection_interval_fixed_up_query
      initial rows J rewards start count span active k hk payload i hp hc hd
      next nextMemory hf ho
  have hMvalEq : M.val = trajectoryM.val := hMval.trans hTrajectoryM.symm
  have hM : M = trajectoryM := Subtype.ext hMvalEq
  have hMsigma : M.val.sigma = payload.sigma.val + 1 := by
    rw [hM, hTrajectorySigma]
  let b := k + 2
  let W := (E.records.drop b).takeWhile
    fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  dsimp only [E, prev, current, b, W] at htrajectory hfixedQuery ⊢
  refine ⟨M, hMval, hMsigma, hMpositive, ?_⟩
  intro n hn hordinary
  have hcount : E.records.length = count := by
    dsimp [E]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
      start count span active
  have hdrop : (E.records.drop b).length = count - b := by
    rw [List.length_drop, hcount]
  have htake : ((E.records.drop b).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length ≤
      (E.records.drop b).length := takeWhile_length_le _ _
  have hnDrop : n < (E.records.drop b).length := lt_of_lt_of_le hn htake
  have hrecordIndex : b + n < E.records.length := by
    rw [List.length_drop] at hnDrop
    omega
  have hbn : b + n < count := by rw [← hcount]; exact hrecordIndex
  let record := E.records[b + n]'(by rw [hcount]; exact hbn)
  have hend := run_record_endpoints initial rows J rewards start count span active
    (b + n) hbn
  have hrecordTime := run_record_time initial rows J rewards start count span active
    (b + n) hbn
  have hcurrentTime := run_record_time initial rows J rewards start count span active
    (k + 1) (by omega)
  have hprefixResult := htrajectory n (by omega)
  have hrecordInputState : record.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (by omega) active).finalState := by
    change (E.records[b + n]'(by rw [hcount]; exact hbn)).input.state = _
    exact hend.1
  have hprefixNotDagger :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (by omega) active).finalState.coordinator ≠ .dagger := by
    intro hdagger
    have hinputDagger : record.input.state.coordinator = .dagger :=
      (congrArg ReferenceActivePhysicalStep.State.coordinator hrecordInputState).trans hdagger
    have hstepDagger :=
      (ReferenceActivePhysicalStep.step_coordinator_dagger record.input hinputDagger).1
    have hrecordDagger : record.output.next.coordinator = .dagger := by
      rw [record.output_eq]
      exact hstepDagger
    exact hordinary hrecordDagger
  obtain ⟨movingLedger, movingSaved, hmovingCollection, hmovingPending,
      hmovingSigma, hmovingCutoff⟩ := hprefixResult.resolve_left hprefixNotDagger
  have hstate : record.input.state.coordinator =
      .collection payload movingLedger movingSaved := by
    exact (congrArg ReferenceActivePhysicalStep.State.coordinator hrecordInputState).trans
      hmovingCollection
  have hnextBound : n + 1 ≤ W.length := Nat.succ_le_of_lt hn
  have hnextResult := htrajectory (n + 1) hnextBound
  have hrecordOutput : record.output.next.coordinator =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + (n + 1))
        (by omega) active).finalState.coordinator := by
    have hcoordRun :
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n + 1)
          (by omega) active).finalState.coordinator =
          ((E.records.get ⟨b + n, by rw [hcount]; exact hbn⟩).output.next.coordinator) :=
      congrArg ReferenceActivePhysicalStep.State.coordinator hend.2
    have hcoordRecord :
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n + 1)
          (by omega) active).finalState.coordinator = record.output.next.coordinator := by
      change (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n + 1)
        (by omega) active).finalState.coordinator =
        (((E.records.get ⟨b + n, by rw [hcount]; exact hbn⟩).output).next.coordinator)
      exact hcoordRun
    have hcoord' :
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + (n + 1))
          (by omega) active).finalState.coordinator = record.output.next.coordinator := by
      simpa only [Nat.add_assoc] using hcoordRecord
    exact hcoord'.symm
  have hnextNotDagger :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + (n + 1))
        (by omega) active).finalState.coordinator ≠ .dagger := by
    intro hdagger
    exact hordinary (hrecordOutput.trans hdagger)
  obtain ⟨outputLedger, outputSaved, houtputCollection, _, _, _⟩ :=
    hnextResult.resolve_left hnextNotDagger
  have hstepCollection :
      (ReferenceActivePhysicalStep.step record.input).next.coordinator =
        .collection payload outputLedger outputSaved := by
    have hrecordCollection : record.output.next.coordinator =
        .collection payload outputLedger outputSaved := hrecordOutput.trans houtputCollection
    have hrecordStep := congrArg
      (fun out : ReferenceActivePhysicalStep.RoundOutput record.input => out.next.coordinator)
      record.output_eq
    exact hrecordStep.symm.trans hrecordCollection
  obtain ⟨tail, htail, hpendingFrame, hsigmaFrame⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame record.input payload
      outputLedger outputSaved hstepCollection
  obtain ⟨_, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin htail
  have htailMoving : tail.ledger = movingLedger := by
    rcases horigin with ⟨hcutoff, _⟩ |
        ⟨_, tailPayload, tailLedger, _, htailState, htailLedger⟩
    · have hcutoffFalse :
          ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        by_cases hvalid : 1 ≤ movingLedger.cutoff ∧ movingLedger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨movingLedger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload movingLedger
            movingSaved cutoff
          have hprepared : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .collection payload movingLedger clock cutoff
                (CoordinatorRoundDispatch.dispatchCollection
                  (ReferenceActivePhysicalStep.collectionInput record.input payload movingLedger
                    clock cutoff)) := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              CoordinatorRoundDispatch.dispatch, hstate, hvalid, cutoff, clock]
            rfl
          simp [ReferenceCollectionPhaseHistory.cutoffChosen, hprepared]
        · simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hstate, hvalid]
      rw [hcutoffFalse] at hcutoff
      cases hcutoff
    · have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
        (htailState.symm.trans hstate)
      exact htailLedger.trans hfields.2.1
  have htailPending : tail.ledger.pending =
      Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
        (current :: W.take n)).toFinset := by
    rw [htailMoving]
    exact hmovingPending
  obtain ⟨recording, L, d, hproof⟩ :=
    ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
      record payload movingLedger movingSaved tail hstate htail hordinary
  rcases hproof with ⟨hrecording, hproof⟩
  rcases hproof with ⟨hstart, hproof⟩
  rcases hproof with ⟨hsite, hproof⟩
  rcases hproof with ⟨hcheck, hproof⟩
  rcases hproof with ⟨hdiagnostic, hproof⟩
  rcases hproof with ⟨hinput, hproof⟩
  rcases hproof with ⟨htailReception, hproof⟩
  rcases hproof with ⟨hnotInvalid, hproof⟩
  rcases hproof with ⟨hreceiveExist, hproof⟩
  rcases hreceiveExist with ⟨receivedLedger, receiveBank, finished, clockFinished,
    hreceived, hfinished, hclock⟩
  rcases hproof with ⟨hdecoderAfter, hproof⟩
  rcases hproof with ⟨hraw, hproof⟩
  rcases hproof with ⟨hparsed, hproof⟩
  rcases hproof with ⟨hlocallyAccepted, hproof⟩
  rcases hproof with ⟨hexpected, hproof⟩
  rcases hproof with ⟨hrawMatches, hproof⟩
  rcases hproof with ⟨hbank, hproof⟩
  rcases hproof with ⟨hdiagnosticTime, hproof⟩
  rcases hproof with ⟨hsample, hproof⟩
  rcases hproof with ⟨hownObservation, hproof⟩
  rcases hproof with ⟨hwrongUnique, hmatching⟩
  have hcandidate := CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
    tail.ledger (record.input.time.val + 1) (by omega) (by omega)
    (ReferenceActivePhysicalStep.collectionEnabled tail.ledger record.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording)
    L hstart
  have hledgerPending : L.pending =
      Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
        (current :: W.take n)).toFinset := by
    rw [hcandidate]
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using htailPending
  have hledgerSigma : L.sigma = payload.sigma.val + 1 := by
    rw [hcandidate]
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using
      (congrArg (fun ledger : ReferenceActivePhysicalStep.Ledger rate => ledger.sigma)
        htailMoving).trans hmovingSigma
  have hledgerCutoff : L.cutoff = current.input.time.val + 1 := by
    rw [hcandidate]
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using
      (congrArg (fun ledger : ReferenceActivePhysicalStep.Ledger rate => ledger.cutoff)
        htailMoving).trans hmovingCutoff
  have hledgerCursor : L.cursor = record.input.time.val + 1 := by
    rw [hcandidate]
    simp [CoordinatorCollectionLedger.startRoundCandidate,
      CoordinatorCollectionLedger.sourceRound]
  have hinputLedger : d.input.ledger = L := by
    have hproj := congrArg CoordinatorUpReception.ReceptionInput.ledger hinput
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hproj
  have hinputTime : d.input.time = record.input.time := by
    have hproj := congrArg CoordinatorUpReception.ReceptionInput.time hinput
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hproj
  have hrecordTimeActual : record.input.time.val = start + (b + n) := by
    simpa [record] using hrecordTime
  have hcurrentTimeActual : current.input.time.val = start + (k + 1) := by
    simpa [current, E] using hcurrentTime
  have hqueryCount : b + n < count := hbn
  have hquery := hfixedQuery n (Nat.le_of_lt hn) hqueryCount hrecordIndex
  refine ⟨tail, recording, L, d, htail, hrecording, hstart, hsite, hcheck,
    hdiagnostic, hinput, htailReception, hnotInvalid,
    ⟨receivedLedger, receiveBank, finished, clockFinished, hreceived, hfinished, hclock⟩,
    hledgerPending, hledgerSigma, hledgerCutoff, hledgerCursor,
    hdecoderAfter, hraw, hparsed,
    hlocallyAccepted, hexpected, hrawMatches, hwrongUnique, hbank, hdiagnosticTime,
    hsample, hownObservation, ?_, ?_, ?_⟩
  · intro hslot hselected hunaccepted
    have hselectedIndex :
        CoordinatorUpMeasurability.selectedFollowerIndex
          (record.input.row.2 record.input.time) = i := by
      simpa [record, ReferenceActivePhysicalStep.upSenderIndex,
        ReferenceActivePhysicalStep.RoundInput.row] using hselected
    have hsenderDraw :
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i := by
      rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
      exact hselectedIndex
    have hinputSlot : d.input.slot = PublicDiscreteDraws.upSlot := by
      rw [hinput]
      simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
        ReferenceActivePhysicalStep.upInputs,
        ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow, record] using hslot
    have hinputSelected : d.input.selectedFollower = i := by
      rw [hinput]
      simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
        ReferenceActivePhysicalStep.upInputs,
        ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        record, PublicDiscreteDraws.followerCount] using hsenderDraw
    have hiNotAccepted : i ∉
        (ReferenceCollectionPhaseHistory.acceptedLabels
          (current :: W.take n)).toFinset := hunaccepted
    have hiPending : i ∈ L.pending := by
      rw [hledgerPending]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiNotAccepted⟩
    have hgate : CoordinatorUpReception.receptionGate d.input := by
      change d.input.ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound d.input.time ∧
        d.input.slot = PublicDiscreteDraws.upSlot ∧
        d.input.selectedFollower ∈ d.input.ledger.pending
      rw [hinputLedger, hinputSelected, hinputSlot]
      refine ⟨?_, rfl, hiPending⟩
      · rw [hledgerCutoff, hinputTime]
        dsimp [CoordinatorCollectionLedger.sourceRound]
        rw [hcurrentTimeActual, hrecordTimeActual]
        dsimp [b]
        omega
    have hroundSelected : (CoordinatorUpReception.roundInput d.input).selected = true :=
      (CoordinatorUpReception.roundInput_selected_iff_gate d.input).2 hgate
    have hroundEnabled :
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true := rfl
    have hcutoffCursor : L.cutoff ≤ L.cursor := by
      rw [hledgerCutoff, hledgerCursor, hcurrentTimeActual, hrecordTimeActual]
      dsimp [b]
      omega
    have haccept : CoordinatorCollectionLedger.acceptUpCheck L i M = true := by
      simp [CoordinatorCollectionLedger.acceptUpCheck, hcutoffCursor, hiPending,
        hledgerSigma, hMsigma]
    exact ⟨hinputSlot, hinputSelected, hgate, hroundSelected, hroundEnabled, haccept⟩
  · intro hslot hselected s mem hchoice
    have hselectedIndex :
        CoordinatorUpMeasurability.selectedFollowerIndex
          (record.input.row.2 record.input.time) = i := by
      simpa [record, ReferenceActivePhysicalStep.upSenderIndex,
        ReferenceActivePhysicalStep.RoundInput.row] using hselected
    have hsenderDraw :
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i := by
      rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
      exact hselectedIndex
    have hslotActual : PublicDiscreteDraws.slotDraw
        (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot := by
      simpa [record] using hslot
    have hqueryResult := hquery s mem hchoice hslotActual hsenderDraw
    simpa only [record, E, b, List.get_eq_getElem] using hqueryResult
  · intro hselected hrawWord hExpectedWord haccept
    have hacceptSender :
        CoordinatorCollectionLedger.acceptUpCheck L
          (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true := by
      rw [hselected]
      exact haccept
    have hmatchingM := hmatching M hrawWord hExpectedWord hacceptSender
    rcases hmatchingM with ⟨hfiltered, hparsedM, hlocalM, hmatchesM,
      hwrongM, decoded, bank, hreceiveM, hacceptedM⟩
    refine ⟨hfiltered, hparsedM, hlocalM, hmatchesM, hwrongM,
      decoded, bank, hreceiveM, ?_⟩
    have hacceptedI : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M := by
      rw [← hselected]
      exact hacceptedM
    simpa only [record, List.get_eq_getElem] using hacceptedI

theorem run_cutoff_up_second_window_acceptance
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k + 1 < count)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (hp : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).input.state.coordinator =
        some payload)
    (hc : ReferenceCollectionPhaseHistory.cutoffChosen
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).input = true)
    (hd : ReferenceAcceptedUpFollowerHistory.RetainedDown
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; omega))
      i (payload.downRecord i))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).output.next.followers i =
        .ordinary next nextMemory)
    (ho : ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).output.next.coordinator ≠ .dagger)
    (n : ℕ)
    (hn : n ≤ (((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.drop
      (k + 2)).takeWhile fun r =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input).length)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2 + n)
      (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.coordinator ≠
        .dagger)
    (hpositiveCount :
      let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2)
        (by omega) active
      let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start
        (k + 2 + n) (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let interval := completedRun.records.drop (k + 2)
      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start
        (k + 2) (k + 2 + n)
        (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let channel := preRun.finalState.upDecoderBank i
      (AffineBatchDecoder.positives p trace rounds).length =
        AffineBatchDecoder.quota p - channel.pending.length + AffineBatchDecoder.quota p) :
    ∃ (M : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
      ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (index : Fin (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start
          (k + 2) (k + 2 + n)
          (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active).length)
        (record : Record p rate)
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
      let b := k + 2
      let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active
      let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let interval := completedRun.records.drop b
      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start b
        (b + n) (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let positive := AffineBatchDecoder.positives p trace rounds
      let channel := preRun.finalState.upDecoderBank i
      let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
      let current := E.records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
      let W := (E.records.drop b).takeWhile
        fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
      M.val = ActiveFollowerQueueOperation.upOfferFields next ∧
      0 < M.val.sigma ∧
      first = channel.pending ++ positive.take (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      last ∈ window ∧
      AffineBatchDecoder.decisionTime window = some last.time ∧
      rounds.get index = last.time ∧
      record ∈ interval ∧
      record.input.time = last.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.followers i =
          .dagger ∨
      ∃ (finalFollower : ReferencePrelaunchFollower.State p rate.eta)
        (finalMemory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
          (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.followers i =
            .ordinary finalFollower finalMemory ∧
        (∀ entry, entry ∈ window →
          AffineBatchDecoder.equation entry.sample
            (ActiveFollowerArmChoice.offeredUpWord rate.eta M)) ∧
        ((∃! v, AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v) →
          diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
          diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
          ∃ (queryIndex : Fin n), record = E.records[b + queryIndex.val]'(by
            have htake : W.length ≤ (E.records.drop b).length :=
              takeWhile_length_le _ _
            have hdrop : queryIndex.val < (E.records.drop b).length :=
              lt_of_lt_of_le (lt_of_lt_of_le queryIndex.isLt hn) htake
            rw [List.length_drop] at hdrop
            omega) ∧
          ∃ (tail : ReferenceCollectionPhaseHistory.Tail record.input)
            (recording : CoordinatorRecordingOperation.Output p)
            (L : ReferenceActivePhysicalStep.Ledger rate),
            ReferenceCollectionPhaseHistory.executedTail record.input = some tail ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare record.input)
                tail.payload tail.started tail.weights) = some recording ∧
            CoordinatorCollectionLedger.startRound tail.ledger
              (record.input.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled tail.ledger record.input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success L ∧
            ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some L ∧
            CoordinatorUpReception.receptionInputCheck
              (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L) = true ∧
            CoordinatorUpReception.receptionGate diagnostic.input ∧
            (CoordinatorUpReception.roundInput diagnostic.input).selected = true ∧
            (CoordinatorUpReception.roundInput diagnostic.input).receiverEnabled = true ∧
            CoordinatorCollectionLedger.acceptUpCheck L i M = true ∧
            L.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
              (current :: W.take queryIndex.val)).toFinset ∧
            L.sigma = payload.sigma.val + 1 ∧
            L.cutoff = current.input.time.val + 1 ∧
            L.cursor = record.input.time.val + 1 ∧
            ReferenceCollectionPhaseHistory.filteredParsed record.input L = some M ∧
            diagnostic.parsed = some M ∧ diagnostic.locallyAccepted = true ∧
            diagnostic.rawMatches = true ∧ diagnostic.wrongUniqueAccepted = false ∧
            ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
              (bank : CoordinatorUpReception.UpDecoderBank p),
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) L).result =
                  .success (decoded, bank) ∧
              ReferenceCollectionPhaseHistory.AcceptedUp record.input i M)) := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let b := k + 2
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  let W := (E.records.drop b).takeWhile
    fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  let endpoint := b + n
  let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active
  let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start endpoint
    (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
  let interval := completedRun.records.drop b
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
  let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start b
    endpoint (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
  let positive := AffineBatchDecoder.positives p trace rounds
  let channel := preRun.finalState.upDecoderBank i
  let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
  obtain ⟨M, first, last, index, record, diagnostic, htruth⟩ :=
    ReferenceFixedUpCompletedWindowTruth.run_cutoff_up_second_window_truth
      initial rows J rewards start count span active k hk payload i hp hc hd next nextMemory hf ho
      n hn hinitial hseed hcoord hpositiveCount
  rcases htruth with ⟨hMval, hMsigma, hfirst, hfirstLen, hwindowLen, hwindowPairwise,
    hlast, hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected,
    hraw, hbranch⟩
  change record ∈ interval at hrecordMem
  change record.input.time = last.time at hrecordTime
  change record.output.coordinator.up = some diagnostic at hdiagnostic
  have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut
    initial rows J rewards start b endpoint (by omega)
    (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn)
    active hinitial hcoord
  rcases hcut with ⟨_, _, hconnected, _, _, _, hnoDagger⟩
  have hrecordCompleted : record ∈ completedRun.records := List.mem_of_mem_drop hrecordMem
  have hordinary : record.output.next.coordinator ≠ .dagger := hnoDagger record hrecordCompleted
  have hcount : E.records.length = count := by
    dsimp [E]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count span active
  have hcompletedCount : completedRun.records.length = endpoint := by
    dsimp [completedRun, endpoint]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start (b + n)
      (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn) active
  have hdropCount : (E.records.drop b).length = count - b := by
    rw [List.length_drop, hcount]
  have htakeCount : W.length ≤ (E.records.drop b).length := takeWhile_length_le _ _
  have hnCount : b + n ≤ count := by
    have hle := hn.trans htakeCount
    rw [hdropCount] at hle
    omega
  have hintervalLength : interval.length = n := by
    dsimp [interval]
    rw [List.length_drop, hcompletedCount]
    dsimp [endpoint, b]
    omega
  obtain ⟨j, hj, hrecordGet⟩ := List.mem_iff_getElem.mp hrecordMem
  have hjn : j < n := by rw [← hintervalLength]; exact hj
  have hfullIndex : b + j < E.records.length := by rw [hcount]; omega
  have hcompletedIndex : b + j < completedRun.records.length := by
    rw [hcompletedCount]
    omega
  obtain ⟨suffix, hprefix0⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards start (b + n) (count - (b + n)) (by omega) active
  have hprefix : E.records = completedRun.records ++ suffix := by
    simpa [E, completedRun, endpoint, Nat.add_sub_of_le hnCount] using hprefix0
  have hprefixGet := List.getElem_of_eq hprefix hfullIndex
  have hrecordOriginal : record = E.records[b + j]'hfullIndex := by
    calc
      record = interval[j]'hj := hrecordGet.symm
      _ = completedRun.records[b + j]'hcompletedIndex := by exact List.getElem_drop
      _ = E.records[b + j]'hfullIndex := by
        symm
        simpa [List.getElem_append, hcompletedIndex] using hprefixGet
  have hintervalOriginal : interval[j]'hj = E.records[b + j]'hfullIndex :=
    hrecordGet.trans hrecordOriginal
  clear hrecordGet
  subst record
  let record := E.records[b + j]'hfullIndex
  have hroundsChronological :=
    ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
      initial rows J rewards start b endpoint (by omega)
      (ReferenceFixedUpCompletedWindowTruth.fixed_window_span initial rows J rewards start count span active k n hk hn)
      active hinitial hcoord
  have hroundValues : (rounds.map Fin.val).Pairwise LT.lt :=
    List.pairwise_map.mpr hroundsChronological
  have htimeValues : (interval.map (fun r => r.input.time.val)).Pairwise LT.lt := by
    simpa [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
      ReferenceCoordinatorUpIntervalWindow.intervalRecords, interval, completedRun,
      endpoint, b, List.map_map, Function.comp_def] using hroundValues
  have hintervalChronological := List.pairwise_map.mp htimeValues
  have htraceRecord := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    interval i hintervalChronological record hrecordMem
  have hlastPositive : last ∈ positive := List.mem_of_mem_drop hlast
  obtain ⟨_, hlastEligible, _⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace rounds last).mp hlastPositive
  obtain ⟨sourceLedger, hsiteSaved, hdiagLedger, _, hdiagTime, _, hselectedIndex, _, hslotField,
    _, hselectedFlag, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      record diagnostic hdiagnostic
  have htraceDiagnostic : trace record.input.time =
      CoordinatorUpReception.roundInput diagnostic.input := by
    dsimp only [record, trace]
    rw [htraceRecord]
    simp [record, ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic,
      hselected, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
  have hrecordEligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    rw [← htraceDiagnostic, hrecordTime]
    exact hlastEligible
  have hselectedTrue := hrecordEligible.1
  rw [hselectedFlag] at hselectedTrue
  have hreceptionGate : CoordinatorUpReception.receptionGate diagnostic.input := by
    have hgateFields := of_decide_eq_true hselectedTrue
    change diagnostic.input.ledger.cutoff ≤
        CoordinatorCollectionLedger.sourceRound diagnostic.input.time ∧
      diagnostic.input.slot = PublicDiscreteDraws.upSlot ∧
      diagnostic.input.selectedFollower ∈ diagnostic.input.ledger.pending
    rw [hdiagLedger, hdiagTime]
    simp only [CoordinatorCollectionLedger.sourceRound]
    exact hgateFields
  have hslot : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot :=
    hslotField.symm.trans hreceptionGate.2.1
  have hselectedValue : CoordinatorUpMeasurability.selectedFollowerIndex
      (record.input.row.2 record.input.time) = i := by
    exact hselectedIndex.symm.trans hselected
  have hselectedRecord : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    simpa [ReferenceActivePhysicalStep.upSenderIndex,
      ReferenceActivePhysicalStep.RoundInput.row] using hselectedValue
  have hqueryResult :=
    ReferenceCollectionUpAcceptance.run_cutoff_collection_receiver_query
      initial rows J rewards start count span active k hk payload i hp hc hd next nextMemory hf ho
  rcases hqueryResult with ⟨queryM, hqueryMval, hqueryMsigma, hqueryMpositive, hqueries⟩
  have hqueryM : queryM = M := Subtype.ext (hqueryMval.trans hMval.symm)
  have hjW : j < W.length := lt_of_lt_of_le hjn hn
  obtain ⟨tail, recording, L, d, htail, hrecording, hstart, hsite, hcheck,
    hqueryDiagnostic, hinput, htailReception, hnotInvalid, hreceive, hpending,
    hsigma, hcutoff, hcursor, hdecoderAfter, hrawQuery, hparsedQuery,
    hlocallyQuery, hexpectedQuery, hrawMatchesQuery, hwrongQuery, hbankQuery,
    htimeQuery, hsampleQuery, hobservationQuery, hqueryGate, hqueryChoice,
    hqueryMatching⟩ := hqueries j hjW hordinary
  have hqueryDiagnosticRecord : (E.records[b + j]'hfullIndex).output.coordinator.up = some d :=
    hqueryDiagnostic
  have hdEq : d = diagnostic := by
    exact Option.some.inj (hqueryDiagnosticRecord.symm.trans hdiagnostic)
  have hsiteRecord : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := record.input) = some L := hsite
  have hledgerEq : sourceLedger = L := Option.some.inj (hsiteSaved.symm.trans hsiteRecord)
  have hselectedQuery : ReferenceActivePhysicalStep.upSenderIndex
      (E.records[b + j]'hfullIndex).input = i := hselectedRecord
  have hslotQuery : PublicDiscreteDraws.slotDraw
      ((E.records[b + j]'hfullIndex).input.row.2
        (E.records[b + j]'hfullIndex).input.time).1 = PublicDiscreteDraws.upSlot := hslot
  have hiLedger : i ∈ L.pending := by
    rw [← hledgerEq]
    have hfields := of_decide_eq_true hselectedTrue
    simpa [hselected] using hfields.2.2
  have hunaccepted : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
      (current :: W.take j)).toFinset := by
    intro hi
    rw [hpending] at hiLedger
    exact (Finset.mem_sdiff.mp hiLedger).2 hi
  rcases hqueryGate hslotQuery hselectedQuery hunaccepted with
    ⟨hinputSlot, hinputSelected, hgateQuery, hroundSelected, hroundEnabled, hacceptQuery⟩
  rcases hbranch with hdagger | ⟨finalFollower, finalMemory, hfinalFollower,
      hequations, huniqueWords⟩
  · have hdaggerExact : completedRun.finalState.followers i = .dagger := by
      simpa [completedRun, endpoint, b] using hdagger
    refine ⟨M, first, last, index, record, diagnostic, ?_⟩
    dsimp only [E, b, preRun, completedRun, interval, trace, rounds, positive, channel,
      window, current, W]
    exact ⟨hMval, hMsigma, hfirst, hfirstLen, hwindowLen, hwindowPairwise, hlast,
      hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected, hraw,
      Or.inl hdaggerExact⟩
  · obtain ⟨queryState, queryMemory, hqueryOutput⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology
        hconnected i finalFollower finalMemory hfinalFollower j hj
    have hrecordOutput : record.output.next.followers i = .ordinary queryState queryMemory := by
      dsimp only [record]
      rw [← hintervalOriginal]
      simpa [ReferenceCoordinatorUpIntervalWindow.intervalRecords, interval, completedRun,
        endpoint, b] using hqueryOutput.1
    obtain ⟨choice, choiceMemory, hchoice, _, _, _⟩ :=
      ReferenceFollowerReplyChronology.record_choice_chronology
        record i queryState queryMemory hrecordOutput
    have hchoiceQuery :
        (ReferenceFollowerFixedReply.actualChoice (E.records[b + j]'hfullIndex) i).configuration =
          .ordinary choice choiceMemory := hchoice
    obtain ⟨_hchecked, _hcheckedActual, _hupSent, hupExpected, _hhash⟩ :=
      hqueryChoice hslotQuery hselectedQuery choice choiceMemory hchoiceQuery
    refine ⟨M, first, last, index, record, diagnostic, ?_⟩
    dsimp only [E, b, preRun, completedRun, interval, trace, rounds, positive, channel,
      window, current, W]
    refine ⟨hMval, hMsigma, hfirst, hfirstLen, hwindowLen, hwindowPairwise, hlast,
      hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected, hraw,
      Or.inr ⟨finalFollower, finalMemory, hfinalFollower, hequations, ?_⟩⟩
    intro hunique
    have hwords := huniqueWords hunique
    have hrawWord : d.raw =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta queryM) := by
      simpa [hdEq, hqueryM] using hwords.1
    have hExpectedWordQuery : d.expected =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta queryM) :=
      hexpectedQuery.trans hupExpected
    rcases hqueryMatching hselectedQuery hrawWord hExpectedWordQuery hacceptQuery with
      ⟨hfiltered, hparsed, hlocal, hmatches, hwrong, decoded, bank, hreceiveSuccess,
        haccepted⟩
    refine ⟨hwords.1, hwords.2, ⟨j, hjn⟩, rfl, tail, recording, L,
      htail, hrecording, hstart, hsite, hcheck, ?_, ?_, ?_, ?_, hpending,
      hsigma, hcutoff, hcursor, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hdEq] using hgateQuery
    · simpa [hdEq] using hroundSelected
    · simpa [hdEq] using hroundEnabled
    · simpa [hqueryM] using hacceptQuery
    · simpa [hqueryM] using hfiltered
    · simpa [hdEq, hqueryM] using hparsed
    · simpa [hdEq] using hlocal
    · simpa [hdEq] using hmatches
    · simpa [hdEq] using hwrong
    · exact ⟨decoded, bank, hreceiveSuccess, by simpa [hqueryM] using haccepted⟩


end Bandits.Support.ReferenceCollectionUpAcceptance

end
