/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateDownReplyHistory
public import Bandits.Support.ReferenceCollectionUpReceiverLocal

/-!
# Actual first-collection late-UP receiver eligibility

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This producer starts from the original late retained DOWN and its actual
first-collection run. It derives the focal pending state and its relative
erasure through the actual successful receiveUp calls. At every selected UP
query it calls the existing one-round receiver producer and exposes the
literal local gate and acceptance test, including zero-observation calls.
Dagger, exhaustion, rejection, and prior acceptance remain distinct.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorCollectionLedger

namespace Bandits.Support.ReferenceFirstCollectionLateUpReceiverEligibility

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_endpoint_unique
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

private theorem run_prefix_endpoints
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
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefix]
    exact htake)
  have hchainPrefix := ReferenceFollowerReplyChronology.connected_take_to_input
    hconnected n hnFull
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] hchainPrefix rfl
  have hrecordsNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hrecordsNext]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem takeWhile_length_le {α : Type} (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

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
    {rate : ReferenceActivePhysicalStep.RateInput p}
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

private theorem executedTail_sigma
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {tail : ReferenceCollectionPhaseHistory.Tail x}
    (htail : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.ledger.sigma = tail.payload.sigma.val + 1 := by
  classical
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinitial hcandidate hdomain hclock hpending hnone selected =>
          have hselected :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinitial hcandidate hdomain hclock
                    hpending hnone selected)) ≠ none := by
            intro hsel
            have hbad : ReferenceCollectionPhaseHistory.executedTail x = none := by
              simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel]
            rw [htail] at hbad
            cases hbad
          have htailEq : tail =
              ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                dispatched.startResult,
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ := by
            have hs : some
                (⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                  dispatched.startResult,
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ :
                  ReferenceCollectionPhaseHistory.Tail x) = some tail := by
              simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
            exact (Option.some.inj hs).symm
          rw [htailEq]
          have hshared := ReferenceActivePhysicalStep.sharedLedger_fields (rate := rate) ledger
          have hinitial := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time
          calc
            (ReferenceActivePhysicalStep.sharedLedger ledger).sigma = ledger.sigma := hshared.2.1
            _ = (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time).sigma := by
                    rw [hcandidate]
                    simp [ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt]
            _ = registers.payload.sigma.val + 1 := hinitial.2.1
      | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hselected :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)) ≠ none := by
            intro hsel
            have hbad : ReferenceCollectionPhaseHistory.executedTail x = none := by
              simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel]
            rw [htail] at hbad
            cases hbad
          have htailEq : tail =
              ⟨payload, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ := by
            have hs : some
                (⟨payload, ledger, snapshot.clockStarted,
                  CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ :
                  ReferenceCollectionPhaseHistory.Tail x) = some tail := by
              simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
            exact (Option.some.inj hs).symm
          rw [htailEq]
          simpa [ReferenceActivePhysicalStep.collectionInput,
            CoordinatorRecorderComplementBridge.sourceStart] using core.ledger_sigma_eq
      | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
  | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail

private theorem actual_collection_output_payload
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hout : r.output.next.coordinator = .collection payload ledger saved)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail) :
    tail.payload = payload := by
  classical
  have hnext : r.output.next.coordinator =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration := by
    rw [r.output_eq]
    exact (ReferenceActivePhysicalStep.step_next_fields r.input).1
  have hobs :
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator =
        ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
          tail.started tail.weights := by
    cases hcoord : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
    | live registers owned base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart oldLedger hinitial hcandidate hdomain hclock hpending hnone selected =>
            have hselected :
                ReferenceActivePhysicalStep.DispatchCut.selection
                  (.live registers owned base
                    (.cutoffChosen dispatched hstart oldLedger hinitial hcandidate hdomain hclock
                      hpending hnone selected)) ≠ none := by
              intro hsel
              have hbad : ReferenceCollectionPhaseHistory.executedTail r.input = none := by
                simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel]
              rw [htail] at hbad
              cases hbad
            have htailEq : tail =
                ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger oldLedger,
                  dispatched.startResult,
                  (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights⟩ := by
              have hs : some
                  (⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger oldLedger,
                    dispatched.startResult,
                    (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights⟩ :
                    ReferenceCollectionPhaseHistory.Tail r.input) = some tail := by
                simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
              exact (Option.some.inj hs).symm
            subst tail
            simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hselected]
        | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
    | collection actualPayload actualLedger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            have hselected :
                ReferenceActivePhysicalStep.DispatchCut.selection
                  (.collection actualPayload actualLedger clock cutoff
                    (.continuing core snapshot boundary scores)) ≠ none := by
              intro hsel
              have hbad : ReferenceCollectionPhaseHistory.executedTail r.input = none := by
                simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel]
              rw [htail] at hbad
              cases hbad
            have htailEq : tail =
                ⟨actualPayload, actualLedger, snapshot.clockStarted,
                  CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (ReferenceActivePhysicalStep.collectionInput r.input actualPayload actualLedger
                      clock cutoff)
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ := by
              have hs : some
                  (⟨actualPayload, actualLedger, snapshot.clockStarted,
                    CoordinatorCollectionInteractive.PreObservationInputs.weights
                      (ReferenceActivePhysicalStep.collectionInput r.input actualPayload actualLedger
                        clock cutoff)
                      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ :
                    ReferenceCollectionPhaseHistory.Tail r.input) = some tail := by
                simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
              exact (Option.some.inj hs).symm
            subst tail
            simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hselected]
        | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
    | _ => simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
  have hstored :
      ReferenceAssignmentPayloadPersistence.storedPayload
        ((ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration) =
          some payload := by
    rw [← hnext, hout]
    rfl
  have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger tail.started tail.weights
  rw [hobs] at hstored
  rcases hframe with hnone | hsome
  · rw [hnone] at hstored
    cases hstored
  · exact Option.some.inj (hsome.symm.trans hstored)

/-! The main producer retains the complete source telescope of L. The
receiver query is conditional only on its actual continuing-collection output
and on the displayed selected-round facts; no sender offer or receiver law is
an input. -/

/-- The original late retained-DOWN branch produces its focal pending
membership and every actual continuing-collection UP receiver call through
the first collection window. `acceptedLabels` is the literal filter-map of
successful `receiveUp` executions. -/
theorem actual_first_collection_late_up_receiver_eligibility
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
    let hactive := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
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
      (∃ hindex : w < E.records.length,
        cutoffRecord = E.records[w]'hindex) ∧
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
        E.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
          (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
          (after : ReferencePrelaunchFollower.State p rate.eta)
          (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
          (scan : FollowerCutoffScan.ScanResult p.T)
          (replayedRegisters : ℕ × ℕ) (lastService : ℕ),
          (r.output.followers i).downInput = some logged ∧
          (r.output.followers i).down = some cutD ∧
          cutD.outcome = .accepted logged after raw M scan replayedRegisters lastService ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 ∧
          ActiveFollowerDownAcceptance.downStart p rate M = P0.sigma ∧
          scan.endpoint = u ∧ after.status = .unoccupied ∧ after.lastDown = some M ∧
          (∃ (_hindex : j < count) (n0 : ℕ),
            n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
            ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
              .ok ⟨replayedRegisters, lastService⟩) ∧
          (let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
           replayedRegisters = V w ∧
           lastService = (V w).1 - (V (w - 1)).1 ∧ after.S = (V w).1 ∧
           after.delta = (V w).1 - (V (w - 1)).1 ∧ after.backlog = (V w).2 ∧
           ReferenceFollowerReplyChronology.reply after =
             (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
           ((r.output.next.followers i = .dagger ∧
               (r.output.next.coordinator = .dagger ∨
                 ∃ ledger saved, r.output.next.coordinator = .collection P0 ledger saved)) ∨
             (∃ (out : ReferencePrelaunchFollower.State p rate.eta)
               (memory : ActiveFollowerLifecycle.LocalMemory p),
               r.output.next.followers i = .ordinary out memory ∧
               out.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply out =
                 (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
               out.lastDown = some M ∧ out.S = (V w).1 ∧
               out.delta = (V w).1 - (V (w - 1)).1 ∧ out.backlog = (V w).2 ∧
               ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
               (r.output.next.coordinator = .dagger ∨
                 ∃ (l0 : ReferenceActivePhysicalStep.Ledger rate)
                   (saved0 : Option (Fin p.T × Bool)),
                   r.output.next.coordinator = .collection P0 l0 saved0 ∧
                   l0.sigma = s + 1 ∧ i ∈ l0.pending ∧
                   let b := j + 1
                   let Wlate := (E.records.drop b).takeWhile
                     (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
                   ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T),
                     (ReferenceActivePhysicalHorizon.run I source.1.2
                       (ActualInitializationPhysicalStep.selectedRowIndex p source)
                       rewards s b hbspan hactive).finalState = r.output.next ∧
                     Wlate = B.drop (k.val + 1) ∧
                     (∀ h (hh : h < Wlate.length),
                       E.records[b + h]? = some Wlate[h] ∧
                         Wlate[h].input.time.val = u + k.val + h) ∧
                     (∀ h (hh : h ≤ Wlate.length),
                       let C := ReferenceActivePhysicalHorizon.run I source.1.2
                         (ActualInitializationPhysicalStep.selectedRowIndex p source)
                         rewards s (b + h) (by
                           have hcount : E.records.length = count := by
                             dsimp only [E, I, s, b0, x0, hactive,
                               ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
                             exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
                               (ActualInitializationPhysicalStep.selectedRowIndex p source)
                               rewards s count hspan hactive
                           have hlen : Wlate.length ≤ count - b := by
                             have hdrop : (E.records.drop b).length = count - b := by
                               rw [List.length_drop, hcount]
                             have htake := takeWhile_length_le
                               (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
                               (E.records.drop b)
                             calc
                               Wlate.length ≤ (E.records.drop b).length := by
                                 dsimp only [Wlate]
                                 exact htake
                               _ = count - b := hdrop
                           have hprefix : b + h ≤ count := by omega
                           have hstart : s + count ≤ p.T := by
                             dsimp only [s, b0, x0]
                             exact hspan
                           omega) hactive
                       C.finalState.coordinator = .dagger ∨
                         ∃ (moving : ReferenceActivePhysicalStep.Ledger rate)
                           (proposal : Option (Fin p.T × Bool)),
                           C.finalState.coordinator = .collection P0 moving proposal ∧
                           moving.sigma = s + 1 ∧
                           moving.pending = l0.pending \
                             (ReferenceCollectionPhaseHistory.acceptedLabels
                               (Wlate.take h)).toFinset ∧
                           (i ∈ moving.pending ↔
                             i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
                               (Wlate.take h)).toFinset)) ∧
                     (∀ n (_hn : n < Wlate.length),
                       let A := ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take n)
                       ∃ hrecord : b + n < E.records.length,
                         let rn := E.records[b + n]'hrecord
                         rn.output.next.coordinator ≠ .dagger →
                         ∃ (tail : ReferenceCollectionPhaseHistory.Tail rn.input)
                           (recording : CoordinatorRecordingOperation.Output p)
                           (pre : ReferenceActivePhysicalStep.Ledger rate)
                           (preSaved : Option (Fin p.T × Bool))
                           (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                           (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                           (received : ReferenceActivePhysicalStep.Ledger rate)
                           (bank : CoordinatorUpReception.UpDecoderBank p)
                           (finished : ReferenceActivePhysicalStep.Ledger rate)
                           (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                           rn.input.state.coordinator = .collection P0 pre preSaved ∧
                           pre.pending = l0.pending \ A.toFinset ∧ pre.sigma = s + 1 ∧
                           ReferenceCollectionPhaseHistory.executedTail rn.input = some tail ∧
                           tail.ledger = pre ∧
                           CoordinatorRecorderComplementBridge.run
                             (ReferenceActivePhysicalStep.collectionRecordingInput
                               (ReferenceActivePhysicalStep.prepare rn.input) tail.payload
                               tail.started tail.weights) = some recording ∧
                           CoordinatorCollectionLedger.startRound tail.ledger
                             (rn.input.time.val + 1)
                             (ReferenceActivePhysicalStep.collectionEnabled tail.ledger rn.input.time)
                             (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                               .success Lsite ∧
                           ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := rn.input) = some Lsite ∧
                           CoordinatorUpReception.receptionInputCheck
                             (ReferenceCoordinatorUpPhysicalCall.actualUpInput rn.input Lsite) = true ∧
                           rn.output.coordinator.up = some d ∧
                           d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput rn.input Lsite ∧
                           tail.reception = some (Lsite,
                             ReferenceActivePhysicalStep.receiveUp
                               (ReferenceActivePhysicalStep.prepare rn.input) Lsite) ∧
                           (ReferenceActivePhysicalStep.receiveUp
                             (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result ≠ .invalid ∧
                           Lsite.pending = pre.pending ∧ Lsite.sigma = s + 1 ∧
                           Lsite.cursor = rn.input.time.val + 1 ∧
                           Lsite.cutoff ≤ Lsite.cursor ∧
                           d.input.upDecoderBank = rn.input.state.upDecoderBank ∧
                           d.input.time = rn.input.time ∧
                           d.input.affineSample = (rn.input.row.2 rn.input.time).2
                             (1, CoordinatorUpMeasurability.selectedChannelFollower
                               (rn.input.row.2 rn.input.time)) ∧
                           d.input.ownObservation =
                             (ReferenceActivePhysicalStep.prepare rn.input).feedback.feedback
                               (ActiveRoundActions.coordinator p.two_le_m) ∧
                           d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
                           d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
                           d.expected = ReferenceActivePhysicalStep.upExpected
                             (ReferenceActivePhysicalStep.prepare rn.input) ∧
                           d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
                           d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
                           d.rawMatches = decide (d.raw = d.expected) ∧
                           ((ReferenceActivePhysicalStep.receiveUp
                             (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result =
                               .success (received, bank) ∨
                            (ReferenceActivePhysicalStep.receiveUp
                             (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result =
                               .rejected (received, bank)) ∧
                           CoordinatorCollectionLedger.finishRound received = .success finished ∧
                           CoordinatorPhaseClock.finishRound p rate.eta.val rn.input.time
                             tail.started.clock finished.pending rn.input.row = .ok clockFinished ∧
                           (d.input.ownObservation.val = 0 →
                             d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧
                             d.raw = none) ∧
                           (∀ _hslot : PublicDiscreteDraws.slotDraw
                               (rn.input.row.2 rn.input.time).1 = PublicDiscreteDraws.upSlot,
                             ∀ _hselected : PublicDiscreteDraws.selectedFollowerDraw
                               p.two_le_m p.m_lt_K (rn.input.row.2 rn.input.time).1 = i,
                             (¬ i ∈ A.toFinset →
                               d.input.selectedFollower = i ∧
                               CoordinatorUpReception.receptionGate d.input ∧
                               (CoordinatorUpReception.roundInput d.input).selected = true ∧
                               (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                               (∀ U : OrdinaryMessageCodec.UpRecord
                                 (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                                 U.val.sigma = s + 1 →
                                 CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true)) ∧
                             (i ∈ A.toFinset →
                               d.input.selectedFollower = i ∧
                               ¬ CoordinatorUpReception.receptionGate d.input ∧
                               (CoordinatorUpReception.roundInput d.input).selected = false ∧
                               (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                               CoordinatorUpReception.decoderTransition d.input =
                                 (d.input.upDecoderBank d.input.selectedFollower, none)))))))) := by
  classical
  intro x0 b0 s I hactive E W w B u
  -- The sole seed, cutoff and original payload are obtained once, before all queries.
  have hseed :=
    ReferenceFirstCollectionLateDownReplyHistory.actual_first_collection_late_down_reply_history
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
      hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, hqueries⟩ := hseed
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
    hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  -- The retained-DOWN query is delegated to L unchanged.
  have hquery := hqueries k i M hretained
  rcases hquery with ⟨logged, hq⟩
  rcases hq with ⟨cutD, hq⟩
  rcases hq with ⟨after, hq⟩
  rcases hq with ⟨raw, hq⟩
  rcases hq with ⟨scan, hq⟩
  rcases hq with ⟨replayedRegisters, hq⟩
  rcases hq with ⟨lastService, hq⟩
  rcases hq with ⟨hinput, hq⟩
  rcases hq with ⟨hdown, hq⟩
  rcases hq with ⟨haccepted, hq⟩
  rcases hq with ⟨hM, hq⟩
  rcases hq with ⟨hMsigma, hq⟩
  rcases hq with ⟨hMq, hq⟩
  rcases hq with ⟨hdownStart, hq⟩
  rcases hq with ⟨hscan, hq⟩
  rcases hq with ⟨hafterStatus, hq⟩
  rcases hq with ⟨hafterLastDown, hq⟩
  rcases hq with ⟨hRecovery, hQueueAndNext⟩
  rcases hRecovery with ⟨hjcount, n0, hn0, hn0eq, hchecked⟩
  rcases hQueueAndNext with
    ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
      hreplyAfter, hbranches⟩
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
  refine ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
    hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan,
    hafterStatus, hafterLastDown, ?_, ?_⟩
  · exact ⟨hjcount, n0, hn0, hn0eq, hchecked⟩
  · refine ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
      hreplyAfter, ?_⟩
    rcases hbranches with ⟨hfollowersDagger, hcoordDaggerOrCollection⟩ |
        ⟨out, memory, hnextOrdinary, houtStatus, houtReply, hlastOut,
          houtS, houtDelta, houtBacklog, houtStart, hcoordBranch⟩
    · exact Or.inl ⟨hfollowersDagger, hcoordDaggerOrCollection⟩
    · rcases hcoordBranch with hcoordDagger |
        ⟨l0, saved0, hcoordCollection, hlateData⟩
      · exact Or.inr ⟨out, memory, hnextOrdinary, houtStatus, houtReply,
          hlastOut, houtS, houtDelta, houtBacklog, houtStart, Or.inl hcoordDagger⟩
      · refine Or.inr ⟨out, memory, hnextOrdinary, houtStatus, houtReply,
          hlastOut, houtS, houtDelta, houtBacklog, houtStart, ?_⟩
        refine Or.inr ⟨l0, saved0, hcoordCollection, ?_⟩
        let b := j + 1
        let Wlate := (E.records.drop b).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
        rcases hlateData with
          ⟨hb, hbspan, hcoordAtB, hfollowerAtB, hWlate, htimeLookup,
            hprefixFacts, hnoApplied, hboundary, hOffers, hPairOffers⟩
        have hgetWindow : E.records[j]? = some r := by
          simpa only [j, r] using (hwindow k).1
        have hRunEq : E =
            ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
              hspan hactive := by
          dsimp only [E, I, s, b0, x0, hactive,
            ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
        have hjlt : j < count := by
          dsimp only [j]
          exact hjcount
        have hendpoint := run_prefix_endpoints I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
          hspan hactive j hjlt
        have hrecordIndex : j < E.records.length := by
          have h := (List.getElem?_eq_some_iff.mp hgetWindow).1
          simpa only [E] using h
        have hrecordEq : E.records[j]'hrecordIndex = r :=
          (List.getElem?_eq_some_iff.mp hgetWindow).2
        have hstateB :
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              hbspan hactive).finalState = r.output.next := by
          have hnext := hendpoint.2
          have hcount :
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive).records.length = count :=
            ReferenceActivePhysicalHorizon.run_record_count I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
              hspan hactive
          have hrecordEq' :
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive).records[j]'(by rw [hcount]; exact hjlt) = r := by
            have hgetFull :
                (ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                  hspan hactive).records[j]? = some r := by
              rw [← hRunEq]
              exact hgetWindow
            exact (List.getElem?_eq_some_iff.mp hgetFull).2
          rw [hrecordEq'] at hnext
          simpa only [b] using hnext
        have hstepNext :
            (ReferenceActivePhysicalStep.step r.input).next.coordinator =
              .collection P0 l0 saved0 := by
          rw [← r.output_eq]
          exact hcoordCollection
        obtain ⟨tail0, htail0, _hframePending0, hframeSigma0⟩ :=
          ReferenceCollectionPhaseHistory.step_collection_frame r.input P0 l0 saved0 hstepNext
        have htailSigma0 := executedTail_sigma htail0
        have hpayload0 := actual_collection_output_payload r P0 l0 saved0
          hcoordCollection tail0 htail0
        have hl0sigma : l0.sigma = s + 1 := by
          calc
            l0.sigma = tail0.ledger.sigma := hframeSigma0
            _ = tail0.payload.sigma.val + 1 := htailSigma0
            _ = P0.sigma.val + 1 := by rw [hpayload0]
            _ = s + 1 := by rw [hP0sigma]
        have hfirst : I.coordinator = .first :=
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).2
        have hhistory := ReferenceCollectionPhaseHistory.run_history
          I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          s b hbspan hactive hfirst
        have hpendingExact := hhistory P0 l0 saved0 hcoordAtB
        -- An absent focal label would have an actual same-start UP acceptance
        -- at q ≤ j. Its sender start cannot precede the late DOWN's strict start.
        have hiPending : i ∈ l0.pending := by
          classical
          by_contra hnot
          rcases hpendingExact with
            ⟨before, cutoff, during, hrecords, _hcut, _hlater, _hduring,
              hpending, _hnodup, haccepted⟩
          have hiNotDiff : i ∉ Finset.univ \
              (ReferenceCollectionPhaseHistory.acceptedLabels (cutoff :: during)).toFinset := by
            rw [← hpending]
            exact hnot
          have hiAccepted : i ∈
              (ReferenceCollectionPhaseHistory.acceptedLabels (cutoff :: during)).toFinset := by
            by_contra hnotAccepted
            exact hiNotDiff (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnotAccepted⟩)
          have hiAcceptedList : i ∈
              ReferenceCollectionPhaseHistory.acceptedLabels (cutoff :: during) :=
            List.mem_toFinset.mp hiAccepted
          obtain ⟨q, hqmem, hqaccepted⟩ := List.mem_filterMap.mp hiAcceptedList
          have hqdata := haccepted q hqmem i hqaccepted
          rcases hqdata with ⟨message, hAcceptedUp, hmessageSigma⟩
          have hcurrent := ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice
            hAcceptedUp
          rcases hcurrent with
            ⟨sender, upState, upMemory, hsender, hsenderIndex, hsenderOrdinary,
              _hUnoccupied, _hOffer, hmessageStart, _hstarted, _hS, _hDelta,
              _hBacklog, _hPriorDown, _hPositive, _hslot⟩
          have hqInC0 : q ∈
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                hbspan hactive).records := by
            rw [hrecords]
            exact List.mem_append.mpr (Or.inr hqmem)
          have hprefixRecords :
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                hbspan hactive).records = E.records.take b := by
            dsimp only [E]
            exact (run_prefix_records I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
              hspan hactive b (by dsimp only [b]; exact hb)).symm
          obtain ⟨qIndex, hqIndexLt, hqIndexEq⟩ := List.mem_iff_getElem.mp hqInC0
          have hqIndexBound : qIndex < b := by
            simpa only [ReferenceActivePhysicalHorizon.run_record_count] using hqIndexLt
          have hjPrefix : j <
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                hbspan hactive).records.length := by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            dsimp only [b]
            omega
          have hsenderChoice :
              (ReferenceFollowerFixedReply.actualChoice q i).configuration =
                .ordinary upState upMemory := by
            have hprepEq : q.output.preparation =
                ReferenceActivePhysicalStep.prepare q.input := by
              rw [q.output_eq]
              rfl
            simpa [ReferenceFollowerFixedReply.actualChoice, hprepEq,
              hsenderIndex, hsender] using hsenderOrdinary
          have hqueryChoice :
              (ReferenceFollowerFixedReply.actualChoice
                ((ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                  hbspan hactive).records[qIndex]'hqIndexLt) i).configuration =
                    .ordinary upState upMemory := by
            simpa only [hqIndexEq] using hsenderChoice
          have hretainedApplied :=
            ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretained
          obtain ⟨downChoice, downMemory, hdownChoice, hstrict, hdownStart⟩ :=
            ReferenceFollowerReplyChronology.record_appliedDown_strict r i M.val.sigma
              hretainedApplied out memory hnextOrdinary
          have hrightChoice :
              (ReferenceFollowerFixedReply.actualChoice
                ((ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                  hbspan hactive).records[j]'hjPrefix) i).configuration =
                    .ordinary downChoice downMemory := by
            simpa only [hprefixRecords, List.getElem_take, hrecordEq] using hdownChoice
          have hqLe : qIndex ≤ j := by
            dsimp only [b] at hqIndexBound
            omega
          have hmono := ReferenceFollowerReplyChronology.run_acceptedStart_mono
            (initial := I) (rows := source.1.2)
            (selected := ActualInitializationPhysicalStep.selectedRowIndex p source)
            (rewards := rewards) (start := s) (count := b) (hspan := hbspan)
            (hmode := hactive) i ⟨qIndex, hqIndexLt⟩ ⟨j, hjPrefix⟩ hqLe
            upState downChoice upMemory downMemory hqueryChoice hrightChoice
          have hleftStart : ReferencePrelaunchFollower.acceptedStart upState = s + 1 := by
            calc
              ReferencePrelaunchFollower.acceptedStart upState = message.val.sigma :=
                hmessageStart.symm
              _ = l0.sigma := hmessageSigma
              _ = s + 1 := hl0sigma
          have hrightStart : ReferencePrelaunchFollower.acceptedStart downChoice < s + 1 := by
            calc
              ReferencePrelaunchFollower.acceptedStart downChoice < M.val.sigma := hstrict
              _ = s + 1 := hMsigma
          omega
        refine ⟨hl0sigma, hiPending, hb, hbspan, hstateB, hWlate, htimeLookup, ?_⟩
        have hElenTop : E.records.length = count := by
          rw [hRunEq]
          exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
            hspan hactive
        have hstartSpan : s + count ≤ p.T := by
          dsimp only [s, b0, x0]
          exact hspan
        have hWlateBound : Wlate.length ≤ count - b := by
          calc
            Wlate.length ≤ (E.records.drop b).length :=
              takeWhile_length_le
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
                (E.records.drop b)
            _ = E.records.length - b := List.length_drop
            _ = count - b := by rw [hElenTop]
        let C := fun (h : ℕ) (hh : h ≤ Wlate.length) =>
          ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + h)
            (by
              have hcount' : b + h ≤ count := by omega
              have hspan' : s + (b + h) ≤ p.T := by omega
              exact hspan') hactive
        have hMovement : ∀ h (hh : h ≤ Wlate.length),
            (C h hh).finalState.coordinator = .dagger ∨
              ∃ (moving : ReferenceActivePhysicalStep.Ledger rate)
                (proposal : Option (Fin p.T × Bool)),
                (C h hh).finalState.coordinator = .collection P0 moving proposal ∧
                moving.sigma = s + 1 ∧
                moving.pending = l0.pending \
                  (ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take h)).toFinset ∧
                (i ∈ moving.pending ↔
                  i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take h)).toFinset) := by
          intro h hh
          induction h with
          | zero =>
              have hC0 : (C 0 hh).finalState = r.output.next := by
                dsimp only [C, b]
                simpa using hstateB
              have hcoord0 : (C 0 hh).finalState.coordinator = .collection P0 l0 saved0 := by
                rw [hC0]
                exact hcoordCollection
              right
              refine ⟨l0, saved0, hcoord0, hl0sigma, ?_, ?_⟩
              · simp [ReferenceCollectionPhaseHistory.acceptedLabels]
              · simp [ReferenceCollectionPhaseHistory.acceptedLabels, hiPending]
          | succ h ih =>
              have hhPrev : h ≤ Wlate.length := by omega
              have hhNext : h + 1 ≤ Wlate.length := by omega
              have hlt : h < Wlate.length := by omega
              have hlookup := (htimeLookup h hlt).1
              have hrecordLt : b + h < E.records.length :=
                (List.getElem?_eq_some_iff.mp hlookup).1
              have hrecordEq : E.records[b + h]'hrecordLt = Wlate[h]'hlt :=
                (List.getElem?_eq_some_iff.mp hlookup).2
              have hfullRecordsEq :
                  E.records =
                    (ReferenceActivePhysicalHorizon.run I source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                      hspan hactive).records :=
                congrArg (fun execution : ReferenceActivePhysicalHorizon.Run I => execution.records)
                  hRunEq
              have hfullLt : b + h < count := by
                rw [← hElenTop]
                exact hrecordLt
              have hfullGet :
                  (ReferenceActivePhysicalHorizon.run I source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                    hspan hactive).records[b + h]? = some Wlate[h] := by
                have hgetTransfer := congrArg
                  (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate)) => records[b + h]?) hfullRecordsEq
                exact hgetTransfer.symm.trans hlookup
              have hfullRecordEq :
                  (ReferenceActivePhysicalHorizon.run I source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                    hspan hactive).records[b + h]'(by
                      rw [ReferenceActivePhysicalHorizon.run_record_count]
                      exact hfullLt) = Wlate[h]'hlt :=
                (List.getElem?_eq_some_iff.mp hfullGet).2
              have hendpoints := run_prefix_endpoints I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive (b + h) hfullLt
              have hinputEndpoint :
                  (C h hhPrev).finalState = (Wlate[h]'hlt).input.state := by
                have h := hendpoints.1
                rw [hfullRecordEq] at h
                simpa only [C] using h
              have hnextEndpoint :
                  (C (h + 1) hhNext).finalState = (Wlate[h]'hlt).output.next := by
                have h := hendpoints.2
                rw [hfullRecordEq] at h
                simpa only [C, Nat.add_assoc] using h
              rcases ih hhPrev with hprevDagger |
                ⟨pre, preSaved, hprevCollection, hprevSigma, hprevPending, _hprevI⟩
              · have hinputDagger : (Wlate[h]'hlt).input.state.coordinator = .dagger := by
                  exact (congrArg
                    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                    hinputEndpoint).symm.trans hprevDagger
                have hstepDagger := ReferenceActivePhysicalStep.step_coordinator_dagger
                  (Wlate[h]'hlt).input hinputDagger
                have hnextDagger : (Wlate[h]'hlt).output.next.coordinator = .dagger := by
                  simpa only [(Wlate[h]'hlt).output_eq] using hstepDagger.1
                left
                exact (congrArg
                  (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                  hnextEndpoint).trans hnextDagger
              · have hinputCollection :
                    (Wlate[h]'hlt).input.state.coordinator = .collection P0 pre preSaved :=
                  (congrArg
                    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                    hinputEndpoint).symm.trans hprevCollection
                have hnextBranch :
                    (Wlate[h]'hlt).output.next.coordinator = .dagger ∨
                      ∃ moving proposal,
                        (Wlate[h]'hlt).output.next.coordinator = .collection P0 moving proposal := by
                  have hfacts := (hprefixFacts (h + 1) hhNext).1
                  have hfacts' :
                      (C (h + 1) hhNext).finalState.coordinator = .dagger ∨
                        ∃ moving proposal,
                          (C (h + 1) hhNext).finalState.coordinator =
                            .collection P0 moving proposal := by
                    simpa only [C] using hfacts
                  rw [hnextEndpoint] at hfacts'
                  exact hfacts'
                rcases hnextBranch with hnextDagger | ⟨moving, proposal, hnextCollection⟩
                · left
                  exact (congrArg
                    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                    hnextEndpoint).trans hnextDagger
                · have hstepCollection :
                      (ReferenceActivePhysicalStep.step (Wlate[h]'hlt).input).next.coordinator =
                        .collection P0 moving proposal := by
                    rw [← (Wlate[h]'hlt).output_eq]
                    exact hnextCollection
                  obtain ⟨tail, htail, hpendFrame, hsigmaFrame⟩ :=
                    ReferenceCollectionPhaseHistory.step_collection_frame
                      (Wlate[h]'hlt).input P0 moving proposal hstepCollection
                  have hcutFalse := cutoffChosen_false_of_collection
                    (Wlate[h]'hlt).input P0 pre preSaved hinputCollection
                  obtain ⟨_, horigin⟩ :=
                    ReferenceCollectionPhaseHistory.executedTail_origin htail
                  have htailLedger : tail.ledger = pre := by
                    rcases horigin with ⟨hcut, _⟩ |
                      ⟨_, oldPayload, oldLedger, oldSaved, hstateOrigin, hledgerOrigin⟩
                    · rw [hcutFalse] at hcut
                      cases hcut
                    · have hfields :=
                        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
                          (hstateOrigin.symm.trans hinputCollection)
                      exact hledgerOrigin.trans hfields.2.1
                  have hlabelsSucc := acceptedLabels_take_succ Wlate h hlt
                  have hnewPending :
                      moving.pending = l0.pending \
                        (ReferenceCollectionPhaseHistory.acceptedLabels
                          (Wlate.take (h + 1))).toFinset := by
                    calc
                      moving.pending = ReferenceCollectionPhaseHistory.eraseEvent
                          tail.ledger.pending
                          (ReferenceCollectionPhaseHistory.acceptedLabel
                            (Wlate[h]'hlt).input) := hpendFrame
                      _ = ReferenceCollectionPhaseHistory.eraseEvent pre.pending
                            (ReferenceCollectionPhaseHistory.acceptedLabel
                              (Wlate[h]'hlt).input) := by rw [htailLedger]
                      _ = ReferenceCollectionPhaseHistory.eraseEvent
                            (l0.pending \
                              (ReferenceCollectionPhaseHistory.acceptedLabels
                                (Wlate.take h)).toFinset)
                            (ReferenceCollectionPhaseHistory.acceptedLabel
                              (Wlate[h]'hlt).input) := by rw [hprevPending]
                      _ = l0.pending \
                            (ReferenceCollectionPhaseHistory.acceptedLabels
                              (Wlate.take (h + 1))).toFinset := by
                        rw [eraseEvent_relative, hlabelsSucc]
                  have hnewSigma : moving.sigma = s + 1 := by
                    calc
                      moving.sigma = tail.ledger.sigma := hsigmaFrame
                      _ = pre.sigma := by rw [htailLedger]
                      _ = s + 1 := hprevSigma
                  have hnewFocal :
                      (i ∈ moving.pending ↔ i ∉
                        (ReferenceCollectionPhaseHistory.acceptedLabels
                          (Wlate.take (h + 1))).toFinset) := by
                    rw [hnewPending]
                    simp [Finset.mem_sdiff, hiPending]
                  right
                  exact ⟨moving, proposal, (congrArg
                    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                    hnextEndpoint).trans hnextCollection,
                    hnewSigma, hnewPending, hnewFocal⟩
        have hReceiver : ∀ n (_hn : n < Wlate.length),
            let A := ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take n)
            ∃ hrecord : b + n < E.records.length,
              let rn := E.records[b + n]'hrecord
              rn.output.next.coordinator ≠ .dagger →
              ∃ (tail : ReferenceCollectionPhaseHistory.Tail rn.input)
                (recording : CoordinatorRecordingOperation.Output p)
                (pre : ReferenceActivePhysicalStep.Ledger rate)
                (preSaved : Option (Fin p.T × Bool))
                (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                (received : ReferenceActivePhysicalStep.Ledger rate)
                (bank : CoordinatorUpReception.UpDecoderBank p)
                (finished : ReferenceActivePhysicalStep.Ledger rate)
                (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                rn.input.state.coordinator = .collection P0 pre preSaved ∧
                pre.pending = l0.pending \ A.toFinset ∧ pre.sigma = s + 1 ∧
                ReferenceCollectionPhaseHistory.executedTail rn.input = some tail ∧
                tail.ledger = pre ∧
                CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.collectionRecordingInput
                    (ReferenceActivePhysicalStep.prepare rn.input) tail.payload tail.started
                    tail.weights) = some recording ∧
                CoordinatorCollectionLedger.startRound tail.ledger (rn.input.time.val + 1)
                  (ReferenceActivePhysicalStep.collectionEnabled tail.ledger rn.input.time)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                    .success Lsite ∧
                ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := rn.input) = some Lsite ∧
                CoordinatorUpReception.receptionInputCheck
                  (ReferenceCoordinatorUpPhysicalCall.actualUpInput rn.input Lsite) = true ∧
                rn.output.coordinator.up = some d ∧
                d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput rn.input Lsite ∧
                tail.reception = some (Lsite,
                  ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare rn.input) Lsite) ∧
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result ≠ .invalid ∧
                Lsite.pending = pre.pending ∧ Lsite.sigma = s + 1 ∧
                Lsite.cursor = rn.input.time.val + 1 ∧ Lsite.cutoff ≤ Lsite.cursor ∧
                d.input.upDecoderBank = rn.input.state.upDecoderBank ∧
                d.input.time = rn.input.time ∧
                d.input.affineSample = (rn.input.row.2 rn.input.time).2
                  (1, CoordinatorUpMeasurability.selectedChannelFollower
                    (rn.input.row.2 rn.input.time)) ∧
                d.input.ownObservation =
                  (ReferenceActivePhysicalStep.prepare rn.input).feedback.feedback
                    (ActiveRoundActions.coordinator p.two_le_m) ∧
                d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
                d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
                d.expected = ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare rn.input) ∧
                d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
                d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
                d.rawMatches = decide (d.raw = d.expected) ∧
                ((ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result =
                    .success (received, bank) ∨
                 (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare rn.input) Lsite).result =
                    .rejected (received, bank)) ∧
                CoordinatorCollectionLedger.finishRound received = .success finished ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val rn.input.time tail.started.clock
                  finished.pending rn.input.row = .ok clockFinished ∧
                (d.input.ownObservation.val = 0 →
                  d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧
                  d.raw = none) ∧
                (∀ _hslot : PublicDiscreteDraws.slotDraw
                    (rn.input.row.2 rn.input.time).1 = PublicDiscreteDraws.upSlot,
                  ∀ _hselected : PublicDiscreteDraws.selectedFollowerDraw
                    p.two_le_m p.m_lt_K (rn.input.row.2 rn.input.time).1 = i,
                  (¬ i ∈ A.toFinset →
                    d.input.selectedFollower = i ∧
                    CoordinatorUpReception.receptionGate d.input ∧
                    (CoordinatorUpReception.roundInput d.input).selected = true ∧
                    (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                    (∀ U : OrdinaryMessageCodec.UpRecord
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                      U.val.sigma = s + 1 →
                      CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true)) ∧
                  (i ∈ A.toFinset →
                    d.input.selectedFollower = i ∧
                    ¬ CoordinatorUpReception.receptionGate d.input ∧
                    (CoordinatorUpReception.roundInput d.input).selected = false ∧
                    (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                    CoordinatorUpReception.decoderTransition d.input =
                      (d.input.upDecoderBank d.input.selectedFollower, none))) := by
          intro n hn
          let A := ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take n)
          have hlookup := (htimeLookup n hn).1
          have hrecordLt : b + n < E.records.length :=
            (List.getElem?_eq_some_iff.mp hlookup).1
          have hrecordEq : E.records[b + n]'hrecordLt = Wlate[n]'hn :=
            (List.getElem?_eq_some_iff.mp hlookup).2
          refine ⟨hrecordLt, ?_⟩
          dsimp only
          rw [hrecordEq]
          intro hnotDagger
          have hfullLt : b + n < count := by
            rw [← hElenTop]
            exact hrecordLt
          have hfullRecordsEq : E.records =
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive).records :=
            congrArg (fun execution : ReferenceActivePhysicalHorizon.Run I => execution.records)
              hRunEq
          have hfullGet :
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive).records[b + n]? = some Wlate[n] := by
            have hgetTransfer := congrArg
              (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate)) => records[b + n]?) hfullRecordsEq
            exact hgetTransfer.symm.trans hlookup
          have hfullRecordEq :
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
                hspan hactive).records[b + n]'(by
                  rw [ReferenceActivePhysicalHorizon.run_record_count]
                  exact hfullLt) = Wlate[n]'hn :=
            (List.getElem?_eq_some_iff.mp hfullGet).2
          have hendpoints := run_prefix_endpoints I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
            hspan hactive (b + n) hfullLt
          have hinputEndpoint :
              (C n (Nat.le_of_lt hn)).finalState = (Wlate[n]'hn).input.state := by
            have h := hendpoints.1
            rw [hfullRecordEq] at h
            simpa only [C] using h
          have hnextEndpoint :
              (C (n + 1) (by omega)).finalState = (Wlate[n]'hn).output.next := by
            have h := hendpoints.2
            rw [hfullRecordEq] at h
            simpa only [C, Nat.add_assoc] using h
          rcases hMovement n (Nat.le_of_lt hn) with hcurrentDagger |
            ⟨pre, preSaved, hcurrentCollection, hpreSigma, hprePending, _hcurrentI⟩
          · have hinputDagger : (Wlate[n]'hn).input.state.coordinator = .dagger :=
              (congrArg
                (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
                hinputEndpoint).symm.trans hcurrentDagger
            have hstepDagger := ReferenceActivePhysicalStep.step_coordinator_dagger
              (Wlate[n]'hn).input hinputDagger
            have hnextDagger : (Wlate[n]'hn).output.next.coordinator = .dagger := by
              rw [(Wlate[n]'hn).output_eq]
              exact hstepDagger.1
            exact (hnotDagger hnextDagger).elim
          have hinputCollection :
              (Wlate[n]'hn).input.state.coordinator = .collection P0 pre preSaved := by
            exact (congrArg
              (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator)
              hinputEndpoint).symm.trans hcurrentCollection
          have hnextCollection :
              (Wlate[n]'hn).output.next.coordinator = .dagger ∨
                ∃ moving proposal,
                  (Wlate[n]'hn).output.next.coordinator = .collection P0 moving proposal := by
            have hfacts := (hprefixFacts (n + 1) (Nat.succ_le_of_lt hn)).1
            have hfacts' :
                (C (n + 1) (by omega)).finalState.coordinator = .dagger ∨
                  ∃ moving proposal,
                    (C (n + 1) (by omega)).finalState.coordinator =
                      .collection P0 moving proposal := by
              simpa only [C] using hfacts
            rw [hnextEndpoint] at hfacts'
            exact hfacts'
          rcases hnextCollection with hnextDagger |
            ⟨outLedger, outSaved, hnextCollection⟩
          · exact (hnotDagger hnextDagger).elim
          have hstepNext :
              (ReferenceActivePhysicalStep.step (Wlate[n]'hn).input).next.coordinator =
                .collection P0 outLedger outSaved := by
            rw [← (Wlate[n]'hn).output_eq]
            exact hnextCollection
          obtain ⟨tail, htail, hframePending, hframeSigma⟩ :=
            ReferenceCollectionPhaseHistory.step_collection_frame
              (Wlate[n]'hn).input P0 outLedger outSaved hstepNext
          have hcutFalse := cutoffChosen_false_of_collection
            (Wlate[n]'hn).input P0 pre preSaved hinputCollection
          obtain ⟨_, horigin⟩ :=
            ReferenceCollectionPhaseHistory.executedTail_origin htail
          have htailLedger : tail.ledger = pre := by
            rcases horigin with ⟨hcut, _⟩ |
              ⟨_, _, _, _, hstateOrigin, hledgerOrigin⟩
            · rw [hcutFalse] at hcut
              cases hcut
            · have hfields :=
                ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
                  (hstateOrigin.symm.trans hinputCollection)
              exact hledgerOrigin.trans hfields.2.1
          obtain ⟨recording, Lsite, d, hrecording, hstart, hsite, hcheck,
            hup, hinputEq, htailReception, hnoninvalid,
            received, bank, finished, clockFinished, hresult, hfinish, hclock,
            hdecoder, hraw, hparsed, hlocallyAccepted, hexpected, hrawMatches, hbank, htime,
            hsample, hobservation, _hwrongUnique⟩ :=
            ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver
              (Wlate[n]'hn) P0 pre preSaved tail hinputCollection htail hnotDagger
          have hledgerDomain :=
            (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp
              (by rw [hinputEq]; exact hcheck)
          rcases CoordinatorUpReception.receptionInputDomain_parts d.input hledgerDomain with
            ⟨_, _, _, _, hcutoffCursor, _, hcursorSource, _⟩
          have hcandidate := ReferenceActivePhysicalStep.collection_started_candidate
            tail.ledger Lsite (Wlate[n]'hn).input.time
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
          have hsiteFrame : Lsite.pending = pre.pending ∧
              Lsite.sigma = pre.sigma ∧
              Lsite.cursor = (Wlate[n]'hn).input.time.val + 1 := by
            rw [hcandidate, htailLedger]
            simp [CoordinatorCollectionLedger.startRoundCandidate,
              CoordinatorCollectionLedger.sourceRound]
          have hsiteSigma : Lsite.sigma = s + 1 := hsiteFrame.2.1.trans hpreSigma
          have hsitePending : Lsite.pending = pre.pending := hsiteFrame.1
          have hsiteCutoff : Lsite.cutoff ≤ Lsite.cursor := by
            rw [hinputEq, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
              ReferenceActivePhysicalStep.upInputs,
              ReferenceUpReception.receptionInputAtRow,
              CoordinatorUpMeasurability.receptionInputAtRow] at hcutoffCursor
            exact hcutoffCursor
          have hzeroResult : d.input.ownObservation.val = 0 →
              d.decoderAfter = d.input.upDecoderBank d.input.selectedFollower ∧ d.raw = none := by
            intro hzero
            have hnotEligible :
                ¬ AffineBatchDecoder.eligible
                  ((CoordinatorUpReception.traceAt d.input) d.input.time) := by
              intro heligible
              have hpositive := heligible.2.2
              change 0 < CoordinatorUpReception.roundedObservationValue p
                d.input.ownObservation at hpositive
              rw [CoordinatorUpReception.roundedObservationValue_zero p
                d.input.ownObservation hzero] at hpositive
              exact (lt_irrefl 0) hpositive
            have htransition := CoordinatorUpReception.decoderTransition_ineligible
              d.input hledgerDomain hnotEligible
            rw [hdecoder, hraw, htransition]
            exact ⟨rfl, rfl⟩
          refine ⟨tail, recording, pre, preSaved, Lsite, d,
            received, bank, finished, clockFinished,
            hinputCollection, hprePending, hpreSigma, htail, htailLedger,
            hrecording, hstart, hsite, hcheck, hup, hinputEq, htailReception,
            hnoninvalid, hsitePending, hsiteSigma, hsiteFrame.2.2,
            hsiteCutoff, hbank, htime, ?_, hobservation,
            hdecoder, hraw, hexpected, hparsed, hlocallyAccepted, hrawMatches,
            ?_⟩
          · exact hsample
          · refine ⟨hresult, hfinish, hclock, hzeroResult, ?_⟩
            intro hslot hselected
            have hinputLedger : d.input.ledger = Lsite := by
              rw [hinputEq]
              rfl
            have hinputDraw : d.input.selectedFollower = i := by
              rw [hinputEq]
              simp only [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
                ReferenceActivePhysicalStep.upInputs,
                ReferenceUpReception.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtControl_selectedFollower]
              exact hselected
            have hinputSlot : d.input.slot = PublicDiscreteDraws.upSlot := by
              simpa [hinputEq, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
                ReferenceActivePhysicalStep.upInputs,
                ReferenceUpReception.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtControl_slot] using hslot
            have hcutoffSource :
                Lsite.cutoff ≤ CoordinatorCollectionLedger.sourceRound d.input.time := by
              rw [htime, CoordinatorCollectionLedger.sourceRound,
                ← hsiteFrame.2.2]
              exact hsiteCutoff
            constructor
            · intro hnotAccepted
              have hpreFocal : i ∈ pre.pending := by
                rw [hprePending]
                exact Finset.mem_sdiff.mpr ⟨hiPending, hnotAccepted⟩
              have hiSitePending : i ∈ Lsite.pending := by
                rw [hsitePending]
                exact hpreFocal
              have hgate : CoordinatorUpReception.receptionGate d.input := by
                unfold CoordinatorUpReception.receptionGate
                rw [hinputLedger]
                rw [hinputDraw]
                exact ⟨hcutoffSource, hinputSlot, hiSitePending⟩
              refine ⟨hinputDraw, hgate,
                (CoordinatorUpReception.roundInput_selected_iff_gate d.input).2 hgate,
                ?_, ?_⟩
              · simp [CoordinatorUpReception.roundInput]
              · intro U hUsigma
                simp [CoordinatorCollectionLedger.acceptUpCheck, hsiteCutoff,
                  hiSitePending, hsiteSigma, hUsigma]
            · intro haccepted
              have hnotSitePending : i ∉ Lsite.pending := by
                rw [hsitePending, hprePending, Finset.mem_sdiff]
                intro hm
                exact hm.2 haccepted
              have hnotGate : ¬ CoordinatorUpReception.receptionGate d.input := by
                intro hg
                have hiMember : d.input.selectedFollower ∈ d.input.ledger.pending :=
                  hg.2.2
                rw [hinputLedger, hinputDraw] at hiMember
                exact hnotSitePending hiMember
              have hroundFalse :
                  (CoordinatorUpReception.roundInput d.input).selected = false := by
                cases hs : (CoordinatorUpReception.roundInput d.input).selected with
                | false => rfl
                | true =>
                    exact (hnotGate
                      ((CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp hs)).elim
              have hnotEligible :
                  ¬ AffineBatchDecoder.eligible
                    ((CoordinatorUpReception.traceAt d.input) d.input.time) := by
                intro heligible
                have hselectedTrue := heligible.1
                change (CoordinatorUpReception.roundInput d.input).selected = true at hselectedTrue
                rw [hroundFalse] at hselectedTrue
                cases hselectedTrue
              have htransition := CoordinatorUpReception.decoderTransition_ineligible
                d.input hledgerDomain hnotEligible
              exact ⟨hinputDraw, hnotGate, hroundFalse,
                by simp [CoordinatorUpReception.roundInput], htransition⟩
        exact ⟨hMovement, hReceiver⟩

end Bandits.Support.ReferenceFirstCollectionLateUpReceiverEligibility

end
