/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCutoffUpReplyInterval
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile

/-!
# Cutoff collection pending trajectory

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-88,105-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,164-177,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

From the actual cutoff reset, this producer tracks the original run's moving
collection ledger through its non-later-chosen prefix. Its exact pending set
removes only labels from successful filtered UP receptions, and its sigma and
cutoff fields remain fixed. The canonical UP word is chosen once before the
prefix-length quantifier. Dagger endpoints remain explicit; no receiver query,
acceptance, delivery, or manuscript-closure claim is made.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionUpPendingInterval

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

private theorem acceptedLabels_append (xs ys : List (Record p rate)) :
    ReferenceCollectionPhaseHistory.acceptedLabels (xs ++ ys) =
      ReferenceCollectionPhaseHistory.acceptedLabels xs ++
        ReferenceCollectionPhaseHistory.acceptedLabels ys := by
  simp [ReferenceCollectionPhaseHistory.acceptedLabels, List.filterMap_append]

private theorem connected_endpoint_unique
    {initial left right : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hl : ReferenceActivePhysicalHorizon.Connected initial records left)
    (hr : ReferenceActivePhysicalHorizon.Connected initial records right) :
    left = right := by
  induction records generalizing initial left right with
  | nil =>
      change left = initial at hl
      change right = initial at hr
      exact hl.trans hr.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hl hr
      exact ih hl.2 hr.2

private def runRecordAt (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start index
    (by omega) active
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
    active prefixRun ⟨start + index, by omega, by omega⟩
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

private theorem run_successor_equations (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).finalState = (runRecordAt initial rows selected rewards start index hspan active).output.next ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) active).records ++
        [runRecordAt initial rows selected rewards start index hspan active] := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  have heq := ReferenceActivePhysicalHorizon.foldRound_equations initial rows selected rewards start
    active (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) active)
    ⟨start + index, by omega, by omega⟩
  simpa [runRecordAt, ReferenceActivePhysicalHorizon.roundInputAt] using heq

private theorem run_prefix_records (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active).records := by
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
        rw [(run_successor_equations initial rows selected rewards start total hspan active).2,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn')]
        exact ih (by omega) hn'

private theorem run_prefix_endpoints (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n (by omega)
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

private theorem getElem_takeWhile_eq {α : Type} (pred : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile pred).length) :
    (xs.takeWhile pred)[k] = xs[k]'(by
      exact Nat.lt_of_lt_of_le hk (takeWhile_length_le pred xs)) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hp : pred head with
      | false => simp [List.takeWhile, hp] at hk
      | true =>
          cases k with
          | zero => simp [List.takeWhile, hp]
          | succ k =>
              have htail : k < (tail.takeWhile pred).length := by
                simpa [List.takeWhile, hp] using hk
              simpa only [List.takeWhile, hp, List.getElem_cons_succ] using ih k htail

private theorem eraseEvent_complement (xs : List (Fin (p.m - 1)))
    (event : Option (Fin (p.m - 1))) :
    ReferenceCollectionPhaseHistory.eraseEvent
        (Finset.univ \ xs.toFinset) event =
      Finset.univ \ (xs ++ event.toList).toFinset := by
  classical
  ext i
  cases event with
  | none => simp [ReferenceCollectionPhaseHistory.eraseEvent]
  | some j =>
      simp [ReferenceCollectionPhaseHistory.eraseEvent, List.toFinset_append]

private theorem ledger_startRound_cutoff_frame
    (ledger out : ReferenceActivePhysicalStep.Ledger rate) (time : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (h : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw =
      .success out) :
    out.cutoff = ledger.cutoff := by
  have hc := CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
    ledger (time.val + 1) (by omega) (Nat.succ_le_of_lt time.isLt) enabled raw out h
  rw [hc]
  rfl

private theorem ledger_finishRound_cutoff_frame
    (ledger out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.finishRound ledger = .success out) :
    out.cutoff = ledger.cutoff := by
  rw [CoordinatorCollectionUpRoundStep.InputsValid.finishRound_success_candidate
    ledger out h]
  rfl

private theorem ledger_decodeUp_cutoff_frame
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.decodeUp ledger i parsed = .success out ∨
      CoordinatorCollectionLedger.decodeUp ledger i parsed = .rejected out) :
    out.cutoff = ledger.cutoff := by
  classical
  by_cases hd : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ ledger.cursor ∧ ledger.cursor ≤ p.T
  · rcases h with hs | hr
    · obtain ⟨M, past, current, _, hout, _, _⟩ :=
        CoordinatorCollectionUpRoundStep.InputsValid.decodeUp_success_candidate
          ledger i parsed out hd hs
      rw [hout]
      rfl
    · unfold CoordinatorCollectionLedger.decodeUp at hr
      rw [dite_eq_left hd] at hr
      cases parsed with
      | none =>
          dsimp only at hr
          split_ifs at hr with hv
          injection hr with hout
          rw [← hout]
      | some M =>
          dsimp only at hr
          by_cases ha : CoordinatorCollectionLedger.acceptUpCheck ledger i M = true
          · rw [ite_eq_left ha] at hr
            split at hr
            · split at hr
              · rename_i past last hpast hlast
                cases last with
                | nil => cases hr
                | cons record tail =>
                    cases tail with
                    | nil =>
                        dsimp only at hr
                        split_ifs at hr
                    | cons record' tail' => cases hr
              · cases hr
            · cases hr
          · rw [ite_eq_right ha] at hr
            split_ifs at hr with hv
            injection hr with hout
            rw [← hout]
  · simp only [CoordinatorCollectionLedger.decodeUp, dite_eq_right hd] at h
    cases h <;> contradiction

private theorem packDecodeResult_cutoff_frame
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank = .success out ∨
      CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank = .rejected out) :
    out.1.cutoff = ledger.cutoff := by
  cases hd : CoordinatorCollectionLedger.decodeUp ledger i parsed with
  | invalid =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      cases h <;> contradiction
  | success decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have hout : out = (decoded, bank) := by
        rcases h with hs | hr
        · exact (CoordinatorCollectionLedger.Checked.success.inj hs).symm
        · cases hr
      rw [hout]
      exact ledger_decodeUp_cutoff_frame ledger i parsed decoded (Or.inl hd)
  | rejected decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have hout : out = (decoded, bank) := by
        rcases h with hs | hr
        · cases hs
        · exact (CoordinatorCollectionLedger.Checked.rejected.inj hr).symm
      rw [hout]
      exact ledger_decodeUp_cutoff_frame ledger i parsed decoded (Or.inr hd)

private theorem receiveUp_cutoff_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .success out ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .rejected out) :
    out.1.cutoff = ledger.cutoff := by
  classical
  unfold ReferenceActivePhysicalStep.receiveUp at h
  dsimp only at h
  unfold ReferenceUpReception.receiveUpFilteredAtRow at h
  dsimp only at h
  split at h
  · exact packDecodeResult_cutoff_frame _ _ _ _ out h
  · cases h <;> contradiction

private theorem collectionFinish_cutoff_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (outPayload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
      (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).configuration =
        .collection outPayload out proposal) :
    out.cutoff = ledgerStarted.cutoff := by
  classical
  cases hc : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result with
  | invalid =>
      simp only [ReferenceActivePhysicalStep.collectionFinish, hc,
        ReferenceActivePhysicalStep.coordinatorFailure] at h
      contradiction
  | success pair =>
      rcases pair with ⟨decoded, bank⟩
      have hdecoded : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result =
          .success (decoded, bank) := hc
      have hframe := receiveUp_cutoff_frame prepared ledgerStarted (decoded, bank)
        (Or.inl hdecoded)
      cases hf : CoordinatorCollectionLedger.finishRound decoded with
      | invalid =>
          simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
          contradiction
      | rejected rejected =>
          simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
          contradiction
      | success finished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finished.pending x.row with
          | error reason =>
              simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf, hclock,
                ReferenceActivePhysicalStep.coordinatorFailure] at h
              contradiction
          | ok clockFinished =>
              rw [ReferenceActivePhysicalStep.collectionFinish_success payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted) decoded finished
                bank clockFinished (Or.inl hdecoded) hf hclock] at h
              have hout : out = finished := by
                exact ((ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj h).2.1).symm
              rw [hout]
              exact (ledger_finishRound_cutoff_frame decoded finished hf).trans hframe
  | rejected pair =>
      rcases pair with ⟨decoded, bank⟩
      have hdecoded : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result =
          .rejected (decoded, bank) := hc
      have hframe := receiveUp_cutoff_frame prepared ledgerStarted (decoded, bank)
        (Or.inr hdecoded)
      cases hf : CoordinatorCollectionLedger.finishRound decoded with
      | invalid =>
          simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
          contradiction
      | rejected rejected =>
          simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
          contradiction
      | success finished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finished.pending x.row with
          | error reason =>
              simp only [ReferenceActivePhysicalStep.collectionFinish, hdecoded, hf, hclock,
                ReferenceActivePhysicalStep.coordinatorFailure] at h
              contradiction
          | ok clockFinished =>
              rw [ReferenceActivePhysicalStep.collectionFinish_success payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted) decoded finished
                bank clockFinished (Or.inr hdecoded) hf hclock] at h
              have hout : out = finished := by
                exact ((ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj h).2.1).symm
              rw [hout]
              exact (ledger_finishRound_cutoff_frame decoded finished hf).trans hframe

private theorem collectionPostChoice_cutoff_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (outPayload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
      started weights).configuration = .collection outPayload out proposal) :
    out.cutoff = ledger.cutoff := by
  classical
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord,
        ReferenceActivePhysicalStep.coordinatorFailure] at h
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
      | rejected rejected =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            ReferenceActivePhysicalStep.coordinatorFailure] at h
      | success ledgerStarted =>
          have hfinishInput :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).configuration =
                .collection outPayload out proposal := by
            simpa only [ReferenceActivePhysicalStep.collectionPostChoice_after_start prepared
              payload ledger started weights recording ledgerStarted hrecord hstart] using h
          have hfinish := collectionFinish_cutoff_frame payload started recording
            prepared ledgerStarted outPayload out proposal hfinishInput
          exact hfinish.trans (ledger_startRound_cutoff_frame ledger ledgerStarted x.time
            (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart)

private theorem cutoff_tail_fields
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {tail : ReferenceCollectionPhaseHistory.Tail x}
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true)
    (htail : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      tail.ledger.cutoff = x.time.val + 1 := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome => simp [hcoord] at hcut
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock hpending hnone selected =>
          simp only [hcoord] at hcut
          have hselected :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock
                    hpending hnone selected)) ≠ none := by
            by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock
                    hpending hnone selected)) = none
            · have hbad : some tail = none := by
                simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel] at htail
              cases hbad
            · exact hsel
          have htail' : tail =
              ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                dispatched.startResult,
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ := by
            have hsome : some
                (⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                  dispatched.startResult,
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ :
                  ReferenceCollectionPhaseHistory.Tail x) = some tail := by
              simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
            exact Option.some.inj hsome |>.symm
          rw [htail']
          have hshared := ReferenceActivePhysicalStep.sharedLedger_fields (rate := rate) ledger
          have hinitial := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
            (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time
          constructor
          · calc
              (ReferenceActivePhysicalStep.sharedLedger ledger).sigma = ledger.sigma := hshared.2.1
              _ = (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                    (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                    (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time).sigma := by
                    rw [hcandidate]
                    simp [ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt]
              _ = registers.payload.sigma.val + 1 := hinitial.2.1
          · calc
              (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff = ledger.cutoff := hshared.2.2.1
              _ = (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                    (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                    (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time).cutoff := by
                    rw [hcandidate]
                    simp [ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt]
              _ = x.time.val + 1 := hinitial.2.2.1
      | _ => simp [hcoord] at hcut
  | collection payload ledger clock cutoff outcome => simp [hcoord] at hcut
  | invalidCollectionCutoff => simp [hcoord] at hcut
  | dagger => simp [hcoord] at hcut

private theorem cutoff_step_cutoff
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true)
    (hout : (ReferenceActivePhysicalStep.step x).next.coordinator =
      .collection payload out proposal) :
    out.cutoff = x.time.val + 1 := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock hpending
          hnone selected =>
          simp only [hcoord] at hcut
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) registers owned base
            (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock
              hpending hnone selected) hcoord
          have hactual :
              (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                .collection payload out proposal := by
            exact (ReferenceActivePhysicalStep.step_next_fields x).1.symm.trans hout
          by_cases hselected :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock
                    hpending hnone selected)) = none
          · have hdagger :
                (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                  .dagger := by
              rw [hobs]
              simp [hselected, ReferenceActivePhysicalStep.coordinatorFailure]
            rw [hdagger] at hactual
            cases hactual
          · have hpost :
                (ReferenceActivePhysicalStep.collectionPostChoice
                  (ReferenceActivePhysicalStep.prepare x) registers.payload
                  (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights).configuration =
                  .collection payload out proposal := by
              have hobs' :
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
                    ReferenceActivePhysicalStep.collectionPostChoice
                      (ReferenceActivePhysicalStep.prepare x) registers.payload
                      (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights := by
                simpa [hselected] using hobs
              exact (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration
                hobs').symm.trans hactual
            have hpostCutoff := collectionPostChoice_cutoff_frame (ReferenceActivePhysicalStep.prepare x)
              registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
              dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
              payload out proposal hpost
            have hshared := ReferenceActivePhysicalStep.sharedLedger_fields (rate := rate) ledger
            have hinitial := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time
            have hreset : (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff =
                x.time.val + 1 := by
              calc
                (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff = ledger.cutoff :=
                  hshared.2.2.1
                _ = (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                      (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time).cutoff := by
                      rw [hcandidate]
                      simp [ReferenceActivePhysicalStep.liveInput,
                        ReferenceActivePhysicalStep.liveRegistersAt]
                _ = x.time.val + 1 := hinitial.2.2.1
            exact hpostCutoff.trans hreset
      | _ => simp [hcoord] at hcut
  | first outcome => simp [hcoord] at hcut
  | collection payload ledger clock cutoff outcome =>
      simp [hcoord] at hcut
  | invalidCollectionCutoff => simp [hcoord] at hcut
  | dagger => simp [hcoord] at hcut

private def cutoffDispatchOrigin
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .live registers owned base _ => x.state.coordinator = .live registers owned base
  | .collection payload ledger _ _ _ =>
      ∃ proposal, x.state.coordinator = .collection payload ledger proposal
  | .first _ => x.state.coordinator = .first
  | .dagger => x.state.coordinator = .dagger
  | .invalidCollectionCutoff => ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal

private theorem cutoff_dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    cutoffDispatchOrigin x (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change cutoffDispatchOrigin x (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live registers owned base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      exact hc
  | collection payload ledger proposal =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨proposal, hc⟩
      · exact ⟨payload, ledger, proposal, hc⟩
  | dagger => exact hc

private theorem cutoff_tail_payload_eq
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {tail : ReferenceCollectionPhaseHistory.Tail x}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator = some payload)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true)
    (htail : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.payload = payload := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  have horigin := cutoff_dispatch_origin x
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock hpending
          hnone selected =>
          rw [hcoord] at horigin
          dsimp only [cutoffDispatchOrigin] at horigin
          have hpayload : registers.payload = payload := by
            simpa [ReferenceAssignmentPayloadPersistence.storedPayload,
              horigin] using hp
          have hselected :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomain hclock
                    hpending hnone selected)) ≠ none := by
            intro hsel
            have hbad : some tail = none := by
              simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hsel] at htail
            cases hbad
          have htail' : tail =
              ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                dispatched.startResult,
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ := by
            have hsome : some
                (⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
                  dispatched.startResult,
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩ :
                  ReferenceCollectionPhaseHistory.Tail x) = some tail := by
              simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
            exact Option.some.inj hsome |>.symm
          rw [htail']
          exact hpayload
      | _ => simp [hcoord] at hcut
  | first outcome => simp [hcoord] at hcut
  | collection phasePayload ledger clock cutoff outcome =>
      simp [hcoord] at hcut
  | invalidCollectionCutoff => simp [hcoord] at hcut
  | dagger => simp [hcoord] at hcut

private theorem cutoff_false_in_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hstate : x.state.coordinator = .collection payload old proposal) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  have ho := cutoff_dispatch_origin x
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      rw [hcoord] at ho
      dsimp only [cutoffDispatchOrigin] at ho
      rw [hstate] at ho
      contradiction
  | first outcome => rfl
  | collection cp ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem collection_step_pending_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hstate : x.state.coordinator = .collection payload old proposal)
    (hout : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection cp out saved) :
    out.pending = ReferenceCollectionPhaseHistory.eraseEvent old.pending
      (ReferenceCollectionPhaseHistory.acceptedLabel x) ∧ out.sigma = old.sigma := by
  obtain ⟨tail, htail, hpending, hsigma⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame x cp out saved hout
  have hcut := cutoff_false_in_collection x payload old proposal hstate
  obtain ⟨_, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin htail
  rcases horigin with ⟨hcutTrue, _⟩ |
      ⟨_, oldPayload, oldLedger, oldProposal, hinput, hledger⟩
  · rw [hcut] at hcutTrue
    cases hcutTrue
  · have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hinput.symm.trans hstate)
    have hledgerEq : tail.ledger = old := by
      exact hledger.trans hfields.2.1
    rw [hledgerEq] at hpending hsigma
    exact ⟨hpending, hsigma⟩

private theorem livePostChoice_not_collection
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .collection payload ledger saved := by
  intro h
  unfold ReferenceActivePhysicalStep.livePostChoice at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> contradiction

private theorem collection_step_cutoff_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hstate : x.state.coordinator = .collection payload old proposal)
    (hout : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection cp out saved) :
    out.cutoff = old.cutoff := by
  classical
  have houtConfig :
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
        .collection cp out saved :=
    (ReferenceActivePhysicalStep.step_next_fields x).1.symm.trans hout
  have horigin := cutoff_dispatch_origin x
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection phasePayload phaseLedger clock cutoff outcome =>
      rw [hcoord] at horigin
      dsimp only [cutoffDispatchOrigin] at horigin
      obtain ⟨phaseSaved, hstate'⟩ := horigin
      have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
        (hstate'.symm.trans hstate)
      rcases hfields with ⟨hpayload, hledger, hsaved⟩
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) phasePayload phaseLedger clock cutoff
            (.continuing core snapshot boundary scores) hcoord
          by_cases hselected : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection phasePayload phaseLedger clock cutoff
                (.continuing core snapshot boundary scores)) = none
          · rw [hobs] at houtConfig
            simp [hselected, ReferenceActivePhysicalStep.coordinatorFailure] at houtConfig
          · have hpost :
                (ReferenceActivePhysicalStep.collectionPostChoice
                  (ReferenceActivePhysicalStep.prepare x) phasePayload phaseLedger snapshot.clockStarted
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (ReferenceActivePhysicalStep.collectionInput x phasePayload phaseLedger clock cutoff)
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration =
                  .collection cp out saved := by
              rw [hobs] at houtConfig
              simpa [hselected] using houtConfig
            have hpostCutoff := collectionPostChoice_cutoff_frame (ReferenceActivePhysicalStep.prepare x)
              phasePayload phaseLedger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x phasePayload phaseLedger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
              cp out saved hpost
            exact hpostCutoff.trans (congrArg
              (fun ledger : ReferenceActivePhysicalStep.Ledger rate => ledger.cutoff) hledger)
      | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) phasePayload phaseLedger clock cutoff
            (.laterChosen core consistent started hstart instruction hi output hcons data
              installed selected) hcoord
          by_cases hselected : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection phasePayload phaseLedger clock cutoff
                (.laterChosen core consistent started hstart instruction hi output hcons data
                  installed selected)) = none
          · rw [hobs] at houtConfig
            simp [hselected, ReferenceActivePhysicalStep.coordinatorFailure] at houtConfig
          · have hlive :
                (ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare x)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore started).configuration =
                  .collection cp out saved := by
              rw [hobs] at houtConfig
              simpa [hselected] using houtConfig
            exact False.elim (livePostChoice_not_collection (ReferenceActivePhysicalStep.prepare x)
              installed.registers installed.ownedRegisters installed.retainedBaseScore started
              cp out saved hlive)
      | _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcoord,
            ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at houtConfig
  | live registers owned base outcome =>
      rw [hcoord] at horigin
      dsimp only [cutoffDispatchOrigin] at horigin
      rw [hstate] at horigin
      cases horigin
  | first outcome =>
      rw [hcoord] at horigin
      dsimp only [cutoffDispatchOrigin] at horigin
      rw [hstate] at horigin
      cases horigin
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at houtConfig
  | dagger =>
      rw [hcoord] at horigin
      dsimp only [cutoffDispatchOrigin] at horigin
      rw [hstate] at horigin
      cases horigin

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (start count : ℕ) (span : start + count ≤ p.T)
  (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
  (k : ℕ) (hk : k + 1 < count)
  (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))

/-- The actual cutoff reset initializes the full pending set; each subsequent
successful filtered UP reception erases exactly its accepted sender. The
moving ledger and saved proposal remain those of the original physical run.
This result is conditional on the cutoff's retained DOWN and local live
continuation, and exposes both dagger and collection endpoint cases.
Sources: `05_binary_transport.tex:36-53,70-88,105-124`,
`06_interruptions.tex:41-70,164-177,277-284,327-348`, and
`appendix_a_local_protocol.tex:92-109,151-157`.
-/
theorem run_cutoff_collection_pending_exact :
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
      ∃ M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
        M.val = ActiveFollowerQueueOperation.upOfferFields next ∧
        M.val.sigma = payload.sigma.val + 1 ∧ 0 < M.val.sigma ∧
        let b := k + 2
        let W := (E.records.drop b).takeWhile
          fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
        let C := fun (n : ℕ) (hn : n ≤ W.length) =>
          ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n) (by
            have hcount : E.records.length = count := by
              dsimp [E]
              exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
                start count span active
            have hdrop : (E.records.drop b).length = count - b := by
              rw [List.length_drop, hcount]
            have htake := takeWhile_length_le
              (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
                !ReferenceCollectionPhaseHistory.laterChosen r.input) (E.records.drop b)
            have hwindow : W.length ≤ count - b := by
              calc
                W.length ≤ (E.records.drop b).length := by
                  dsimp [W]
                  exact htake
                _ = count - b := hdrop
            omega) active
        ∀ n (hn : n ≤ W.length),
          (C n hn).finalState.coordinator = .dagger ∨
          ∃ movingLedger movingSaved,
            (C n hn).finalState.coordinator = .collection payload movingLedger movingSaved ∧
            movingLedger.pending = Finset.univ
              \ (ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take n)).toFinset ∧
            movingLedger.sigma = payload.sigma.val + 1 ∧
            movingLedger.cutoff = current.input.time.val + 1 := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let prev := E.records[k]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; omega)
  let current := E.records[k + 1]'(by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)
  intro hp hc hd next nextMemory hf ho
  obtain ⟨choice, choiceMemory, M, _, _, _, _, hMval, hMsigma, hMpos⟩ :=
    ReferenceCutoffUpReplyInterval.cutoff_fixed_up_word
      initial rows J rewards start count span active k hk payload i hp hc hd
      next nextMemory hf ho
  let b := k + 2
  let W := (E.records.drop b).takeWhile
    fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  let C := fun (n : ℕ) (hn : n ≤ W.length) =>
    ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n) (by
      have hcount : E.records.length = count := by
        dsimp [E]
        exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
          start count span active
      have hdrop : (E.records.drop b).length = count - b := by
        rw [List.length_drop, hcount]
      have htake := takeWhile_length_le
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          !ReferenceCollectionPhaseHistory.laterChosen r.input) (E.records.drop b)
      have hwindow : W.length ≤ count - b := by
        calc
          W.length ≤ (E.records.drop b).length := by
            dsimp [W]
            exact htake
          _ = count - b := hdrop
      omega) active
  have hcount : E.records.length = count := by
    dsimp [E]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
      start count span active
  have hWle : W.length ≤ count - b := by
    calc
      W.length ≤ (E.records.drop b).length := by
        dsimp [W]
        exact takeWhile_length_le
          (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.laterChosen r.input) (E.records.drop b)
      _ = count - b := by rw [List.length_drop, hcount]
  have hb : b ≤ count := by dsimp [b]; omega
  obtain ⟨s, memory, choice', choiceMemory', ledger, saved, hs, hchoice,
      hstart, hlastDown, hchoiceUnoccupied, hchoiceReply, hnextUnoccupied,
      hnextReply, hnextDown, hnextStart, hcollection, hboundary,
      hretainedDetails, hnextUnoccupied', hnextStart', hcoord, hseed,
      hproducers⟩ :=
    ReferenceCutoffUpReplyInterval.cutoff_collection_interval_producers
      initial rows J rewards start count span active k hk payload i hp hc hd
      next nextMemory hf ho
  have hstates : ∀ n (hn : n ≤ W.length),
      ((C n hn).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          (C n hn).finalState.coordinator = .collection payload movingLedger movingSaved) ∧
      ((C n hn).finalState.followers i = .dagger ∨
        ∃ state memory,
          (C n hn).finalState.followers i = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state =
            ReferenceFollowerReplyChronology.reply next) := by
    dsimp only [ReferenceCutoffUpReplyInterval.CollectionWindowProducers] at hproducers
    exact hproducers.1
  have hinterval : ∀ n (hn : n ≤ W.length),
      (C n hn).finalState.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        (C n hn).finalState.coordinator = .collection payload movingLedger movingSaved ∧
        movingLedger.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take n)).toFinset ∧
        movingLedger.sigma = payload.sigma.val + 1 ∧
        movingLedger.cutoff = current.input.time.val + 1 := by
    intro n hn
    induction n with
    | zero =>
        have hboundaryState : (C 0 hn).finalState = current.output.next := by
          have hbdy := hboundary
          simpa [C, b] using hbdy
        have hC0collection : (C 0 hn).finalState.coordinator = .collection payload ledger saved := by
          exact (congrArg
            (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
            hboundaryState).trans hcollection
        have hstep : (ReferenceActivePhysicalStep.step current.input).next.coordinator =
            .collection payload ledger saved := by
          have hc' := hcollection
          rw [current.output_eq] at hc'
          exact hc'
        obtain ⟨tail, htail, hpendFrame, hsigmaFrame⟩ :=
          ReferenceCollectionPhaseHistory.step_collection_frame current.input payload ledger
            saved hstep
        obtain ⟨_, horigin⟩ := ReferenceCollectionPhaseHistory.executedTail_origin htail
        have htailPending : tail.ledger.pending = Finset.univ := by
          rcases horigin with ⟨hcut, hpending⟩ | ⟨hcut, _, _, _, _, _⟩
          · simpa [hc] using hpending
          · rw [hc] at hcut
            cases hcut
        have htailPayload := cutoff_tail_payload_eq payload hp hc htail
        have htailFields := cutoff_tail_fields hc htail
        have hcutoff := cutoff_step_cutoff payload ledger saved hc hstep
        have hbasePending : ledger.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take 0)).toFinset := by
          calc
            ledger.pending = ReferenceCollectionPhaseHistory.eraseEvent tail.ledger.pending
                (ReferenceCollectionPhaseHistory.acceptedLabel current.input) := hpendFrame
            _ = ReferenceCollectionPhaseHistory.eraseEvent Finset.univ
                (ReferenceCollectionPhaseHistory.acceptedLabel current.input) := by
                  rw [htailPending]
            _ = Finset.univ \ ((ReferenceCollectionPhaseHistory.acceptedLabel current.input).toList.toFinset) := by
                  have he := eraseEvent_complement ([] : List (Fin (p.m - 1)))
                    (ReferenceCollectionPhaseHistory.acceptedLabel current.input)
                  simpa using he
            _ = Finset.univ \
                (ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take 0)).toFinset := by
                  have hlabels0 : ReferenceCollectionPhaseHistory.acceptedLabels
                      (current :: W.take 0) =
                        (ReferenceCollectionPhaseHistory.acceptedLabel current.input).toList := by
                    rw [List.take_zero]
                    cases he : ReferenceCollectionPhaseHistory.acceptedLabel current.input <;>
                      simp [ReferenceCollectionPhaseHistory.acceptedLabels, he]
                  rw [hlabels0]
        right
        refine ⟨ledger, saved, hC0collection, hbasePending, ?_, ?_⟩
        · calc
            ledger.sigma = tail.ledger.sigma := hsigmaFrame
            _ = tail.payload.sigma.val + 1 := htailFields.1
            _ = payload.sigma.val + 1 := by rw [htailPayload]
        · exact hcutoff
    | succ n ih =>
        have hnPrev : n ≤ W.length := by omega
        have hprev := ih hnPrev
        have hnlt : n < W.length := by omega
        have hq : b + n < count := by omega
        let r : Record p rate := E.records[b + n]'
          (by rw [hcount]; exact hq)
        have hWget : W[n]'hnlt = r := by
          dsimp [W, r]
          rw [getElem_takeWhile_eq
            (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              !ReferenceCollectionPhaseHistory.laterChosen r.input)
            (E.records.drop b) n hnlt]
          simp [List.getElem_drop]
        have hmem : r ∈ W := by
          rw [← hWget]
          exact List.getElem_mem hnlt
        have hlater : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
          have htake := List.mem_takeWhile_imp (by simpa [W] using hmem)
          cases hvalue : ReferenceCollectionPhaseHistory.laterChosen r.input with
          | false => rfl
          | true => simp [hvalue] at htake
        have hendpoints := run_prefix_endpoints initial rows J rewards start count span active
          (b + n) hq
        have hinput : (C n hnPrev).finalState = r.input.state := by
          simpa [C, r, Nat.add_assoc] using hendpoints.1
        have houtput : (C (n + 1) hn).finalState = r.output.next := by
          simpa [C, r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hendpoints.2
        have hnewState := (hstates (n + 1) hn).1
        rcases hprev with hprevDagger |
            ⟨oldLedger, oldSaved, hprevCollection, hprevPending, hprevSigma, hprevCutoff⟩
        · have hinputDagger : r.input.state.coordinator = .dagger := by
            have heq := congrArg ReferenceActivePhysicalStep.State.coordinator hinput
            exact heq.symm.trans hprevDagger
          have houtDagger := (ReferenceActivePhysicalStep.step_coordinator_dagger
            r.input hinputDagger).1
          have houtRecord : r.output.next.coordinator = .dagger := by
            exact (congrArg
              (fun o : ReferenceActivePhysicalStep.RoundOutput r.input => o.next.coordinator)
              r.output_eq).trans houtDagger
          have hnewDagger : (C (n + 1) hn).finalState.coordinator = .dagger := by
            have heq := congrArg
              (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) houtput
            exact heq.trans houtRecord
          exact Or.inl hnewDagger
        · rcases hnewState with hnewDagger |
              ⟨newLedger, newSaved, hnewCollection⟩
          · exact Or.inl hnewDagger
          · have hinputCollection : r.input.state.coordinator =
                .collection payload oldLedger oldSaved := by
              have heq := congrArg
                (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) hinput
              exact heq.symm.trans hprevCollection
            have houtRecord : r.output.next.coordinator =
                .collection payload newLedger newSaved := by
              have heq := congrArg
                (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) houtput
              exact heq.symm.trans hnewCollection
            have hout : (ReferenceActivePhysicalStep.step r.input).next.coordinator =
                .collection payload newLedger newSaved := by
              exact (congrArg
                (fun o : ReferenceActivePhysicalStep.RoundOutput r.input => o.next.coordinator)
                r.output_eq).symm.trans houtRecord
            have hframe := collection_step_pending_frame payload oldLedger oldSaved
              payload newLedger newSaved hinputCollection hout
            have hcutframe := collection_step_cutoff_frame payload oldLedger oldSaved
              payload newLedger newSaved hinputCollection hout
            have hlabels :
                ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take (n + 1)) =
                  ReferenceCollectionPhaseHistory.acceptedLabels (current :: W.take n) ++
                    (ReferenceCollectionPhaseHistory.acceptedLabel r.input).toList := by
              have htake : W.take (n + 1) = W.take n ++ [r] := by
                rw [List.take_add_one]
                simp [hnlt, hWget]
              rw [htake, ← List.cons_append, acceptedLabels_append]
              cases he : ReferenceCollectionPhaseHistory.acceptedLabel r.input <;>
                simp [ReferenceCollectionPhaseHistory.acceptedLabels, he]
            have hnewPending : newLedger.pending = Finset.univ \
                (ReferenceCollectionPhaseHistory.acceptedLabels
                  (current :: W.take (n + 1))).toFinset := by
              calc
                newLedger.pending = ReferenceCollectionPhaseHistory.eraseEvent oldLedger.pending
                    (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := hframe.1
                _ = ReferenceCollectionPhaseHistory.eraseEvent
                    (Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                      (current :: W.take n)).toFinset)
                    (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
                      rw [hprevPending]
                _ = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                    (current :: W.take n) ++
                      (ReferenceCollectionPhaseHistory.acceptedLabel r.input).toList).toFinset := by
                      exact eraseEvent_complement _ _
                _ = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels
                    (current :: W.take (n + 1))).toFinset := by rw [hlabels]
            refine Or.inr ⟨newLedger, newSaved, hnewCollection, hnewPending, ?_, ?_⟩
            · exact hframe.2.trans hprevSigma
            · exact hcutframe.trans hprevCutoff
  exact ⟨M, hMval, hMsigma, hMpos, hinterval⟩
end Bandits.Support.ReferenceCollectionUpPendingInterval

end
