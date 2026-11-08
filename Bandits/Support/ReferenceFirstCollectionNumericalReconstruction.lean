/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream

import Lean.Elab.Tactic.Omega

/-!
# Numerical reconstruction at the actual first empty collection boundary

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal result carries the accepted original-source all-arm collection
stream through its actual empty boundary, with endpoint ledger equations and
the original terminal or next-input case. It does not assert equations for the
later reconstructed start: the admitted public dispatch type does not expose
the equality between its stored operation ledger and the ledger projection
computed from the actual collection input. It is not a manuscript theorem or a
regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCollectionNumericalReconstruction

variable {p : ConstructorDimensions.Parameters}

private theorem replay_transition_score_ge (capacity : ℕ) (state : ℕ × ℕ)
    (record : Bool × ℕ) :
    state.1 ≤ (QueueReplay.transition capacity state record).1 := by
  cases record with
  | mk enabled arrival =>
      cases enabled <;> simp [QueueReplay.transition]

private theorem replay_score_ge_start (capacity : ℕ) (state : ℕ × ℕ)
    (records : List (Bool × ℕ)) :
    state.1 ≤ (QueueReplay.replay capacity state records).1 := by
  induction records generalizing state with
  | nil => simp [QueueReplay.replay]
  | cons record records ih =>
      rw [show record :: records = [record] ++ records by rfl,
        QueueReplay.replay_append]
      rw [show QueueReplay.replay capacity state [record] =
        QueueReplay.transition capacity state record by rfl]
      exact le_trans (replay_transition_score_ge capacity state record)
        (ih (QueueReplay.transition capacity state record))

private theorem replay_score_le_of_append (capacity : ℕ) (state : ℕ × ℕ)
    (firstRecords suffix : List (Bool × ℕ)) :
    (QueueReplay.replay capacity state firstRecords).1 ≤
      (QueueReplay.replay capacity state (firstRecords ++ suffix)).1 := by
  calc
    (QueueReplay.replay capacity state firstRecords).1 ≤
        (QueueReplay.replay capacity (QueueReplay.replay capacity state firstRecords) suffix).1 :=
      replay_score_ge_start capacity (QueueReplay.replay capacity state firstRecords) suffix
    _ = (QueueReplay.replay capacity state (firstRecords ++ suffix)).1 :=
      congrArg Prod.fst (QueueReplay.replay_append capacity state firstRecords suffix).symm

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)

local notation "s" => ReferenceFirstCollectionReadyStream.startTime (rate := rate)
  source rewards C_star C_h
local notation "L" => ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan))
local notation "Cells" => ReferenceFirstWindowNumericalStream.actualLiveSourceCells
  rate source rewards C_star C_h hcross count hspan
local notation "V" => fun a : Fin p.K =>
  QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)
local notation "Vpre" => fun a : Fin p.K =>
  QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
      (List.take (List.length L - 1) Cells))
local notation "Rprefix" => fun (D : List (RecordedQueueRun.RoundInput p.K))
    (a : Fin p.K) (h : ℕ) =>
  QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ List.take h D))
local notation "Rwhole" => fun (D : List (RecordedQueueRun.RoundInput p.K))
    (a : Fin p.K) =>
  QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))

/-- The actual original-source first-collection prefix, endpoint numerical
ledger, and original terminal or next-input boundary. -/
theorem actual_first_collection_numerical_prefix_and_boundary :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let out := d.stream
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧
      head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      (∀ n : Fin out.ell,
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = out.payload ∧
          CollectionBufferProvenance.collectionContext call.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
          (∀ a : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
          (0 < n.val →
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
      (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
        (out.window.take h).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
            ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take h)) ∧
      (∀ n : Fin out.ell,
        let l := out.ledgers n
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        record.output.coordinator.failure = none ∧
        record.output.next.coordinator = .collection out.payload l out.saved ∧
        l.cursor = s + (L).length + 1 + n.val + 1 ∧
        CollectionBufferProvenance.collectionContext l =
          CollectionBufferProvenance.collectionContext head.preLedger ∧
        ∀ a : Fin p.K, l.gammaLoc a = 0 ∧
          (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (¬ CoordinatorCollectionLedger.armPending l a →
            l.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
            l.currentRegisters a = some ⟨(Rprefix D a (n.val + 1)).2,
              (Rprefix D a (n.val + 1)).1 - (Rprefix D a n.val).1⟩ ∧
            l.increment a =
              (QueueReplay.replay (4 * rate.n) (0, (V a).2)
                (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take (n.val + 1)))).1 ∧
            (V a).1 + l.increment a = (Rprefix D a (n.val + 1)).1)) ∧
      (d.ledger.pending = ∅ → ∀ a : Fin p.K,
        d.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
        d.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
          (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
        d.ledger.increment a =
          (QueueReplay.replay (4 * rate.n) (0, (V a).2)
            (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
        (V a).1 + d.ledger.increment a = (Rwhole D a).1) ∧
      (∀ a : Fin p.K, (Vpre a).1 ≤ (V a).1) ∧
      (∀ e, d.outcome = .empty e →
        d.ledger.pending = ∅ ∧
        d.record.output.next.coordinator = .collection d.stream.payload d.ledger d.stream.saved ∧
        (∀ a : Fin p.K,
          d.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
          d.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
            (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
          d.ledger.increment a =
            (QueueReplay.replay (4 * rate.n) (0, (V a).2)
              (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
          (V a).1 + d.ledger.increment a = (Rwhole D a).1) ∧
        (match e.nextBoundary with
        | .terminal _ _ =>
            d.record.input.time.val + 1 = p.T ∧ d.ledger.cursor = p.T + 1
        | .next beforeHorizon _ x _ _ _ _ _ _ _ _ _ =>
            d.record.input.time.val + 1 < p.T ∧
            ReferenceFirstCollectionReadyStream.startTime (rate := rate)
              source rewards C_star C_h ≤ d.record.input.time.val ∧
            x = ReferenceActivePhysicalHorizon.roundInputAt
              (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards
                C_star C_h hcross)
              source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                source rewards C_star C_h)
              (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
                rate source rewards C_star C_h hcross).1
              e.prefixRun ⟨d.record.input.time.val + 1, by
                exact ⟨by omega, beforeHorizon⟩⟩ ∧
            x.state = d.record.output.next ∧
            x.time.val = d.record.input.time.val + 1 ∧
            x.rows = source.1.2 ∧
            x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            x.rewards = rewards ∧
            x.time.val = s + (L).length + out.ell )) := by
  classical
  obtain ⟨d, head, initializer, valid, D, hhead, hpayload, hinitializer,
    hchecked, hDlen, hDzero, hstream⟩ :=
    ReferenceFirstCollectionAllArmNumericalStream.actual_initialized_first_collection_all_arm_numerical_stream
      rate source rewards C_star C_h hcross count hspan hshort
  dsimp only at hstream
  rcases hstream with ⟨hCells, hPrefix, hRecords, hEndpoint⟩
  refine ⟨d, ?_⟩
  dsimp only
  let out := d.stream
  have hDtake : D.take out.ell = D := by
    rw [List.take_of_length_le hDlen.le]
  have hRfull (a : Fin p.K) : Rprefix D a out.ell = Rwhole D a := by
    change QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
          (Cells ++ D.take out.ell)) =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))
    rw [hDtake]
  have hEndpointRoot : d.ledger.pending = ∅ → ∀ a : Fin p.K,
      d.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
      d.ledger.currentRegisters a = some ⟨(Rwhole D a).2,
        (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ ∧
      d.ledger.increment a =
        (QueueReplay.replay (4 * rate.n) (0, (V a).2)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a D)).1 ∧
      (V a).1 + d.ledger.increment a = (Rwhole D a).1 := by
    intro hempty a
    have h := hEndpoint hempty a
    refine ⟨h.1, ?_, h.2.2.1, ?_⟩
    · simpa only [← hRfull a] using h.2.1
    · simpa only [← hRfull a] using h.2.2.2
  refine ⟨head, initializer, valid, D, hhead, hpayload, hinitializer,
    hchecked, hDlen, hDzero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hCells
  · exact hPrefix
  · exact hRecords
  · intro hempty
    exact hEndpointRoot hempty
  · intro a
    let n := (L).length - 1
    have hsplit :
        ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).take n) ++
          ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).drop n) =
        ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells := by
      simp only [ReferenceFirstCollectionAllArmNumericalStream.arrivals]
      rw [← List.map_append, List.take_append_drop]
    change (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).take n))).1 ≤
      (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).1
    calc
      _ ≤ (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).take n) ++
           ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).drop n))).1 :=
        replay_score_le_of_append (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).take n))
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a ((Cells).drop n))
      _ = (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).1 :=
        congrArg (fun records =>
          (QueueReplay.replay (4 * rate.n) (0, 0) records).1) hsplit
  · intro e _
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact e.pendingEmpty
    · exact e.actualNextCoordinator
    · exact hEndpointRoot e.pendingEmpty
    · cases e.nextBoundary with
      | terminal timeAtHorizon cursorAtSentinel =>
          exact ⟨timeAtHorizon, cursorAtSentinel⟩
      | next beforeHorizon currentAtOrAfterStart x isOriginalPrefixInput
          stateIsPriorFinish timeIsNext rowsAreOriginal selectedIsOriginal
          rewardsAreWhole _ _ _ =>
          have hCellsLast := hCells d.last
          have hrecord : out.window[d.last.val]'(lt_of_lt_of_le d.last.isLt out.withinWindow) = d.record :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans d.recordAt)
          rw [hrecord] at hCellsLast
          obtain ⟨_, _, _, _, _, _, _, _, _, lastTime, _, _, _, _, _⟩ := hCellsLast
          have htime : x.time.val = s + (L).length + out.ell := by
            calc
              x.time.val = d.record.input.time.val + 1 := timeIsNext
              _ = s + (L).length + d.last.val + 1 := by rw [lastTime]
              _ = s + (L).length + out.ell := by
                simp only [Nat.add_assoc, d.lastIsLast, out]
          exact ⟨beforeHorizon, currentAtOrAfterStart, isOriginalPrefixInput,
            stateIsPriorFinish, timeIsNext, rowsAreOriginal, selectedIsOriginal,
            rewardsAreWhole, htime⟩

end Actual

end Bandits.Support.ReferenceFirstCollectionNumericalReconstruction

end
