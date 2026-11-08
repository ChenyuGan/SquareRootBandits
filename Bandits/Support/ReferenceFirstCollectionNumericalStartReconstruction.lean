/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNumericalReconstruction
public import Bandits.Support.ReferenceFirstCollectionCanonicalNextDispatch

import Lean.Elab.Tactic.Omega

/-!
# Numerical reconstruction at the actual first collection next start

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal assembly keeps the original-source stream, its first actual
empty-pending endpoint, and the actual next input on the same dispatch and
source list. At that input it applies only the local canonical constructor to
the existing dispatch certificate. The resulting reconstructed register
vectors are identified with the numerical replay endpoint. The result retains
the terminal sentinel and does not establish sampling or installation success,
an all-calendar source law, or a manuscript regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionStreamEmptyDispatch

namespace Bandits.Support.ReferenceFirstCollectionNumericalStartReconstruction

variable {p : ConstructorDimensions.Parameters}

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

/-- Preserve the complete actual first-collection numerical prefix and empty
boundary while identifying the same physical next-start reconstruction with
the replay score and queue on the same source list. -/
theorem actual_first_collection_numerical_next_start_reconstruction :
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
            x.time.val = s + (L).length + out.ell ∧
            ∃ k : ActualNextDispatch x out.payload d.ledger out.saved,
              (k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x out.payload d.ledger
                  (ReferenceActivePhysicalStep.collectionClock out.payload d.ledger out.saved
                    k.cutoffTime)
                  k.cutoffTime) k.core.payload_n_eq ∧
              (k.operationLedger.assignment = d.ledger.assignment ∧
                k.operationLedger.sigma = d.ledger.sigma ∧
                k.operationLedger.cutoff = d.ledger.cutoff ∧
                k.operationLedger.freezeAt = d.ledger.freezeAt ∧
                k.operationLedger.baseScore = d.ledger.baseScore ∧
                k.operationLedger.pending = d.ledger.pending ∧
                k.operationLedger.cutoffRegisters = d.ledger.cutoffRegisters ∧
                k.operationLedger.currentRegisters = d.ledger.currentRegisters ∧
                k.operationLedger.increment = d.ledger.increment ∧
                k.operationLedger.gammaLoc = d.ledger.gammaLoc ∧
                k.operationLedger.rawBuffer = d.ledger.rawBuffer ∧
                k.operationLedger.enabledHistory = d.ledger.enabledHistory ∧
                k.operationLedger.cursor = d.ledger.cursor ∧
                k.operationLedger.phase = d.ledger.phase) ∧
              AssignmentScoreReconstruction.reconstructLaterStart k.operationLedger k.instruction =
                .success k.operationLedger k.instruction k.reconstructed ∧
              (CoordinatorCollectionLedger.validLedgerCheck k.operationLedger = true ∧
                k.operationLedger.phase = .ready ∧
                k.operationLedger.cursor = k.instruction.time.val + 1 ∧
                k.operationLedger.pending = ∅ ∧
                k.instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
                  k.operationLedger.freezeAt k.instruction.time ∧
                AssignmentScoreReconstruction.currentOutputDomainsCheck k.operationLedger = true ∧
                AssignmentScoreReconstruction.previousOutputDomainsCheck
                  k.operationLedger k.instruction = true) ∧
              (∀ a, d.ledger.cutoffRegisters a = some (k.reconstructed.registers.cutoff a)) ∧
              (∀ a, d.ledger.currentRegisters a = some (k.reconstructed.registers.current a)) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a =
                (k.reconstructed.registers.cutoff a).score + d.ledger.increment a) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a =
                (k.reconstructed.registers.current a).queue) ∧
              (∀ a, AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  AssignmentScoreReconstruction.sourceScore k.reconstructed a) ∧
              (∀ a, AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  (k.reconstructed.registers.cutoff a).score) ∧
              (∀ a, 0 < AssignmentScoreReconstruction.currentWeight k.reconstructed a) ∧
              (∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight k.reconstructed a) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a ≤
                p.T * ConstructorDimensions.D p) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue k.reconstructed a ≤
                p.T * ConstructorDimensions.D p) ∧
              (k.instruction.kind = .corrected ↔
                x.time.val + 1 < d.ledger.freezeAt) ∧
              (k.instruction.kind = .renewal ↔
                d.ledger.freezeAt ≤ x.time.val + 1) ∧
              (k.instruction.kind = .corrected →
                AssignmentScoreReconstruction.previousScore k.reconstructed =
                  some (fun a : Fin p.K => (k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService) ∧
                (∀ a, (k.reconstructed.registers.cutoff a).score =
                  ((k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService) +
                  (k.reconstructed.registers.cutoff a).lastService) ∧
                (∃ weights, AssignmentScoreReconstruction.previousWeight k.reconstructed =
                    some weights ∧
                  ∀ a, weights a = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                    ((k.reconstructed.registers.cutoff a).score -
                      (k.reconstructed.registers.cutoff a).lastService)) ∧
                (∀ a, 0 < (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  ((k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService))) ∧
              (k.instruction.kind = .renewal →
                AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed = none)) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.sourceScore k.reconstructed a = (Rwhole D a).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.initialQueue k.reconstructed a = (Rwhole D a).2) ∧
              (∀ a : Fin p.K,
                (k.reconstructed.registers.cutoff a).score = (V a).1 ∧
                (k.reconstructed.registers.cutoff a).queue = (V a).2 ∧
                (k.reconstructed.registers.cutoff a).lastService = (V a).1 - (Vpre a).1) ∧
              (∀ a : Fin p.K,
                (k.reconstructed.registers.current a).queue = (Rwhole D a).2 ∧
                (k.reconstructed.registers.current a).lastService =
                  (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                  (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1) ∧
              (∀ a : Fin p.K,
                AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                  (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1) ∧
              (k.instruction.time.val + 1 < k.operationLedger.freezeAt →
                AssignmentScoreReconstruction.previousScore k.reconstructed =
                  some (fun a : Fin p.K => (Vpre a).1) ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed =
                  some (fun a : Fin p.K =>
                    (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1)) ∧
              (k.operationLedger.freezeAt ≤ k.instruction.time.val + 1 →
                AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
                AssignmentScoreReconstruction.previousWeight k.reconstructed = none))) := by
  classical
  obtain ⟨d, head, initializer, valid, D, hhead, hpayload, hinitializer,
    hchecked, hDlen, hDzero, hstream⟩ :=
    ReferenceFirstCollectionNumericalReconstruction.actual_first_collection_numerical_prefix_and_boundary
      rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hstream
  rcases hstream with ⟨hCells, hPrefix, hRecords, hEndpoint, hVpre, _hBoundary⟩
  refine ⟨d, head, initializer, valid, D, hhead, hpayload, hinitializer,
    hchecked, hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, ?_⟩
  let out := d.stream
  · intro e _
    refine ⟨e.pendingEmpty, e.actualNextCoordinator,
      hEndpoint e.pendingEmpty, ?_⟩
    cases e.nextBoundary with
    | terminal timeAtHorizon cursorAtSentinel =>
        exact ⟨timeAtHorizon, cursorAtSentinel⟩
    | next beforeHorizon currentAtOrAfterStart x isOriginalPrefixInput
        stateIsPriorFinish timeIsNext rowsAreOriginal selectedIsOriginal
        rewardsAreWhole equalsRetainedWindow equalsRetainedRun old =>
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
        refine ⟨beforeHorizon, currentAtOrAfterStart, isOriginalPrefixInput,
          stateIsPriorFinish, timeIsNext, rowsAreOriginal, selectedIsOriginal,
          rewardsAreWhole, htime, ?_⟩
        have hnum := hEndpoint e.pendingEmpty
        obtain ⟨k, hKdata⟩ :=
          ReferenceFirstCollectionCanonicalNextDispatch.exists_canonical_actual_next_dispatch_equations
            x out.payload d.ledger out.saved old
        have hKdataCopy := hKdata
        rcases hKdata with
          ⟨hcanonical, hcopies, hsuccess, hchecks, hcutoffSome, hcurrentSome,
            hscore, hqueue, hweight, hcutoffWeight, hcurrentWeightPos,
            hcutoffWeightPos, hscoreBound, hqueueBound, hcorrected, hrenewal,
            hcorrectedEquations, hrenewalEquations⟩
        rcases hcopies with
          ⟨_, _, _, hfreezeCopy, _, _, _, _, _, _, _, _, _, _⟩
        have hcutoffValue (a : Fin p.K) :
            k.reconstructed.registers.cutoff a =
              ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ := by
          exact Option.some.inj ((hcutoffSome a).symm.trans (hnum a).1)
        have hcurrentValue (a : Fin p.K) :
            k.reconstructed.registers.current a =
              ⟨(Rwhole D a).2,
                (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1⟩ := by
          exact Option.some.inj ((hcurrentSome a).symm.trans (hnum a).2.1)
        have hsourceScore (a : Fin p.K) :
            AssignmentScoreReconstruction.sourceScore k.reconstructed a = (Rwhole D a).1 := by
          calc
            AssignmentScoreReconstruction.sourceScore k.reconstructed a =
                (k.reconstructed.registers.cutoff a).score + d.ledger.increment a := hscore a
            _ = (V a).1 + d.ledger.increment a := by rw [hcutoffValue a]
            _ = (Rwhole D a).1 := (hnum a).2.2.2
        have hinitialQueue (a : Fin p.K) :
            AssignmentScoreReconstruction.initialQueue k.reconstructed a = (Rwhole D a).2 := by
          calc
            AssignmentScoreReconstruction.initialQueue k.reconstructed a =
                (k.reconstructed.registers.current a).queue := hqueue a
            _ = (Rwhole D a).2 := by rw [hcurrentValue a]
        have hcutoffFields (a : Fin p.K) :
            (k.reconstructed.registers.cutoff a).score = (V a).1 ∧
            (k.reconstructed.registers.cutoff a).queue = (V a).2 ∧
            (k.reconstructed.registers.cutoff a).lastService = (V a).1 - (Vpre a).1 := by
          rw [hcutoffValue a]
          exact ⟨rfl, rfl, rfl⟩
        have hcurrentFields (a : Fin p.K) :
            (k.reconstructed.registers.current a).queue = (Rwhole D a).2 ∧
            (k.reconstructed.registers.current a).lastService =
              (Rprefix D a out.ell).1 - (Rprefix D a (out.ell - 1)).1 := by
          rw [hcurrentValue a]
          exact ⟨rfl, rfl⟩
        have hcurrentWeight (a : Fin p.K) :
            AssignmentScoreReconstruction.currentWeight k.reconstructed a =
              (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1 := by
          calc
            AssignmentScoreReconstruction.currentWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  AssignmentScoreReconstruction.sourceScore k.reconstructed a := hweight a
            _ = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Rwhole D a).1 := by
              rw [hsourceScore a]
        have hcutoffWeightResult (a : Fin p.K) :
            AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
              (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1 := by
          calc
            AssignmentScoreReconstruction.cutoffWeight k.reconstructed a =
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  (k.reconstructed.registers.cutoff a).score := hcutoffWeight a
            _ = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (V a).1 := by
              rw [(hcutoffFields a).1]
        have hpreviousSub (a : Fin p.K) :
            (V a).1 - ((V a).1 - (Vpre a).1) = (Vpre a).1 := by
          have hsplit : (Vpre a).1 + ((V a).1 - (Vpre a).1) = (V a).1 := by
            calc
              (Vpre a).1 + ((V a).1 - (Vpre a).1) =
                  ((V a).1 - (Vpre a).1) + (Vpre a).1 := Nat.add_comm _ _
              _ = (V a).1 := Nat.sub_add_cancel (hVpre a)
          calc
            (V a).1 - ((V a).1 - (Vpre a).1) =
                ((Vpre a).1 + ((V a).1 - (Vpre a).1)) - ((V a).1 - (Vpre a).1) := by
                  exact congrArg (fun score => score - ((V a).1 - (Vpre a).1)) hsplit.symm
            _ = (Vpre a).1 := Nat.add_sub_cancel_right _ _
        have hpreviousCutoffFunction :
            (fun a : Fin p.K => (k.reconstructed.registers.cutoff a).score -
              (k.reconstructed.registers.cutoff a).lastService) =
              fun a : Fin p.K => (Vpre a).1 := by
          funext a
          rw [hcutoffValue a]
          exact hpreviousSub a
        have hbeforeOperation (hbefore : k.instruction.time.val + 1 <
            k.operationLedger.freezeAt) :
            x.time.val + 1 < d.ledger.freezeAt := by
          calc
            x.time.val + 1 = k.instruction.time.val + 1 := by
              exact congrArg (fun time : Fin p.T => time.val + 1)
                k.instructionTime.symm
            _ < k.operationLedger.freezeAt := hbefore
            _ = d.ledger.freezeAt := hfreezeCopy
        have hafterOperation (hafter : k.operationLedger.freezeAt ≤
            k.instruction.time.val + 1) :
            d.ledger.freezeAt ≤ x.time.val + 1 := by
          calc
            d.ledger.freezeAt = k.operationLedger.freezeAt := hfreezeCopy.symm
            _ ≤ k.instruction.time.val + 1 := hafter
            _ = x.time.val + 1 := congrArg (fun time : Fin p.T => time.val + 1)
              k.instructionTime
        have hpreviousCorrected (hbefore : k.instruction.time.val + 1 <
            k.operationLedger.freezeAt) :
            AssignmentScoreReconstruction.previousScore k.reconstructed =
              some (fun a : Fin p.K => (Vpre a).1) ∧
            AssignmentScoreReconstruction.previousWeight k.reconstructed =
              some (fun a : Fin p.K =>
                (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1) := by
          have hkind : k.instruction.kind = .corrected :=
            hcorrected.mpr (hbeforeOperation hbefore)
          rcases hcorrectedEquations hkind with
            ⟨hpreviousScore, _, ⟨weights, hpreviousWeight, hweightFormula⟩, _⟩
          have hweights : weights = fun a : Fin p.K =>
              (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1 := by
            funext a
            calc
              weights a = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                  ((k.reconstructed.registers.cutoff a).score -
                    (k.reconstructed.registers.cutoff a).lastService) := hweightFormula a
              _ = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (Vpre a).1 := by
                rw [hcutoffValue a, hpreviousSub a]
          refine ⟨?_, ?_⟩
          · rw [hpreviousScore, hpreviousCutoffFunction]
          · rw [hpreviousWeight, hweights]
        have hpreviousRenewal (hafter : k.operationLedger.freezeAt ≤
            k.instruction.time.val + 1) :
            AssignmentScoreReconstruction.previousScore k.reconstructed = none ∧
            AssignmentScoreReconstruction.previousWeight k.reconstructed = none := by
          have hkind : k.instruction.kind = .renewal :=
            hrenewal.mpr (hafterOperation hafter)
          exact hrenewalEquations hkind
        exact ⟨k, hKdataCopy, hsourceScore, hinitialQueue, hcutoffFields,
          hcurrentFields, hcurrentWeight, hcutoffWeightResult,
          hpreviousCorrected, hpreviousRenewal⟩

end Actual

end Bandits.Support.ReferenceFirstCollectionNumericalStartReconstruction

end
