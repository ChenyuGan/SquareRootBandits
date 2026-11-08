/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

/-!
# Canonical stored ledger at the actual next collection dispatch

An `ActualNextDispatch` stores an operation ledger as data. Its default does
not assert that every inhabitant stores the canonical projection. We construct
a new inhabitant at the same physical input and FINISH ledger, using the
canonical ledger supplied by its exhaustive classification. The old inhabitant
supplies a genuine local constructor certificate, including the absence of the
literal corrected prior-domain failure. No equality with its stored ledger is
required or asserted.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

These are internal constructor and checked-operation results. They do not
identify reconstructed data with physical replay vectors, certify sampling or
installation, or close a manuscript statement.

The local constructor also applies to the same `d` and source list `D` produced
by the separate numerical endpoint theorem. The next consumer,
`ReferenceFirstCollectionNumericalStartReconstruction`, can combine that
endpoint with this new witness without identifying two existential streams.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstCollectionCanonicalNextDispatch

open ReferenceFirstCollectionStreamEmptyDispatch

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Construct a canonical stored-ledger witness at the same actual input.
The input `old` is a local constructor certificate, not a numerical truth
assumption or a source-facing premise. Its stored ledger is not identified
with the new ledger; its failure iff and absence proof exclude the same
literal bad condition after transporting both instruction times to `x.time`.
The full classifier, including sample and installation failures, is retained.
-/
theorem exists_canonical_actual_next_dispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceFirstCollectionStreamEmptyDispatch.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (old : ActualNextDispatch x payload l saved) :
    ∃ k : ActualNextDispatch x payload l saved,
      k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved k.cutoffTime)
          k.cutoffTime) k.core.payload_n_eq := by
  rcases old.classification with ⟨cutoff, hcutoff, core, started, hstart, instruction,
    hassignment, consistent, htime, hkind, hprepared, hiff, hcases⟩
  let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
    core.payload_n_eq
  have habsent :
      AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction ≠
        .failure .previousOutputDomain := by
    intro hfailure
    have hbad := hiff.mp hfailure
    apply old.correctedFailureAbsent
    apply old.correctedFailureIff.mpr
    refine ⟨?_, hbad.2⟩
    simpa only [old.instructionTime, htime] using hbad.1
  rcases hcases with hbad | hsuccess
  · rcases hbad with ⟨_a, _c, _hc, _hscore, hfailure, _⟩
    exact False.elim (habsent hfailure)
  · rcases hsuccess with ⟨reconstructed, hcall, _remainingCases⟩
    let k : ActualNextDispatch x payload l saved := {
      actualState := old.actualState
      validLedger := old.validLedger
      readyPhase := old.readyPhase
      sigma := old.sigma
      order := old.order
      cutoffBeforeCursor := old.cutoffBeforeCursor
      cursor := old.cursor
      freeze := old.freeze
      assignment := old.assignment
      emptyPending := old.emptyPending
      unitAnchor := old.unitAnchor
      currentMassBounds := old.currentMassBounds
      currentServiceSpan := old.currentServiceSpan
      nextBankCheck := old.nextBankCheck
      classification := old.classification
      cutoffTime := cutoff
      cutoffTimeEq := hcutoff
      core := core
      started := started
      startCheck := hstart
      instruction := instruction
      assignmentStart := hassignment
      operationLedger := operationLedger
      consistent := consistent
      instructionTime := htime
      expectedKind := hkind
      preparedCoordinator := hprepared
      correctedFailureIff := hiff
      correctedFailureAbsent := habsent
      reconstructed := reconstructed
      reconstructionSuccess := hcall }
    exact ⟨k, rfl⟩

/-- The same constructed witness exposes every copied ledger field and the
equations of its actual successful reconstruction. Corrected starts return
`some` preceding vectors; renewal returns `none`. No sampler or installation
success is selected from the retained exhaustive classifier.
-/
theorem exists_canonical_actual_next_dispatch_equations
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceFirstCollectionStreamEmptyDispatch.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (old : ActualNextDispatch x payload l saved) :
    ∃ k : ActualNextDispatch x payload l saved,
      k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved k.cutoffTime)
          k.cutoffTime) k.core.payload_n_eq ∧
      (k.operationLedger.assignment = l.assignment ∧
        k.operationLedger.sigma = l.sigma ∧
        k.operationLedger.cutoff = l.cutoff ∧
        k.operationLedger.freezeAt = l.freezeAt ∧
        k.operationLedger.baseScore = l.baseScore ∧
        k.operationLedger.pending = l.pending ∧
        k.operationLedger.cutoffRegisters = l.cutoffRegisters ∧
        k.operationLedger.currentRegisters = l.currentRegisters ∧
        k.operationLedger.increment = l.increment ∧
        k.operationLedger.gammaLoc = l.gammaLoc ∧
        k.operationLedger.rawBuffer = l.rawBuffer ∧
        k.operationLedger.enabledHistory = l.enabledHistory ∧
        k.operationLedger.cursor = l.cursor ∧
        k.operationLedger.phase = l.phase) ∧
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
      (∀ a, l.cutoffRegisters a = some (k.reconstructed.registers.cutoff a)) ∧
      (∀ a, l.currentRegisters a = some (k.reconstructed.registers.current a)) ∧
      (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a =
        (k.reconstructed.registers.cutoff a).score + l.increment a) ∧
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
      (k.instruction.kind = .corrected ↔ x.time.val + 1 < l.freezeAt) ∧
      (k.instruction.kind = .renewal ↔ l.freezeAt ≤ x.time.val + 1) ∧
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
        AssignmentScoreReconstruction.previousWeight k.reconstructed = none) := by
  obtain ⟨k, hcanonical⟩ :=
    exists_canonical_actual_next_dispatch x payload l saved old
  have hfields := CoordinatorRoundDispatch.collectionOperationLedger_fields
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved k.cutoffTime)
      k.cutoffTime) k.core.payload_n_eq
  rw [← hcanonical] at hfields
  simp only [ReferenceActivePhysicalStep.collectionInput] at hfields
  rcases hfields with ⟨hassignment, hsigma, hcutoff, hfreeze, hbase, hpending,
    hcutoffRegisters, hcurrentRegisters, hincrement, hgamma, hraw, henabled, hcursor,
    hphase⟩
  obtain ⟨hchecks, hcutoffEq, hcurrentEq, hscore, hqueue, hweight, hcutoffWeight,
    hweightPos, hcutoffPos, hscoreBound, hqueueBound⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
  have hcorrected := AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff
    k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
  have hrenewal := AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff
    k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
  refine ⟨k, hcanonical,
    ⟨hassignment, hsigma, hcutoff, hfreeze, hbase, hpending, hcutoffRegisters,
      hcurrentRegisters, hincrement, hgamma, hraw, henabled, hcursor, hphase⟩,
    k.reconstructionSuccess, hchecks, ?_, ?_, ?_, hqueue, hweight, hcutoffWeight,
    hweightPos, hcutoffPos, hscoreBound, hqueueBound, ?_, ?_, ?_, ?_⟩
  · simpa only [hcutoffRegisters] using hcutoffEq
  · simpa only [hcurrentRegisters] using hcurrentEq
  · simpa only [hincrement] using hscore
  · simpa only [k.instructionTime, hfreeze] using hcorrected
  · simpa only [k.instructionTime, hfreeze] using hrenewal
  · exact AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
      k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
  · exact AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
      k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess

/-- Instantiate the admitted actual-source producer, then canonicalize its
actual next input inside the conclusion. The terminal sentinel and every
original-prefix identity are retained. The same output `d` still carries its
exhaustion alternative, original accepted FINISH, and full stream evidence.
No output, history, ledger identity, or reconstruction success is an input.
-/
theorem actual_initialized_first_collection_canonical_next_dispatch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ActualInitializedStreamDispatch (p := p) (rate := rate)
        source rewards C_star C_h count hcross hspan hshort,
      ∀ e : EmptyPendingBoundary source rewards C_star C_h count hcross hspan hshort
        d.stream d.last d.ledger d.record,
      d.outcome = .empty e →
      match e.nextBoundary with
      | .terminal _ _ =>
          d.record.input.time.val + 1 = p.T ∧ d.ledger.cursor = p.T + 1
      | .next before current x _ _ _ _ _ _ _ _ _ =>
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
            e.prefixRun ⟨d.record.input.time.val + 1,
              ⟨Nat.le_trans current (Nat.le_succ _), before⟩⟩ ∧
          x.state = d.record.output.next ∧
          x.time.val = d.record.input.time.val + 1 ∧
          x.rows = source.1.2 ∧
          x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          x.rewards = rewards ∧
          (∀ rNext, d.stream.window[d.stream.ell]? = some rNext → x = rNext.input) ∧
          (∀ rNext,
            (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
              source rewards C_star C_h hcross count hspan).records[
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                  (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                    source rewards C_star C_h hcross count hspan).records).length +
                d.stream.ell]? = some rNext → x = rNext.input) ∧
            ∃ k : ActualNextDispatch x d.stream.payload d.ledger d.stream.saved,
              k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x d.stream.payload d.ledger
                  (ReferenceActivePhysicalStep.collectionClock d.stream.payload d.ledger d.stream.saved k.cutoffTime)
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
              (k.instruction.kind = .corrected ↔ x.time.val + 1 < d.ledger.freezeAt) ∧
              (k.instruction.kind = .renewal ↔ d.ledger.freezeAt ≤ x.time.val + 1) ∧
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
                AssignmentScoreReconstruction.previousWeight k.reconstructed = none) := by
  obtain ⟨d⟩ :=
    ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  intro e _hempty
  cases e.nextBoundary with
  | terminal htime hcursor => exact ⟨htime, hcursor⟩
  | next before current x original hstate htime hrows hselected hwhole hwindow hrun old =>
      exact ⟨before, current, original, hstate, htime, hrows, hselected, hwhole, hwindow, hrun,
        exists_canonical_actual_next_dispatch_equations
          x d.stream.payload d.ledger d.stream.saved old⟩

end Bandits.Support.ReferenceFirstCollectionCanonicalNextDispatch

end
