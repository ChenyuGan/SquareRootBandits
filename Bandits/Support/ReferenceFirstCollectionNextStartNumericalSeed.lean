/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream
public import Bandits.Support.ReferenceFirstCollectionCanonicalNextDispatch

import Lean.Elab.Tactic.Omega

/-!
# Numerical seed at the first actual replacement assignment

Pinned mathematical evidence: `appendix_a_local_protocol.tex:42-64`,
`06_interruptions.tex:46-61,80-100,192-233,391-408`, and
`04_slow_fast_learner.tex:157-174`, under `sources/zip4/manuscript/`.

The common source prefix includes every old FINISH and excludes the new
assignment round. The actual boundary retains exhaustion, terminal and checked
prefix-failure cases. This deterministic join supplies the first-replacement
accepted-UP numerical seed consumer; it is not a global assignment induction.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionAllArmNumericalStream

namespace Bandits.Support.ReferenceFirstCollectionNextStartNumericalSeed

variable {p : ConstructorDimensions.Parameters}

private theorem reconstruction_numerical
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (reconstructed : AssignmentScoreReconstruction.ReconstructedStart
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq) instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq) instruction =
      .success _ instruction reconstructed)
    (V Vpre Q Qprev : Fin p.K → ℕ × ℕ)
    (hcut : ∀ a, input.ledger.cutoffRegisters a =
      some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩)
    (hcur : ∀ a, input.ledger.currentRegisters a =
      some ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩)
    (hsum : ∀ a, (V a).1 + input.ledger.increment a = (Q a).1) :
    ∀ a, AssignmentScoreReconstruction.sourceScore reconstructed a = (Q a).1 ∧
      AssignmentScoreReconstruction.initialQueue reconstructed a = (Q a).2 ∧
      reconstructed.registers.current a =
        ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩ := by
  have he := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
    _ instruction reconstructed hrec
  obtain ⟨_, hc, hq, hz, hb, _⟩ := he
  intro a
  have hcv := Option.some.inj ((hc a).symm.trans (hcut a))
  have hqv := Option.some.inj ((hq a).symm.trans (hcur a))
  refine ⟨?_, ?_, hqv⟩
  · rw [hz a, hcv]
    exact hsum a
  · rw [hb a, hqv]

private theorem next_dispatch_numerical_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch x payload l saved)
    (V Vpre Q Qprev : Fin p.K → ℕ × ℕ)
    (hcut : ∀ a, l.cutoffRegisters a =
      some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩)
    (hcur : ∀ a, l.currentRegisters a =
      some ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩)
    (hsum : ∀ a, (V a).1 + l.increment a = (Q a).1) :
    let input := ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved dispatch.cutoffTime) dispatch.cutoffTime
    let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
    ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
    ∃ reconstructed : AssignmentScoreReconstruction.ReconstructedStart operationLedger dispatch.instruction,
      AssignmentScoreReconstruction.reconstructLaterStart operationLedger dispatch.instruction =
        .success operationLedger dispatch.instruction reconstructed ∧
      (∀ a, AssignmentScoreReconstruction.sourceScore reconstructed a = (Q a).1 ∧
        AssignmentScoreReconstruction.initialQueue reconstructed a = (Q a).2 ∧
        reconstructed.registers.current a = ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩) ∧
      ((∃ (arm : Fin p.K) (reason : CheckedPrefixSampler.FailureReason),
        dispatch.instruction.kind = .corrected ∧
        ∃ hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger dispatch.instruction input.row consistent =
            .prefixFailure (some arm) reason,
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterPrefixFailure dispatch.core consistent dispatch.started dispatch.startCheck
            dispatch.instruction dispatch.assignmentStart (some arm) reason hlater) ∨
      ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
          dispatch.instruction input.row,
      ∃ hlocal : output.localConsistency = consistent,
      ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
      ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
      ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
          dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        output.reconstruction = reconstructed ∧
        LaterAssignmentStartOperation.laterAssignmentStart input.payload operationLedger
          dispatch.instruction input.row consistent = .success output hlocal ∧
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
            dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
        installed.registers.payload = output.payload ∧
        installed.registers.payload.sigma = x.time ∧
        installed.assignmentVector = output.assignmentVector ∧
        installed.reconstruction = reconstructed ∧
        (∀ a, installed.registers.payload.queues a = (Q a).2) ∧
        (∀ i : Fin (p.m - 1),
          installed.registers.payload.assignment.assigned i = output.payload.assignment.assigned i ∧
          installed.retainedBaseScore i =
            (Q (installed.registers.payload.assignment.assigned i)).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (Q (installed.registers.payload.assignment.assigned i)).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          installed.registers.complementScores j = (Q j.val).1 ∧
          installed.ownedRegisters.queue j = (Q j.val).2 ∧
          installed.ownedRegisters.previousService j = (Q j.val).1 - (Qprev j.val).1)) := by
  classical
  dsimp only
  obtain ⟨cutoff, hcutoff, core, started, hstart, instruction, hassignment,
    consistent, htime, _hkind, _hprepared, _hfailure, cases⟩ := dispatch.classification
  have hcutoffEq : cutoff = dispatch.cutoffTime := by
    apply Fin.ext
    have h := dispatch.cutoffTimeEq
    omega
  subst cutoff
  have hstartedEq : started = dispatch.started := by
    have h := hstart.symm.trans dispatch.startCheck
    injection h
  subst started
  have hinstructionEq : instruction = dispatch.instruction :=
    Option.some.inj (hassignment.symm.trans dispatch.assignmentStart)
  subst instruction
  rcases cases with hfailure | ⟨reconstructed, hrec, hcase⟩
  · obtain ⟨a, c, hc, hbad, _⟩ := hfailure
    have hc' := Option.some.inj (hc.symm.trans (hcut a))
    subst c
    exact False.elim (Nat.not_lt_of_ge (Nat.sub_le _ _) hbad)
  · have hnum := reconstruction_numerical _ core dispatch.instruction reconstructed hrec
      V Vpre Q Qprev hcut hcur hsum
    refine ⟨consistent, reconstructed, hrec, hnum, ?_⟩
    rcases hcase with hprefix | hsuccess
    · left
      obtain ⟨_hcut, _hpos, _law, arm, reason, hcorrected, _hselected,
        previous, _hprevious, _hprevpos, _hanchor, _hmass, hlater, _hrest,
        _state, _hstate, _hstep, _hpositive, _hratio, hdispatch⟩ := hprefix
      exact ⟨arm, reason, hcorrected, hlater, hdispatch⟩
    · right
      obtain ⟨output, hlocal, clockData, installed, selection, hinstall,
        _hchoice, _hreconstructed, hlater, hdispatch, _hrest⟩ := hsuccess
      have hreconstruction : output.reconstruction = reconstructed := by
        have h := output.reconstruction_eq.symm.trans hrec
        exact eq_of_heq (AssignmentScoreReconstruction.Result.success.inj h).2.2
      refine ⟨output, hlocal, clockData, installed, selection, hinstall, hreconstruction,
        hlater, hdispatch, ?_⟩
      subst installed
      refine ⟨rfl, output.payload_start.trans dispatch.instructionTime, rfl,
        hreconstruction, ?_, ?_, ?_⟩
      · intro a
        rw [CoordinatorAssignmentRegisterInstall.later_payload_queue_eq_initial_queue,
          hreconstruction]
        exact (hnum a).2.1
      · intro i
        refine ⟨rfl, ?_, ?_⟩
        · change output.baseScore i = (Q (output.payload.assignment.assigned i)).1
          rw [output.baseScore_eq_source, hreconstruction]
          exact (hnum _).1
        · change (output.payload.downRecord i).val.q =
            (Q (output.payload.assignment.assigned i)).2
          calc
            _ = output.payload.queues (output.payload.assignment.assigned i) :=
              output.payload.downRecord_initialQueue i
            _ = AssignmentScoreReconstruction.initialQueue output.reconstruction
                (output.payload.assignment.assigned i) := output.payload_queues _
            _ = _ := by rw [hreconstruction]; exact (hnum _).2.1
      · intro j
        refine ⟨?_, ?_, ?_⟩
        · change AssignmentScoreReconstruction.sourceScore output.reconstruction j.val = (Q j.val).1
          rw [hreconstruction]
          exact (hnum j.val).1
        · change AssignmentScoreReconstruction.initialQueue output.reconstruction j.val = (Q j.val).2
          rw [hreconstruction]
          exact (hnum j.val).2.1
        · change (output.reconstruction.registers.current j.val).lastService =
            (Q j.val).1 - (Qprev j.val).1
          rw [hreconstruction, (hnum j.val).2.2]

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)

local notation "s" => ReferenceFirstCollectionReadyStream.startTime (rate := rate)
  source rewards C_star C_h
local notation "E" => ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
  source rewards C_star C_h hcross count hspan
local notation "L" => ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan))
local notation "B" => ReferenceFirstCollectionReadyStream.actualWindow (rate := rate)
  source rewards C_star C_h hcross count hspan
local notation "Cells" => ReferenceFirstWindowNumericalStream.actualLiveSourceCells
  rate source rewards C_star C_h hcross count hspan

include hshort

/-- Join the common original-source numerical prefix to the reconstruction
and installation in the actual next-dispatch classification. All witnesses of
S are retained. At that same boundary a canonical certificate exposes its
stored reconstruction's numerical identity. The physical classification and
its installed payload are retained alongside this certificate; no equality
with the old certificate's unconstrained stored operation ledger is asserted.
Exhaustion, terminal and corrected prefix failure remain literal alternatives. -/
theorem actual_initialized_first_collection_classified_next_start_numerical_seed :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let out := d.stream
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧ head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      let V := fun a => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a Cells)
      let Vpre := fun a => QueueReplay.replay (4 * rate.n) (0, 0)
        (arrivals rate a ((Cells).take ((L).length - 1)))
      let R := fun a h => QueueReplay.replay (4 * rate.n) (0, 0)
        (arrivals rate a (Cells ++ D.take h))
      let I := fun a h => QueueReplay.replay (4 * rate.n) (0, (V a).2) (arrivals rate a (D.take h))
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
          (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
      (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
        (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
          arrivals rate a (D.take h)) ∧
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
            l.currentRegisters a = some ⟨(R a (n.val + 1)).2,
              (R a (n.val + 1)).1 - (R a n.val).1⟩ ∧
            l.increment a = (I a (n.val + 1)).1 ∧
            (V a).1 + l.increment a = (R a (n.val + 1)).1)) ∧
      (d.ledger.pending = ∅ → ∀ a : Fin p.K,
        d.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
        d.ledger.currentRegisters a = some ⟨(R a out.ell).2,
          (R a out.ell).1 - (R a (out.ell - 1)).1⟩ ∧
        d.ledger.increment a = (QueueReplay.replay (4 * rate.n) (0, (V a).2)
          (arrivals rate a D)).1 ∧
        (V a).1 + d.ledger.increment a = (R a out.ell).1) ∧
      (match d.outcome with
      | .exhausted _ _ _ _ _ => True
      | .empty e =>
        match e.nextBoundary with
        | .terminal _ _ => True
        | .next _ _ x _ _ _ _ _ _ _ _ dispatch =>
          x.time.val = s + (L).length + out.ell ∧
          let Q := fun a => QueueReplay.replay (4 * rate.n) (0, 0)
            (arrivals rate a (Cells ++ D))
          let Qprev := fun a => QueueReplay.replay (4 * rate.n) (0, 0)
            (arrivals rate a (Cells ++ D.take (out.ell - 1)))
          ∃ k : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
              x out.payload d.ledger out.saved,
            k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceActivePhysicalStep.collectionInput x out.payload d.ledger
                (ReferenceActivePhysicalStep.collectionClock out.payload d.ledger out.saved
                  k.cutoffTime) k.cutoffTime) k.core.payload_n_eq ∧
            (∀ a, AssignmentScoreReconstruction.sourceScore k.reconstructed a = (Q a).1 ∧
              AssignmentScoreReconstruction.initialQueue k.reconstructed a = (Q a).2 ∧
              k.reconstructed.registers.current a =
                ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩) ∧
          let input := ReferenceActivePhysicalStep.collectionInput x out.payload d.ledger
            (ReferenceActivePhysicalStep.collectionClock out.payload d.ledger out.saved dispatch.cutoffTime) dispatch.cutoffTime
          let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
          ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
          ∃ reconstructed : AssignmentScoreReconstruction.ReconstructedStart operationLedger dispatch.instruction,
            AssignmentScoreReconstruction.reconstructLaterStart operationLedger dispatch.instruction =
              .success operationLedger dispatch.instruction reconstructed ∧
            (∀ a, AssignmentScoreReconstruction.sourceScore reconstructed a = (Q a).1 ∧
              AssignmentScoreReconstruction.initialQueue reconstructed a = (Q a).2 ∧
              reconstructed.registers.current a = ⟨(Q a).2, (Q a).1 - (Qprev a).1⟩) ∧
            ((∃ (arm : Fin p.K) (reason : CheckedPrefixSampler.FailureReason),
              dispatch.instruction.kind = .corrected ∧
              ∃ hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
                operationLedger dispatch.instruction input.row consistent =
                  .prefixFailure (some arm) reason,
              CoordinatorRoundDispatch.dispatchCollection input =
                .laterPrefixFailure dispatch.core consistent dispatch.started dispatch.startCheck
                  dispatch.instruction dispatch.assignmentStart (some arm) reason hlater) ∨
            ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
                dispatch.instruction input.row,
            ∃ hlocal : output.localConsistency = consistent,
            ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
            ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
            ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
                dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
              installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
              output.reconstruction = reconstructed ∧
              LaterAssignmentStartOperation.laterAssignmentStart input.payload operationLedger
                dispatch.instruction input.row consistent = .success output hlocal ∧
              CoordinatorRoundDispatch.dispatchCollection input =
                .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
                  dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
              installed.registers.payload = output.payload ∧
              installed.registers.payload.sigma = x.time ∧
              installed.assignmentVector = output.assignmentVector ∧
              installed.reconstruction = reconstructed ∧
              (∀ a, installed.registers.payload.queues a = (Q a).2) ∧
              (∀ i : Fin (p.m - 1),
                installed.registers.payload.assignment.assigned i = output.payload.assignment.assigned i ∧
                installed.retainedBaseScore i =
                  (Q (installed.registers.payload.assignment.assigned i)).1 ∧
                (installed.registers.payload.downRecord i).val.q =
                  (Q (installed.registers.payload.assignment.assigned i)).2) ∧
              (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
                installed.registers.complementScores j = (Q j.val).1 ∧
                installed.ownedRegisters.queue j = (Q j.val).2 ∧
                installed.ownedRegisters.previousService j = (Q j.val).1 - (Qprev j.val).1))) := by
  classical
  obtain ⟨d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
    hDlen, hzero, hcells, hprefix, hledgers, hfinal⟩ :=
    ReferenceFirstCollectionAllArmNumericalStream.actual_initialized_first_collection_all_arm_numerical_stream
      rate source rewards C_star C_h hcross count hspan hshort
  refine ⟨d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
    hDlen, hzero, hcells, hprefix, hledgers, hfinal, ?_⟩
  cases houtcome : d.outcome with
  | exhausted _ _ _ _ _ => trivial
  | empty e =>
    cases hnext : e.nextBoundary with
    | terminal _ _ => simp only [hnext]
    | next _ _ x _ _ _ _ _ _ _ _ dispatch =>
      simp only [hnext]
      have hcursor := (hledgers d.last).2.2.1
      rw [← d.ledgerIsLast] at hcursor
      have hnextCursor := dispatch.cursor
      have hlast := d.lastIsLast
      refine ⟨by omega, ?_⟩
      obtain ⟨k, hcanonical, _hfields, _hrec, _hchecks, hkcut, hkcur, hkscore,
        hkqueue, _hrest⟩ :=
        ReferenceFirstCollectionCanonicalNextDispatch.exists_canonical_actual_next_dispatch_equations
          x d.stream.payload d.ledger d.stream.saved dispatch
      refine ⟨k, hcanonical, ?_, ?_⟩
      · intro a
        have hcut := Option.some.inj ((hkcut a).symm.trans (hfinal e.pendingEmpty a).1)
        have hcurrent := Option.some.inj ((hkcur a).symm.trans (hfinal e.pendingEmpty a).2.1)
        have hcurrent' : k.reconstructed.registers.current a =
            ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
                (arrivals rate a (Cells ++ D))).2,
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (arrivals rate a (Cells ++ D))).1 -
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (arrivals rate a (Cells ++ D.take (d.stream.ell - 1)))).1⟩ := by
          simpa only [List.take_of_length_le hDlen.le] using hcurrent
        refine ⟨?_, ?_, hcurrent'⟩
        · rw [hkscore a, hcut]
          simpa only [List.take_of_length_le hDlen.le] using (hfinal e.pendingEmpty a).2.2.2
        · rw [hkqueue a, hcurrent']
      apply next_dispatch_numerical_seed rate x d.stream.payload d.ledger d.stream.saved dispatch
        (fun a => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a Cells))
        (fun a => QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a ((Cells).take ((L).length - 1))))
        (fun a => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ D)))
        (fun a => QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a (Cells ++ D.take (d.stream.ell - 1))))
      · intro a
        exact (hfinal e.pendingEmpty a).1
      · intro a
        simpa only [List.take_of_length_le hDlen.le] using (hfinal e.pendingEmpty a).2.1
      · intro a
        simpa only [List.take_of_length_le hDlen.le] using (hfinal e.pendingEmpty a).2.2.2

end Actual

end Bandits.Support.ReferenceFirstCollectionNextStartNumericalSeed

end
