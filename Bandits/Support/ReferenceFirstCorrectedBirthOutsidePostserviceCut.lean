/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover

import Mathlib.Tactic

/-!
# Corrected first-birth outside service and replay

This module derives the finite source-mass bound at the actual corrected
first-call birth.  The inputs are the complete reward table and the original
private source; retained past cells are obtained from the actual calendar
coverage and the original live/collection readouts.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstLaunchNumericalCell (queueParameters)

namespace Bandits.Support.ReferenceFirstCorrectedBirthOutsidePostserviceCut

variable {p : ConstructorDimensions.Parameters}

private theorem pastCell_rate_feasible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    ∀ a : Fin p.K, (rate.n : ℝ) ≤ (D p : ℝ) * c.rate a := by
  intro a
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r) = some c at hc
  cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some live =>
      have hliveEq : live = c := by simpa [hlive] using hc
      subst c
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r live hlive
      have hβ : CanonicalRecordingRates.beta p rate.eta.val ≤ live.rate a := by
        rw [hrate]
        exact selected.view.payload.beta_le_rate a
      rw [rate.n_scale, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (AssignmentStartPayload.Input.eta_le_beta.trans hβ)
        (Nat.cast_nonneg (D p))
  | none =>
      have hcollection :
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
        simpa [hlive] using hc
      obtain ⟨payload, _, _, _, _, _, _, _, _, _, hrate, _, _, _, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
          0 r c hcollection
      have hβ : CanonicalRecordingRates.beta p rate.eta.val ≤ c.rate a := by
        rw [hrate]
        exact payload.beta_le_rate a
      rw [rate.n_scale, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (AssignmentStartPayload.Input.eta_le_beta.trans hβ)
        (Nat.cast_nonneg (D p))

private theorem acceptedTotal_unstopped_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (cells : List (RecordedQueueRun.RoundInput p.K))
    (hfeasible : ∀ c ∈ cells, ∀ a : Fin p.K,
      ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate a)
    (a : Fin p.K) :
    RecordedQueueRun.acceptedTotal
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
        (queueParameters rate) c a) ≤ cells.length * (D p) := by
  induction cells with
  | nil => simp [RecordedQueueRun.acceptedTotal]
  | cons c cells ih =>
      have hhead :
          RecordedQueueRun.acceptedArrival
            (UnstoppedRecordedQueueComparison.unstoppedRecord
              (queueParameters rate) c a) ≤ D p := by
        cases hc : c.enabled
        · simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hc,
            RecordedQueueRun.acceptedArrival]
        · simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, hc,
            ite_true, RecordedQueueRun.acceptedArrival]
          have hcellFeasible : ∀ i : Fin p.K,
              ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate i :=
            hfeasible c (by simp)
          exact RecordedQueueRun.quantizedArrival_le_D (queueParameters rate) c
            hcellFeasible a
      have hcellTail : ∀ round ∈ cells, ∀ i : Fin p.K,
          ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * round.rate i := by
        intro round hround i
        exact hfeasible round (by simp [hround]) i
      have htail := ih hcellTail
      change RecordedQueueRun.acceptedArrival
          (UnstoppedRecordedQueueComparison.unstoppedRecord
            (queueParameters rate) c a) +
        RecordedQueueRun.acceptedTotal
          (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
            (queueParameters rate) c a) ≤
        (List.length (c :: cells)) * D p
      rw [List.length_cons]
      calc
        _ ≤ D p + cells.length * D p := Nat.add_le_add hhead htail
        _ = (cells.length + 1) * D p := by rw [Nat.add_mul]; simp [Nat.add_comm]

private theorem unstopped_replay_mass
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (cells : List (RecordedQueueRun.RoundInput p.K))
    (hfeasible : ∀ c ∈ cells, ∀ a : Fin p.K,
      ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate a)
    (a : Fin p.K) :
    let state := UnstoppedRecordedQueueComparison.unstoppedReplay
      (queueParameters rate) cells cells.length a
    state.1 + state.2 ≤ cells.length * D p := by
  let records := cells.map fun c =>
    UnstoppedRecordedQueueComparison.unstoppedRecord (queueParameters rate) c a
  have htotal :
      (QueueReplay.replay (4 * (queueParameters rate).n) (0, 0) records).1 +
        (QueueReplay.replay (4 * (queueParameters rate).n) (0, 0) records).2 =
        0 + 0 + RecordedQueueRun.acceptedTotal records := by
    simpa using RecordedQueueRun.replay_total
      (4 * (queueParameters rate).n) (0, 0) records
  have hsum := acceptedTotal_unstopped_le rate cells hfeasible a
  dsimp only
  dsimp only [UnstoppedRecordedQueueComparison.unstoppedReplay]
  rw [List.take_length]
  change
    (QueueReplay.replay (4 * (queueParameters rate).n) (0, 0)
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
        (queueParameters rate) c a)).1 +
      (QueueReplay.replay (4 * (queueParameters rate).n) (0, 0)
        (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
          (queueParameters rate) c a)).2 ≤ cells.length * D p
  rw [show cells.map (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
      (queueParameters rate) c a) = records from rfl]
  calc
    _ = 0 + 0 + RecordedQueueRun.acceptedTotal records := htotal
    _ ≤ cells.length * D p := by simpa [records] using hsum

/-- Every strict-past original cell is feasible at every arm, whether it was
read through the live recorder or through the collection recorder. -/
theorem firstCell_birth_past_rate_feasible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some L) :
    ∀ c ∈ L, ∀ a : Fin p.K,
      ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate a := by
  obtain ⟨hc, hs, hshort, f, head, valid, D0, L0, _hsu, _hut, _hu, _ht,
      _hpending, _hlast, _hhead, _hDlen, _hD0, _hDread,
      hLsource, hcoverage, hlength, hslots⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz.1
  have hsame : L0 = L := Option.some.inj (hcoverage.symm.trans hL)
  intro c hmem a
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  subst c
  have hi0 : i < L0.length := by rw [hsame]; exact hi
  obtain ⟨r, _hrecord, _htime, hcell⟩ := hslots ⟨i, hi0⟩
  have hcell' : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some L[i] := by
    simpa [hsame] using hcell
  exact pastCell_rate_feasible rate r L[i] hcell' a

/-- The actual first corrected birth has a finite all-arm strict-past mass
bound. The current service is not included in this prefix bound. -/
theorem firstCell_birth_past_mass
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    ∃ L c,
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z ∧
      c.enabled = true ∧
      ∀ a : Fin p.K,
        let state := UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length a
        state.1 + state.2 ≤ L.length * D p := by
  obtain ⟨L, c, hL, hc, hinputs, hlength⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_initial_inputs
      rate rewards C_star C_h u t z hz
  obtain ⟨L0, c0, birth0, _hL0, _hc0, _hpref0, _hLb, _hbsub, _htime,
      henabled, _hbirth, _hrecord, _hbtime, _hrows, _hselected, _hrewards,
      _hprep, _hnext⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  have hsameL : L0 = L := Option.some.inj (_hL0.symm.trans hL)
  have hsameC : c0 = c := Option.some.inj (_hc0.symm.trans hc)
  subst L0
  subst c0
  refine ⟨L, c, hL, hc, hinputs, hlength, henabled, ?_⟩
  have hfeasible := firstCell_birth_past_rate_feasible
    rate rewards C_star C_h u t z hz L hL
  intro a
  exact unstopped_replay_mass rate L hfeasible a

private theorem firstCell_birth_current_total_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hmass : ∀ a : Fin p.K,
      let state := UnstoppedRecordedQueueComparison.unstoppedReplay
        (queueParameters rate) L L.length a
      state.1 + state.2 ≤ L.length * D p)
    (hcurrentFeasible : ∀ a : Fin p.K,
      ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate a)
    (hlen : L.length + 1 ≤ p.T) (a : Fin p.K) :
    let state := UnstoppedRecordedQueueComparison.unstoppedReplay
      (queueParameters rate) L L.length a
    state.1 + state.2 + RecordedQueueRun.quantizedArrival
      (queueParameters rate) c a ≤ p.T * D p := by
  have harrival := RecordedQueueRun.quantizedArrival_le_D
    (queueParameters rate) c hcurrentFeasible a
  have hbound := hmass a
  change _ + _ + _ ≤ _
  calc
    _ ≤ L.length * D p + D p := Nat.add_le_add hbound harrival
    _ = (L.length + 1) * D p := by rw [Nat.add_mul]; simp [Nat.add_comm]
    _ ≤ p.T * D p := Nat.mul_le_mul_right (D p) hlen

/-- The native first-birth service pass succeeds before confirmation or
FINISH.  Every field below is tied to the same actual birth, installation,
recording and serviced register vector; later rejection leaves this service
and its replay identity intact. -/
theorem firstCell_birth_outside_postservice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z ∧
      c.enabled = true ∧
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧
      birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
          instruction.time = t ∧ instruction.kind = .corrected ∧
          installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          installed.registers.payload = output.payload ∧
          installed.registers.payload.sigma = t ∧
          (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
            (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
              UnstoppedRecordedQueueComparison.unstoppedReplay
                (queueParameters rate) L L.length j.val ∧
            installed.ownedRegisters.previousService j =
              (UnstoppedRecordedQueueComparison.unstoppedReplay
                (queueParameters rate) L L.length j.val).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay
                (queueParameters rate) (L.take (L.length - 1))
                  (L.take (L.length - 1)).length j.val).1) ∧
          c.rate = installed.registers.payload.rate ∧
          birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
            birth.output.preparation installed.registers installed.ownedRegisters
            installed.retainedBaseScore started ∧
          birth.output.next.coordinator = birth.output.coordinator.configuration ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
              installed.registers installed.ownedRegisters),
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation
                installed.registers started) = some recording ∧
            birth.output.coordinator.recording = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers
              installed.ownedRegisters recording = .ok serviced ∧
            (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
              (serviced.score j, serviced.queue j) =
                UnstoppedRecordedQueueComparison.unstoppedReplay
                  (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val ∧
              serviced.previousService j =
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (queueParameters rate) L L.length j.val).1) ∧
            (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
              (serviced.queue j : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val) →
              ∃ d : Fin p.K,
                z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent
                  rate rewards C_star C_h u t d) ∧
            ((CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = none ∧
              birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                birth.input.state.upDecoderBank (.live .confirmationRejected)
                (some recording) none) ∨
             (∃ pending reason,
              CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = some pending ∧
              CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
                started.clock pending birth.input.row = .error reason ∧
              birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                birth.input.state.upDecoderBank
                (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
                (some recording) none) ∨
             (∃ pending finished,
              CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = some pending ∧
              CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
                started.clock pending birth.input.row = .ok finished ∧
              birth.output.coordinator =
                ⟨.live {
                    payload := installed.registers.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := birth.input.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  { queue := serviced.queue
                    previousService := serviced.previousService }
                  installed.retainedBaseScore,
                  birth.input.state.upDecoderBank, none, some recording, none⟩))
      | _ => False) := by
  obtain ⟨L, c, hL, hc, hprefix, hlength, henabled, hmass⟩ :=
    firstCell_birth_past_mass rate rewards C_star C_h u t z hz
  obtain ⟨L0, c0, birth, hL0, hc0, _hprefix0, hLb, hbsub, _htime,
      henabled0, hbirthSource, hactual, hbirthTime, hrows, hselected, hrewards,
      hprepared, hnextCase⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  have hsameL : L0 = L := Option.some.inj (hL0.symm.trans hL)
  have hsameC : c0 = c := Option.some.inj (hc0.symm.trans hc)
  subst L0
  subst c0
  change (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? = some birth at hbirthSource
  have hlengthT : L.length + 1 ≤ p.T := by rw [hlength]; omega
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  obtain ⟨hinstTime, hkind, hinstall, hpayload, hsigma, _hvector,
    _hvectorRow, hreconstruction, _hwhole, _hfollowers, hcomplement,
    hrate, _hreward, hco, hconfiguration, hreturnCase⟩ := hprepared
  obtain ⟨n0, birth0, theta, _hbslot, _hbirthTime, hactual0, _hcall,
      _hrows0, _hselected0, _hrewards0, hreal⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_realization
      rate rewards C_star C_h u t z hz.1
  have hbirthEq : birth0 = birth := Option.some.inj (hactual0.symm.trans hactual)
  subst birth0
  simp only [hcoord] at hreal
  obtain ⟨_hn, _hinstallReal, cell, hcell, _hread, _hselection, hview,
      _hpayloadCell, _hpending, _hsigmaCell, _hstates, _hfollowersCell,
      henabledCell, hrateCell, _hrewardCell, _hmarker, _hquantized,
      _hfollowerArrival, hrecording, _hlogging, _howners, _hallowners⟩ := hreal
  have hcellEq : cell.input = c := Option.some.inj (hcell.symm.trans hc)
  have hcurrentFeasible : ∀ a : Fin p.K,
      ((queueParameters rate).n : ℝ) ≤ (D p : ℝ) * c.rate a := by
    intro a
    have hβ : CanonicalRecordingRates.beta p rate.eta.val ≤
        installed.registers.payload.rate a :=
      installed.registers.payload.beta_le_rate a
    rw [← hcellEq, hrateCell]
    change (rate.n : ℝ) ≤ (D p : ℝ) * installed.registers.payload.rate a
    rw [rate.n_scale, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (AssignmentStartPayload.Input.eta_le_beta.trans hβ)
      (Nat.cast_nonneg (D p))
  have hcellEnabled : c.enabled = true := by simpa [hcellEq] using henabledCell
  have hlenPrefix : (L ++ [c]).length = L.length + 1 := by simp
  have hcurrentMass (a : Fin p.K) :
      let state := UnstoppedRecordedQueueComparison.unstoppedReplay
        (queueParameters rate) L L.length a
      state.1 + state.2 + RecordedQueueRun.quantizedArrival
        (queueParameters rate) c a ≤ p.T * D p := by
    exact firstCell_birth_current_total_bound rate L c hmass hcurrentFeasible
      hlengthT a
  have hdomains := CoordinatorAssignmentRegisterInstall.later_register_domains
    output clockData
  have hqueueInput : installed.ownedRegisters.queueDomainValid := by
    rw [hinstall]
    exact hdomains.2.1
  have hpreviousInput : installed.ownedRegisters.previousServiceDomainValid := by
    rw [hinstall]
    exact hdomains.2.2
  have hrecordTrace :
      ReferenceCoordinatorRecorderCallTrace.recording
        (ReferenceActiveHorizonMeasurability.roundRecordCode birth) =
        birth.output.coordinator.recording :=
    ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics birth
  obtain ⟨recording0, hdiagRecording, hraw⟩ := hrecording
  have htraceRecording :
      ReferenceCoordinatorRecorderCallTrace.recording
        (ReferenceActiveHorizonMeasurability.roundRecordCode birth) = some recording0 := by
    rw [hrecordTrace]
    exact hdiagRecording
  let selectedData := ReferenceLiveDispatchOutputMeasurability.encodeSelection cell.selected
  have hselectedPayload : selectedData.1.payload = installed.registers.payload := by
    simpa [selectedData, ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hview
  have hrawJoin (j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      CoordinatorLiveServiceFinish.complementArrival installed.registers.payload
          recording0 j = RecordedQueueRun.quantizedArrival
            (queueParameters rate) c j.val := by
    have houtside : j.val ∉ cell.selected.view.payload.slowSet.val := by
      rw [hview]
      exact (Finset.mem_sdiff.mp j.2).2
    have hrawActual := hraw j.val houtside
    rw [hcellEq] at hrawActual
    let selectedJ : CanonicalFastSampling.FastArm selectedData.1.payload.slowSet :=
      ⟨j.val, by simp [selectedData, hselectedPayload]⟩
    have htrace := ReferenceCoordinatorRecorderCallTrace.coordinatorRaw_eq_complementArrival
      (ReferenceActiveHorizonMeasurability.roundRecordCode birth) selectedData selectedJ
    rw [htraceRecording] at htrace
    simp only [Option.map_some] at htrace
    have hjoin : CoordinatorLiveServiceFinish.complementArrival
        selectedData.1.payload recording0 selectedJ =
      CoordinatorLiveServiceFinish.complementArrival
        installed.registers.payload recording0 j := by
      simp [CoordinatorLiveServiceFinish.complementArrival, selectedJ]
    have htrace' :
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
            (ReferenceActiveHorizonMeasurability.roundRecordCode birth) j.val =
          some (CoordinatorLiveServiceFinish.complementArrival
            installed.registers.payload recording0 j) := by
      calc
        _ = some (CoordinatorLiveServiceFinish.complementArrival
            selectedData.1.payload recording0 selectedJ) := by
              simpa [selectedData, selectedJ] using htrace
        _ = some (CoordinatorLiveServiceFinish.complementArrival
            installed.registers.payload recording0 j) := congrArg some hjoin
    rw [hrawActual] at htrace'
    exact Option.some.inj htrace'.symm
  have harrivalInput : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      CoordinatorLiveServiceFinish.complementArrival installed.registers.payload
          recording0 j ≤ D p := by
    intro j
    rw [hrawJoin j]
    exact RecordedQueueRun.quantizedArrival_le_D (queueParameters rate) c
      hcurrentFeasible j.val
  have hclock_n : installed.registers.payload.n = (queueParameters rate).n := by
    exact ReferenceActivePhysicalStep.payload_n_eq installed.registers.payload
  have hserviceInput : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      CappedService.service (4 * installed.registers.payload.n)
        (installed.ownedRegisters.queue j)
        (CoordinatorLiveServiceFinish.complementArrival installed.registers.payload
          recording0 j) ≤ D p := by
    intro j
    have hcap : 4 * installed.registers.payload.n ≤ D p := by
      calc
        4 * installed.registers.payload.n = 4 * (queueParameters rate).n := by
          rw [show installed.registers.payload.n = (queueParameters rate).n from hclock_n]
        _ ≤ D p := (queueParameters rate).capacity_le_D
    exact (CappedService.service_le_capacity _ _ _).trans hcap
  have hscoreOutput : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      installed.registers.complementScores j +
          CappedService.service (4 * installed.registers.payload.n)
            (installed.ownedRegisters.queue j)
            (CoordinatorLiveServiceFinish.complementArrival installed.registers.payload
              recording0 j) ≤ p.T * D p := by
    intro j
    have htotal := hcurrentMass j.val
    have hseedS : installed.registers.complementScores j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).1 := by
      simpa using congrArg Prod.fst (hcomplement j).1
    have hseedB : installed.ownedRegisters.queue j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).2 := by
      simpa using congrArg Prod.snd (hcomplement j).1
    dsimp only at htotal
    rw [← hseedS, ← hseedB] at htotal
    have hserviceEq :
        CappedService.service (4 * installed.registers.payload.n)
          (installed.ownedRegisters.queue j)
          (CoordinatorLiveServiceFinish.complementArrival
            installed.registers.payload recording0 j) =
        CappedService.service (4 * installed.registers.payload.n)
          (installed.ownedRegisters.queue j)
          (RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val) := by
      rw [hrawJoin j]
    rw [hserviceEq]
    have hconservation := CappedService.residual_add_service
      (4 * installed.registers.payload.n) (installed.ownedRegisters.queue j)
      (RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val)
    omega
  have hqueueOutput : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      CappedService.residual (4 * installed.registers.payload.n)
        (installed.ownedRegisters.queue j)
        (CoordinatorLiveServiceFinish.complementArrival installed.registers.payload
          recording0 j) ≤ p.T * D p := by
    intro j
    have htotal := hcurrentMass j.val
    have hseedS : installed.registers.complementScores j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).1 := by
      simpa using congrArg Prod.fst (hcomplement j).1
    have hseedB : installed.ownedRegisters.queue j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).2 := by
      simpa using congrArg Prod.snd (hcomplement j).1
    dsimp only at htotal
    rw [← hseedS, ← hseedB] at htotal
    have hresidualEq :
        CappedService.residual (4 * installed.registers.payload.n)
          (installed.ownedRegisters.queue j)
          (CoordinatorLiveServiceFinish.complementArrival
            installed.registers.payload recording0 j) =
        CappedService.residual (4 * installed.registers.payload.n)
          (installed.ownedRegisters.queue j)
          (RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val) := by
      rw [hrawJoin j]
    rw [hresidualEq]
    have hconservation := CappedService.residual_add_service
      (4 * installed.registers.payload.n) (installed.ownedRegisters.queue j)
      (RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val)
    omega
  have hserviceExists : ∃ serviced : CoordinatorLiveServiceFinish.ServicedRegisters
      installed.registers installed.ownedRegisters,
      CoordinatorLiveServiceFinish.servicePass installed.registers
        installed.ownedRegisters recording0 = .ok serviced := by
    unfold CoordinatorLiveServiceFinish.servicePass
    simp [hqueueInput, hpreviousInput, harrivalInput, hserviceInput,
      hscoreOutput, hqueueOutput]
  obtain ⟨serviced, hservice⟩ := hserviceExists
  have hsrec : serviced.recording = recording0 := by
    have hproj := congrArg (fun result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ServicedRegisters installed.registers
          installed.ownedRegisters) =>
        result.toOption.map (fun s => s.recording)) hservice
    simp [CoordinatorLiveServiceFinish.servicePass, hqueueInput, hpreviousInput,
      harrivalInput, hserviceInput, hscoreOutput, hqueueOutput] at hproj
    exact Option.some.inj hproj.symm
  have hrun : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation
        installed.registers started) = some recording0 := by
    have hcoRecording := congrArg (fun obs => obs.recording) hco
    calc
      _ = (ReferenceActivePhysicalStep.livePostChoice birth.output.preparation
          installed.registers installed.ownedRegisters installed.retainedBaseScore started).recording :=
        (ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run
          birth.output.preparation installed.registers installed.ownedRegisters
          installed.retainedBaseScore started).symm
      _ = birth.output.coordinator.recording := hcoRecording.symm
      _ = some recording0 := hdiagRecording
  have harrivalEq (j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      serviced.arrival j = RecordedQueueRun.quantizedArrival
        (queueParameters rate) c j.val := by
    rw [serviced.arrival_eq]
    rw [show serviced.recording = recording0 from hsrec]
    rw [hrawJoin]
  have hqueueReplay (j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      (serviced.score j, serviced.queue j) =
        UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val := by
    have htransition := CoordinatorLiveServiceFinish.serviced_queueReplay_transition
      installed.registers installed.ownedRegisters serviced j
    have hseedS : installed.registers.complementScores j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).1 := by
      simpa using congrArg Prod.fst (hcomplement j).1
    have hseedB : installed.ownedRegisters.queue j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).2 := by
      simpa using congrArg Prod.snd (hcomplement j).1
    rw [hseedS, hseedB] at htransition
    have hstep :
        QueueReplay.transition (4 * (queueParameters rate).n)
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (queueParameters rate) L L.length j.val)
          (true, RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val) =
          (serviced.score j, serviced.queue j) := by
      simpa [hclock_n, harrivalEq j] using htransition
    have htake : List.take (L.length + 1) (L ++ [c]) = L ++ [c] := by
      calc
        List.take (L.length + 1) (L ++ [c]) =
            List.take ((L ++ [c]).length) (L ++ [c]) := by simp
        _ = L ++ [c] := by simp
    have happend :
        UnstoppedRecordedQueueComparison.unstoppedReplay
            (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val =
          QueueReplay.transition (4 * (queueParameters rate).n)
            (UnstoppedRecordedQueueComparison.unstoppedReplay
              (queueParameters rate) L L.length j.val)
            (true, RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val) := by
      unfold UnstoppedRecordedQueueComparison.unstoppedReplay
      simp only [List.length_append, List.length_singleton, htake,
        List.take_length, List.map_append]
      rw [QueueReplay.replay_append]
      simp [UnstoppedRecordedQueueComparison.unstoppedRecord, hcellEnabled,
        QueueReplay.replay]
    exact hstep.symm.trans happend.symm
  have hpreviousReplay
      (j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      serviced.previousService j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val).1 -
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).1 := by
    have hpair := hcomplement j
    have hbase : installed.registers.complementScores j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) L L.length j.val).1 := by
      simpa using congrArg Prod.fst hpair.1
    have hnew : serviced.score j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val).1 := by
      simpa using congrArg Prod.fst (hqueueReplay j)
    have hdiff : serviced.score j -
        (installed.registers.complementScores j) = serviced.service j := by
      rw [serviced.score_eq j]
      omega
    rw [serviced.previousService_eq j]
    omega
  have hconfirmCases :
      ((CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
          started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row
          birth.output.preparation.coordinatorObservation = none ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank (.live .confirmationRejected)
          (some recording0) none) ∨
       (∃ pending reason,
        CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
          started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row
          birth.output.preparation.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
          started.clock pending birth.input.row = .error reason ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank
          (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
          (some recording0) none) ∨
       (∃ pending finished,
        CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
          started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row
          birth.output.preparation.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
          started.clock pending birth.input.row = .ok finished ∧
        birth.output.coordinator =
          ⟨.live {
              payload := installed.registers.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := birth.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue
              previousService := serviced.previousService }
          installed.retainedBaseScore,
            birth.input.state.upDecoderBank, none, some recording0, none⟩)) := by
    cases hnext : birth.output.next.coordinator with
    | first =>
        simp only [hnext] at hreturnCase
    | live rout qout baseout =>
        simp only [hnext] at hreturnCase
        rcases hreturnCase with ⟨_hrout, _hbase, recording, serviced', pending,
          finished, hrun', hservice', hconfirm', hfinish', hout, _hqueues⟩
        have hrecordingEq : recording = recording0 := Option.some.inj
          (hrun'.symm.trans hrun)
        subst recording
        have hservicedEq : serviced' = serviced := Except.ok.inj
          (hservice'.symm.trans hservice)
        subst serviced'
        exact Or.inr (Or.inr ⟨pending, finished, hconfirm', hfinish', hout⟩)
    | dagger =>
        simp only [hnext] at hreturnCase
        rcases hreturnCase with hnone | ⟨recording, reason, hrun', hservice', _hout⟩ |
          ⟨recording, serviced', hrun', hservice', hconfirm', hout⟩ |
          ⟨recording, serviced', pending, reason, hrun', hservice', hconfirm', hfinish', hout⟩
        · have hbad : none = some recording0 := hnone.1.symm.trans hrun
          cases hbad
        · have hrecordingEq : recording = recording0 := Option.some.inj
            (hrun'.symm.trans hrun)
          subst recording
          have hbad : Except.error reason = Except.ok serviced := hservice'.symm.trans hservice
          cases hbad
        · have hrecordingEq : recording = recording0 := Option.some.inj
            (hrun'.symm.trans hrun)
          subst recording
          have hservicedEq : serviced' = serviced := Except.ok.inj
            (hservice'.symm.trans hservice)
          subst serviced'
          exact Or.inl ⟨hconfirm', hout⟩
        · have hrecordingEq : recording = recording0 := Option.some.inj
            (hrun'.symm.trans hrun)
          subst recording
          have hservicedEq : serviced' = serviced := Except.ok.inj
            (hservice'.symm.trans hservice)
          subst serviced'
          exact Or.inr (Or.inl ⟨pending, reason, hconfirm', hfinish', hout⟩)
    | collection payload ledger proposal =>
        simp only [hnext] at hreturnCase
  refine ⟨L, c, birth, hL, hc, hprefix, hlength, henabled, ?_⟩
  refine ⟨hbirthSource, hactual, hbirthTime, hrows, hselected, hrewards, ?_⟩
  simp only [hcoord]
  refine ⟨hinstTime, hkind, hinstall, hpayload, hsigma, ?_, hrate, hco,
    hconfiguration, ?_⟩
  · intro j
    exact hcomplement j
  · refine ⟨recording0, serviced, hrun, hdiagRecording, hservice, ?_, ?_, hconfirmCases⟩
    · intro j
      exact ⟨hqueueReplay j, hpreviousReplay j⟩
    · intro j hcross
      classical
      have hfullCross : UnstoppedRecordedQueueComparison.replay_crosses_overflow
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length := by
        apply (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length).2
        refine ⟨j.val, ?_⟩
        have hqueueEq := congrArg Prod.snd (hqueueReplay j)
        change ((UnstoppedRecordedQueueComparison.unstoppedReplay
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length j.val).2 : ℝ) /
            ((queueParameters rate).n : ℝ) >
          1 / (32 * (queueParameters rate).eta)
        change _ / (rate.n : ℝ) > 1 / (32 * rate.eta.val)
        rw [← hqueueEq]
        exact hcross
      let h := UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (queueParameters rate) (L ++ [c])
      have hcrossingExists : ∃ n, 1 ≤ n ∧ n ≤ (L ++ [c]).length ∧
          UnstoppedRecordedQueueComparison.replay_crosses_overflow
            (queueParameters rate) (L ++ [c]) n :=
        ⟨(L ++ [c]).length, by simp [List.length_append], le_rfl, hfullCross⟩
      have hfirstle : h ≤ (L ++ [c]).length := by
        change UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (queueParameters rate) (L ++ [c]) ≤ (L ++ [c]).length
        rw [UnstoppedRecordedQueueComparison.firstOverflowPrefix,
          dite_eq_left hcrossingExists]
        exact Nat.find_min' hcrossingExists
          ⟨by simp [List.length_append], le_rfl, hfullCross⟩
      have hfirstcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
        (queueParameters rate) (L ++ [c]) hfirstle
      obtain ⟨d, hcut⟩ := hfirstcross
      let on := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run (queueParameters rate) (L ++ [c]))
      have hon : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h (t.val + 1) z = some on := by
        simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
          hprefix, Option.map_some]
        simp only [on]
      have hprefixState :=
        (UnstoppedRecordedQueueComparison.prefix_state_comparison
          (queueParameters rate) (L ++ [c]) (L ++ [c]).length le_rfl).1 d
      have hmin : min (L ++ [c]).length h = h := Nat.min_eq_right hfirstle
      rw [List.take_length, hmin] at hprefixState
      have hregister : (on.1 d).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (queueParameters rate) (L ++ [c]) h d).2 := by
        change ((RecordedQueueRun.run (queueParameters rate) (L ++ [c])).registers d).2 = _
        exact congrArg Prod.snd hprefixState
      have hcutCurrent : 32 * (on.1 d).2 > (queueParameters rate).D := by
        rw [hregister]
        exact hcut
      have hnormalized :=
        (RecordedQueueRun.overflowCutoff_iff (queueParameters rate) (on.1 d).2).mpr
          hcutCurrent
      change _ > 1 / (32 * rate.eta.val) at hnormalized
      have hend :=
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
          rate rewards C_star C_h u t z hz).1
      refine ⟨d, ?_⟩
      exact ⟨hz, t.val + 1, le_rfl, hend, on, hon, hnormalized⟩

end Bandits.Support.ReferenceFirstCorrectedBirthOutsidePostserviceCut

end
