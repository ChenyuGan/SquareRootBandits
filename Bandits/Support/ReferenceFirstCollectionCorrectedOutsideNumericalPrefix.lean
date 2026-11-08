/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedCurrentNumericalOutput
public import Bandits.Support.ReferenceCompleteLaterLiveComplementPrefixReplay

import Mathlib.Data.List.TakeDrop

/-!
# Initialized outside-arm replay after the corrected first collection call

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:391-408,425-426`, and `appendix_a_local_protocol.tex:28-64`.
The continuing interval ends before the first cutoff dispatch. Physical service
is unstopped; no queue survival or later successful assignment is assumed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceFirstCollectionCorrectedOutsideNumericalPrefix

variable {p : ConstructorDimensions.Parameters}

/-- The literal union readout keeps the same present LIVE cell at origin zero. -/
private theorem cell0_of_live {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : RoundRecord (p := p) (rate := rate)) (s : ℕ)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  classical
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  have hzero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hzero, Option.some_or]

/-- The collection call occurs strictly after launch, on the original run. -/
private theorem firstCell_start_lt (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < t.val := by
  obtain ⟨n, r, theta, hr, ht, _har, hcall, _⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_record
      rate rewards C_star C_h u t z hz.1
  obtain ⟨old, ledger, saved, hcoord, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hafter := ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
    rate rewards C_star C_h z n r hr old ledger saved hcoord
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h n r hr
  rw [ht] at htime
  omega

/-- Disabled raw arrivals may differ as records, but their transitions agree. -/
private theorem raw_replay_eq (Q : RecordedQueueRun.Parameters)
    (seed : ℕ × ℕ) (cells : List (RecordedQueueRun.RoundInput p.K)) (a : Fin p.K) :
    QueueReplay.replay (4 * Q.n) seed
      (cells.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c a)) =
    QueueReplay.replay (4 * Q.n) seed
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord Q c a) := by
  induction cells generalizing seed with
  | nil => rfl
  | cons c cells ih =>
    simp only [List.map_cons, QueueReplay.replay, List.foldl_cons]
    change QueueReplay.replay _ _ _ = QueueReplay.replay _ _ _
    rw [ih]
    congr 1
    cases he : c.enabled <;>
      simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he,
        Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]

/-- Composition eliminates the arbitrary query seed using the initialized
whole prefix. It compares folds, without equating disabled raw records. -/
private theorem initialized_replay (rate : ReferenceActivePhysicalStep.RateInput p)
    (A B : List (RecordedQueueRun.RoundInput p.K)) (v : ℕ) (a : Fin p.K) :
    QueueReplay.replay (4 * rate.n)
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length a)
      (((B).take v).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) =
    UnstoppedRecordedQueueComparison.unstoppedReplay
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (A ++ (B).take v) (A ++ (B).take v).length a := by
  simp only [UnstoppedRecordedQueueComparison.unstoppedReplay,
    List.take_length, List.map_append, QueueReplay.replay_append]
  exact raw_replay_eq (ReferenceFirstLaunchNumericalCell.queueParameters rate) _ (B.take v) a

private theorem take_before_last {α : Type*} (A B : List α) (v : ℕ)
    (hv : v ≤ (B).length) (hpos : 0 < v) :
    (A ++ (B).take v).take ((A ++ (B).take v).length - 1) = A ++ (B).take (v - 1) := by
  have hlen : ((B).take v).length = v := List.length_take_of_le hv
  have hcut : (A ++ (B).take v).length - 1 = A.length + (v - 1) := by
    simp only [List.length_append, hlen]
    omega
  rw [hcut, List.take_append]
  simp only [List.take_of_length_le (by omega : A.length ≤ A.length + (v - 1)),
    Nat.add_sub_cancel_left, List.take_take, Nat.min_eq_left (by omega : v - 1 ≤ v)]

section Continuing

variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
variable (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h).length)
variable (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
variable (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
variable (baseout : Fin (p.m - 1) → ℕ)
variable (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h)[k.val]).input.state.coordinator = .live rout qout baseout)
variable (hlater : ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h < rout.payload.sigma.val)

local notation "W" => ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
  rate rewards C_star C_h z k.val
local notation "B" => ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
  rewards C_star C_h z k rout qout baseout hstate hlater
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- Internal seed substitution; its inputs are discharged by the actual current
output in `firstCell_outside_prefix`. The empty interval keeps prior service. -/
private theorem continuing_initialized (L : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hseed : ∀ j : FastArm rout.payload.slowSet,
      (rout.complementScores j, qout.queue j) =
        UnstoppedRecordedQueueComparison.unstoppedReplay Q (L ++ [c]) (L ++ [c]).length j.val ∧
      qout.previousService j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q (L ++ [c]) (L ++ [c]).length j.val).1 -
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q L L.length j.val).1)
    (v : ℕ) (hv : v ≤ (W).length) :
    let A := (L ++ [c]) ++ (B).take v
    ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
      (hp : rv.payload = rout.payload),
      (∀ hpos : 0 < v, (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv baseout) ∧
      (∀ hnext : k.val + v < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val + v]).input.state.coordinator = .live rv qv baseout) ∧
      ∀ j : FastArm rout.payload.slowSet,
        let jv : FastArm rv.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
        (rv.complementScores jv, qv.queue jv) =
          UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val ∧
        qv.previousService jv =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length j.val).1 -
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q
            (A.take (A.length - 1)) (A.take (A.length - 1)).length j.val).1 := by
  dsimp only
  obtain ⟨rv, qv, hp, hout, hin, hvalues⟩ :=
    ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_replay
      rewards C_star C_h z k rout qout baseout hstate hlater v hv
  refine ⟨rv, qv, hp, hout, hin, ?_⟩
  intro j
  obtain ⟨hvalue, hprevious⟩ := hvalues j
  have hreplay (w : ℕ) :
      QueueReplay.replay (4 * rate.n) (rout.complementScores j, qout.queue j)
        (((B).take w).map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c j.val)) =
      UnstoppedRecordedQueueComparison.unstoppedReplay Q
        ((L ++ [c]) ++ (B).take w) ((L ++ [c]) ++ (B).take w).length j.val := by
    rw [(hseed j).1]
    exact initialized_replay rate (L ++ [c]) B w j.val
  refine ⟨hvalue.trans (hreplay v), ?_⟩
  rw [hprevious]
  by_cases hv0 : v = 0
  · subst v
    simp only [ite_true, List.take_zero, List.append_nil]
    have htake : (L ++ [c]).take ((L ++ [c]).length - 1) = L := by
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
        List.take_left]
    rw [htake]
    exact (hseed j).2
  · simp only [ite_eq_right hv0]
    rw [hreplay v, hreplay (v - 1)]
    have hvB : v ≤ (B).length := by
      rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length]
      exact hv
    rw [take_before_last (L ++ [c]) B v hvB (by omega)]

/-- Append the unique continuing cells to the same original optional mapM
prefix, one actual record at a time. -/
private theorem continuing_prefixInputs (t : Fin p.T)
    (A : List (RecordedQueueRun.RoundInput p.K))
    (hA : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (t.val + 1) z = some A)
    (hdate : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val =
      t.val + 1)
    (v : ℕ) (hv : v ≤ (W).length) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (t.val + 1 + v) z = some (A ++ (B).take v) := by
  induction v with
  | zero => simpa only [Nat.add_zero, List.take_zero, List.append_nil] using hA
  | succ v ih =>
    have hvlt : v < (W).length := by omega
    have hb := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le rewards C_star C_h z k
    have hindex : k.val + v < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length := by omega
    have hread := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_readout
      rewards C_star C_h z k rout qout baseout hstate hlater ⟨v, hvlt⟩
    rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
      rewards C_star C_h z k v hvlt] at hread
    have hcell := cell0_of_live _ _ _ hread
    have hi : t.val + 1 + v - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z = k.val + v := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      omega
    have happ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
      rate rewards C_star C_h (t.val + 1 + v) z (A ++ (B).take v) (ih (by omega)) _ _
      (by rw [hi]; exact List.getElem?_eq_getElem hindex) hcell
    have hvB : v < (B).length := by
      rw [ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length]
      exact hvlt
    rw [List.take_add_one, List.getElem?_eq_getElem hvB, Option.toList_some]
    simpa only [Nat.add_assoc, List.append_assoc] using happ

end Continuing

/-- The actual corrected current output initializes every continuing outside-arm
endpoint on the same complete source. The original current failure constructors
and terminal/no-next alternative are retained literally. This is a deterministic
component for physical overflow coverage, not a global all-arm claim. -/
theorem firstCell_outside_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ b = t.val - s ∧ s + b = t.val ∧ c.enabled = true ∧
      R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
        instruction.time = t ∧ instruction.kind = .corrected ∧
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload = output.payload ∧ installed.registers.payload.sigma = t ∧
        installed.assignmentVector = output.assignmentVector ∧
        output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector birth.input.row t ∧
        installed.reconstruction = output.reconstruction ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 ∧
          (output.reconstruction.registers.current a).lastService =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length a).1 ∧
          installed.registers.payload.queues a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
        (∀ i : Fin (p.m - 1),
          let a := installed.registers.payload.assignment.assigned i
          installed.retainedBaseScore i =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
            UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val ∧
          installed.ownedRegisters.previousService j =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length j.val).1) ∧
        c.rate = installed.registers.payload.rate ∧
        c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          birth.output.preparation installed.registers installed.ownedRegisters
          installed.retainedBaseScore started ∧
        birth.output.next.coordinator = birth.output.coordinator.configuration ∧
        (match birth.output.next.coordinator with
        | .live rout qout baseout =>
          rout.payload = installed.registers.payload ∧ baseout = installed.retainedBaseScore ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters installed.registers installed.ownedRegisters)
            (pending : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p),
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) =
                some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .ok finished ∧
            birth.output.coordinator =
              ⟨.live {
                  payload := installed.registers.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := birth.input.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
                { queue := serviced.queue, previousService := serviced.previousService } installed.retainedBaseScore,
                birth.input.state.upDecoderBank, none, some recording, none⟩ ∧
            ∀ j : CanonicalFastSampling.FastArm rout.payload.slowSet,
              (rout.complementScores j, qout.queue j) =
                UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val ∧
              qout.previousService j =
                (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val).1
        | .dagger =>
          (CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .recorderRejected) none none) ∨
          (∃ recording reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live reason) (some recording) none) ∨
          (∃ recording serviced,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .confirmationRejected) (some recording) none) ∨
          (∃ recording serviced pending reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank
                (.live (CoordinatorLiveServiceFinish.finishFailureCode reason)) (some recording) none)
        | _ => False)
      | _ => False) ∧
      (∀ hq : t.val + 1 < p.T,
        ∃ next : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          R[b + 1]? = some next ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h ⟨t.val + 1, hq⟩ z = some next ∧
          next.input.time = ⟨t.val + 1, hq⟩ ∧ next.input.state = birth.output.next ∧
          next.input.rows = z.1.2 ∧
          next.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          next.input.rewards = rewards) ∧
      (∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
        (baseout : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout baseout →
        rout.payload.sigma = t ∧
        ∀ _hq : t.val + 1 < p.T,
          ∃ (next : RoundRecord (p := p) (rate := rate))
            (hk : b + 1 < R.length)
            (hstate : (R[b + 1]'hk).input.state.coordinator = .live rout qout baseout)
            (hlater : s < rout.payload.sigma.val),
            R[b + 1]? = some next ∧ next.input.state = birth.output.next ∧
            let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b + 1)
            let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
              rewards C_star C_h z ⟨b + 1, hk⟩ rout qout baseout hstate hlater
            B.length = W.length ∧ b + 1 + W.length ≤ R.length ∧
            t.val + 1 + W.length ≤ p.T ∧
            W.map (fun r => r.input.time.val) = List.range' (t.val + 1) W.length ∧
            ∀ (v : ℕ) (hv : v ≤ W.length),
              let A := (L ++ [c]) ++ B.take v
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                rate rewards C_star C_h (t.val + 1 + v) z = some A ∧
              A.length = b + 1 + v ∧ s + A.length = t.val + 1 + v ∧
              (∀ hi : b + 1 + v < R.length,
                (R[b + 1 + v]).input.time.val = t.val + 1 + v) ∧
              ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
                (hp : rv.payload = rout.payload),
                (∀ hpos : 0 < v,
                  (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv baseout) ∧
                (∀ hi : b + 1 + v < R.length,
                  (R[b + 1 + v]).input.state.coordinator = .live rv qv baseout) ∧
                ∀ j : FastArm rout.payload.slowSet,
                  let jv : FastArm rv.payload.slowSet :=
                    ⟨j.val, by simpa only [hp] using j.property⟩
                  (rv.complementScores jv, qv.queue jv) =
                    UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length j.val ∧
                  qv.previousService jv =
                    (UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length j.val).1 -
                    (UnstoppedRecordedQueueComparison.unstoppedReplay
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      (A.take (A.length - 1)) (A.take (A.length - 1)).length j.val).1) := by
  classical
  dsimp only
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hcurrent, hnext⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hcurrent, hnext, ?_⟩
  intro rout qout baseout hlive
  have hcur := hcurrent
  cases hd : birth.output.preparation.coordinator <;> simp only [hd] at hcur
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hcur
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  obtain ⟨_hinstTime, _hkind, _hinstall, _hpay, hsigma, _hvector, _hvectorRow,
    _hreconstruction, _hall, _hfollowers, _hcomplement, _hrate, _hreward,
    _hco, _hconfiguration, htail⟩ := hcur
  rw [hlive] at htail
  obtain ⟨hpayload, _hbase, recording, serviced, pending, finished,
    _hrecording, _hservice, _hconfirm, _hfinish, _houtput, hseed⟩ := htail
  have hsigmaOut : rout.payload.sigma = t := by rw [hpayload, hsigma]
  refine ⟨hsigmaOut, ?_⟩
  intro hq
  obtain ⟨next, hn, _han, _hnt, hnstate, _hnrows, _hnselected, _hnrewards⟩ := hnext hq
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hk : b + 1 < R.length := (List.getElem?_eq_some_iff.mp hn).1
  have hget : (R[b + 1]'hk) = next := (List.getElem?_eq_some_iff.mp hn).2
  have hstate : (R[b + 1]'hk).input.state.coordinator = .live rout qout baseout := by
    rw [hget, hnstate]
    exact hlive
  have hlater : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h < rout.payload.sigma.val := by
    rw [hsigmaOut]
    exact firstCell_start_lt rate rewards C_star C_h u t z hz
  let k : Fin R.length := ⟨b + 1, hk⟩
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z k rout qout baseout hstate hlater
  have hB : B.length = W.length :=
    ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
      rewards C_star C_h z k rout qout baseout hstate hlater
  have hbound : b + 1 + W.length ≤ R.length :=
    ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
      rewards C_star C_h z k
  have hdate : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      k.val = t.val + 1 := by
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z + b = t.val at htime
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z + (b + 1) = t.val + 1
    omega
  have hT : t.val + 1 + W.length ≤ p.T := by
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    change R.length = p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h at hlen
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    dsimp only [k] at hdate
    omega
  refine ⟨next, hk, hstate, hlater, hn, hnstate, hB, hbound, hT, ?_, ?_⟩
  · simpa only [hdate] using
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_times rewards C_star C_h z k
  intro v hv
  have hvB : v ≤ B.length := by rw [hB]; exact hv
  have hlenA : ((L ++ [c]) ++ B.take v).length = b + 1 + v := by
    simp only [List.length_append, List.length_singleton, List.length_take_of_le hvB]
    rw [hLb]
  refine ⟨continuing_prefixInputs rewards C_star C_h z k rout qout baseout
    hstate hlater t (L ++ [c]) hprefix hdate v hv, hlenA, ?_, ?_, ?_⟩
  · rw [hlenA]
    change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z + b = t.val at htime
    omega
  · intro hi
    have hr : R[b + 1 + v]? = some (R[b + 1 + v]'hi) := List.getElem?_eq_getElem hi
    have hcalendar := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h (b + 1 + v) _ hr
    change (R[b + 1 + v]'hi).input.time.val = t.val + 1 + v
    rw [hcalendar]
    dsimp only [k] at hdate
    omega
  · exact continuing_initialized rewards C_star C_h z k rout qout baseout
      hstate hlater L c hseed v hv

end Bandits.Support.ReferenceFirstCollectionCorrectedOutsideNumericalPrefix
