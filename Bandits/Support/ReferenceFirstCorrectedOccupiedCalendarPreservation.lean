/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover

import Lean.Elab.Tactic.Omega

/-!
# Actual source and occupied-step foundations on the first corrected LIVE tail

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:110-163,192-233,246-299`, and
`04_slow_fast_learner.tex:157-187,256-290` under `sources/zip4/manuscript/`.

This module propagates actual occupied follower storage through the remaining
LIVE records of the same first corrected assignment, conditional on one literal
score/backlog equality at a real occupied boundary. The seed is not discharged
here. No unconditional storage, DOWN initialization, or manuscript closure is
claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCorrectedAssignedArrivalPrefix
open ReferenceCompletePhysicalHistory
open ReferenceFirstReplacementFollowerBoundary
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceCompleteOccupiedFollowerDataArrival
open ReferenceLaterLiveNumericalReadout
open ActiveFollowerLifecycle
open ActiveFollowerQueueOperation
open DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstCorrectedOccupiedCalendarPreservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem continuing_prefix_eq_liveTail
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h source
        (birthIndex rate rewards C_star C_h source + 1) =
      liveTail rate rewards C_star C_h source := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  have htest :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    funext r
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    cases r.output.preparation.coordinator with
    | live rv qv base chosen => cases chosen <;> rfl
    | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
  rw [htest]

private theorem complete_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, hr0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, hr1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [hr0, hr1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem continuing_tail_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (b n : ℕ)
    (hn : n + 1 < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) b).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let W := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b
    (W.get ⟨n + 1, hn⟩).input.state =
      (W.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).output.next ∧
    (W.get ⟨n + 1, hn⟩).input.time.val =
      (W.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).input.time.val + 1 := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let W := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b
  change n + 1 < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b).length at hn
  have hn0 : n < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b).length :=
    Nat.lt_trans (Nat.lt_succ_self n) hn
  have hg0 := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R b ⟨n, hn0⟩
  have hg1 := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R b ⟨n + 1, hn⟩
  have hget0 : R.get ⟨b + 1 + n, (List.getElem?_eq_some_iff.mp hg0).1⟩ =
      W.get ⟨n, hn0⟩ :=
    (List.getElem?_eq_some_iff.mp hg0).2
  have hget1 : R.get ⟨b + 1 + (n + 1), (List.getElem?_eq_some_iff.mp hg1).1⟩ =
      W.get ⟨n + 1, hn⟩ := (List.getElem?_eq_some_iff.mp hg1).2
  have hadj := complete_adjacent rate source rewards C_star C_h (b + 1 + n) (by
    have := (List.getElem?_eq_some_iff.mp hg1).1
    omega)
  have hR0 : b + 1 + n < R.length := by
    simpa only [Fin.val_mk] using (List.getElem?_eq_some_iff.mp hg0).1
  have hR1 : b + 1 + (n + 1) < R.length := by
    simpa only [Fin.val_mk] using (List.getElem?_eq_some_iff.mp hg1).1
  have hR1' : b + 1 + n + 1 < R.length := by omega
  have hget1' : R.get ⟨b + 1 + n + 1, hR1'⟩ =
      W.get ⟨n + 1, hn⟩ := by
    have hidx : (⟨b + 1 + n + 1, hR1'⟩ : Fin R.length) =
        ⟨b + 1 + (n + 1), hR1⟩ := by
      apply Fin.ext
      change b + 1 + n + 1 = b + 1 + (n + 1)
      omega
    exact (congrArg (fun x : Fin R.length => R.get x) hidx).trans hget1
  rcases hadj with ⟨hstate, htime⟩
  constructor
  · exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.state)
      hget1').symm.trans (hstate.trans
        (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.output.next) hget0))
  · exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.time.val)
      hget1').symm.trans (htime.trans
        (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord => r.input.time.val + 1)
          hget0))

private theorem occupied_fixed_event
    (P : Payload rate) (snapshot : ActiveRoundActions.Snapshot P.assignment)
    (i : Fin (p.m - 1)) (hoccupied : snapshot.status i ≠ .unoccupied)
    (w : Fin p.K → ℝ) (hw : ∀ a, 0 < w a)
    (hlower : ∀ a, P.anchor a ≤ w a) (hupper : ∀ a, w a ≤ 2 * P.anchor a) :
    {x | SnapshotRecordingKernel.recordingMap p (.live P.assignment snapshot)
      true rate.eta.val rate.eta.property rate.sourceCap P.anchor w P.anchor_pos hw
      hlower hupper x = some (P.assignment.assigned i)} =
    {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m
      p.m_lt_K (ConstructorDimensions.K_pos p)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (P.assignment.assigned i)
      (CanonicalRecordingRates.xi p rate.eta.val P.anchor (P.assignment.assigned i) /
        CanonicalRecordingSlice.deterministicOwnedGateRawProbability (K := p.K)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) x} := by
  have hsource := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hsource
  apply SnapshotRecordingKernel.recordingMap_fixed_event_eq
  · simp only [SnapshotRecordingKernel.owns, hsource, dite_false, hindex]
  · intro x
    simp only [SnapshotRecordingKernel.dataAction, hsource, dite_false, hindex,
      hoccupied]
  · simp only [SnapshotRecordingKernel.actionProbability, hsource, dite_false,
      hindex, hoccupied, eq_self, dite_true]

private theorem occupied_sourceArm_gate
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v : Selection r.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (i : Fin (p.m - 1)) (hoccupied : (states i).status ≠ .unoccupied) :
    ActiveFollowerQueueOperation.recorderGate rate.eta i r.input.row r.input.time
      (v.view.payload.downRecord i) ↔
    ReferenceFirstWindowNumericalStream.sourceArm r v.view.payload v.view.pendingAtChoice
      states v.view.complementWeights v.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid v) =
      some (v.view.payload.assignment.assigned i) := by
  let P := v.view.payload
  let snapshot := ReferenceActiveDataOwnership.choiceSnapshot v states
  have hstatus : (states i).status.occupied := by
    cases hs : (states i).status with
    | unoccupied => exact False.elim (hoccupied hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hgate := ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
    P snapshot i r.input.row r.input.time (states i) rfl hstatus
  have hsnapshot : snapshot.status i ≠ .unoccupied := hoccupied
  have hanchor := occupied_fixed_event P snapshot i hsnapshot P.anchor P.anchor_pos
    (fun _ => le_rfl) (fun a => by
      rw [two_mul]
      exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos a)))
  have hcurrent := occupied_fixed_event P snapshot i hsnapshot
    (ReferenceFirstWindowNumericalStream.sourceWeights P v.view.complementWeights)
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
  have hevent := Set.ext_iff.mp (hanchor.trans hcurrent.symm)
    ((r.input.row.2 r.input.time).1)
  apply hgate.trans
  simpa only [Set.mem_ofPred_eq, ReferenceFirstWindowNumericalStream.sourceArm,
    ReferenceActiveDataOwnership.choiceSnapshot, P, snapshot, ← v.pending_eq] using hevent

/-- One actual occupied checked service, normalized to the selected LIVE
source cell. This is the existing service producer, including release/finish;
the equality makes an enabled zero-arrival record remain enabled. -/
private theorem actual_occupied_cell_service
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.preparation.coordinator.selection =
        some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time)
    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val])
    (hrewards : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.rewards = rewards)
    (i : Fin (p.m - 1))
    (hoccupied : (ReferenceLaterLiveNumericalReadout.preparedStates
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] ho i).status ≠ .unoccupied) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
    let prep := ReferenceActivePhysicalStep.prepare r.input
    let f := prep.followers.followers i
    let y := prep.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let cell := ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
      selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
    let arrival := RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
      (selected.view.payload.assignment.assigned i)
    ∃ serviced next nextMemory,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        f.follower f.row f.activation f.time y (states i) = .success serviced ∧
      serviced.arrival = arrival ∧
      serviced.service = min (4 * rate.n) ((states i).backlog + arrival) ∧
      serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n (states i) arrival ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).result =
          .ok serviced.output ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).downInput = none ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).down = none ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time y
        (states i) (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i)
        serviced.output = .ok (next, nextMemory) ∧
      (r.output.followers i).configuration = .ordinary next nextMemory ∧
      (r.output.followers i).failure = none ∧
      r.output.next.followers i = .ordinary next nextMemory ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        ((states i).S, (states i).backlog) (cell.enabled, arrival) ∧
      next.delta = next.S - (states i).S ∧
      next.lastDown = (states i).lastDown ∧ next.buffer = (states i).buffer ∧
      (next.status = .released ↔
        (states i).status = .released ∨
          ((states i).status = .pending ∧
            ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
              y (selected.view.payload.downRecord i))) ∧
      (next.status = .pending ↔
        (states i).status = .pending ∧
          ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
            y (selected.view.payload.downRecord i)) := by
  classical
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
  let memories := ReferenceLaterLiveNumericalReadout.preparedMemories r ho
  have hactual (f : Fin (p.m - 1)) :
      (ReferenceFollowerFixedReply.actualChoice r f).configuration =
        .ordinary (states f) (memories f) :=
    ReferenceLaterLiveNumericalReadout.prepared_configuration r ho f
  obtain ⟨otherStates, otherMemories, _, hother, _, _, hservice⟩ :=
    ReferenceCompleteOccupiedFollowerDataArrival.complete_selected_occupied_follower_arrival_service
      (rate := rate) rewards C_star C_h source k selected hselected hlive
  have heq (f : Fin (p.m - 1)) : otherStates f = states f :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hother f).symm.trans (hactual f))).1
  have hmem (f : Fin (p.m - 1)) : otherMemories f = memories f :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hother f).symm.trans (hactual f))).2
  have hstates : otherStates = states := funext heq
  have hmemories : otherMemories = memories := funext hmem
  subst otherStates
  subst otherMemories
  obtain ⟨serviced, next, nextMemory, hchecked, harrivalDelta, hserviceGamma,
    hserviceOutputDelta, hrecordOutput, hrecordNoDownInput, hrecordNoDown,
    hreleaseFinish, houtputConfig, houtputOK, hnextConfig, hscoreGamma,
    hdeltaGamma, hbacklogGamma, hqueue, hnextDown, hbufferNext,
    hreleasedSource, hpendingSource, hgateMap⟩ := hservice i hoccupied
  have hgate := occupied_sourceArm_gate r selected states i hoccupied
  have harrival : RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
        selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
      (selected.view.payload.assignment.assigned i) =
      if ActiveFollowerQueueOperation.recorderGate rate.eta i r.input.row r.input.time
        (selected.view.payload.downRecord i) then
        Nat.floor ((D p : ℝ) * rate.eta.val *
          (((rewards r.input.time (selected.view.payload.assignment.assigned i)).val : ℝ) /
            (D p : ℝ)) /
          OrdinaryMessageCodec.dyadicRate (selected.view.payload.downRecord i).val.h)
      else 0 := by
    rw [ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival]
    rw [hrewards, selected.view.payload.downRecord_rate i,
      selected.view.payload.rate_eq_canonical]
    have hn : (rate.n : ℝ) = (D p : ℝ) * rate.eta.val := by
      rw [rate.n_scale, mul_comm]
    rw [hn]
    exact if_congr hgate.symm rfl rfl
  have hqueueCell : (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
      ((states i).S, (states i).backlog)
      ((ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
        selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)).enabled,
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
            selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
          (selected.view.payload.assignment.assigned i)) := by
    rw [ReferenceFirstWindowNumericalStream.sourceCell_enabled, harrival]
    exact hqueue
  have hdeltaScore : next.delta = next.S - (states i).S := by
    rw [hdeltaGamma, hscoreGamma]
    omega
  have harrivalServiced : serviced.arrival =
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
        (selected.view.payload.assignment.assigned i) := by
    exact harrivalDelta.trans harrival.symm
  have hserviceCell : serviced.service = min (4 * rate.n)
      ((states i).backlog + RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
        (selected.view.payload.assignment.assigned i)) := by
    rw [harrival]
    simpa only using hserviceGamma
  have hserviceOutputCell : serviced.output = ActiveFollowerQueueOperation.serviceUpdate
      rate.n (states i) (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
        (selected.view.payload.assignment.assigned i)) := by
    rw [harrival]
    exact hserviceOutputDelta
  exact ⟨serviced, next, nextMemory, hchecked, harrivalServiced, hserviceCell, hserviceOutputCell,
    hrecordOutput, hrecordNoDownInput, hrecordNoDown, hreleaseFinish,
    houtputConfig, houtputOK, hnextConfig, hqueueCell, hdeltaScore,
    hnextDown, hbufferNext, hreleasedSource, hpendingSource⟩

/-- Actual ordinary/occupied boundary data at every record of the same
continuing LIVE tail. The only branch selectors are the actual birth record,
its installation witness, and the actual `laterChosen` constructor. This
exports no numerical storage equality and assumes none. -/
theorem internal_first_corrected_actual_tail_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1)) :
    ∀ k : Fin (liveTail rate rewards C_star C_h source).length,
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
      let W := liveTail rate rewards C_star C_h source
      let r := W.get k
      R[birthIndex rate rewards C_star C_h source + 1 + k.val]? = some r ∧
      ∃ selected state memory next nextMemory,
        r.input.rows = source.1.2 ∧
        r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        r.input.rewards = rewards ∧
        r.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = P ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
        r.input.state.followers i = .ordinary state memory ∧
        localStateDomainValid state ∧
        (state.status ≠ .unoccupied → state.lastDown = some (P.downRecord i)) ∧
        (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
        (r.output.followers i).configuration = .ordinary next nextMemory ∧
        (r.output.followers i).failure = none ∧
        (state.status ≠ .unoccupied → next.status ≠ .unoccupied) ∧
        interruptionDecision rate.eta r.input.time state memory = .ok false ∧
        (state.status ≠ .unoccupied →
          ∃ token, memory.lastProposalRead = some token ∧
            token.timestamp.val + 1 = r.input.time.val ∧
            token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              r.input.row token.timestamp) ∧
        (next.status ≠ .unoccupied →
          ∃ token, nextMemory.lastProposalRead = some token ∧
            token.timestamp.val + 1 = r.input.time.val + 1 ∧
            token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              r.input.row token.timestamp) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let W := liveTail rate rewards C_star C_h source
  have hprep : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  have hboundary := complete_first_replacement_follower_boundary rate source rewards C_star C_h
  dsimp only at hboundary
  have hbExpanded :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length +
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length]? =
        some birth := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hb
  have hbranch := hboundary
  rw [hbExpanded] at hbranch
  cases hcoord : birth.output.preparation.coordinator with
  | first outcome =>
      have hfalse := hchosen
      unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
      rw [← hprep, hcoord] at hfalse
      simp at hfalse
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hs instruction hi output hcons clockData installed selectedBirth =>
          have hborn' : P = installed.registers.payload ∧
              P.sigma.val = birth.input.time.val := by
            simpa only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] using hborn
          have hpayload : P = installed.registers.payload := hborn'.1
          subst P
          simp only [hcoord] at hbranch
          intro k
          obtain ⟨hindex, hrows, hselectedRow, hrewards, selected, hselection,
            hpay, hlive, _hgrid, _hbits, hfollowers⟩ := hbranch k
          obtain ⟨state, memory, next, nextMemory, hinput, hdomain, _hmass,
            _hzero, _hstrict, hbusy, _hpair, _hbefore, _hsigma, _hstart,
            _hcredit, hdecision, hprepare, houtput, hfailure, _hinitFailure,
            _hdomainNext, _hmassNext, _hdeltaNext, _hlastDownNone,
            _hunoccupiedNext, hoccupiedNext, hpreserves⟩ := hfollowers i
          refine ⟨hindex, selected, state, memory, next, nextMemory,
            hrows, hselectedRow, hrewards, hselection, hpay, hlive, hinput,
            hdomain, ?_, hprepare, houtput, hfailure, hpreserves, hdecision, ?_, ?_⟩
          · intro hocc
            exact (hbusy hocc).1
          · intro hocc
            exact (hbusy hocc).2
          · intro hocc
            exact (hoccupiedNext hocc).2
      | _ =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn

private theorem actual_cutoff_prepare
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[birthIndex rate rewards C_star C_h source + 1 +
        (liveTail rate rewards C_star C_h source).length]? = some r)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true)
    (i : Fin (p.m - 1)) :
    ∃ state memory,
      r.input.state.followers i = .ordinary state memory ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
        .ok ({state with status := .unoccupied}, memory) ∧
      (r.output.preparation.followers.followers i).configuration =
        .ordinary {state with status := .unoccupied} memory := by
  classical
  have hsource :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hsource
  have hbExpanded := hb
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] at hbExpanded
  rw [hbExpanded] at hsource
  have hprep : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  cases hcoord : birth.output.preparation.coordinator with
  | first outcome =>
      unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
      rw [← hprep, hcoord] at hchosen
      simp at hchosen
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | dagger => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hs instruction hi output hcons clockData installed selectedBirth =>
          simp only [hcoord] at hsource
          have hrExpanded := hr
          simp only [liveTail, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex] at hrExpanded
          rw [hrExpanded] at hsource
          obtain ⟨_hnotContinuing, hsource⟩ := hsource
          have hrprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
            rw [r.output_eq]
            rfl
          unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
          rw [← hrprep] at hcut
          cases hrc : r.output.preparation.coordinator with
          | live registers owned base outcome =>
              cases outcome with
              | cutoffChosen dispatched hstart ledger hinit heq hdomain hclock hpending hassign arm =>
                  simp only [hrc] at hsource
                  obtain ⟨_hpay, _htime, _hoffset, _hrows, _hrow, _hrewards, _hsigma,
                    _hlater, _hfirst, _hgrid, _htrigger, selected, _hselection,
                    _hselectedPay, _hselectedPending, _hselectedCutoff, hfollowers⟩ := hsource
                  obtain ⟨state, memory, hinput, _hdomain, _hmass, _hzero, _hstrict,
                    _hbusy, _hdecision, hstart, hprepare, _hrest⟩ := hfollowers i
                  exact ⟨state, memory, hinput, hstart, hprepare⟩
              | _ => simp [hrc] at hcut
          | _ => simp [hrc] at hcut
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn

private theorem actual_tail_occupied_service_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1))
    (B : List (RecordedQueueRun.RoundInput p.K))
    (hB : B.length = (liveTail rate rewards C_star C_h source).length)
    (k : Fin (liveTail rate rewards C_star C_h source).length)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((liveTail rate rewards C_star C_h source).get k) =
        some (B[k.val]'(by omega)))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : ((liveTail rate rewards C_star C_h source).get k).input.state.followers i =
      .ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    ∃ next nextMemory,
      (((liveTail rate rewards C_star C_h source).get k).output.followers i).configuration =
        .ordinary next nextMemory ∧
      (((liveTail rate rewards C_star C_h source).get k).output.followers i).failure = none ∧
      ((liveTail rate rewards C_star C_h source).get k).output.next.followers i =
        .ordinary next nextMemory ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        (state.S, state.backlog)
        ((B[k.val]'(by omega)).enabled,
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (B[k.val]'(by omega)) (P.assignment.assigned i)) ∧
      next.delta = next.S - state.S ∧
      next.lastDown = state.lastDown ∧ next.buffer = state.buffer := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let W := liveTail rate rewards C_star C_h source
  obtain ⟨hindex, selectedBoundary, stateBoundary, memoryBoundary, nextBoundary,
    nextMemoryBoundary, _hrows, _hselectedRow, hrewards, hselectionBoundary,
    hpay, hliveBoundary, hinputBoundary, _hdomain, hlastDown,
    hprepareBoundary, houtputBoundary, hfailureBoundary, hpreserves,
    _hdecisionBoundary, _hmemoryBoundary, _hnextMemoryBoundary⟩ :=
      internal_first_corrected_actual_tail_boundary rate source rewards C_star C_h
        birth P hb hchosen hborn i k
  have hstateEq : state = stateBoundary := by
    obtain ⟨hs, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinput.symm.trans hinputBoundary)
    exact hs
  have hmemoryEq : memory = memoryBoundary := by
    obtain ⟨hs, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinput.symm.trans hinputBoundary)
    exact hm
  let kr : Fin R.length := ⟨b + 1 + k.val, (List.getElem?_eq_some_iff.mp hindex).1⟩
  have hrecord : R.get kr = W.get k := (List.getElem?_eq_some_iff.mp hindex).2
  have hreadR : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) (R.get kr) =
        some (B[k.val]'(by omega)) := by
    rw [hrecord]
    exact hread
  obtain ⟨selected, ho, hselection, _hlater, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (R.get kr) (B[k.val]'(by omega)) hreadR
  have hselectionMap :
      (R.get kr).output.preparation.coordinator.selection.map
          (fun x => x.view.payload) =
        (W.get k).output.preparation.coordinator.selection.map
          (fun x => x.view.payload) := by
    exact congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord =>
      r.output.preparation.coordinator.selection.map (fun x => x.view.payload)) hrecord
  have hpayloadRead : selected.view.payload = selectedBoundary.view.payload := by
    have hmapR := congrArg (Option.map fun x : Selection (R.get kr).input => x.view.payload)
      hselection
    have hmapW := congrArg (Option.map fun x : Selection (W.get k).input => x.view.payload)
      hselectionBoundary
    have hsome : some selected.view.payload = some selectedBoundary.view.payload := by
      calc
        some selected.view.payload =
            (R.get kr).output.preparation.coordinator.selection.map
              (fun x => x.view.payload) := hmapR.symm
        _ = (W.get k).output.preparation.coordinator.selection.map
              (fun x => x.view.payload) := hselectionMap
        _ = some selectedBoundary.view.payload := hmapW
    exact Option.some.inj hsome
  have hpayRead : selected.view.payload = P := hpayloadRead.trans hpay
  have hpreparedEq :
      (ReferenceLaterLiveNumericalReadout.preparedStates (R.get kr) ho i) = state := by
    have hcanonical := ReferenceLaterLiveNumericalReadout.prepared_configuration
      (R.get kr) ho i
    have hboundaryR :
        ((R.get kr).output.preparation.followers.followers i).configuration =
          .ordinary state memory := by
      rw [hrecord, hstateEq, hmemoryEq]
      exact hprepareBoundary
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hcanonical.symm.trans hboundaryR)).1
  have hoccupiedR : (ReferenceLaterLiveNumericalReadout.preparedStates
      (R.get kr) ho i).status ≠ .unoccupied := by
    rw [hpreparedEq]
    exact hoccupied
  have hselectedR : (R.get kr).output.preparation.coordinator.selection = some selected :=
    hselection
  have hRewardsR : (R.get kr).input.rewards = rewards := by
    rw [hrecord]
    exact hrewards
  obtain ⟨_serviced, next, nextMemory, _hchecked, _harrival, _hservice, _hserviceOutput,
    _hrecordResult, _hnoDownInput, _hnoDown, _hreleaseFinish, houtput,
    hfailure, hnext, hqueue, hdelta, hnextDown, hbuffer, _hreleased, _hpending⟩ :=
    actual_occupied_cell_service rewards C_star C_h source kr selected hselectedR
      hlive ho hRewardsR i hoccupiedR
  simp only [List.get_eq_getElem, R, kr] at hpreparedEq
  rw [hpreparedEq] at hqueue hdelta hnextDown hbuffer
  have hqueueGet := hqueue
  have houtputGet := houtput
  have hfailureGet := hfailure
  have hnextGet := hnext
  simp only [← List.get_eq_getElem] at hqueueGet houtputGet hfailureGet hnextGet
  rw [hrecord] at houtputGet hfailureGet hnextGet
  have hqueueWord : (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
      (state.S, state.backlog)
        ((B[k.val]'(by omega)).enabled,
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (B[k.val]'(by omega)) (P.assignment.assigned i)) := by
    simpa only [hcell, hpayRead] using hqueueGet
  exact ⟨next, nextMemory, houtputGet, hfailureGet, hnextGet, hqueueWord, hdelta,
    hnextDown, hbuffer⟩

/-- The actual installation and first corrected numerical cell. This small
source projection is kept internal to the worker module; it does not claim
actual follower storage equals the reconstructed word. -/
theorem actual_first_corrected_assignment_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate) (base : Fin (p.m - 1) → ℕ),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t source = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t source = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) source = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a : Fin p.K, P.queues a =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i : Fin (p.m - 1),
        base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
          (P.assignment.assigned i)).1 ∧
        (P.downRecord i).val.q =
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
            (P.assignment.assigned i)).2) := by
  dsimp only
  obtain ⟨L, c, birth, P, base, hL, hc, hprefix, hLb, hbirth, _hrecord,
    _htime, _hrowsBirth, _hselectedBirth, _hrewardBirth, _hrecordFields,
    _hchosen, _henabled, hborn, hSigma, _hrate, _hreward, hqueues, hbase,
    _hterminal, _hterminalWord, _hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t source hz
  exact ⟨L, c, birth, P, base, hL, hc, hprefix, hLb, hbirth, hborn,
    hSigma, hqueues, hbase⟩

private theorem actual_first_corrected_live_words
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t)
    (hq : t.val + 1 < p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let W := liveTail rate rewards C_star C_h source
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate) (B : List (RecordedQueueRun.RoundInput p.K)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧ c.enabled = true ∧
      ReferenceCollectionPhaseHistory.laterChosen birth.input = true ∧
      ∃ hB : B.length = W.length,
        (R.drop b).take (1 + W.length) = birth :: W ∧
        (∀ i : Fin (p.m - 1), ∀ v : ℕ, 1 ≤ v → v ≤ 1 + W.length →
          ((birth :: W).take v).mapM
            (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some (([c] ++ B.take (v - 1)).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i)))) ∧
        (∀ j : Fin W.length,
          ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[j.val] =
            some (B[j.val]'(by omega))) ∧
        (∀ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          R[b + 1 + W.length]? = some r →
          ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) := by
  dsimp only
  obtain ⟨L, c, birth, P, base, _hL, _hc, _hprefix, _hLb, hbirth,
    _hrecord, _htime, _hrows, _hselected, _hrewards, _hrecordFields,
    hchosen, henabled, hborn, hSigma, _hrate, _hreward, _hqueues, _hbase,
    _hterminal, _hterminalWord, hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t source hz
  obtain ⟨rout, qout, beta, _hbirthNext, hk, hstate, hlater, hB,
    hallv, _hEbound, _hprefixEnd, hdrop, hreadouts, hrest⟩ := hafter hq
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let W := liveTail rate rewards C_star C_h source
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h source ⟨b + 1, hk⟩ rout qout beta hstate hlater
  have hW0 : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h source
        (birthIndex rate rewards C_star C_h source + 1) = W := by
    change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h source
        (birthIndex rate rewards C_star C_h source + 1) =
      liveTail rate rewards C_star C_h source
    exact continuing_prefix_eq_liveTail rate rewards C_star C_h source
  rw [hW0] at hB hdrop hallv hrest
  refine ⟨c, birth, P, B, hbirth, hborn, hSigma, henabled, hchosen,
    ⟨hB, hdrop, ?_, ?_, ?_⟩⟩
  · exact hallv
  · intro j
    have hj0 : j.val <
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h source
          (birthIndex rate rewards C_star C_h source + 1)).length := by
      rw [hW0]
      exact j.isLt
    let j0 : Fin (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h source
      (birthIndex rate rewards C_star C_h source + 1)).length := ⟨j.val, hj0⟩
    obtain ⟨_, hread, _⟩ := hreadouts j0
    simpa only [hW0, B, Fin.val_mk] using hread

  · intro r hr
    obtain ⟨rE, qE, _hpay, _hstate, hend⟩ := hrest
    rcases hend with hend | ⟨he, seg, I, l0, ccut, _hsegment, hentry, _hpayload,
      _hledger, _hinit, _hI, _hchecked, _harm, _hstart, _hcutoff, _hfirst,
      _hfreeze, _hbase, hchosenCut, _hremaining⟩
    · have he : b + 1 + W.length < R.length := (List.getElem?_eq_some_iff.mp hr).1
      have hendW : b + 1 + W.length = R.length := hend
      omega
    · have hrEq : r = R[b + 1 + W.length]'he :=
        ((List.getElem?_eq_some_iff.mp hr).2).symm
      rw [hrEq]
      rw [hentry] at hchosenCut
      exact hchosenCut

private theorem occupied_record_service
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k = r)
    (selected : Selection
      r.input)
    (hselected : r.output.preparation.coordinator.selection =
        some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff
      r.input.time)
    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
      r)
    (hrewards : r.input.rewards = rewards)
    (i : Fin (p.m - 1))
    (hoccupied : (ReferenceLaterLiveNumericalReadout.preparedStates
      r ho i).status ≠ .unoccupied) :
    let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
    let prep := ReferenceActivePhysicalStep.prepare r.input
    let f := prep.followers.followers i
    let y := prep.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let cell := ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
      selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
    let arrival := RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
      (selected.view.payload.assignment.assigned i)
    ∃ serviced next nextMemory,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        f.follower f.row f.activation f.time y (states i) = .success serviced ∧
      serviced.arrival = arrival ∧
      serviced.service = min (4 * rate.n) ((states i).backlog + arrival) ∧
      serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n (states i) arrival ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).result =
          .ok serviced.output ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).downInput = none ∧
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y (states i)).down = none ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time y
        (states i) (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i)
        serviced.output = .ok (next, nextMemory) ∧
      (r.output.followers i).configuration = .ordinary next nextMemory ∧
      (r.output.followers i).failure = none ∧
      r.output.next.followers i = .ordinary next nextMemory ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        ((states i).S, (states i).backlog) (cell.enabled, arrival) ∧
      next.delta = next.S - (states i).S ∧
      next.lastDown = (states i).lastDown ∧ next.buffer = (states i).buffer ∧
      (next.status = .released ↔
        (states i).status = .released ∨
          ((states i).status = .pending ∧
            ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
              y (selected.view.payload.downRecord i))) ∧
      (next.status = .pending ↔
        (states i).status = .pending ∧
          ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
            (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
            y (selected.view.payload.downRecord i)) := by
  subst r
  exact actual_occupied_cell_service rewards C_star C_h source k selected
    hselected hlive ho hrewards i hoccupied

private theorem replay_live_cell_succ
    (rate : ReferenceActivePhysicalStep.RateInput p) (P : Payload rate)
    (i : Fin (p.m - 1)) (c : RecordedQueueRun.RoundInput p.K)
    (B : List (RecordedQueueRun.RoundInput p.K)) (k : ℕ) (hk : k < B.length) :
    QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
        (([c] ++ B.take (k + 1)).map fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
            (P.assignment.assigned i))) =
      QueueReplay.transition (4 * rate.n)
        (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
          (([c] ++ B.take k).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
              (P.assignment.assigned i))))
        ((B[k]).enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) B[k]
          (P.assignment.assigned i)) := by
  rw [← List.take_concat_get' B k hk, ← List.append_assoc, List.map_append,
    QueueReplay.replay_append]
  rfl

/-- Propagation on the actual continuing tail. The score/backlog equality at
`k0` is the sole numerical seed. Occupation at later inputs is derived from
actual outputs and adjacency, with the actual local memory carried along. -/
private theorem actual_tail_inputs_from_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[birthIndex rate rewards C_star C_h source]? = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1)) (c : RecordedQueueRun.RoundInput p.K)
    (B : List (RecordedQueueRun.RoundInput p.K))
    (hB : B.length = (liveTail rate rewards C_star C_h source).length)
    (hread : ∀ k : Fin (liveTail rate rewards C_star C_h source).length,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        ((liveTail rate rewards C_star C_h source).get k) = some (B[k.val]'(by omega)))
    (k0 : Fin (liveTail rate rewards C_star C_h source).length)
    (state0 : ReferencePrelaunchFollower.State p rate.eta)
    (memory0 : ActiveFollowerLifecycle.LocalMemory p)
    (hinput0 : ((liveTail rate rewards C_star C_h source).get k0).input.state.followers i =
      .ordinary state0 memory0)
    (hoccupied0 : state0.status ≠ .unoccupied)
    (hseed : (state0.S, state0.backlog) =
      QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
        (([c] ++ B.take k0.val).map fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
            (P.assignment.assigned i)))) :
    ∀ k : Fin (liveTail rate rewards C_star C_h source).length, k0.val ≤ k.val →
      ∃ state memory,
        ((liveTail rate rewards C_star C_h source).get k).input.state.followers i =
          .ordinary state memory ∧
        state.status ≠ .unoccupied ∧
        (state.S, state.backlog) =
          QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
            (([c] ++ B.take k.val).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i))) := by
  classical
  let W := liveTail rate rewards C_star C_h source
  have hinputs : ∀ n : ℕ, ∀ hn : n < W.length, k0.val ≤ n →
      ∃ state memory,
        (W.get ⟨n, hn⟩).input.state.followers i = .ordinary state memory ∧
        state.status ≠ .unoccupied ∧
        (state.S, state.backlog) =
          QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
            (([c] ++ B.take n).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn hle
        by_cases heq : n = k0.val
        · subst n
          exact ⟨state0, memory0, hinput0, hoccupied0, hseed⟩
        · have hpos : 0 < n := by omega
          have hprev : n - 1 < W.length := by omega
          have hleprev : k0.val ≤ n - 1 := by omega
          let prev : Fin W.length := ⟨n - 1, hprev⟩
          obtain ⟨state, memory, hinput, hoccupied, hstorage⟩ :=
            ih (n - 1) (by omega) hprev hleprev
          obtain ⟨next, nextMemory, houtput, _hfailure, hnext, hqueue,
            _hdelta, _hdown, _hbuffer⟩ :=
            actual_tail_occupied_service_step rate rewards C_star C_h source birth P
              hb hchosen hborn i B hB prev (hread prev) state memory hinput hoccupied
          obtain ⟨_hindex, _selected, sb, mb, nb, nmb, _hrows, _hrow,
            _hrewards, _hselection, _hpay, _hlive, hinputB, _hdomain, _hdownB,
            _hprepare, houtputB, _hfailureB, hpreserves, _hdecisionB,
            _hmemoryB, _hnextMemoryB⟩ :=
            internal_first_corrected_actual_tail_boundary rate source rewards C_star C_h
              birth P hb hchosen hborn i prev
          have hs : state = sb :=
            (LocalConfiguration.ordinary.inj (hinput.symm.trans hinputB)).1
          have hns : next = nb :=
            (LocalConfiguration.ordinary.inj (houtput.symm.trans houtputB)).1
          have hoccNext : next.status ≠ .unoccupied := by
            rw [hns]
            apply hpreserves
            rw [← hs]
            exact hoccupied
          have hadj := (continuing_tail_adjacent rate source rewards C_star C_h
            (birthIndex rate rewards C_star C_h source) (n - 1) (by
              change n - 1 + 1 < W.length
              omega)).1
          have hnEq : n - 1 + 1 = n := by omega
          simp only [hnEq] at hadj
          have hnextInput : (W.get ⟨n, hn⟩).input.state.followers i =
              .ordinary next nextMemory := by
            exact (congrArg (fun s => s.followers i) hadj).trans hnext
          refine ⟨next, nextMemory, hnextInput, hoccNext, ?_⟩
          have hprevB : n - 1 < B.length := by
            rw [hB]
            exact hprev
          have hrec := replay_live_cell_succ rate P i c B (n - 1) hprevB
          rw [hnEq] at hrec
          exact hqueue.trans ((congrArg
            (fun registers => QueueReplay.transition (4 * rate.n) registers
              ((B[n - 1]'hprevB).enabled,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (B[n - 1]'hprevB) (P.assignment.assigned i))) hstorage).trans hrec.symm)
  intro k hk
  exact hinputs k.val k.isLt hk

private theorem cons_live_record
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (W : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j : ℕ) (hj : j < (birth :: W).length) (hpos : 1 ≤ j) :
    (birth :: W)[j] = W.get ⟨j - 1, by simp only [List.length_cons] at hj; omega⟩ := by
  cases j with
  | zero => omega
  | succ n => rfl

/-- INTERNAL conditional preservation, on the SAME actual corrected assignment.
The numerical word is uniquely identified by the actual `mapM` equations.
Only the displayed score/backlog equality at the actual occupied boundary is
an extra numerical input. In particular, no initial last-service equality is
required. All later occupation, selection, PREPARE identity, current DOWN,
service, release, proposal memory and adjacency facts are derived internally.

The score/backlog seed is UNDISCHARGED by this module: the intended
consumer `ReferenceFirstCorrectedAssignedNativeFollowerPrefix` must construct
it from accepted native DOWN and SAME-source boundary transport. This is not
an initialization, unconditional storage, later collection, or source theorem.
The nonterminal selector only selects a real continuing tail; if it is empty
there is no `j0`. At terminal birth the consumer uses native acceptance directly.
The last LIVE output is retained even when no next `Fin p.T` date exists. -/
theorem internal_occupied_live_prefix_from_actual_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ _hq : t.val + 1 < p.T,
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    let W := liveTail rate rewards C_star C_h source
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate) (B : List (RecordedQueueRun.RoundInput p.K)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧ c.enabled = true ∧
      ∃ hB : B.length = W.length,
        (R.drop b).take (1 + W.length) = birth :: W ∧
        let V := birth :: W
        let word := fun (i : Fin (p.m - 1)) (v : ℕ) =>
          ([c] ++ B.take (v - 1)).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
              (P.assignment.assigned i))
        (∀ i v, 1 ≤ v → v ≤ V.length →
          (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some (word i v)) ∧
        (∀ k : Fin W.length, (B[k.val]'(by omega)).enabled = true) ∧
        (∀ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          R[b + 1 + W.length]? = some r → ∀ i : Fin (p.m - 1),
          ∃ state memory,
            r.input.state.followers i = .ordinary state memory ∧
            ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
              .ok ({state with status := .unoccupied}, memory) ∧
            (r.output.preparation.followers.followers i).configuration =
              .ordinary {state with status := .unoccupied} memory) ∧
        ∀ (i : Fin (p.m - 1)) (j0 : ℕ) (_hpos0 : 1 ≤ j0) (hj0 : j0 < V.length)
          (state0 : ReferencePrelaunchFollower.State p rate.eta)
          (memory0 : ActiveFollowerLifecycle.LocalMemory p),
          (V[j0]).input.state.followers i = .ordinary state0 memory0 →
          state0.status ≠ .unoccupied →
          (state0.S, state0.backlog) =
            QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j0) →
          ∀ (j : ℕ) (hj : j < V.length), j0 ≤ j →
            let r := V[j]
            ∃ (selected : Selection r.input) (ho : preparedOrdinary r)
              (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p)
              (next : ReferencePrelaunchFollower.State p rate.eta)
              (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b + j]? = some r ∧
              r.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = P ∧
              CoordinatorLocalArmChoice.assignmentIsLive P selected.view.cutoff r.input.time ∧
              r.input.state.followers i = .ordinary state memory ∧
              (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              preparedStates r ho i = state ∧ preparedMemories r ho i = memory ∧
              state.status ≠ .unoccupied ∧ state.lastDown = some (P.downRecord i) ∧
              interruptionDecision rate.eta r.input.time state memory = .ok false ∧
              (state.S, state.backlog) =
                QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j) ∧
              (r.output.followers i).configuration = .ordinary next nextMemory ∧
              (r.output.followers i).failure = none ∧
              r.output.next.followers i = .ordinary next nextMemory ∧
              next.status ≠ .unoccupied ∧ next.lastDown = some (P.downRecord i) ∧
              next.buffer = state.buffer ∧
              (next.S, next.backlog) =
                QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i (j + 1)) ∧
              next.delta =
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i (j + 1))).1 -
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word i j)).1 ∧
              (∃ token, memory.lastProposalRead = some token ∧
                token.timestamp.val + 1 = r.input.time.val ∧
                token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  r.input.row token.timestamp) ∧
              (∃ token, nextMemory.lastProposalRead = some token ∧
                token.timestamp.val = r.input.time.val ∧
                token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  r.input.row token.timestamp) ∧
              (∀ hnext : j + 1 < V.length,
                (V[j + 1]).input.state.followers i = .ordinary next nextMemory ∧
                (V[j + 1]).input.time.val = r.input.time.val + 1) ∧
              (∀ hafter : b + j + 1 < R.length,
                (R.get ⟨b + j + 1, hafter⟩).input.state.followers i = .ordinary next nextMemory ∧
                (R.get ⟨b + j + 1, hafter⟩).input.time.val = r.input.time.val + 1) ∧
              let prep := ReferenceActivePhysicalStep.prepare r.input
              let f := prep.followers.followers i
              let y := prep.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let arrival := RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (B[j - 1]'(by
                  have hlen : V.length = W.length + 1 := rfl
                  rw [hB]
                  omega))
                (P.assignment.assigned i)
              ∃ serviced,
                ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
                  f.follower f.row f.activation f.time y (preparedStates r ho i) = .success serviced ∧
                serviced.arrival = arrival ∧
                serviced.service = min (4 * rate.n) (state.backlog + arrival) ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).result =
                    .ok serviced.output ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).downInput = none ∧
                (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                  f.follower f.row f.activation f.time f.active f.arm y (preparedStates r ho i)).down = none ∧
                DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time y
                  (preparedStates r ho i) (preparedMemories r ho i) serviced.output = .ok (next, nextMemory) ∧
                serviced.output.S = next.S ∧ serviced.output.backlog = next.backlog ∧
                serviced.output.delta = next.delta ∧ next.delta = serviced.service ∧
                (next.status = .released ↔ state.status = .released ∨
                  (state.status = .pending ∧ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                    y (P.downRecord i))) ∧
                (next.status = .pending ↔ state.status = .pending ∧
                  ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                    y (P.downRecord i)) := by
  classical
  intro hq
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let b := birthIndex rate rewards C_star C_h source
  let W := liveTail rate rewards C_star C_h source
  obtain ⟨c, birth, P, B, hb, hborn, hSigma, hc, hchosen, hB, hdrop, hwords, hread, hcutoff⟩ :=
    actual_first_corrected_live_words rate rewards C_star C_h u t source hz hq
  have hBW : B.length = W.length := hB
  have henabled (k : Fin W.length) : (B[k.val]'(by omega)).enabled = true :=
    (laterLiveReadout_numerical _ _ _ (hread k)).1
  have hwordsV := hwords
  have hlenV : 1 + W.length = (birth :: W).length := by simp only [List.length_cons, Nat.add_comm]
  change ∀ i v, 1 ≤ v → v ≤ 1 + W.length → _ at hwordsV
  rw [hlenV] at hwordsV
  have hcutoffPrepare : ∀ r,
      R[b + 1 + W.length]? = some r → ∀ i : Fin (p.m - 1),
      ∃ state memory,
        r.input.state.followers i = .ordinary state memory ∧
        ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
          .ok ({state with status := .unoccupied}, memory) ∧
        (r.output.preparation.followers.followers i).configuration =
          .ordinary {state with status := .unoccupied} memory := by
    intro r hr i
    exact actual_cutoff_prepare rate rewards C_star C_h source birth P hb hchosen hborn
      r hr (hcutoff r hr) i
  refine ⟨c, birth, P, B, hb, hborn, hSigma, hc, hB, hdrop, hwordsV, henabled,
    hcutoffPrepare, ?_⟩
  intro i j0 hpos0 hj0 state0 memory0 hinput0 hoccupied0 hseed index hj hle
  cases index with
  | zero => omega
  | succ n =>
      let j := n + 1
      have hk0 : j0 - 1 < W.length := by simp only [List.length_cons] at hj0; omega
      have hk : j - 1 < W.length := by simp only [List.length_cons] at hj; omega
      let k0 : Fin W.length := ⟨j0 - 1, hk0⟩
      let k : Fin W.length := ⟨j - 1, hk⟩
      have hpos : 1 ≤ j := by omega
      have hr0 := cons_live_record birth W j0 hj0 hpos0
      have hr := cons_live_record birth W j hj hpos
      rw [hr0] at hinput0
      obtain ⟨state, memory, hinput, hoccupied, hstorage⟩ :=
        actual_tail_inputs_from_seed rate rewards C_star C_h source birth P hb hchosen hborn
          i c B hB hread k0 state0 memory0 hinput0 hoccupied0 hseed k (by dsimp [k0, k]; omega)
      obtain ⟨hindex, selectedBoundary, sb, mb, nb, nmb, hrows, hrow, hrewards,
        hselectionB, hpayB, hliveB, hinputB, _hdomain, hdownB, hprepareB,
        houtputB, _hfailureB, hpreserves, hdecisionB, hmemoryB, hnextMemoryB⟩ :=
        internal_first_corrected_actual_tail_boundary rate source rewards C_star C_h
          birth P hb hchosen hborn i k
      obtain ⟨hs, hm⟩ := LocalConfiguration.ordinary.inj (hinput.symm.trans hinputB)
      subst sb
      subst mb
      have hreadK := hread k
      obtain ⟨selected, ho, hselection, _hlater, hlive, hcell⟩ :=
        laterLiveReadout_some _ _ _ hreadK
      have hcellW : (B[k.val]'(by omega)) =
          ReferenceFirstWindowNumericalStream.sourceCell (W.get k) selected.view.payload
            selected.view.pendingAtChoice (preparedStates (W.get k) ho)
            selected.view.complementWeights selected.view.cutoff (selection_choiceValid selected) := hcell
      have hselectedEq : selected = selectedBoundary := Option.some.inj
        (hselection.symm.trans hselectionB)
      subst selectedBoundary
      have hstates : preparedStates (W.get k) ho i = state :=
        (LocalConfiguration.ordinary.inj
          ((prepared_configuration (W.get k) ho i).symm.trans hprepareB)).1
      have hmemories : preparedMemories (W.get k) ho i = memory :=
        (LocalConfiguration.ordinary.inj
          ((prepared_configuration (W.get k) ho i).symm.trans hprepareB)).2
      let kr : Fin R.length := ⟨b + 1 + k.val, (List.getElem?_eq_some_iff.mp hindex).1⟩
      have hrecord : R.get kr = W.get k := (List.getElem?_eq_some_iff.mp hindex).2
      obtain ⟨serviced, next, nextMemory, hchecked, harrival, hservice, hserviceOutput,
        hrecordResult, hnoDownInput, hnoDown, hrelease, houtput, hfailure, hnext,
        hqueue, hdelta, hdown, hbuffer, hreleased, hpending⟩ :=
        occupied_record_service rewards C_star C_h source (W.get k) kr hrecord selected
          hselection hlive ho hrewards i (by rw [hstates]; exact hoccupied)
      have hn : next = nb := (LocalConfiguration.ordinary.inj (houtput.symm.trans houtputB)).1
      have hnm : nextMemory = nmb := (LocalConfiguration.ordinary.inj (houtput.symm.trans houtputB)).2
      have hoccupiedNext : next.status ≠ .unoccupied := by
        rw [hn]
        exact hpreserves hoccupied
      rw [hstates] at hqueue hdelta hdown hbuffer hreleased hpending
      conv at hservice => rhs; rw [hstates]
      conv at hserviceOutput => rhs; rw [hstates]
      rw [← hcellW] at harrival hservice hqueue hserviceOutput
      rw [hpayB] at harrival hservice hqueue hreleased hpending hserviceOutput
      have hstep := replay_live_cell_succ rate P i c B k.val (by omega)
      have houtputStorage : (next.S, next.backlog) =
          QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
            (([c] ++ B.take (k.val + 1)).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i))) := by
        rw [hstep]
        rw [← hstorage]
        exact hqueue
      have hjEq : k.val + 1 = j := by dsimp [k]; omega
      have houtWord := houtputStorage
      rw [hjEq] at houtWord
      have hdeltaWord : next.delta =
          (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
            (([c] ++ B.take j).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i)))).1 -
          (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
            (([c] ++ B.take (j - 1)).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                (P.assignment.assigned i)))).1 := by
        rw [← houtWord, ← hstorage]
        exact hdelta
      have hlastDown : next.lastDown = some (P.downRecord i) := hdown.trans (hdownB hoccupied)
      have htokenNext : ∃ token, nextMemory.lastProposalRead = some token ∧
          token.timestamp.val = (W.get k).input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (W.get k).input.row token.timestamp := by
        obtain ⟨token, hmem, htime, hbit⟩ := hnextMemoryB (by rw [← hn]; exact hoccupiedNext)
        refine ⟨token, ?_, ?_, hbit⟩
        · rw [hnm]
          exact hmem
        · have htimeW : token.timestamp.val + 1 = (W.get k).input.time.val + 1 := htime
          omega
      have hadj : ∀ hnext : j + 1 < (birth :: W).length,
          ((birth :: W)[j + 1]).input.state.followers i = .ordinary next nextMemory ∧
          ((birth :: W)[j + 1]).input.time.val = (W.get k).input.time.val + 1 := by
        intro hnextIndex
        have hnextTail : k.val + 1 < W.length := by
          simp only [List.length_cons] at hnextIndex
          omega
        have ha := continuing_tail_adjacent rate source rewards C_star C_h b k.val hnextTail
        rw [cons_live_record birth W (j + 1) hnextIndex (by omega)]
        have hnextIdx : j + 1 - 1 = k.val + 1 := by omega
        simp only [hnextIdx]
        exact ⟨(congrArg (fun s => s.followers i) ha.1).trans hnext, ha.2⟩
      have hglobalAdj : ∀ hafter : b + j + 1 < R.length,
          (R.get ⟨b + j + 1, hafter⟩).input.state.followers i = .ordinary next nextMemory ∧
          (R.get ⟨b + j + 1, hafter⟩).input.time.val = (W.get k).input.time.val + 1 := by
        intro hafter
        have hprev : b + j < R.length := by omega
        have hidx : (⟨b + j, hprev⟩ : Fin R.length) = kr := by
          apply Fin.ext
          change b + j = b + 1 + k.val
          omega
        have ha := complete_adjacent rate source rewards C_star C_h (b + j) hafter
        have hprevRecord : R.get ⟨b + j, hprev⟩ = W.get k := by rw [hidx]; exact hrecord
        have hstateAdj : (R.get ⟨b + j + 1, hafter⟩).input.state =
            (R.get ⟨b + j, hprev⟩).output.next := ha.1
        have htimeAdj : (R.get ⟨b + j + 1, hafter⟩).input.time.val =
            (R.get ⟨b + j, hprev⟩).input.time.val + 1 := ha.2
        rw [hprevRecord] at hstateAdj htimeAdj
        exact ⟨(congrArg (fun s => s.followers i) hstateAdj).trans hnext, htimeAdj⟩
      have hserviceFrame : serviced.output.S = next.S ∧
          serviced.output.backlog = next.backlog ∧ serviced.output.delta = next.delta ∧
          next.delta = serviced.service := by
        have he : (B[k.val]'(by omega)).enabled = true := henabled k
        have hq := hqueue
        simp only [he, QueueReplay.transition, ↓reduceIte, Prod.mk.injEq] at hq
        have hS := hq.1
        have hbacklog := hq.2
        have hd : next.delta = min (4 * rate.n)
            (state.backlog + RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (B[k.val]'(by omega)) (P.assignment.assigned i)) := by omega
        rw [hserviceOutput]
        simp only [ActiveFollowerQueueOperation.serviceUpdate, ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity, CappedService.service, CappedService.residual]
        exact ⟨hS.symm, hbacklog.symm, hd.symm, hd.trans hservice.symm⟩
      refine ⟨selected, ho, state, memory, next, nextMemory, ?_, hselection, hpayB,
        ?_, hinput, hprepareB, hstates, hmemories, hoccupied, hdownB hoccupied,
        hdecisionB, hstorage, houtput, hfailure, hnext, hoccupiedNext, hlastDown,
        hbuffer, ?_, ?_, hmemoryB hoccupied, htokenNext, hadj, hglobalAdj, serviced, hchecked,
        harrival, hservice, hrecordResult, hnoDownInput, hnoDown, hrelease,
        hserviceFrame.1, hserviceFrame.2.1, hserviceFrame.2.2.1, hserviceFrame.2.2.2,
        hreleased, hpending⟩
      · have hidx : b + j = b + 1 + k.val := by omega
        rw [hidx]
        exact hindex
      · rw [← hpayB]
        exact hlive
      · simpa only [Nat.add_sub_cancel] using houtWord
      · simpa only [j, Nat.add_sub_cancel] using hdeltaWord

/-- At terminal corrected birth there is no subsequent LIVE boundary at which
this module's conditional seed could be supplied. Native acceptance itself is
the downstream consumer's endpoint operation. -/
theorem internal_first_corrected_terminal_no_live_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : source ∈ correctedCell rate rewards C_star C_h u t)
    (hterminal : t.val + 1 = p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h source
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      b + 1 = R.length ∧ liveTail rate rewards C_star C_h source = [] ∧
      (birth :: liveTail rate rewards C_star C_h source).length = 1 ∧
      ¬ ∃ j0 : ℕ, 1 ≤ j0 ∧ j0 < (birth :: liveTail rate rewards C_star C_h source).length := by
  dsimp only
  obtain ⟨L, c, birth, P, base, _hL, _hc, _hpref, _hLb, hb, _hrecord,
    _htime, _hrows, _hselected, _hrewards, _hfields, _hchosen, _henabled,
    hborn, _hSigma, _hrate, _hreward, _hqueues, _hbase, hterm, _hword, _hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t source hz
  have hend := hterm hterminal
  have hW : liveTail rate rewards C_star C_h source = [] := by
    simp only [liveTail, ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords, hend,
      List.drop_length, List.takeWhile_nil]
  refine ⟨birth, P, hb, hborn, hend, hW, ?_, ?_⟩
  · rw [hW]
    rfl
  · rw [hW]
    simp only [List.length_cons, List.length_nil]
    omega

end Bandits.Support.ReferenceFirstCorrectedOccupiedCalendarPreservation

end
