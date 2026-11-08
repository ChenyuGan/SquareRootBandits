/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedInheritedFollowerCutoffQueue
public import Bandits.Support.ReferenceFirstLiveOriginalSourceOverflowBound

import Mathlib.Tactic

/-!
# Literal old inherited follower queues in the first-window overflow event

This module covers only the old stored-backlog observations retained across
the actual first corrected replacement. The source event reads actual follower
state fields at the admitted physical sites. It is a subevent of the original
first-window overflow event, not a claim about every physical queue event.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-187,256-290`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-299,391-408,425-426`,
and `sources/zip4/manuscript/08_main_theorem.tex:29-42,111-128`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCorrectedInheritedQueueOverflowCover

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}

/-- The literal ordinary follower register observation: its old DOWN word is
not the current replacement's word, and its stored backlog exceeds the
printed normalized threshold. -/
def ordinaryRecordStoredBacklogOverflow
    (rate : RateInput p) (P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (allowOutput : Bool) : Prop :=
  ∃ state memory,
    ((r.input.state.followers i = .ordinary state memory ∨
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
      (allowOutput = true ∧ r.output.next.followers i = .ordinary state memory)) ∧
      state.lastDown ≠ some (P.downRecord i) ∧
      (state.backlog : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val))

/-- At a fixed corrected slice, inspect only ordinary states physically present
at the birth-through-live records, actual cutoff INPUT/CHOICE, or the same
collection segment through its first excluded INPUT/CHOICE boundary. The
boundary OUTPUT is excluded. -/
def literalOldInheritedFollowerStoredBacklogOverflowAt
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p) : Prop :=
  z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∃ birth, ∃ (P : ReferenceActivePhysicalStep.Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∃ i : Fin (p.m - 1),
       ((∃ j : Fin V.length,
          ordinaryRecordStoredBacklogOverflow rate P i V[j.val] true) ∨
        (∃ cutoff, R[e]? = some cutoff ∧
          ordinaryRecordStoredBacklogOverflow rate P i cutoff false) ∨
        (∃ seg, ∃ (q : Fin R.length),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          e ≤ q.val ∧ q.val ≤ e + seg.records.length ∧
          ordinaryRecordStoredBacklogOverflow rate P i R[q.val]
            (decide (q.val < e + seg.records.length)))))

/-- The union of the literal old stored-backlog events over all original
corrected-slice indices. Each member still quantifies an original source in
that slice's corrected cell. -/
def literalOldInheritedFollowerStoredBacklogOverflow
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    Set (SourceInput p) :=
  {z | ∃ u : Fin p.T, ∃ t : Fin p.T,
    literalOldInheritedFollowerStoredBacklogOverflowAt
      rate rewards C_star C_h u t z}

private theorem firstOverflowPrefix_le_of_backlog_overflow
    (rate : RateInput p) (cells : List (RecordedQueueRun.RoundInput p.K))
    (i : Fin p.K) (backlog : ℕ)
    (hbacklog : backlog =
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cells cells.length i).2)
    (hlarge : (backlog : ℝ) / (rate.n : ℝ) >
      1 / (32 * rate.eta.val)) :
    UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells ≤ cells.length := by
  classical
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hnormalized :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay q cells cells.length i).2 : ℝ) /
          (q.n : ℝ) > 1 / (32 * q.eta) := by
    rw [← hbacklog]
    simpa only [q, ReferenceFirstLaunchNumericalCell.queueParameters] using hlarge
  have hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow
      q cells cells.length :=
    (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      q cells cells.length).mpr ⟨i, hnormalized⟩
  have hlength_pos : 0 < cells.length := by
    by_contra hnot
    have hzeroLength : cells.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero :
        (UnstoppedRecordedQueueComparison.unstoppedReplay q cells cells.length i).2 = 0 := by
      rw [hzeroLength]
      simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay]
    rw [hzero] at hnormalized
    have heta : 0 < q.eta := q.eta_pos
    have hpositive : 0 < q.eta⁻¹ * (1 / 32 : ℝ) := by positivity
    norm_num at hnormalized
    linarith
  have hex : ∃ n, 1 ≤ n ∧ n ≤ cells.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n :=
    ⟨cells.length, hlength_pos, le_rfl, hcross⟩
  unfold UnstoppedRecordedQueueComparison.firstOverflowPrefix
  rw [dite_eq_left hex]
  exact Nat.find_min' hex ⟨hlength_pos, le_rfl, hcross⟩


private theorem literalOldInheritedFollowerStoredBacklogOverflowAt_mem_firstWindowOverflow
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hOverflow : literalOldInheritedFollowerStoredBacklogOverflowAt
      rate rewards C_star C_h u t z) :
    z ∈ ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
      rate rewards C_star C_h := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
    rate rewards C_star C_h z
  let V := (R.drop b).take (1 + W.length)
  let e := b + (1 + W.length)
  change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    (∃ birth, ∃ (P : ReferenceActivePhysicalStep.Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∃ i : Fin (p.m - 1),
       ((∃ j : Fin V.length,
          ordinaryRecordStoredBacklogOverflow rate P i V[j.val] true) ∨
        (∃ cutoff, R[e]? = some cutoff ∧
          ordinaryRecordStoredBacklogOverflow rate P i cutoff false) ∨
        (∃ seg, ∃ (q : Fin R.length),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          e ≤ q.val ∧ q.val ≤ e + seg.records.length ∧
          ordinaryRecordStoredBacklogOverflow rate P i R[q.val]
            (decide (q.val < e + seg.records.length)))))) at hOverflow
  rcases hOverflow with ⟨hz, birth, eventP, hEventBirthLookup,
    hEventInstall, _hEventSigma, i, hSite⟩
  have hRoot :=
    ReferenceFirstCorrectedInheritedFollowerCutoffQueue.actual_prior_first_collection_canonical_replies
      rate rewards C_star C_h u t z hz
  rcases hRoot with ⟨hc, hspan, _hshort, _hsource,
    currentBirth, originalBirth, currentP, P0,
    hCurrentLookup, hCurrentInstall, _hCurrentSigma,
    _hOriginalLookup, _hOriginalInstall, _hOriginalTime, _hP0Sigma,
    _hP0First, _hP0Queues, hReplies⟩
  have hBirthEq : currentBirth = birth :=
    Option.some.inj (hCurrentLookup.symm.trans hEventBirthLookup)
  subst birth
  have hPayloadEq :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      currentBirth eventP currentP hEventInstall hCurrentInstall
  subst eventP

  let count := p.T - s
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hc count hspan
  let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hspan
  have hRecords : R = E.records := by
    exact ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
  have hLength : L0.length =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    change L0.length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    rw [hRecords]
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hspan
  have hwholeCross :
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
    simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hc
  have hWholeCells :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z = L0 := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    rw [dite_eq_left hwholeCross]
  have hWholePrefixEq :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
        rate rewards C_star C_h z =
      UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
    rw [hWholeCells]

  rcases hReplies i with ⟨k, acceptedRound, M, seedState, seedMemory, hReplyFields⟩
  rcases hReplyFields with ⟨_hwindowLower, _hkBirth, _hAcceptedLookup,
    _hAccepted, _hSender, _hSeedUnoccupied, _hSeedLastDown,
    _hSigma, _hServed, _hDelta, hQueueSeed, _hDownQueueZero,
    _hReplayServed, hReplayQueue, _hReplayDelta, hAfterBirth⟩
  rcases hAfterBirth with ⟨inputState, inputMemory, choiceState,
    _hBirthInput, _hInputUnoccupied, _hInputLastDown, _hInputReply,
    _hStarted, _hBirthChoice, _hChoiceUnoccupied, _hChoiceReply,
    _hNoDown, hLiveSites, hCutoffSites, hCollectionSites⟩
  have hSeedBacklogReplay : seedState.backlog =
      (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        L0 L0.length (P0.assignment.assigned i)).2 :=
    hQueueSeed.symm.trans hReplayQueue

  have hObserved : ∃ backlog : ℕ,
      (backlog : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val) ∧
      backlog =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          L0 L0.length (P0.assignment.assigned i)).2 := by
    rcases hSite with hLive | hCutoff | hCollection
    · rcases hLive with ⟨j, hObs⟩
      rcases hObs with ⟨observed, observedMemory, hPhysical, hNotCurrent, hLarge⟩
      have hPhysical' :
          (V[j.val].input.state.followers i = .ordinary observed observedMemory ∨
            (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
              .ordinary observed observedMemory ∨
            V[j.val].output.next.followers i = .ordinary observed observedMemory) := by
        rcases hPhysical with hInput | hChoice | hOutput
        · exact Or.inl hInput
        · exact Or.inr (Or.inl hChoice)
        · exact Or.inr (Or.inr hOutput.2)
      have hKeep := hLiveSites j.val j.isLt observed observedMemory
        hPhysical' hNotCurrent
      have hReply := hKeep.2.2.1
      have hObservedSeed : observed.backlog = seedState.backlog := by
        have h := congrArg (fun fields => fields.2.2.2) hReply
        simpa only [ReferenceFollowerReplyChronology.reply] using h
      exact ⟨observed.backlog, hLarge,
        hObservedSeed.trans hSeedBacklogReplay⟩
    · rcases hCutoff with ⟨cutoff, hLookup, hObs⟩
      rcases hObs with ⟨observed, observedMemory, hPhysical, hNotCurrent, hLarge⟩
      obtain ⟨endpoint, endpointMemory, hInput, hChoice, hEndpointFrame⟩ :=
        hCutoffSites cutoff hLookup
      have hStateEq : observed = endpoint ∨
          observed = {endpoint with status := .unoccupied} := by
        rcases hPhysical with hInputObserved | hChoiceObserved | hImpossible
        · obtain ⟨hState, _hMemory⟩ :=
            DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hInput.symm.trans hInputObserved)
          exact Or.inl hState.symm
        · obtain ⟨hState, _hMemory⟩ :=
            DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hChoice.symm.trans hChoiceObserved)
          exact Or.inr hState.symm
        · exact False.elim (by simpa using hImpossible.1)
      have hNotEndpoint : endpoint.lastDown ≠ some (currentP.downRecord i) := by
        intro hCurrent
        apply hNotCurrent
        rcases hStateEq with hState | hState
        · simpa [hState] using hCurrent
        · simpa [hState] using hCurrent
      have hEndpointReply := hEndpointFrame hNotEndpoint
      have hObservedSeed : observed.backlog = seedState.backlog := by
        have hObservedEndpoint : observed.backlog = endpoint.backlog := by
          rcases hStateEq with hState | hState
          · rw [hState]
          · rw [hState]
        have hEndpointSeed : endpoint.backlog = seedState.backlog := by
          have h := congrArg (fun fields => fields.2.2.2) hEndpointReply.2.2
          simpa only [ReferenceFollowerReplyChronology.reply] using h
        exact hObservedEndpoint.trans hEndpointSeed
      exact ⟨observed.backlog, hLarge,
        hObservedSeed.trans hSeedBacklogReplay⟩
    · rcases hCollection with ⟨seg, q, hSegEvent, hLower, hUpper, hObs⟩
      have hIndex : e < R.length := lt_of_le_of_lt hLower q.isLt
      rcases hObs with ⟨observed, observedMemory, hPhysical, hNotCurrent, hLarge⟩
      rcases hCollectionSites with hEnd | ⟨_hIndex, rootSeg, hSegRoot,
          _hEntry, _hPayload, _hRecords, hSites⟩
      · exact False.elim ((Nat.ne_of_lt hIndex) hEnd)
      · have hSegEq : rootSeg = seg :=
          Option.some.inj (hSegRoot.symm.trans hSegEvent)
        subst rootSeg
        have hPhysical' :
            (R[q.val].input.state.followers i = .ordinary observed observedMemory ∨
              (ReferenceFollowerFixedReply.actualChoice R[q.val] i).configuration =
                .ordinary observed observedMemory ∨
              (q.val < e + seg.records.length ∧
                R[q.val].output.next.followers i = .ordinary observed observedMemory)) := by
          rcases hPhysical with hInput | hChoice | hOutput
          · exact Or.inl hInput
          · exact Or.inr (Or.inl hChoice)
          · have hStrict : q.val < e + seg.records.length := by
              simpa only [decide_eq_true_eq] using hOutput.1
            exact Or.inr (Or.inr ⟨hStrict, hOutput.2⟩)
        have hKeep := hSites q hLower hUpper observed observedMemory
          hPhysical' hNotCurrent
        have hReply := hKeep.2.2.1
        have hObservedSeed : observed.backlog = seedState.backlog := by
          have h := congrArg (fun fields => fields.2.2.2) hReply
          simpa only [ReferenceFollowerReplyChronology.reply] using h
        exact ⟨observed.backlog, hLarge,
          hObservedSeed.trans hSeedBacklogReplay⟩

  rcases hObserved with ⟨observedBacklog, hLarge, hObservedBacklogReplay⟩
  have hPrefix :
      UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L0 ≤ L0.length := by
    exact firstOverflowPrefix_le_of_backlog_overflow rate L0
      (P0.assignment.assigned i) observedBacklog hObservedBacklogReplay hLarge
  have hWholeBound :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
          rate rewards C_star C_h z ≤
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
          rate rewards C_star C_h z := by
    rw [hWholePrefixEq]
    exact hPrefix.trans (Nat.le_of_eq hLength)
  change ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rate rewards C_star C_h z ≠ none
  unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
  rw [ite_eq_left hWholeBound]
  simp

/-- Every literal old stored-backlog observation in any corrected slice is
contained in the same original first-live overflow event. -/
theorem literalOldInheritedFollowerStoredBacklogOverflow_subset_firstWindowOverflow
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    literalOldInheritedFollowerStoredBacklogOverflow
        rate rewards C_star C_h ⊆
      ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
        rate rewards C_star C_h := by
  rintro z ⟨u, t, hOverflow⟩
  exact literalOldInheritedFollowerStoredBacklogOverflowAt_mem_firstWindowOverflow
    rate rewards C_star C_h u t z hOverflow

/-- The original source-law finite measure of the joint old-queue union has
the same inverse-square bound as the containing first-window event. The
continuous control input is used only by that original-event bound. -/
theorem literalOldInheritedFollowerStoredBacklogOverflow_measureReal_le_inv_N_sq
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (literalOldInheritedFollowerStoredBacklogOverflow
          rate rewards C_star C_h) ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (literalOldInheritedFollowerStoredBacklogOverflow
          rate rewards C_star C_h) ≤
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h) :=
      measureReal_mono
        (literalOldInheritedFollowerStoredBacklogOverflow_subset_firstWindowOverflow
          rate rewards C_star C_h)
    _ ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 :=
      ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow_measureReal_le_inv_N_sq
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedInheritedQueueOverflowCover

end
