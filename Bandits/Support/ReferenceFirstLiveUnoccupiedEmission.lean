/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstWindowNumericalStream

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Actual first-live unoccupied follower emissions

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

The current saved contribution is evaluated on the actual physical record and
its selected payload's retained DOWN. The numerical input is the existing
actualLiveSourceCellAt, including its whole snapshot map. Logging is checked
before thinning and does not require a positive observation. The continuing
proof uses the public physical ownership and logging bodies directly.

This is an internal one-round producer for firstReplyQueueRecords before and
through the retained first DOWN. It proves no sparse recovery, queue or score
coupling, recording law, collection alignment, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.ReferenceFirstLiveUnoccupiedEmission

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev RoundRecord {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : RateInput p}

/-- The existing two contribution functions use exactly the same DOWN arm,
exponent, timestamp, and actual current emission. No occupancy premise is needed. -/
theorem actualCurrentSavedContribution_eq_emissionContribution
    (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record payload i =
      ReferenceFollowerSparseEmissionRecovery.emissionContribution (payload.downRecord i) i record := by
  have hi : ReferenceContinuingRecordingPhysicalReward.bufferFollowerIndex i = i := rfl
  unfold ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
    ReferenceFollowerSparseEmissionRecovery.emissionContribution
  rw [hi, ReferenceActiveDataOwnership.downRecord_arm]
  rfl

/-- The whole actual snapshot map selects this undecoded assignment exactly
on the source, DATA, own-pilot, mask, and inclusive unoccupied thinning event. -/
theorem sourceArm_eq_some_iff_unoccupied
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied) :
    ReferenceFirstWindowNumericalStream.sourceArm record cell.selected.view.payload
        cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
        cell.selected.view.cutoff cell.choiceInputsValid =
      some (cell.selected.view.payload.assignment.assigned i) ↔
    recorderSourceDraw p.two_le_m p.m_lt_K (record.input.row.2 record.input.time).1 =
        followerPlayer p.two_le_m i ∧
      ReferenceFirstLaunchNumericalCell.firstFollowerEvent i record.input.row record.input.time
        (cell.selected.view.payload.assignment.assigned i)
        (cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i)) := by
  classical
  let payload := cell.selected.view.payload
  let snapshot : ActiveRoundActions.Snapshot payload.assignment :=
    { missing := cell.selected.view.pendingAtChoice, status := fun j => (cell.states j).status }
  let weights := ReferenceFirstWindowNumericalStream.sourceWeights payload
    cell.selected.view.complementWeights
  have hpos := ReferenceFirstWindowNumericalStream.sourceWeights_pos payload
    cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
    cell.choiceInputsValid
  have hlower := ReferenceFirstWindowNumericalStream.sourceWeights_lower payload
    cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
    cell.choiceInputsValid
  have hupper := ReferenceFirstWindowNumericalStream.sourceWeights_upper payload
    cell.selected.view.complementWeights cell.selected.view.cutoff record.input.time
    cell.choiceInputsValid
  have hne := followerPlayer_ne_coordinator p.two_le_m i
  have hindex := followerIndex_followerPlayer p.two_le_m i hne
  have howner : SnapshotRecordingKernel.owns p (.live payload.assignment snapshot)
      (followerPlayer p.two_le_m i) (payload.assignment.assigned i) := by
    simp only [SnapshotRecordingKernel.owns, dite_eq_right hne, hindex]
  have haction : ∀ u, SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor weights payload.anchor_pos
      hpos hlower hupper u (followerPlayer p.two_le_m i) =
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i) u := by
    intro u
    simp [SnapshotRecordingKernel.dataAction, hne, hindex, snapshot, hunoccupied]
  have hprob : SnapshotRecordingKernel.actionProbability p (.live payload.assignment snapshot)
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor weights payload.anchor_pos
      hpos hlower hupper (followerPlayer p.two_le_m i) (payload.assignment.assigned i) =
        1 / (p.K : ℝ) := by
    simp [SnapshotRecordingKernel.actionProbability, hne, hindex, snapshot, hunoccupied]
  have hsets := SnapshotRecordingKernel.recordingMap_pilot_event_eq p
    (.live payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
    payload.anchor weights payload.anchor_pos hpos hlower hupper
    (followerPlayer p.two_le_m i) (payload.assignment.assigned i) howner haction hprob
  have hgate := Set.ext_iff.mp hsets (record.input.row.2 record.input.time).1
  simp only [Set.mem_ofPred_eq] at hgate
  rw [CanonicalRecordingSlice.unoccupiedFollower_savedThreshold_eq p payload.anchor i
    (payload.assignment.assigned i)] at hgate
  simpa only [ReferenceFirstWindowNumericalStream.sourceArm,
    CanonicalRecordingSlice.pilotRecordingGate, CanonicalRecordingSlice.recordingMask,
    ContinuousControlSlice.coordinate,
    ReferenceFirstLaunchNumericalCell.firstFollowerEvent, PublicDiscreteDraws.followerCount,
    AssignmentStartPayload.Input.rate, and_left_comm, and_assoc, payload, snapshot, weights]
    using hgate

private theorem logAt_contribution_eq_event
    (eta : ReferencePrelaunchFollower.LearningRate)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (time : Fin p.T)
    (activation : ReferencePrelaunchFollower.Activation p)
    (hactive : activation.val ≤ time.val + 1)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (arm : Fin p.K) (xi : ℝ)
    (hown : slotDraw (row.2 time).1 = dataSlot →
      own.1 = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
        (row.2 time).1)
    (hsource : recorderSourceDraw p.two_le_m p.m_lt_K (row.2 time).1 =
      followerPlayer p.two_le_m i)
    (hxi : xi = OrdinaryMessageCodec.dyadicRate M.val.h) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
      eta.val M.val.h arm (time.val + 1)
      (ReferencePrelaunchFollower.logAt i row activation time own) =
    if ReferenceFirstLaunchNumericalCell.firstFollowerEvent i row time arm xi then
      Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0 := by
  classical
  let thinGate : Prop :=
    ((row.2 time).1 Label.thin).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * xi) /
        CanonicalRecordingSlice.recordingZeta p.m p.K
  let savedGate : Prop :=
    ((row.2 time).1 Label.thin).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
        (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  have hthreshold : thinGate ↔ savedGate := by
    dsimp [thinGate, savedGate]
    have hnum : (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * xi) /
        CanonicalRecordingSlice.recordingZeta p.m p.K =
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
        (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
      rw [hxi, OrdinaryMessageCodec.dyadicRate,
        CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    rw [hnum]
  have htestsEq :
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i row activation time own) ↔
        slotDraw (row.2 time).1 = dataSlot ∧
          (∀ player : Fin p.m, player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ own.1) := by
    rw [ActiveFollowerLogging.loggingTestsPass_iff_source_mask]
    constructor
    · rintro ⟨_, hd, _, hm⟩
      exact ⟨hd, by simpa [hown hd] using hm⟩
    · rintro ⟨hd, hm⟩
      exact ⟨hactive, hd, hsource, by simpa [hown hd] using hm⟩
  let event := ReferenceFirstLaunchNumericalCell.firstFollowerEvent i row time arm xi
  by_cases htests : SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row activation time own)
  · have ⟨hdata, hmask⟩ := htestsEq.mp htests
    by_cases hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
        (row.2 time).1 = arm
    · have hownArm : own.1 = arm := (hown hdata).trans hpilot
      have hmaskArm : ∀ player : Fin p.m,
          player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ arm := by
        intro player hplayer hsame
        exact hmask player hplayer (by simpa [hownArm] using hsame)
      have hevent : event ↔ thinGate := by
        change (slotDraw (row.2 time).1 = dataSlot ∧
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 time).1 = arm ∧
          (∀ player : Fin p.m, player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ arm) ∧
          thinGate) ↔ thinGate
        constructor
        · intro he
          exact he.2.2.2
        · intro ht
          exact ⟨hdata, hpilot, hmaskArm, ht⟩
      rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation time own htests]
      change (if time.val + 1 = time.val + 1 ∧ own.1 = arm then
          SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p)
            eta.val M.val.h own.2.val
            ((row.2 time).1 Label.thin) else 0) =
        if event then Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
      have hkey : time.val + 1 = time.val + 1 ∧ own.1 = arm :=
        ⟨rfl, hownArm⟩
      rw [ite_eq_left hkey]
      by_cases hthin : thinGate
      · have he : event := hevent.mpr hthin
        have hsaved : savedGate := hthreshold.mp hthin
        have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor
          (p := p) eta M own.2
        unfold ActiveFollowerQueueOperation.sourceArrivalFloor at hfloor
        rw [← hxi] at hfloor
        rw [SparseCalendarReplay.savedContribution_eq_floor_of_le
          p.K (p.m - 1) (D p) eta.val M.val.h own.2.val
          ((row.2 time).1 Label.thin) hsaved]
        change Nat.floor ((D p : ℝ) * eta.val * (2 : ℝ) ^ M.val.h *
          own.2.val.val) = if event then
            Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
        rw [ite_eq_left he, hfloor.symm]
      · have hnotEvent : ¬ event := fun he => hthin (hevent.mp he)
        have hnotSaved : ¬ savedGate := fun hs => hthin (hthreshold.mpr hs)
        have hsavedNot : ¬ ((row.2 time).1 Label.thin).val ≤
            (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
              (((2 : ℝ) ^ M.val.h)⁻¹)) /
              SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
          simpa [savedGate] using hnotSaved
        change (if ((row.2 time).1 Label.thin).val ≤
            (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
              (((2 : ℝ) ^ M.val.h)⁻¹)) /
              SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) then
            Nat.floor ((D p : ℝ) * eta.val * (2 : ℝ) ^ M.val.h *
              own.2.val.val) else 0) =
          if event then Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
        rw [ite_eq_right hsavedNot, ite_eq_right hnotEvent]
    · have hownNe : own.1 ≠ arm := by
        intro heq
        exact hpilot ((hown hdata).symm.trans heq)
      have hnotEvent : ¬ event := by
        intro he
        exact hpilot he.2.1
      rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation time own htests]
      simp [SparseCalendarReplay.sparseBufferContribution,
        SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound,
        hownNe, hnotEvent, event]
  · have hnotEvent : ¬ event := by
      intro he
      exact htests (htestsEq.mpr ⟨he.1,
        by simpa [hown he.1, he.2.1] using he.2.2.1⟩)
    rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i row activation time own htests]
    simp [SparseCalendarReplay.sparseBufferContribution, hnotEvent, event]

/-- At an actual ordinary unoccupied preparation, emission is the existing
logger's literal output on the actual own entry. -/
theorem logEmission_eq_logAt_unoccupied
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied) :
    ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i)) := by
  simp only [ReferenceFollowerBufferProvenance.logEmission, cell.ordinary i,
    hunoccupied, dite_true]

/-- DATA feedback is used only on the true source map's assigned-arm atom.
The public owner geometry proves collision freedom, including zero reward. -/
theorem unoccupied_feedback_of_sourceArm
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hfields : ∀ j, (cell.states j).status ≠ .unoccupied →
      (cell.states j).lastDown = some (cell.selected.view.payload.downRecord j))
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied)
    (hmarker : ReferenceFirstWindowNumericalStream.sourceArm record cell.selected.view.payload
      cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
      cell.selected.view.cutoff cell.choiceInputsValid =
        some (cell.selected.view.payload.assignment.assigned i)) :
    record.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
        cell.selected.view.payload.assignment.assigned i ∧
      record.output.preparation.feedback.feedback (followerPlayer p.two_le_m i) =
        record.input.rewards record.input.time (cell.selected.view.payload.assignment.assigned i) ∧
      (record.output.ownEntries (followerPlayer p.two_le_m i)).2.val.val =
        ((record.input.rewards record.input.time
          (cell.selected.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ) := by
  have hevent := (sourceArm_eq_some_iff_unoccupied record cell i hunoccupied).mp hmarker
  have hdata := hevent.2.1
  have haction : record.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
      cell.selected.view.payload.assignment.assigned i := by
    rw [(cell.followerDataClaim i hdata).1, ite_eq_left hunoccupied]
    exact hevent.2.2.1
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some cell.selected := by
    rw [← hprep]
    exact cell.selection_actual
  have hordinary : ∀ j,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers j).configuration =
        .ordinary (cell.states j) (cell.memories j) := by
    intro j
    rw [← hprep]
    exact cell.ordinary j
  have howns : SnapshotRecordingKernel.owns p
      (.live cell.selected.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states))
      (followerPlayer p.two_le_m i) (cell.selected.view.payload.assignment.assigned i) := by
    simp only [SnapshotRecordingKernel.owns,
      dite_eq_right (followerPlayer_ne_coordinator p.two_le_m i),
      followerIndex_followerPlayer p.two_le_m i
        (followerPlayer_ne_coordinator p.two_le_m i)]
  have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback record.input
    cell.selected hselected cell.states cell.memories hordinary hfields cell.assignment_live
    hdata (followerPlayer p.two_le_m i) (cell.selected.view.payload.assignment.assigned i)
    (by rw [← hprep]; exact haction) howns hevent.2.2.2.1
  refine ⟨haction, ?_, ?_⟩
  · rw [hprep]
    exact hfeedback.1
  · rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared i record, hprep]
    exact hfeedback.2

/-- A different actual recorder source makes this follower's current log
empty, even though the whole map may record another owner's arm. -/
theorem emissionContribution_zero_of_other_source
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied)
    (hsource : recorderSourceDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 ≠ followerPlayer p.two_le_m i) :
    ReferenceFollowerSparseEmissionRecovery.emissionContribution
      (cell.selected.view.payload.downRecord i) i record = 0 := by
  have htests : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i))) := by
    intro hpass
    exact hsource ((ActiveFollowerLogging.loggingTestsPass_iff_source_mask i
      record.input.row (record.input.state.activations i) record.input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i))).mp hpass).2.2.1
  unfold ReferenceFollowerSparseEmissionRecovery.emissionContribution
  rw [logEmission_eq_logAt_unoccupied record cell i hunoccupied,
    ActiveFollowerLogging.logAt_eq_nil_of_not_tests i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i)) htests]
  rfl

/-- Direct physical-body composition for one unoccupied record. The only
conditional history input is the explicitly displayed retained DOWN agreement
for occupied co-players; the actual root below produces it from W. -/
theorem emissionContribution_eq_quantizedArrival
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hfields : ∀ j, (cell.states j).status ≠ .unoccupied →
      (cell.states j).lastDown = some (cell.selected.view.payload.downRecord j))
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied) :
    ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (cell.selected.view.payload.downRecord i) i record =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) := by
  classical
  let payload := cell.selected.view.payload
  let assigned := payload.assignment.assigned i
  let own := record.output.ownEntries (followerPlayer p.two_le_m i)
  let event := ReferenceFirstLaunchNumericalCell.firstFollowerEvent i record.input.row
    record.input.time assigned (payload.rate assigned)
  have hmap := sourceArm_eq_some_iff_unoccupied record cell i hunoccupied
  rw [cell.quantizedArrival_eq assigned]
  by_cases hsource : recorderSourceDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = followerPlayer p.two_le_m i
  · have hown : slotDraw (record.input.row.2 record.input.time).1 = dataSlot →
        own.1 = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
      intro hdata
      calc
        own.1 = (record.output.preparation.feedback.ownEntries
            (followerPlayer p.two_le_m i)).1 := by
          dsimp only [own]
          rw [record.output_eq]
          rfl
        _ = record.output.preparation.arms.actions (followerPlayer p.two_le_m i) := by
          rw [ReferenceActivePhysicalStep.PreparedRound.own_entry]
        _ = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
            (record.input.row.2 record.input.time).1 := by
          rw [(cell.followerDataClaim i hdata).1, ite_eq_left hunoccupied]
    have hxi : payload.rate assigned =
        OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h := by
      exact (payload.downRecord_rate i).symm
    have hcandidate := logAt_contribution_eq_event rate.eta (payload.downRecord i) i
      record.input.row record.input.time (record.input.state.activations i)
      (record.input.active i) own assigned (payload.rate assigned) hown hsource hxi
    have hcontribution : ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (payload.downRecord i) i record =
        if event then Nat.floor ((D p : ℝ) * rate.eta.val * own.2.val.val /
          payload.rate assigned) else 0 := by
      unfold ReferenceFollowerSparseEmissionRecovery.emissionContribution
      rw [ReferenceActiveDataOwnership.downRecord_arm,
        logEmission_eq_logAt_unoccupied record cell i hunoccupied]
      exact hcandidate
    rw [hcontribution]
    by_cases hevent : event
    · have hmarker := hmap.mpr ⟨hsource, hevent⟩
      have hfeedback := unoccupied_feedback_of_sourceArm record cell hfields i hunoccupied hmarker
      rw [ite_eq_left hevent, ite_eq_left hmarker]
      dsimp only [own]
      rw [hfeedback.2.2, rate.n_scale]
      congr 1
      ring
    · have hnotMap := fun hm => hevent (hmap.mp hm).2
      rw [ite_eq_right hevent, ite_eq_right hnotMap]
  · rw [emissionContribution_zero_of_other_source record cell i hunoccupied hsource,
      ite_eq_right (fun hm => hsource (hmap.mp hm).1)]

/-- A retained first-live index is exactly the existing physical successor
of the original run prefix, and hence P's candidate at its original control.
The strict calendar domain is produced from the finite window index. -/
theorem window_record_eq_candidate
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompleteRows p)
    (J : Fin (M p)) (rewards : RewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length) :
    ∃ hstep : start + (k.val + 1) ≤ p.T,
      let record := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[k.val]
      let x := ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards
        start k.val hstep active
      record = ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k.val hstep active ∧
      record = ReferenceContinuingDataCandidateLogging.candidateRecord
        initial rows J rewards start k.val hstep active (x.row.2 x.time) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  have hkcount : k.val < count := lt_of_lt_of_le k.isLt (hprefix.length_le.trans_eq hcount)
  have hstep : start + (k.val + 1) ≤ p.T := by omega
  refine ⟨hstep, ?_⟩
  have hnextPrefix : (ReferenceActivePhysicalHorizon.run initial rows J rewards start
      (k.val + 1) hstep active).records.IsPrefix E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start (k.val + 1) (count - (k.val + 1)) (by omega) active
    exact ⟨suffix, by simpa only [Nat.add_sub_of_le (by omega : k.val + 1 ≤ count)]
      using heq.symm⟩
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
    start k.val (by omega) active
  have hkNext : k.val < (ReferenceActivePhysicalHorizon.run initial rows J rewards start
      (k.val + 1) hstep active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have helem : (ReferenceActivePhysicalHorizon.run initial rows J rewards start
      (k.val + 1) hstep active).records[k.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
        start k.val hstep active := by
    simp only [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt,
      List.getElem_append_right (by omega :
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k.val
          (by omega) active).records.length ≤ k.val),
      hlength, Nat.sub_self, List.getElem_singleton]
  have hrecord := (hprefix.getElem k.isLt).trans
    ((hnextPrefix.getElem hkNext).symm.trans helem)
  refine ⟨hrecord, ?_⟩
  rw [hrecord]
  exact (congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
    (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ : RoundRecord))
      (ReferenceContinuingLiveSlicePreparation.inputAtControl_actual
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards
          start k.val hstep active))).symm

/-- On the initial physical record, the actual selector is produced by its
nonempty computed selection. A's sparse-cell theorem is then consumed only
on the actual selected-follower source branch. The other-source branch is zero
for this follower while retaining N's whole map. -/
theorem first_record_emissionContribution_eq_quantizedArrival
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate source rewards C_star C_h hc hs))
    (i : Fin (p.m - 1)) :
    ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (cell.selected.view.payload.downRecord i) i
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate source rewards C_star C_h hc hs) =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) := by
  classical
  let record := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate source rewards C_star C_h hc hs
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  have hseedPrepared : ∀ j,
      (record.output.preparation.followers.followers j).configuration =
        .ordinary (seed.followers j) (seed.memory j) :=
    ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_prepared_seed
      rate source rewards C_star C_h hc hs
  have hstates : ∀ j, cell.states j = seed.followers j := by
    intro j
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((cell.ordinary j).symm.trans (hseedPrepared j))).1
  have hunoccupied : (cell.states i).status = .unoccupied := by
    rw [hstates i]
    exact seed.unoccupied i
  have hstate : record.input.state.coordinator = .first := by
    rw [(ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
      rate source rewards C_star C_h hc hs).1]
    exact seed.coordinatorFirst
  have hprep : record.output.preparation.coordinator = .first
      (CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput record.input)) := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq.trans
      (ReferenceActivePhysicalStep.dispatch_first record.input hstate)
  have hselection := cell.selection_actual
  change record.output.preparation.coordinator.selection = some cell.selected at hselection
  cases hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput record.input) with
  | choiceDomainFailure installed =>
      rw [hprep, hchosen] at hselection
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
        reduceCtorEq] at hselection
  | recorderBoundaryFailure installed =>
      rw [hprep, hchosen] at hselection
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
        reduceCtorEq] at hselection
  | choiceRejected installed =>
      rw [hprep, hchosen] at hselection
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
        reduceCtorEq] at hselection
  | chosen installed arm =>
      have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
        record.input installed arm hchosen
      have hselected : record.output.preparation.coordinator.selection =
          some (ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights arm htime) := by
        rw [hprep, hchosen]
        exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
          record.input installed.registers.payload installed.startRoundResult
          installed.registers.time installed.registers.complementWeights arm htime
      have hselectedEq := Option.some.inj (cell.selection_actual.symm.trans hselected)
      have hpayload : cell.selected.view.payload = installed.registers.payload := by
        rw [hselectedEq]
        rfl
      have hfacts := ReferenceFirstLaunchNumericalCell.first_installation_payload_facts
        rate source rewards C_star C_h hc hs installed arm hchosen
      have hrate : cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i) =
          OrdinaryMessageCodec.dyadicRate (cell.selected.view.payload.downRecord i).val.h := by
        rw [hpayload]
        exact (hfacts.2.2.1 i).2.2
      have hmap := sourceArm_eq_some_iff_unoccupied record cell i hunoccupied
      rw [cell.quantizedArrival_eq]
      by_cases hsource : recorderSourceDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = followerPlayer p.two_le_m i
      · have hsparse := ReferenceFirstLaunchNumericalCell.first_launch_sparse_numerical_cell
          rate source rewards C_star C_h hc hs i installed arm hchosen hsource
        have hformula : ReferenceFollowerSparseEmissionRecovery.emissionContribution
            (cell.selected.view.payload.downRecord i) i record =
            if ReferenceFirstLaunchNumericalCell.firstFollowerEvent i record.input.row record.input.time
                (cell.selected.view.payload.assignment.assigned i)
                (cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i)) then
              Nat.floor ((D p : ℝ) * rate.eta.val *
                (((record.input.rewards record.input.time
                  (cell.selected.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
                cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i))
            else 0 := by
          rw [hpayload]
          exact hsparse.2.2.2.1
        rw [hformula]
        by_cases hevent : ReferenceFirstLaunchNumericalCell.firstFollowerEvent i record.input.row
            record.input.time (cell.selected.view.payload.assignment.assigned i)
            (cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i))
        · rw [ite_eq_left hevent, ite_eq_left (hmap.mpr ⟨hsource, hevent⟩), hrate,
            rate.n_scale]
          congr 1
          ring
        · rw [ite_eq_right hevent, ite_eq_right (fun hm => hevent (hmap.mp hm).2)]
      · rw [emissionContribution_zero_of_other_source record cell i hunoccupied hsource,
          ite_eq_right (fun hm => hsource (hmap.mp hm).1)]

section ActualWindow

variable (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)

/-- W's ordinary configurations and actual selection are identified with N's
cell by constructor and Option injectivity. Thus every occupied co-player has
the same retained DOWN, with no accepted-DOWN premise at this root. -/
theorem actual_retained_down_fields :
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    ∀ j, (cell.states j).status ≠ .unoccupied →
      (cell.states j).lastDown = some (cell.selected.view.payload.downRecord j) := by
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  rcases htruth k with ⟨_, _, states, memories, hordinary, hbranch⟩
  have hstates : states = cell.states := by
    funext j
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hordinary j).symm.trans (cell.ordinary j))).1
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, hbranch, hfields, htime, selected, hselected,
      hselection, hinput, hretained, out, hrecording, hidentity, hlive, hdata⟩
    have hselectedEq : selected = cell.selected :=
      Option.some.inj (hselected.symm.trans cell.selection_actual)
    simpa only [hstates, hselectedEq] using hretained
  · rcases hcontinuing with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, hfields,
        selected, hselected, hselection, hinput, hretained, out, hrecording,
        hidentity, hlive, hdata⟩
    have hselectedEq : selected = cell.selected :=
      Option.some.inj (hselected.symm.trans cell.selection_actual)
    simpa only [hstates, hselectedEq] using hretained

/-- The actual current DATA call succeeds before thinning. Its append is the
actual logEmission, with the exact singleton/empty logging tests. The original
prefix supplies all buffer domains; zero observations and failed thinning are
not additional inputs. -/
theorem actual_checkedLogging
    (i : Fin (p.m - 1))
    (hunoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status = .unoccupied) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    slotDraw (record.input.row.2 record.input.time).1 = dataSlot →
      ∃ logged,
        ActiveFollowerLogging.checkedLogging i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i)) (cell.states i) = .ok logged ∧
        (record.output.followers i).downInput = some logged ∧
        logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
        (SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time
            (record.output.ownEntries (followerPlayer p.two_le_m i))) →
          ReferenceFollowerBufferProvenance.logEmission i record =
            [SparseCalendarReplay.recordAt (record.input.time.val + 1)
              (ReferencePrelaunchFollower.loggingRound i record.input.row
                (record.input.state.activations i) record.input.time
                (record.output.ownEntries (followerPlayer p.two_le_m i)))]) ∧
        (¬ SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time
            (record.output.ownEntries (followerPlayer p.two_le_m i))) →
          ReferenceFollowerBufferProvenance.logEmission i record = []) := by
  dsimp only
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  obtain ⟨hstep, hrecord, hcandidate⟩ := window_record_eq_candidate initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    seed.activeAtStart k
  let x := ReferenceContinuingDataCandidateLogging.candidateInput initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val hstep
    seed.activeAtStart
  have hinput : record.input = x := congrArg
    (fun r : RoundRecord (p := p) (rate := rate) => r.input) hrecord
  have hordinary : ∀ j, ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
      .ordinary (cell.states j) (cell.memories j) := by
    intro j
    rw [← hinput]
    have h := cell.ordinary j
    rw [record.output_eq] at h
    exact h
  have hlogging := ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start k.val hstep seed.activeAtStart i (seed.followers i) (seed.memory i)
    (seed.configuration i) (seed.bufferValid i) (seed.chronologicalBuffer i)
    (seed.bufferStamps i) cell.states cell.memories hordinary hunoccupied
  intro hdata
  have hdataOriginal : slotDraw (x.row.2 x.time).1 = dataSlot := by
    rw [← hinput]
    exact hdata
  rcases hlogging.2.2.2.2 (x.row.2 x.time) hdataOriginal with
    ⟨logged, hcheck, hdown, happend, _, _, hsingle, hnil, _⟩
  have hcandidate' : record = ReferenceContinuingDataCandidateLogging.candidateRecord
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start k.val hstep seed.activeAtStart (x.row.2 x.time) := hcandidate
  have hown := congrArg (fun r : RoundRecord (p := p) (rate := rate) =>
    r.output.ownEntries (followerPlayer p.two_le_m i)) hcandidate'
  have hdownEq := congrArg (fun r : RoundRecord (p := p) (rate := rate) =>
    (r.output.followers i).downInput) hcandidate'
  refine ⟨logged, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hcandidate', ← hown] using hcheck
  · exact hdownEq.trans hdown
  · simpa only [← hcandidate'] using happend
  · simpa only [← hcandidate', ← hown] using hsingle
  · simpa only [← hcandidate', ← hown] using hnil

/-- At index zero, the actual original window record is A's first physical
record. A terminal or empty window cannot supply this finite index. -/
theorem actual_initial_record (hzero : k.val = 0) :
    ∃ hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T,
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[k.val] =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
        rate source rewards C_star C_h hc hs := by
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  obtain ⟨hstep, hrecord, _⟩ := window_record_eq_candidate initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    seed.activeAtStart k
  have hs : start < p.T := by omega
  refine ⟨hs, ?_⟩
  have hrecord' : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
        hstep seed.activeAtStart := hrecord
  have hrecordZero : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start 0
        (by omega) seed.activeAtStart := by
    simpa only [hzero] using hrecord'
  exact hrecordZero

/-- Every actual first-live unoccupied follower has precisely N's numerical
arrival, on the same original-source cell. The initial branch consumes A;
positive offsets use the actual ownership/logging bodies directly, with W's
retained DOWN fields. No receiver success or future DOWN acceptance is assumed. -/
theorem actual_first_live_unoccupied_emission
    (i : Fin (p.m - 1))
    (hunoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status = .unoccupied) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    let payload := cell.selected.view.payload
    ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record payload i =
        ReferenceFollowerSparseEmissionRecovery.emissionContribution (payload.downRecord i) i record ∧
      ReferenceFollowerSparseEmissionRecovery.emissionContribution (payload.downRecord i) i record =
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          cell.input (payload.assignment.assigned i) := by
  dsimp only
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  refine ⟨actualCurrentSavedContribution_eq_emissionContribution record cell.selected.view.payload i, ?_⟩
  by_cases hzero : k.val = 0
  · obtain ⟨hs, hfirst⟩ := actual_initial_record rate source rewards C_star C_h hc count hspan k hzero
    have htransfer : ∀ (r : RoundRecord (p := p) (rate := rate))
        (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
        r = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
          rate source rewards C_star C_h hc hs →
        ReferenceFollowerSparseEmissionRecovery.emissionContribution
            (c.selected.view.payload.downRecord i) i r =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            c.input (c.selected.view.payload.assignment.assigned i) := by
      intro r c hr
      subst r
      exact first_record_emissionContribution_eq_quantizedArrival
        rate source rewards C_star C_h hc hs c i
    exact htransfer record cell hfirst
  · exact emissionContribution_eq_quantizedArrival record cell
      (actual_retained_down_fields rate source rewards C_star C_h hc count hspan k) i hunoccupied

/-- The corresponding entry of N's existing source numerical list has this
actual current emission as its assigned-arm arrival. -/
theorem actualLiveSourceCells_unoccupied_arrival
    (i : Fin (p.m - 1))
    (hunoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status = .unoccupied) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hc count hspan)[k.val]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact k.isLt)) (cell.selected.view.payload.assignment.assigned i) =
        ReferenceFollowerSparseEmissionRecovery.emissionContribution
          (cell.selected.view.payload.downRecord i) i record := by
  dsimp only
  rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get]
  exact (actual_first_live_unoccupied_emission
    rate source rewards C_star C_h hc count hspan k i hunoccupied).2.symm

/-- Conditional consumer equation for the existing first-reply list on the
same full physical run. The explicit `j`, `m`, and index inequalities select
its pre/on-DOWN branch only. They do not assert an acceptance at `j` or identify
some other retained message with the current payload's DOWN. -/
theorem actual_firstReplyQueueRecords_before_down
    (i : Fin (p.m - 1))
    (hunoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status = .unoccupied)
    (j m : ℕ) (hbefore : k.val ≤ j) (hinclude : k.val < m) :
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j
      (cell.selected.view.payload.downRecord i) m)[k.val]'(by
        simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
          List.length_map, List.length_zipIdx, List.length_take]
        exact Nat.lt_min.mpr ⟨hinclude, lt_of_lt_of_le k.isLt (List.takeWhile_prefix _).length_le⟩) =
      (true, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
        (cell.selected.view.payload.assignment.assigned i)) := by
  dsimp only
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hfull : k.val < E.records.length := lt_of_lt_of_le k.isLt hprefix.length_le
  have htake : k.val < (E.records.take m).length := by
    rw [List.length_take]
    exact Nat.lt_min.mpr ⟨hinclude, hfull⟩
  have hget : (E.records.take m)[k.val] = W[k.val] :=
    (List.getElem_take (h := htake)).trans (hprefix.getElem k.isLt).symm
  simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
    List.getElem_map, List.getElem_zipIdx, Nat.zero_add, ite_eq_left hbefore]
  change (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution
      (cell.selected.view.payload.downRecord i) i (E.records.take m)[k.val]) = _
  rw [hget, (actual_first_live_unoccupied_emission
    rate source rewards C_star C_h hc count hspan k i hunoccupied).2]

/-- The actual physical feedback on the assigned-arm marker, using the same
whole reward table. No reward positivity or thinning success is added to the
unconditional emission identity. -/
theorem actual_unoccupied_marker_feedback
    (i : Fin (p.m - 1))
    (hunoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status = .unoccupied) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    cell.input.recordedArm = some (cell.selected.view.payload.assignment.assigned i) →
      record.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
          cell.selected.view.payload.assignment.assigned i ∧
        record.output.preparation.feedback.feedback (followerPlayer p.two_le_m i) =
          rewards record.input.time (cell.selected.view.payload.assignment.assigned i) ∧
        (record.output.ownEntries (followerPlayer p.two_le_m i)).2.val.val =
          ((rewards record.input.time (cell.selected.view.payload.assignment.assigned i)).val : ℝ) /
            (D p : ℝ) := by
  dsimp only
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  intro hmarker
  have hmap : ReferenceFirstWindowNumericalStream.sourceArm record cell.selected.view.payload
      cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
      cell.selected.view.cutoff cell.choiceInputsValid =
        some (cell.selected.view.payload.assignment.assigned i) := by
    rw [← cell.recordedArm_eq]
    exact hmarker
  have hfeedback := unoccupied_feedback_of_sourceArm record cell
    (actual_retained_down_fields rate source rewards C_star C_h hc count hspan k) i hunoccupied hmap
  have hrewards : record.input.rewards = rewards :=
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
      rate source rewards C_star C_h hc count hspan k).2.2.1
  have hreward := congrArg (fun table : RewardTable p =>
    table record.input.time (cell.selected.view.payload.assignment.assigned i)) hrewards
  exact ⟨hfeedback.1, hfeedback.2.1.trans hreward,
    hfeedback.2.2.trans (congrArg (fun y : Fin (D p + 1) => (y.val : ℝ) / (D p : ℝ)) hreward)⟩

end ActualWindow

end Bandits.Support.ReferenceFirstLiveUnoccupiedEmission

end
