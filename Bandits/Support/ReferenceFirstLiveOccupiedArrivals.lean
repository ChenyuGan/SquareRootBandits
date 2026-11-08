/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstWindowNumericalStream

import Mathlib.Tactic.Ring

/-!
# Actual occupied-follower arrivals in the first live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

For an occupied follower at an actual first-live record, this identifies the
prepared DOWN record, the whole-source recording gate, and the physical raw
arrival with the same cell's quantized numerical arrival. The result retains
the DATA and mask conditions on the actual feedback claim; it makes no queue
induction, service law, recording-law, or manuscript-closure claim. It places
no positivity restriction on rewards, so the feedback identity includes zero
reward, and exposes the literal occupied threshold `4 (m - 1) xi / zeta`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveFollowerSafety
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceFirstLiveOccupiedArrivals

variable {p : ConstructorDimensions.Parameters}

/-- The actual occupied follower uses the assignment already present in its
prepared state. The whole-row map selects its DATA/source/mask/thinning event
exactly when the local occupied recorder gate passes, and on that event its
raw integer arrival is the same cell's quantized numerical arrival.

The only per-cell hypothesis is occupancy. The run, seed, selected payload,
prepared states, complement weights, and numerical cell are all the original
computed first-live objects. -/
theorem actual_occupied_follower_arrival
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (i : Fin (p.m - 1))
    (hoccupied : ((ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).states i).status ≠ .unoccupied) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    let payload := cell.selected.view.payload
    let assigned := payload.assignment.assigned i
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
    let own := record.output.ownEntries player
    let slice := (record.input.row.2 record.input.time).1
    (cell.states i).lastDown = some (payload.downRecord i) ∧
    PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i) = assigned ∧
    (payload.downRecord i).val.h = payload.exponent assigned ∧
    OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h =
      payload.rate assigned ∧
    payload.rate assigned = CanonicalRecordingRates.xi p rate.eta.val
      payload.anchor assigned ∧
    (rate.n : ℝ) = rate.eta.val * (D p : ℝ) ∧
    CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
      CanonicalRecordingSlice.deterministicOwnedGateRawProbability
        (K := p.K) player =
      (4 * (((p.m - 1 : ℕ) : ℝ)) *
        CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) ∧
    (slotDraw slice = dataSlot →
      record.output.preparation.arms.actions player = assigned ∧
      ∀ _hmask : CanonicalRecordingSlice.recordingMask (K_pos p) player assigned slice,
        record.gridFeedback player = rewards record.input.time assigned ∧
        ReferenceActivePhysicalHorizon.observationValue own.2 =
          ((rewards record.input.time assigned).val : ℝ) / (D p : ℝ)) ∧
    (cell.input.recordedArm = some assigned ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (payload.downRecord i)) ∧
    ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row
      record.input.time (payload.downRecord i) own.2 =
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input assigned := by
  classical
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let start := ReferenceInitializationRun.elapsed p b.completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  let payload := cell.selected.view.payload
  let assigned := payload.assignment.assigned i
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let own := record.output.ownEntries player
  let slice := (record.input.row.2 record.input.time).1
  have hseed := seed
  have hsafety := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hprepared := hsafety.2 k i
  rcases hprepared with
    ⟨choice, choiceMemory, _next, _nextMemory, hchoice, _hnext, _hfailure,
      hlast⟩
  have hchoiceState : choice = cell.states i :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (cell.ordinary i))).1
  have hchoiceOccupied : choice.status ≠ .unoccupied := by
    rw [hchoiceState]
    exact hoccupied
  have hlastChoice : choice.lastDown = some (payload.downRecord i) :=
    hlast cell.selected cell.selection_actual hchoiceOccupied
  have hlastDown : (cell.states i).lastDown = some (payload.downRecord i) := by
    rw [← hchoiceState]
    exact hlastChoice

  have hdownArm : PrelaunchBufferRecovery.downArm rate.eta
      (payload.downRecord i) = assigned := by
    apply Fin.ext
    simp [PrelaunchBufferRecovery.downArm, payload.downRecord_fields i]
    rfl
  have hdownExponent : (payload.downRecord i).val.h = payload.exponent assigned := by
    rw [payload.downRecord_fields i]
  have hdownRate : OrdinaryMessageCodec.dyadicRate
      (payload.downRecord i).val.h = payload.rate assigned :=
    payload.downRecord_rate i
  have hrateCanonical : payload.rate assigned =
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned :=
    payload.rate_eq_canonical assigned
  have hpayloadNumerator : payload.n = rate.n :=
    ReferenceActivePhysicalStep.payload_n_eq payload
  have hn : (rate.n : ℝ) = rate.eta.val * (D p : ℝ) := by
    rw [← hpayloadNumerator]
    exact payload.n_eq_eta_mul_D

  have hrewardInput : record.input.rewards = rewards := by
    exact (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
      rate source rewards C_star C_h hc count hspan k).2.2.1
  have hdataAndFeedback := cell.followerDataClaim i
  have hactualAction : slotDraw slice = dataSlot →
      record.output.preparation.arms.actions player = assigned := by
    intro hdata
    have h := (hdataAndFeedback hdata).1
    simpa [record, cell, assigned, player, slice, hoccupied] using h
  have hactualFeedback : slotDraw slice = dataSlot →
      ∀ hmask : CanonicalRecordingSlice.recordingMask (K_pos p) player assigned slice,
        record.gridFeedback player = rewards record.input.time assigned ∧
        ReferenceActivePhysicalHorizon.observationValue own.2 =
          ((rewards record.input.time assigned).val : ℝ) / (D p : ℝ) := by
    intro hdata hmask
    have h := (hdataAndFeedback hdata).2 hoccupied hmask
    constructor
    · simpa [record, cell, assigned, player, slice, hrewardInput] using h.1
    · simpa [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries,
        ReferenceActivePhysicalHorizon.observationValue, record, cell, assigned,
        player, own, slice, hrewardInput] using h.2

  have hrateSourceWeights :
      ∀ arm, 0 < ReferenceFirstWindowNumericalStream.sourceWeights payload
        cell.selected.view.complementWeights arm :=
    ReferenceFirstWindowNumericalStream.sourceWeights_pos payload
      cell.selected.view.complementWeights cell.selected.view.cutoff
      record.input.time cell.choiceInputsValid
  have hrateSourceLower :
      ∀ arm, payload.anchor arm ≤
        ReferenceFirstWindowNumericalStream.sourceWeights payload
          cell.selected.view.complementWeights arm :=
    ReferenceFirstWindowNumericalStream.sourceWeights_lower payload
      cell.selected.view.complementWeights cell.selected.view.cutoff
      record.input.time cell.choiceInputsValid
  have hrateSourceUpper :
      ∀ arm, ReferenceFirstWindowNumericalStream.sourceWeights payload
        cell.selected.view.complementWeights arm ≤ 2 * payload.anchor arm :=
    ReferenceFirstWindowNumericalStream.sourceWeights_upper payload
      cell.selected.view.complementWeights cell.selected.view.cutoff
      record.input.time cell.choiceInputsValid
  let snapshot : Snapshot payload.assignment :=
    { missing := cell.selected.view.pendingAtChoice
      status := fun follower => (cell.states follower).status }
  let regime : Regime p := .live payload.assignment snapshot
  have hplayerNe : player ≠ coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hplayerIndex : ActiveRoundActions.followerIndex p.two_le_m player hplayerNe = i := by
    exact ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe
  have howner : SnapshotRecordingKernel.owns p regime player assigned := by
    change payload.assignment.assigned i =
      payload.assignment.assigned
        (ActiveRoundActions.followerIndex p.two_le_m player hplayerNe)
    exact (congrArg payload.assignment.assigned hplayerIndex).symm
  have hstatus : snapshot.status i ≠ .unoccupied := by
    simpa [snapshot] using hoccupied
  have hmapAction : ∀ x : CanonicalRecordingSlice.Slice p.m p.K,
      SnapshotRecordingKernel.dataAction p regime rate.eta.val rate.eta.property
        rate.sourceCap payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights payload
          cell.selected.view.complementWeights)
        payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper
        x player = assigned := by
    intro x
    simp [regime, SnapshotRecordingKernel.dataAction, hplayerNe,
      hplayerIndex, hstatus, assigned]
  have hmapProbability : SnapshotRecordingKernel.actionProbability p regime
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor
      (ReferenceFirstWindowNumericalStream.sourceWeights payload
        cell.selected.view.complementWeights)
      payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper
      player assigned = 1 := by
    simp [regime, SnapshotRecordingKernel.actionProbability, hplayerNe,
      hplayerIndex, hstatus, assigned]
  have hxiDyadic : CanonicalRecordingRates.xi p rate.eta.val
        payload.anchor assigned = OrdinaryMessageCodec.dyadicRate
          (payload.downRecord i).val.h := by
    calc
      _ = payload.rate assigned := hrateCanonical.symm
      _ = OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h := hdownRate.symm
  have hmaskCountPos : 0 < p.m - 1 := by omega
  have hmaskCountLt : p.m - 1 < p.K :=
    lt_of_le_of_lt (Nat.sub_le _ _) p.m_lt_K
  have hzeta : SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) ≠ 0 :=
    ne_of_gt (SparseCalendarReplay.sparseMaskProbability_pos p.K (p.m - 1)
      (K_pos p) hmaskCountLt)
  have hdpos : 0 < ((p.m - 1 : ℕ) : ℝ) := by
    exact_mod_cast hmaskCountPos
  have hthresholdExact :
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
        CanonicalRecordingSlice.deterministicOwnedGateRawProbability
          (K := p.K) player =
      (4 * (((p.m - 1 : ℕ) : ℝ)) *
        CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    rw [CanonicalRecordingSlice.deterministicOwnedGateRawProbability_follower
        p.two_le_m p.m_lt_K i,
        CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    simp only [PublicDiscreteDraws.followerCount]
    field_simp [hzeta, ne_of_gt hdpos]
    ring_nf
  have hthreshold :
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
        CanonicalRecordingSlice.deterministicOwnedGateRawProbability
          (K := p.K) player =
          ActiveFollowerQueueOperation.thinningProbability rate.eta
            (payload.downRecord i) := by
    rw [hthresholdExact]
    unfold ActiveFollowerQueueOperation.thinningProbability
    rw [hxiDyadic]
  have hmapEvent := SnapshotRecordingKernel.recordingMap_fixed_event_eq p regime
    rate.eta.val rate.eta.property rate.sourceCap payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights payload
      cell.selected.view.complementWeights)
    payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper
    player assigned howner hmapAction hmapProbability
  have hmapAt : SnapshotRecordingKernel.recordingMap p regime true
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor
      (ReferenceFirstWindowNumericalStream.sourceWeights payload
        cell.selected.view.complementWeights)
      payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper slice =
        some assigned ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (payload.downRecord i) := by
    have hpoint :
        SnapshotRecordingKernel.recordingMap p regime true
          rate.eta.val rate.eta.property rate.sourceCap payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights payload
            cell.selected.view.complementWeights)
          payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper slice =
            some assigned ↔
          CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m
            p.m_lt_K (K_pos p) player assigned
              (CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
                CanonicalRecordingSlice.deterministicOwnedGateRawProbability
                  (K := p.K) player) slice := by
      constructor
      · intro hmap
        have hmem : slice ∈ {x | SnapshotRecordingKernel.recordingMap p regime true
            rate.eta.val rate.eta.property rate.sourceCap payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights payload
              cell.selected.view.complementWeights)
            payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper x =
              some assigned} := hmap
        rw [hmapEvent] at hmem
        exact hmem
      · intro hgate
        have hmem : slice ∈ {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate
            p.two_le_m p.m_lt_K (K_pos p) player assigned
            (CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
              CanonicalRecordingSlice.deterministicOwnedGateRawProbability
                (K := p.K) player) x} := hgate
        rw [← hmapEvent] at hmem
        exact hmem
    have hpoint' :
        SnapshotRecordingKernel.recordingMap p regime true
          rate.eta.val rate.eta.property rate.sourceCap payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights payload
            cell.selected.view.complementWeights)
          payload.anchor_pos hrateSourceWeights hrateSourceLower hrateSourceUpper slice =
            some assigned ↔
      CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m
            p.m_lt_K (K_pos p) player assigned
              (CanonicalRecordingRates.xi p rate.eta.val payload.anchor assigned /
                CanonicalRecordingSlice.deterministicOwnedGateRawProbability
                  (K := p.K) player) slice := by
      exact hpoint
    simpa [ActiveFollowerQueueOperation.recorderGate,
      CanonicalRecordingSlice.deterministicOwnedRecordingGate,
      hdownArm, hthreshold] using hpoint'
  have hsourceArmGate :
      ReferenceFirstWindowNumericalStream.sourceArm record payload
        cell.selected.view.pendingAtChoice cell.states
        cell.selected.view.complementWeights cell.selected.view.cutoff
        cell.choiceInputsValid = some assigned ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (payload.downRecord i) := by
    simpa [ReferenceFirstWindowNumericalStream.sourceArm,
      ReferenceFirstWindowNumericalStream.sourceWeights_pos,
      ReferenceFirstWindowNumericalStream.sourceWeights_lower,
      ReferenceFirstWindowNumericalStream.sourceWeights_upper,
      slice, regime, snapshot] using hmapAt
  have hrecordedArmGate : cell.input.recordedArm = some assigned ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (payload.downRecord i) := by
    rw [cell.recordedArm_eq]
    exact hsourceArmGate

  have hfeedbackObs
      (hdata : slotDraw slice = dataSlot)
      (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) player assigned slice) :
      (own.2.val.1 : ℝ) =
        ((record.input.rewards record.input.time assigned).val : ℝ) / (D p : ℝ) := by
    have hfeedback := (hdataAndFeedback hdata).2 hoccupied hmask
    change ReferenceActivePhysicalHorizon.observationValue own.2 = _
    simpa [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries,
      ReferenceActivePhysicalHorizon.observationValue, record, own, player] using
      hfeedback.2
  have hfloorFormula :
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (payload.downRecord i) →
      Nat.floor ((rate.n : ℝ) *
        (((record.input.rewards record.input.time assigned).val : ℝ) /
          (D p : ℝ)) / payload.rate assigned) =
      ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta
        (payload.downRecord i) own.2 := by
    intro hgate
    rcases hgate with ⟨hdata, _hsource, hmask, _hthin⟩
    have hfeedbackObs := hfeedbackObs hdata hmask
    have hinside :
        (rate.n : ℝ) *
          (((record.input.rewards record.input.time assigned).val : ℝ) /
            (D p : ℝ)) / payload.rate assigned =
        (D p : ℝ) * rate.eta.val * own.2.val.1 /
          OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h := by
      rw [← hdownRate, hn, ← hfeedbackObs]
      ring
    exact congrArg Nat.floor hinside

  have harrival :
      ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row
        record.input.time (payload.downRecord i) own.2 =
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input assigned := by
    by_cases hgate : ActiveFollowerQueueOperation.recorderGate rate.eta i
        record.input.row record.input.time (payload.downRecord i)
    · have hrecorded := hsourceArmGate.mpr hgate
      rw [ActiveFollowerQueueOperation.rawArrival_eq_floor_of_gate
        rate.eta i record.input.row record.input.time (payload.downRecord i) own.2 hgate]
      rw [cell.quantizedArrival_eq assigned]
      rw [ite_eq_left hrecorded]
      exact (hfloorFormula hgate).symm
    · have hnotrecorded :
          ReferenceFirstWindowNumericalStream.sourceArm record payload
            cell.selected.view.pendingAtChoice cell.states
            cell.selected.view.complementWeights cell.selected.view.cutoff
            cell.choiceInputsValid ≠ some assigned := by
        intro hrecorded
        exact hgate (hsourceArmGate.mp hrecorded)
      have hnotrecordedActual :
          ReferenceFirstWindowNumericalStream.sourceArm
            (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
              rate source rewards C_star C_h hc count hspan)[k.val]
            cell.selected.view.payload cell.selected.view.pendingAtChoice cell.states
            cell.selected.view.complementWeights cell.selected.view.cutoff
            cell.choiceInputsValid ≠ some assigned := by
        simpa only [record] using hnotrecorded
      rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
      rw [cell.quantizedArrival_eq assigned]
      rw [ite_eq_right hgate]
      rw [ite_eq_right hnotrecordedActual]

  exact ⟨hlastDown, hdownArm, hdownExponent, hdownRate, hrateCanonical, hn,
    hthresholdExact,
    (fun hdata => ⟨hactualAction hdata, hactualFeedback hdata⟩),
    hrecordedArmGate, harrival⟩

end Bandits.Support.ReferenceFirstLiveOccupiedArrivals

end
