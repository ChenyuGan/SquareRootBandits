/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveDownNumericalRecovery
public import Bandits.Support.ReferenceFirstLiveOccupiedService

import Lean.Elab.Tactic.Omega

/-!
# Actual first-live follower queue replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-408`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396,426-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module follows one actual follower through every boundary of the first
live window in the original physical run. It joins saved emissions before the
first accepted DOWN to occupied numerical service after that acceptance.
Enabled zero-arrival rounds remain in the replay. This is an internal
first-window result and does not assert source-law or regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower

namespace Bandits.Support.ReferenceFirstLiveFollowerQueueReplay

variable {p : ConstructorDimensions.Parameters}

private theorem actual_live_window_selector
    (rate : ReferenceFirstLiveDownNumericalRecovery.RateInput p)
    (source : ReferenceFirstLiveDownNumericalRecovery.SourceInput p)
    (rewards : ReferenceFirstLiveDownNumericalRecovery.RewardTable p)
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
      rate source rewards C_star C_h hc count hspan).length) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    ∃ selected, record.output.preparation.coordinator.selection = some selected ∧
      selected = cell.selected := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst seed.followers seed.memory
    seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none
    seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  dsimp only [E, W] at htruth
  dsimp only
  specialize htruth k
  rcases htruth with ⟨_, _, states, memories, hordinary, hbranch⟩
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, hbranch, hfields, htime, selected,
      hselected, hselection, htrace, hselectedFields, out, hrecording, hrest⟩
    have hsame : selected = (cell k).selected :=
      Option.some.inj (hselected.symm.trans (cell k).selection_actual)
    exact ⟨selected, hselected, hsame⟩
  · rcases hcontinuing with ⟨r, q, base, dispatched, hstart, continuation, arm,
      hbranch, hfields, selected, hselected, hselection, htrace, hselectedFields,
      out, hrecording, hrest⟩
    have hsame : selected = (cell k).selected :=
      Option.some.inj (hselected.symm.trans (cell k).selection_actual)
    exact ⟨selected, hselected, hsame⟩

private theorem actual_live_payload_stable
    (rate : ReferenceFirstLiveDownNumericalRecovery.RateInput p)
    (source : ReferenceFirstLiveDownNumericalRecovery.SourceInput p)
    (rewards : ReferenceFirstLiveDownNumericalRecovery.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)
    (k l : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).selected.view.payload =
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan l).selected.view.payload := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  obtain ⟨selectedK, hselectedK, hselectedKCell⟩ := actual_live_window_selector
    rate source rewards C_star C_h hc count hspan k
  obtain ⟨selectedL, hselectedL, hselectedLCell⟩ := actual_live_window_selector
    rate source rewards C_star C_h hc count hspan l
  have hgeomK := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst k selectedK hselectedK
  have hgeomL := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst l selectedL hselectedL
  have hsigmaK : selectedK.view.payload.sigma.val = start := hgeomK.1
  have hsigmaL : selectedL.view.payload.sigma.val = start := hgeomL.1
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hpayload := ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst W[k.val] W[l.val]
    selectedK selectedL
    (hprefix.sublist.subset (List.getElem_mem k.isLt))
    (hprefix.sublist.subset (List.getElem_mem l.isLt))
    hselectedK hselectedL
    (by omega)
  simpa only [cell, hselectedKCell, hselectedLCell] using hpayload

private theorem prepared_state_eq_of_unchanged_start
    (rate : ReferenceFirstLiveDownNumericalRecovery.RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time state memory =
      .ok (state, memory))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (DeclaredFollowerLocalRound.prepare rate i row activation time active
      (.ordinary state memory)).configuration = .ordinary choice choiceMemory) :
    choice = state ∧ choiceMemory = memory := by
  classical
  unfold DeclaredFollowerLocalRound.prepare at hchoice
  simp only [hstart] at hchoice
  cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state with
  | failure => simp only [hoff] at hchoice; cases hchoice
  | noOffer =>
      cases harm : ActiveFollowerArmChoice.followerArmChoice state row time i none with
      | none => simp only [hoff, harm] at hchoice; cases hchoice
      | some arm =>
          simp only [hoff, harm, DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
            at hchoice
          exact ⟨hchoice.1.symm, hchoice.2.symm⟩
  | offer offered =>
      cases harm : ActiveFollowerArmChoice.followerArmChoice state row time i (some offered) with
      | none => simp only [hoff, harm] at hchoice; cases hchoice
      | some arm =>
          simp only [hoff, harm, DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
            at hchoice
          exact ⟨hchoice.1.symm, hchoice.2.symm⟩

/-- The first-live follower's actual state at every boundary is the original
physical prefix state. An occupied endpoint has a retained accepted DOWN and
the exact saved-cell replay; an unoccupied endpoint retains its actual initial
buffer followed by every literal saved emission. -/
theorem actual_first_live_follower_prefix_replay
    (rate : ReferenceFirstLiveDownNumericalRecovery.RateInput p)
    (source : ReferenceFirstLiveDownNumericalRecovery.SourceInput p)
    (rewards : ReferenceFirstLiveDownNumericalRecovery.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)
    (i : Fin (p.m - 1)) (b : ℕ)
    (hb : b ≤ (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan
    ∃ hprefix : start + b ≤ p.T,
      ∃ sb mb,
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
          hprefix seed.activeAtStart).finalState.followers i = .ordinary sb mb ∧
        (b = 0 → sb = seed.followers i ∧ mb = seed.memory i ∧
          sb.lastDown = none ∧ sb.status = .unoccupied ∧ sb.S = 0 ∧
          sb.delta = 0 ∧ sb.backlog = 0 ∧
          sb.buffer = (seed.followers i).buffer) ∧
        (0 < b →
          ∃ k0 : Fin W.length, k0.val = 0 ∧
            let P0 := (cell k0).selected.view.payload
            let a := P0.assignment.assigned i
            let M0 := P0.downRecord i
            let arrivals := fun v => (cells.take v).map (fun c =>
              (c.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
            let replay := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals v)
            ((sb.status ≠ .unoccupied) →
              sb.lastDown = some M0 ∧
              (sb.S, sb.backlog) = replay b ∧
              sb.delta = (replay b).1 - (replay (b - 1)).1 ∧
              sb.S ≤ p.T * D p ∧ sb.delta ≤ D p ∧ sb.backlog ≤ p.T * D p ∧
              sb.S + sb.backlog ≤ b * D p ∧
              ∃ j : Fin W.length, j.val < b ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i M0) ∧
            (sb.status = .unoccupied →
              sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer = (seed.followers i).buffer ++
                (E.records.take b).flatMap
                  (ReferenceFollowerBufferProvenance.logEmission i) ∧
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i b M0 b = arrivals b)) := by
  classical
  dsimp only
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let E := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan seed.activeAtStart
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
      seed.activeAtStart
  have hwindowBound : W.length ≤ count := hwindowPrefix.length_le.trans_eq hcount
  have hprefixBound : ∀ n, n ≤ W.length → start + n ≤ p.T := by
    intro n hn
    exact (Nat.add_le_add_left (hn.trans hwindowBound) start).trans hspan
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start count hspan seed.activeAtStart seed.coordinatorFirst seed.followers seed.memory
    seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none
    seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  dsimp only [E, W] at hsafe
  have hseedConfiguration := seed.configuration i
  have hnoPrefix (n : ℕ) (hn : n ≤ W.length)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (hstate : (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).finalState.followers i = .ordinary state memory)
      (hzero : state.status = .unoccupied → state.lastDown = none ∧
        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
      (hunoccupied : state.status = .unoccupied) :
      ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records,
        ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
    intro record hrecord hreset
    have hnpos : 0 < n := by
      by_contra hnpos
      have hzero : n = 0 := by omega
      subst n
      rw [ReferenceActivePhysicalHorizon.run_zero_records] at hrecord
      simp at hrecord
    obtain ⟨j, hj⟩ := List.getElem_of_mem hrecord
    rcases hj with ⟨hjfull, hindexed⟩
    have hjlt : j < n := by
      have hlen : j < (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records.length := hjfull
      rw [ReferenceActivePhysicalHorizon.run_record_count] at hlen
      exact hlen
    have hrecordEq : record = (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records[j] := hindexed.symm
    have hchain := (ReferenceActivePhysicalHorizon.run_connected initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
      (hprefixBound n hn) seed.activeAtStart)
    obtain ⟨next, nextMemory, hnext, hstartBound⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology hchain i state memory
        hstate j hjfull
    rw [← hrecordEq] at hnext
    rcases hreset with ⟨cut, hcut, before, after, raw, message, scan, registers,
      lastService, houtcome⟩
    obtain ⟨_, _, logged, _, _, _, hinput, hcutActual⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
        record i cut hcut
    have houtcomeActual :
        (ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView
          (record.output.preparation.followers.followers i).follower
          (record.output.preparation.followers.followers i).row
          (record.output.preparation.followers.followers i).time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
          .accepted before after raw message scan registers lastService := by
      rw [← hcutActual]
      exact houtcome
    have hbefore := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged before after raw
      message scan registers lastService houtcomeActual
    subst before
    have happlied : ReferenceFollowerReplyChronology.appliedDown
        record i message.val.sigma :=
      ⟨logged, cut, after, raw, message, scan, registers, lastService,
        hinput, hcut, houtcome, rfl⟩
    obtain ⟨_, _, _, _, hnextStart⟩ :=
      ReferenceFollowerReplyChronology.record_appliedDown_strict
        record i message.val.sigma happlied next nextMemory hnext
    have hstartZero : ReferencePrelaunchFollower.acceptedStart state = 0 := by
      simp [ReferencePrelaunchFollower.acceptedStart, (hzero hunoccupied).1]
    omega
  have hbufferAt (n : ℕ) (hn : n ≤ W.length)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (hstate : (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).finalState.followers i = .ordinary state memory)
      (hunoccupied : state.status = .unoccupied)
      (hno : ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records,
        ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record) :
      state.buffer = (seed.followers i).buffer ++
        ((ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
          (hprefixBound n hn) seed.activeAtStart).records).flatMap
            (ReferenceFollowerBufferProvenance.logEmission i) := by
    have hprov := ReferenceFollowerBufferProvenance.run_buffer_provenance i initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
      (hprefixBound n hn) seed.activeAtStart (seed.followers i) (seed.memory i)
      (seed.configuration i) (seed.bufferValid i) (seed.chronologicalBuffer i)
      (seed.bufferStamps i) state memory hstate
    rw [ReferenceFollowerSparseEmissionRecovery.bufferFold_eq_seed_append_emissions_of_no_reset
      i (seed.followers i).buffer _ hno] at hprov
    exact hprov

  have hrunPrefix (n : ℕ) (hn : n ≤ W.length) :
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records = E.records.take n := by
    have hnc : n ≤ count := hn.trans hwindowBound
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start n (count - n) (by simpa only [Nat.add_sub_of_le hnc] using hspan)
      seed.activeAtStart
    have heq' : E.records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
          (hprefixBound n hn) seed.activeAtStart).records ++ suffix := by
      simpa only [Nat.add_sub_of_le hnc] using heq
    have hp : (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start n
        (hprefixBound n hn) seed.activeAtStart).records.IsPrefix E.records :=
      ⟨suffix, heq'.symm⟩
    have ht := List.prefix_iff_eq_take.mp hp
    rw [ReferenceActivePhysicalHorizon.run_record_count] at ht
    exact ht

  have hcellBoundary (k : Fin W.length) :
      ∃ state memory,
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
          (hprefixBound k.val (Nat.le_of_lt k.isLt)) seed.activeAtStart).finalState.followers i =
            .ordinary state memory ∧
        (cell k).states i = state ∧ (cell k).memories i = memory := by
    obtain ⟨hspanK, hstates⟩ := hsafe.1 k.val (Nat.le_of_lt k.isLt)
    obtain ⟨state, memory, hstate, hdomain, _, _, _, hzero, hoccupied⟩ := hstates i
    obtain ⟨choice, choiceMemory, _, _, hchoice, _, _, _⟩ := hsafe.2 k i
    have hcellChoice : (cell k).states i = choice ∧ (cell k).memories i = choiceMemory := by
      have hconfig := ((cell k).ordinary i).symm.trans hchoice
      exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig
    obtain ⟨hstep, hactual, _⟩ :=
      ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
        initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start count hspan seed.activeAtStart k
    let record := W[k.val]
    have hstateInput : record.input.state.followers i = .ordinary state memory := by
      have hactualInput := congrArg
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          r.input.state.followers i) hactual
      calc
        record.input.state.followers i =
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
              k.val hstep seed.activeAtStart).input.state.followers i := hactualInput
        _ = .ordinary state memory := by
          change (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            k.val hspanK seed.activeAtStart).finalState.followers i =
              .ordinary state memory
          exact hstate
    have hprepared : (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (.ordinary state memory)).configuration = .ordinary choice choiceMemory := by
      have hfull := record.output.preparation.followers.followers_eq i
      simp only [ReferenceActivePhysicalStep.followerInput,
        ReferenceActiveFeedbackCut.prepareFollowers] at hfull
      rw [hstateInput] at hfull
      have hchosen :
          (record.output.preparation.followers.followers i).configuration =
            .ordinary choice choiceMemory := by
        exact hchoice
      have hpreparedEq := congrArg (fun prepared => prepared.configuration) hfull
      exact hpreparedEq.symm.trans hchoice
    have hstart : ActiveFollowerLifecycle.startRound rate.eta record.input.time state memory =
        .ok (state, memory) := by
      by_cases hu : state.status = .unoccupied
      · exact ActiveFollowerLifecycle.startRound_unoccupied rate.eta record.input.time state memory
          hdomain hu
      · obtain ⟨hpos, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := hoccupied hu
        have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start count hspan seed.activeAtStart seed.coordinatorFirst k
          (cell k).selected (cell k).selection_actual
        obtain ⟨hsigma, htime, hgrid, hbits⟩ := hgeometry
        have htimeRecord : record.input.time.val = start + k.val := by
          simpa [record, W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
            ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using htime
        have hcoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate M =
            (cell k).selected.view.payload.sigma := by
          apply Fin.ext
          have hone := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
          omega
        have hstarted : M.val.sigma ≤ record.input.time.val := by
          rw [hMsigma, htimeRecord]
          omega
        have hbitFalse : token.bit = false := by
          rw [hbit]
          apply hbits token.timestamp
          · omega
          · omega
        have hgridAtRecord : record.input.time.val + 2 ≤
            FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
          have hgridRecord : record.input.time.val + 2 ≤
              FollowerCutoffScan.gridBoundary p rate.eta.val
                (cell k).selected.view.payload.sigma := by
              simpa [record, W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
                ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hgrid
          have hsameGrid := congrArg
            (FollowerCutoffScan.gridBoundary p rate.eta.val) hcoordinate
          rw [hsameGrid]
          exact hgridRecord
        have hgridNe :
            FollowerCutoffScan.gridBoundary p rate.eta.val
                (ActiveFollowerLifecycle.acceptedStartCoordinate M) ≠
              record.input.time.val + 1 := by
          have h := hgridAtRecord
          omega
        have hnotmissed : record.input.time.val + 1 ≤
            FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by omega
        have hstampRecord : token.timestamp.val + 1 = record.input.time.val := by
          rw [htimeRecord]
          exact hstamp
        have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch
          rate.eta record.input.time state memory hu hdomain M hM hstarted
          hnotmissed token hread hstampRecord
        simpa [hgridNe, hbitFalse] using hbranch
    obtain ⟨hchoiceState, hchoiceMemory⟩ :=
      prepared_state_eq_of_unchanged_start rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        state memory hstart choice choiceMemory hprepared
    refine ⟨state, memory, ?_, hcellChoice.1.trans hchoiceState,
      hcellChoice.2.trans hchoiceMemory⟩
    exact hstate

  by_cases hb0 : b = 0
  · subst b
    refine ⟨hprefixBound 0 (Nat.zero_le _), seed.followers i, seed.memory i, ?_, ?_, ?_⟩
    · rw [ReferenceActivePhysicalHorizon.run_zero_final]
      exact hseedConfiguration
    · intro _
      exact ⟨rfl, rfl, seed.lastDown_none i, seed.unoccupied i,
        seed.S_zero i, seed.delta_zero i, seed.backlog_zero i, rfl⟩
    · intro hpos
      omega
  · have hbpos : 0 < b := by omega
    have hbW : b ≤ W.length := by simpa only [W] using hb
    obtain ⟨hprefixB, hstatesB⟩ := hsafe.1 b hb
    obtain ⟨sb, mb, hstateB, hdomainB, hmassB, _, _, hzeroB, hoccupiedB⟩ := hstatesB i
    refine ⟨hprefixB, sb, mb, hstateB, ?_, ?_⟩
    · intro hbEq
      omega
    · intro _
      have hWpositive : 0 < W.length := lt_of_lt_of_le hbpos hb
      let k0 : Fin W.length := ⟨0, by omega⟩
      let P0 := (cell k0).selected.view.payload
      let a := P0.assignment.assigned i
      let M0 := P0.downRecord i
      let arrivals := fun v => (cells.take v).map (fun c =>
        (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
      let replay := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals v)
      refine ⟨k0, rfl, (show _ ∧ _ from ?_)⟩
      by_cases huB : sb.status = .unoccupied
      · refine ⟨?_, ?_⟩
        · intro hocc
          exact (hocc huB).elim
        · intro _
          obtain ⟨hnone, hS, hdelta, hbacklog⟩ := hzeroB huB
          have hnoB := hnoPrefix b hb sb mb hstateB hzeroB huB
          have hbuffer := hbufferAt b hb sb mb hstateB huB hnoB
          have hrunBtake := hrunPrefix b hb
          have hbuffer' : sb.buffer = (seed.followers i).buffer ++
              (E.records.take b).flatMap (ReferenceFollowerBufferProvenance.logEmission i) := by
            rw [hrunBtake] at hbuffer
            exact hbuffer
          let jLast : Fin W.length := ⟨b - 1, by omega⟩
          have hnoLast : ∀ record ∈ E.records.take jLast.val,
              ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
            intro record hrecord
            apply hnoB record
            rw [hrunBtake]
            exact List.take_subset_take_left E.records
              (by simpa only [jLast] using (Nat.sub_le b 1)) hrecord
          have halign := ReferenceFirstLiveDownNumericalRecovery.actual_pre_down_alignment
            rate source rewards C_star C_h hc count hspan i jLast hnoLast
          have hbc : b ≤ count := by omega
          have hleftLength :
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i b M0 b).length = b := by
            simp [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
              hcount, Nat.min_eq_left hbc]
          have hcellsLength : cells.length = W.length := by
            simpa only [cells, W] using
              ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                rate source rewards C_star C_h hc count hspan
          have hrightLength : (arrivals b).length = b := by
            calc
              (arrivals b).length = min b cells.length := by simp [arrivals]
              _ = b := by rw [hcellsLength]; exact Nat.min_eq_left hbW
          have hlist : ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i b M0 b = arrivals b := by
            apply List.ext_getElem
            · rw [hleftLength, hrightLength]
            · intro n hleft hright
              have hn : n < b := by simpa only [hleftLength] using hleft
              let k : Fin W.length := ⟨n, by omega⟩
              have hkLast : k.val ≤ jLast.val := by
                dsimp [k, jLast]
                omega
              have hpre := halign k hkLast
              have hmessageK : M0 = (cell k).selected.view.payload.downRecord i := by
                have hp := actual_live_payload_stable rate source rewards C_star C_h hc
                  count hspan k0 k
                exact congrArg (fun payload => payload.downRecord i) hp
              have hmessageLists :
                  ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                      E.records i b M0 b =
                    ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i b
                      ((cell k).selected.view.payload.downRecord i) b := by
                rw [hmessageK]
              have hpayloadLength :
                  (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i b
                    ((cell k).selected.view.payload.downRecord i) b).length = b := by
                calc
                  _ = (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                      E.records i b M0 b).length := (congrArg List.length hmessageLists).symm
                  _ = b := hleftLength
              have hpayloadBound : n <
                  (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i b
                    ((cell k).selected.view.payload.downRecord i) b).length := by
                simpa only [hpayloadLength] using hn
              have hUraw := ReferenceFirstLiveUnoccupiedEmission.actual_firstReplyQueueRecords_before_down
                rate source rewards C_star C_h hc count hspan k i hpre.2.1 b b
                (by simp only [k]; omega) (by simp only [k]; omega)
              have hU :
                  (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i b
                    ((cell k).selected.view.payload.downRecord i) b)[n]'hpayloadBound =
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cell k).input
                      ((cell k).selected.view.payload.assignment.assigned i)) := by
                simpa [k, E, cell,
                  ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
                  initial, start, seed] using hUraw
              have hcellGet : cells[n]'(by
                  rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
                  exact k.isLt) = (cell k).input := by
                simpa only [cells] using
                  ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
                    rate source rewards C_star C_h hc count hspan k
              have hArrival : (arrivals b)[n]'hright =
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                    (cell k).input ((cell k).selected.view.payload.assignment.assigned i)) := by
                simp only [arrivals, List.getElem_map, List.getElem_take]
                rw [hcellGet]
                rw [(cell k).enabled]
                have hArm0K : a =
                    (cell k).selected.view.payload.assignment.assigned i := by
                  exact congrArg (fun payload => payload.assignment.assigned i)
                    (actual_live_payload_stable rate source rewards C_star C_h hc count hspan
                      k0 k)
                rw [← hArm0K]
              have hlistGet := congrArg (fun xs : List (Bool × ℕ) => xs[n]?) hmessageLists
              rw [List.getElem?_eq_getElem hleft,
                List.getElem?_eq_getElem hpayloadBound] at hlistGet
              have hindexEq := Option.some.inj hlistGet
              calc
                _ = (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i b
                    ((cell k).selected.view.payload.downRecord i) b)[n]'hpayloadBound := hindexEq
                _ = (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cell k).input
                      ((cell k).selected.view.payload.assignment.assigned i)) := hU
                _ = (arrivals b)[n]'hright := hArrival.symm
          exact ⟨hnone, hS, hdelta, hbacklog, hbuffer', hlist⟩
      · obtain ⟨_, Mfinal, tokenFinal, hlastB, hMsigmaB, _, _, _⟩ := hoccupiedB huB
        have hstartFinal : ReferencePrelaunchFollower.acceptedStart sb = start + 1 := by
          simp [ReferencePrelaunchFollower.acceptedStart, hlastB, hMsigmaB]
        have hstartSeed : ReferencePrelaunchFollower.acceptedStart (seed.followers i) = 0 :=
          seed.acceptedStart_zero i
        have hstartsDifferent :
            ReferencePrelaunchFollower.acceptedStart (seed.followers i) ≠
              ReferencePrelaunchFollower.acceptedStart sb := by
          rw [hstartSeed, hstartFinal]
          omega
        have hchron := ReferenceFollowerReplyChronology.run_prefix_final_chronology
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start b hprefixB seed.activeAtStart 0 (Nat.zero_le _) i
          (seed.followers i) sb (seed.memory i) mb
          (by rw [ReferenceActivePhysicalHorizon.run_zero_final]; exact hseedConfiguration)
          hstateB
        obtain ⟨record, hrecord, sigma, happly, _, _⟩ := hchron.2.2 hstartsDifferent
        have hrunBtake := hrunPrefix b hb
        have hrunBprefix :
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
              hprefixB seed.activeAtStart).records.IsPrefix E.records := by
          rw [hrunBtake]
          exact List.take_prefix b E.records
        obtain ⟨n, hn, hrecordAt⟩ := List.getElem_of_mem hrecord
        have hnfull : n < (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
            hprefixB seed.activeAtStart).records.length := hn
        have hrunBcount :
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
              hprefixB seed.activeAtStart).records.length = b :=
          ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
            hprefixB seed.activeAtStart
        have hnlt : n < b := by simpa only [hrunBcount] using hn
        let j : Fin W.length := ⟨n, by omega⟩
        have hrecordRunToWindow :
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
              hprefixB seed.activeAtStart).records[n] = W[n] := by
          calc
            _ = E.records[n] := hrunBprefix.getElem hn
            _ = W[n] := (hwindowPrefix.getElem (by omega : n < W.length)).symm
        have hwindowRecord : W[j.val] = record := by
          exact hrecordRunToWindow.symm.trans hrecordAt
        rcases happly with ⟨logged, cut, after, raw, message, scan, registers,
            lastService, hlogged, hdown, houtcome, _⟩
        have hretained' : ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i message := by
          rw [← hwindowRecord] at hlogged hdown
          exact ⟨logged, cut, after, raw, scan, registers, lastService,
            hlogged, hdown, houtcome⟩
        have hD := ReferenceFirstLiveDownNumericalRecovery.actual_first_live_down_numerical_recovery
          rate source rewards C_star C_h hc count hspan i j message hretained'
        dsimp only at hD
        rcases hD with ⟨hDmessage, hDsigma, hDMsigma, hDq, hDalign, hDno,
          hDlists, hDVzero, loggedD, cutD, afterD, rawD, scanD, registersD,
          lastServiceD, nextD, nextMemoryD, hloggedD, hdownD, houtcomeD,
          hendpointD, hendpointSubD, hrecoveryD, hcheckedD, hregistersD,
          hlastD, hdomainsD, hafterD, hnextD, hfailureD, hreleaseD,
          hnextLastD, hnextSD, hnextDeltaD, hnextBacklogD, hnextPendingD,
          hnextBufferD, hnextBatchD, hnextFailureD⟩
        have hpayload0j := actual_live_payload_stable rate source rewards C_star C_h hc
          count hspan k0 j
        have harm0j : P0.assignment.assigned i =
            (cell j).selected.view.payload.assignment.assigned i :=
          congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
            payload.assignment.assigned i) hpayload0j
        have harm0jArm : a = (cell j).selected.view.payload.assignment.assigned i := by
          simpa only [a, P0] using harm0j
        have hmessageM0 : message = M0 := by
          calc
            message = (cell j).selected.view.payload.downRecord i := hDmessage
            _ = P0.downRecord i := by
              exact congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
                payload.downRecord i) hpayload0j.symm
            _ = M0 := rfl
        have hDReplayAt (v : ℕ) :
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
              rate source rewards C_star C_h hc count hspan |>.take v).map (fun c =>
                (c.enabled, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                  ((cell j).selected.view.payload.assignment.assigned i))) = arrivals v := by
          change (cells.take v).map (fun c =>
              (c.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                ((cell j).selected.view.payload.assignment.assigned i))) =
            (cells.take v).map (fun c =>
              (c.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
          rw [← harm0jArm]
        have hReplayRoot (v : ℕ) :
            QueueReplay.replay (4 * rate.n) (0, 0)
                ((cells.take v).map (fun c =>
                  (c.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                    ((cell j).selected.view.payload.assignment.assigned i)))) = replay v := by
          dsimp only [replay, arrivals]
          rw [hDReplayAt v]
        have hregistersRoot : registersD = replay (j.val + 1) := by
          calc
            registersD = QueueReplay.replay (4 * rate.n) (0, 0)
                ((cells.take (j.val + 1)).map (fun c =>
                  (c.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                    ((cell j).selected.view.payload.assignment.assigned i)))) := hregistersD
            _ = replay (j.val + 1) := hReplayRoot (j.val + 1)
        have hbaseDelta : nextD.delta =
            (replay (j.val + 1)).1 - (replay j.val).1 := by
          rw [hnextDeltaD]
          calc
            lastServiceD =
                (QueueReplay.replay (4 * rate.n) (0, 0)
                  ((cells.take (j.val + 1)).map (fun c =>
                    (c.enabled, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                        ((cell j).selected.view.payload.assignment.assigned i))))).1 -
                (QueueReplay.replay (4 * rate.n) (0, 0)
                  ((cells.take j.val).map (fun c =>
                    (c.enabled, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                        ((cell j).selected.view.payload.assignment.assigned i))))).1 := hlastD
            _ = (replay (j.val + 1)).1 - (replay j.val).1 := by
              rw [hReplayRoot (j.val + 1), hReplayRoot j.val]
        have hjNext : j.val + 1 ≤ W.length := Nat.succ_le_of_lt j.isLt
        obtain ⟨hstepJ, hactualJ, _⟩ :=
          ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
            initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards start count hspan seed.activeAtStart j
        have hbaseState :
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
              (j.val + 1) (hprefixBound (j.val + 1) hjNext) seed.activeAtStart).finalState.followers i =
              .ordinary nextD nextMemoryD := by
          rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
          have hnextConfig : W[j.val].output.next.followers i = .ordinary nextD nextMemoryD := by
            have hframe : W[j.val].output.next.followers i =
                (W[j.val].output.followers i).configuration := by
              rw [W[j.val].output_eq]
              rfl
            rw [hframe]
            exact hnextD
          have hactualConfig := congrArg
            (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              r.output.next.followers i) hactualJ
          exact hactualConfig.symm.trans hnextConfig
        have hbaseReplay : (nextD.S, nextD.backlog) = replay (j.val + 1) := by
          rw [hnextSD, hnextBacklogD, hregistersRoot]
        have hbaseOcc : nextD.status ≠ .unoccupied := by
          rw [hnextPendingD]
          decide
        have hbaseDomain :
            nextD.S ≤ p.T * D p ∧ nextD.delta ≤ D p ∧ nextD.backlog ≤ p.T * D p := by
          have hdomain' := (ActiveFollowerDownAcceptance.checkedRecovery_success
            p rate message loggedD scanD.endpoint ⟨registersD, lastServiceD⟩ hcheckedD).1
          change ActiveFollowerDownAcceptance.replay_register_domain
            (D p) (p.T * D p) ⟨registersD, lastServiceD⟩ at hdomain'
          rcases hdomain' with ⟨hS, hdelta, hbacklog⟩
          exact ⟨by simpa [hnextSD] using hS, by simpa [hnextDeltaD] using hdelta,
            by simpa [hnextBacklogD] using hbacklog⟩
        have hmassBase : nextD.S + nextD.backlog ≤ (j.val + 1) * D p := by
          obtain ⟨_, hstates⟩ := hsafe.1 (j.val + 1) hjNext
          obtain ⟨stateJ, memoryJ, hstateJ, _, hmassJ, _, _, _, _⟩ := hstates i
          have heq : stateJ = nextD ∧ memoryJ = nextMemoryD := by
            have hsame := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hstateJ.symm.trans hbaseState))
            exact hsame
          rcases heq with ⟨rfl, rfl⟩
          exact hmassJ
        have hnextLastRoot : nextD.lastDown = some M0 := by
          simpa only [hmessageM0] using hnextLastD
        have hwalk : ∀ d, (hd : j.val + 1 + d ≤ b) →
            ∃ state memory,
              (ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                (j.val + 1 + d) (hprefixBound (j.val + 1 + d) (hd.trans hb))
                seed.activeAtStart).finalState.followers i = .ordinary state memory ∧
              state.lastDown = some M0 ∧ state.status ≠ .unoccupied ∧
              (state.S, state.backlog) = replay (j.val + 1 + d) ∧
              state.delta = (replay (j.val + 1 + d)).1 -
                (replay (j.val + d)).1 ∧
              state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧
              state.backlog ≤ p.T * D p ∧
              state.S + state.backlog ≤ (j.val + 1 + d) * D p := by
          intro d
          induction d with
          | zero =>
              intro _
              refine ⟨nextD, nextMemoryD, hbaseState, hnextLastRoot, hbaseOcc,
                hbaseReplay, hbaseDelta, hbaseDomain.1, hbaseDomain.2.1,
                hbaseDomain.2.2, hmassBase⟩
          | succ d ih =>
              intro hbound
              have hprevBound : j.val + 1 + d ≤ b := by omega
              obtain ⟨current, currentMemory, hcurrent, hcurrentLast, hcurrentOcc,
                hcurrentReplay, hcurrentDelta, hcurrentSbound, hcurrentDeltabound,
                hcurrentBacklogbound, hcurrentMass⟩ := ih hprevBound
              let n := j.val + 1 + d
              have hnW : n < W.length := by dsimp [n]; omega
              let k : Fin W.length := ⟨n, hnW⟩
              obtain ⟨pre, preMemory, hboundary, hcellState, hcellMemory⟩ := hcellBoundary k
              have hsameBoundary : pre = current ∧ preMemory = currentMemory := by
                have hconfig := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  (hboundary.symm.trans hcurrent))
                exact hconfig
              have hpreOcc : pre.status ≠ .unoccupied := by
                rw [hsameBoundary.1]
                exact hcurrentOcc
              have hpreOccCell : ((cell k).states i).status ≠ .unoccupied := by
                rw [hcellState]
                exact hpreOcc
              have hpayloadK0 := actual_live_payload_stable rate source rewards C_star C_h hc
                count hspan k0 k
              have hmessageK :
                  (cell k).selected.view.payload.downRecord i = M0 :=
                (congrArg (fun payload => payload.downRecord i) hpayloadK0).symm
              have hArmK0 :
                  (cell k).selected.view.payload.assignment.assigned i = a :=
                (congrArg (fun payload => payload.assignment.assigned i) hpayloadK0).symm
              have hservice := ReferenceFirstLiveOccupiedService.actual_occupied_follower_numerical_service
                rate source rewards C_star C_h hc count hspan k i hpreOccCell
              dsimp only at hservice
              rcases hservice with ⟨serviced, next, nextMemory, hchecked, hpreparedFollower,
                hpreparedRow, hpreparedActivation, hpreparedTime, hpreDown, harrival,
                hserviceAmount, hserviceOutput, hrecordResult, hnextConfig, hfailure,
                hdownInput, hdown, hnextS, hnextDelta, hnextBacklog, htransition,
                hnextLast, hnextBuffer, hnextBatch, harrivalBound, hserviceBound,
                hnextSBound, hnextDeltaBound, hnextBacklogBound⟩
              have hnextLastRoot : next.lastDown = some M0 := by
                rw [hcellState] at hnextLast
                calc
                  next.lastDown = pre.lastDown := hnextLast
                  _ = current.lastDown := by rw [hsameBoundary.1]
                  _ = some M0 := hcurrentLast
              let rootArrival := RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cell k).input a
              have hpreRegisters : (pre.S, pre.backlog) = replay n := by
                calc
                  (pre.S, pre.backlog) = (current.S, current.backlog) := by
                    rw [hsameBoundary.1]
                  _ = replay n := by simpa only [n] using hcurrentReplay
              have htransitionPre := htransition
              rw [hcellState] at htransitionPre
              have htransitionRoot : (next.S, next.backlog) =
                  QueueReplay.transition (4 * rate.n) (replay n) (true, rootArrival) := by
                calc
                  (next.S, next.backlog) =
                      QueueReplay.transition (4 * rate.n) (pre.S, pre.backlog)
                        (true, RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          (cell k).input
                          ((cell k).selected.view.payload.assignment.assigned i)) := htransitionPre
                  _ = QueueReplay.transition (4 * rate.n) (replay n) (true, rootArrival) := by
                    rw [hpreRegisters, hArmK0]
              have hcellsLength : cells.length = W.length := by
                simpa only [cells, W] using
                  ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                    rate source rewards C_star C_h hc count hspan
              have hnCells : n < cells.length := by rw [hcellsLength]; exact hnW
              have htakeCells : cells.take (n + 1) = cells.take n ++ [cells[n]'hnCells] := by
                exact (List.take_append_getElem hnCells).symm
              have hcellGet : cells[n]'hnCells = (cell k).input := by
                simpa only [cells] using
                  ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
                    rate source rewards C_star C_h hc count hspan k
              have harrivalList : arrivals (n + 1) = arrivals n ++ [(true, rootArrival)] := by
                dsimp only [arrivals]
                rw [htakeCells, List.map_append]
                simp only [List.map_singleton]
                rw [hcellGet, (cell k).enabled]
              have hreplayStep : replay (n + 1) =
                  QueueReplay.transition (4 * rate.n) (replay n) (true, rootArrival) := by
                dsimp only [replay]
                rw [harrivalList, QueueReplay.replay_append]
                simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil]
              have hnextReplay : (next.S, next.backlog) = replay (n + 1) := by
                calc
                  (next.S, next.backlog) =
                      QueueReplay.transition (4 * rate.n) (replay n) (true, rootArrival) :=
                        htransitionRoot
                  _ = replay (n + 1) := hreplayStep.symm
              have hbackCell : ((cell k).states i).backlog = pre.backlog :=
                congrArg (fun state : ReferencePrelaunchFollower.State p rate.eta =>
                  state.backlog) hcellState
              have hserviceRoot :
                  min (4 * rate.n) ((replay n).2 + rootArrival) = serviced.service := by
                have hserviceAmountRoot : serviced.service =
                    min (4 * rate.n) (pre.backlog + rootArrival) := by
                  calc
                    serviced.service = min (4 * rate.n)
                        (((cell k).states i).backlog +
                          RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            (cell k).input
                            ((cell k).selected.view.payload.assignment.assigned i)) := hserviceAmount
                    _ = min (4 * rate.n) (pre.backlog + rootArrival) := by
                      rw [hbackCell, hArmK0]
                have hback : (replay n).2 = pre.backlog := by
                  exact congrArg Prod.snd hpreRegisters |>.symm
                rw [hback]
                exact hserviceAmountRoot.symm
              have hscoreStep : (replay (n + 1)).1 = (replay n).1 + serviced.service := by
                rw [hreplayStep]
                simp only [QueueReplay.transition, Bool.and_eq_true, decide_true,
                  ite_true, Prod.fst]
                rw [hserviceRoot]
              have hpreBacklog : pre.backlog = (replay n).2 :=
                congrArg Prod.snd hpreRegisters
              have hnextDeltaService : next.delta = serviced.service := by
                calc
                  next.delta = min (4 * rate.n)
                      (((cell k).states i).backlog +
                        RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          (cell k).input
                          ((cell k).selected.view.payload.assignment.assigned i)) := hnextDelta
                  _ = min (4 * rate.n) ((replay n).2 + rootArrival) := by
                    rw [hbackCell, hpreBacklog, hArmK0]
                  _ = serviced.service := hserviceRoot
              have hdeltaNext : next.delta = (replay (n + 1)).1 - (replay n).1 := by
                rw [hnextDeltaService, hscoreStep]
                omega
              have hnextBoundary :
                  (ReferenceActivePhysicalHorizon.run initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                    (n + 1) (hprefixBound (n + 1) (by omega)) seed.activeAtStart).finalState.followers i =
                    .ordinary next nextMemory := by
                rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
                obtain ⟨_, hactualK, _⟩ :=
                  ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
                    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards start count hspan seed.activeAtStart k
                have hframe : W[k.val].output.next.followers i =
                    (W[k.val].output.followers i).configuration := by
                  rw [W[k.val].output_eq]
                  rfl
                have hnextOutput : W[k.val].output.next.followers i = .ordinary next nextMemory := by
                  rw [hframe]
                  exact hnextConfig
                have hactualNext := congrArg
                  (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
                    r.output.next.followers i) hactualK
                exact hactualNext.symm.trans hnextOutput
              have hnNextW : n + 1 ≤ W.length := Nat.succ_le_of_lt hnW
              have hsafeNextBound : n + 1 ≤
                  (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                    (ReferenceActivePhysicalHorizon.run initial source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                      count hspan seed.activeAtStart).records).length := by
                simpa only [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
                  ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hnNextW
              have hmassNext : next.S + next.backlog ≤ (n + 1) * D p := by
                obtain ⟨_, statesNext⟩ := hsafe.1 (n + 1) hsafeNextBound
                obtain ⟨stateNext, memoryNext, hstateNext, _, hmass, _, _, _, _⟩ := statesNext i
                have heq : stateNext = next ∧ memoryNext = nextMemory := by
                  exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                    (hstateNext.symm.trans hnextBoundary)
                rcases heq with ⟨rfl, rfl⟩
                exact hmass
              have hnextOcc : next.status ≠ .unoccupied := by
                obtain ⟨_, statesNext⟩ := hsafe.1 (n + 1) hsafeNextBound
                obtain ⟨stateNext, memoryNext, hstateNext, _, _, _, _, hzeroNext, _⟩ := statesNext i
                have heq : stateNext = next ∧ memoryNext = nextMemory := by
                  exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                    (hstateNext.symm.trans hnextBoundary)
                intro hu
                have hnone := (hzeroNext (by simpa only [heq.1] using hu)).1
                have hnoneNext : next.lastDown = none := by simpa only [heq.1] using hnone
                rw [hnextLastRoot] at hnoneNext
                cases hnoneNext
              have hnextIndex : j.val + 1 + (d + 1) = n + 1 := by
                dsimp [n]
                omega
              refine ⟨next, nextMemory, ?_, hnextLastRoot, hnextOcc, ?_, ?_,
                hnextSBound, hnextDeltaBound, hnextBacklogBound, ?_⟩
              · simpa only [hnextIndex] using hnextBoundary
              · simpa only [hnextIndex] using hnextReplay
              · have hprevIndex : j.val + (d + 1) = n := by
                  dsimp [n]
                  omega
                simpa only [hnextIndex, hprevIndex] using hdeltaNext
              · rw [hnextIndex]
                simpa only [hnextIndex] using hmassNext
        let d := b - (j.val + 1)
        have hjSuccLeB : j.val + 1 ≤ b := by
          have hjltB : j.val < b := by simpa only [j] using hnlt
          omega
        have hdIdentity : j.val + 1 + d = b := by
          dsimp [d]
          omega
        have hdPrevIdentity : j.val + d = b - 1 := by
          dsimp [d]
          omega
        have hdBound : j.val + 1 + d ≤ b := by omega
        obtain ⟨stateB, memoryB, hwalkState, hwalkLast, hwalkOcc, hwalkReplay,
            hwalkDelta, hwalkSbound, hwalkDeltabound, hwalkBacklogbound, _⟩ := hwalk d hdBound
        have heqB : stateB = sb ∧ memoryB = mb := by
          have hconfig :
              (ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start b
                (hprefixBound b hb) seed.activeAtStart).finalState.followers i =
                .ordinary stateB memoryB := by
            simpa only [hdIdentity] using hwalkState
          exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hconfig.symm.trans hstateB)
        constructor
        · intro _
          exact ⟨by simpa only [heqB.1] using hwalkLast,
            by simpa only [heqB.1, hdIdentity] using hwalkReplay,
            by simpa only [heqB.1, hdIdentity, hdPrevIdentity] using hwalkDelta,
            by simpa only [heqB.1] using hwalkSbound,
            by simpa only [heqB.1] using hwalkDeltabound,
            by simpa only [heqB.1] using hwalkBacklogbound,
            by simpa only [heqB.1] using hmassB,
            j, by simpa only [j] using hnlt,
            (by simpa only [hmessageM0] using hretained')⟩
        · intro hu
          exact (huB hu).elim

end Bandits.Support.ReferenceFirstLiveFollowerQueueReplay

end
