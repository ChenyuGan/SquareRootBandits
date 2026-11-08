/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project
-/
module

public import Bandits.Support.ReferenceFirstLiveOccupiedArrivals

/-!
# Actual occupied-follower numerical service in the first live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-124,354-396`,
`sources/zip4/manuscript/06_interruptions.tex:246-297,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module follows the same actual first-live record and numerical cell as
the occupied-arrival result. It proves that the physical occupied service
call succeeds, uses that cell's quantized arrival, and preserves the source
queue and logging fields across the actual release and end-of-round operations.
Pending and released followers are both covered, including zero arrivals.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceFirstLiveFollowerSafety
open Bandits.Support.ReferenceFirstLiveOccupiedArrivals
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RecordedQueueRun
open Bandits.Support.QueueReplay
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec

namespace Bandits.Support.ReferenceFirstLiveOccupiedService

variable {p : ConstructorDimensions.Parameters}

private theorem finishFollower_ordinary_inv
    {rate : ReferenceFirstWindowNumericalStream.RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary choice choiceMemory)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
        observation choice choiceMemory post = .ok (next, nextMemory) := by
  classical
  unfold ReferenceActivePhysicalStep.finishFollower at hout
  rw [hconfiguration] at hout
  cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure =>
      simp only [hrecord] at hout
      cases hout
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation choice choiceMemory post with
      | error failure =>
          simp only [hrecord, hfinish] at hout
          cases hout
      | ok result =>
          rcases result with ⟨final, finalMemory⟩
          simp only [hrecord, hfinish] at hout
          injection hout with hstate hmemory
          subst final
          subst finalMemory
          exact ⟨post, rfl, hfinish⟩

private theorem finishFollower_occupied_noDown
    {rate : ReferenceFirstWindowNumericalStream.RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = none ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = none := by
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration,
    ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem releaseAfterService_success_frames
    {eta : LearningRate} (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (preChoice postService out : ReferencePrelaunchFollower.State p eta)
    (hout : ActiveFollowerLifecycle.releaseAfterService eta i t row own preChoice postService =
      .ok out) :
    out.lastDown = postService.lastDown ∧
    out.S = postService.S ∧
    out.delta = postService.delta ∧
    out.backlog = postService.backlog ∧
    out.downBatch = postService.downBatch ∧
    out.buffer = postService.buffer := by
  classical
  by_cases hpending : preChoice.status = .pending
  · by_cases hpreRegs : ActiveFollowerLifecycle.localStateDomainValid preChoice
    · cases hrecord : preChoice.lastDown with
      | none =>
          rw [ActiveFollowerLifecycle.releaseAfterService_missing_record eta i t row own
            preChoice postService hpending hpreRegs hrecord] at hout
          cases hout
      | some M =>
        by_cases htime : M.val.sigma ≤ t.val
        · by_cases hpostRegs : ActiveFollowerLifecycle.localStateDomainValid postService
          · let released := if ActiveFollowerLifecycle.releaseCondition eta i row own M then
                { postService with status := .released } else postService
            by_cases houtput : released.status = .unoccupied ∨
                (∃ M', released.lastDown = some M' ∧ M'.val.sigma ≤ t.val + 1)
            · have hout' :
                  (Except.ok released : ActiveFollowerLifecycle.LifecycleCheck
                    (ReferencePrelaunchFollower.State p eta)) = .ok out := by
                simpa [ActiveFollowerLifecycle.releaseAfterService, hpending, hpreRegs,
                  hrecord, htime, hpostRegs, houtput, released] using hout
              have heq : released = out := Except.ok.inj hout'
              subst out
              by_cases htest : ActiveFollowerLifecycle.releaseCondition eta i row own M
              · simp [released, htest]
              · simp [released, htest]
            · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpreRegs,
                hrecord, htime, hpostRegs, houtput, released] at hout
          · simp [ActiveFollowerLifecycle.releaseAfterService, hpending, hpreRegs,
              hrecord, htime, hpostRegs] at hout
        · have hlate : t.val < M.val.sigma := Nat.lt_of_not_ge htime
          rw [ActiveFollowerLifecycle.releaseAfterService_incompatible_start eta i t row own
            preChoice postService hpending hpreRegs M hrecord hlate] at hout
          cases hout
    · rw [ActiveFollowerLifecycle.releaseAfterService_invalid_pre_domain eta i t row own
        preChoice postService hpending hpreRegs] at hout
      cases hout
  · rw [ActiveFollowerLifecycle.releaseAfterService_not_pending eta i t row own
      preChoice postService hpending] at hout
    have heq : postService = out := Except.ok.inj hout
    subst out
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual occupied service in the actual first-live window. The sole local
branch premise is the existing cell's occupied status; the original rate,
whole source, whole reward table, initialization witnesses and finite run are
retained. The checked service is the one used by the physical record, and the
returned numerical fields persist through release and `finishRound`.
-/
theorem actual_occupied_follower_numerical_service
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
    let prepared := record.output.preparation.followers.followers i
    let pre := cell.states i
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
    let own := record.output.ownEntries player
    let arrival := RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
      (payload.assignment.assigned i)
    let service := min (4 * rate.n) (pre.backlog + arrival)
    ∃ (serviced : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n
        prepared.follower prepared.row prepared.activation prepared.time own.2 pre)
      (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        prepared.follower prepared.row prepared.activation prepared.time own.2 pre =
          .success serviced ∧
      prepared.follower = i ∧ prepared.row = record.input.row ∧
      prepared.activation = record.input.state.activations i ∧
      prepared.time = record.input.time ∧
      pre.lastDown = some (payload.downRecord i) ∧
      serviced.arrival = arrival ∧
      serviced.service = service ∧
      serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival ∧
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm own.2 pre).result =
          .ok serviced.output ∧
      (record.output.followers i).configuration = .ordinary next nextMemory ∧
      (record.output.followers i).failure = none ∧
      (record.output.followers i).downInput = none ∧
      (record.output.followers i).down = none ∧
      next.S = pre.S + service ∧
      next.delta = service ∧
      next.backlog = pre.backlog + arrival - service ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        (pre.S, pre.backlog) (true, arrival) ∧
      next.lastDown = pre.lastDown ∧
      next.buffer = pre.buffer ∧
      next.downBatch = pre.downBatch ∧
      serviced.arrival ≤ D p ∧ serviced.service ≤ D p ∧
      next.S ≤ p.T * D p ∧ next.delta ≤ D p ∧ next.backlog ≤ p.T * D p := by
  classical
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  let payload := cell.selected.view.payload
  let preparedRound := record.output.preparation
  let prepared := preparedRound.followers.followers i
  let pre := cell.states i
  let mu := cell.memories i
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let own := record.output.ownEntries player
  let arrival := RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
    (payload.assignment.assigned i)
  let service := min (4 * rate.n) (pre.backlog + arrival)

  have hroot := ReferenceFirstLiveOccupiedArrivals.actual_occupied_follower_arrival
    rate source rewards C_star C_h hc count hspan k i hoccupied
  rcases hroot with ⟨hlastRoot, _, _, _, _, _, _, _, _, hrawArrival⟩

  have hsafety := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst seed.followers
    seed.memory seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero
    seed.lastDown_none seed.unoccupied seed.bufferValid seed.chronologicalBuffer
    seed.bufferStamps seed.decoderValid
  obtain ⟨choice, _choiceMemory, next, nextMemory, hchoice, hnext, hfailure, hselected⟩ :=
    hsafety.2 k i
  have hchoiceState : choice = pre :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (cell.ordinary i))).1
  have hchoiceOccupied : choice.status ≠ .unoccupied := by
    rw [hchoiceState]
    exact hoccupied
  have hpreOccupied : pre.status ≠ .unoccupied := by
    rw [← hchoiceState]
    exact hchoiceOccupied
  have hlastChoice : choice.lastDown = some (payload.downRecord i) :=
    hselected cell.selected cell.selection_actual hchoiceOccupied
  have hlastPre : pre.lastDown = some (payload.downRecord i) := by
    rw [← hchoiceState]
    exact hlastChoice
  have hpreDown : pre.lastDown = some (payload.downRecord i) := by
    simpa only [pre, cell, payload] using hlastRoot

  have hownPrepared : own = preparedRound.feedback.ownEntries player := by
    dsimp only [own, record, preparedRound]
    rw [record.output_eq]
    rfl
  have hownObservation : own.2 = preparedRound.feedback.observations player := by
    rw [hownPrepared]
    exact congrArg Prod.snd (preparedRound.feedback.ownEntries_eq player)
  have hfeedbackFollower :
      record.output.followers i =
        ReferenceActivePhysicalStep.finishFollower preparedRound.coordinator.downView
          prepared (preparedRound.feedback.observations player) := by
    dsimp only [record, preparedRound, prepared]
    rw [record.output_eq]
    rfl
  have hfinishOrdinary :
      (ReferenceActivePhysicalStep.finishFollower preparedRound.coordinator.downView
        prepared (preparedRound.feedback.observations player)).configuration =
        .ordinary next nextMemory := by
    rw [← hfeedbackFollower]
    exact hnext
  have hpreparedConfiguration : prepared.configuration = .ordinary pre mu := cell.ordinary i
  obtain ⟨post, hrecordStage, hreleaseFinish⟩ := finishFollower_ordinary_inv
    preparedRound.coordinator.downView prepared (preparedRound.feedback.observations player)
    pre mu next nextMemory hpreparedConfiguration hfinishOrdinary

  have halign := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    preparedRound i
  have hoccupiedStage :
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm
        own.2 pre = .ok post := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hpreOccupied,
      hownObservation] using
      hrecordStage
  have hserviceEquation := DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
    rate prepared.follower prepared.row prepared.activation prepared.time prepared.active
    prepared.arm own.2 pre hpreOccupied
  rw [hserviceEquation] at hoccupiedStage
  cases hserviceCall : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale prepared.follower prepared.row prepared.activation
      prepared.time own.2 pre with
  | failure =>
      simp only [hserviceCall] at hoccupiedStage
      cases hoccupiedStage
  | success serviced =>
      simp only [hserviceCall] at hoccupiedStage
      have hpost : post = serviced.output := (Except.ok.inj hoccupiedStage).symm
      have hserviceActual :
          ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
            prepared.follower prepared.row prepared.activation prepared.time own.2 pre =
            .success serviced := hserviceCall
      have hrecordFollower :
          (ReferenceActivePhysicalStep.recordFollower
            preparedRound.coordinator.downView prepared.follower prepared.row
            prepared.activation prepared.time prepared.active prepared.arm own.2 pre).result =
            .ok serviced.output := by
        simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hpreOccupied]
        rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
          rate prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm own.2 pre hpreOccupied,
          hserviceCall]

      rcases ActiveFollowerQueueOperation.serviceSuccess_equations serviced with
        ⟨hqueueUpdate, harrivalBound, hserviceBound, hscoreBound, hbacklogBound, haction⟩
      have hactionFields :
          serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
            prepared.follower prepared.row prepared.time (payload.downRecord i) own.2 ∧
          serviced.service = ActiveFollowerQueueOperation.localService rate.n
            pre.backlog serviced.arrival := by
        cases hstatus : pre.status with
        | unoccupied => exact (hpreOccupied hstatus).elim
        | pending =>
            simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
            rcases haction with ⟨_, M, hM, _, hraw, hservice⟩
            have hM' : M = payload.downRecord i := Option.some.inj (hM.symm.trans hlastPre)
            subst M
            exact ⟨hraw, hservice⟩
        | released =>
            simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
            rcases haction with ⟨_, M, hM, _, hraw, hservice⟩
            have hM' : M = payload.downRecord i := Option.some.inj (hM.symm.trans hlastPre)
            subst M
            exact ⟨hraw, hservice⟩
      have harrival : serviced.arrival = arrival := by
        calc
          serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta i
              record.input.row record.input.time (payload.downRecord i) own.2 := by
            calc
              serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
                  prepared.follower prepared.row prepared.time (payload.downRecord i) own.2 :=
                hactionFields.1
              _ = ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row
                    record.input.time (payload.downRecord i) own.2 := by
                rw [halign.2.1, halign.1, halign.2.2.1]
          _ = arrival := by
            simpa only [record, cell, payload, own, arrival] using hrawArrival
      have hserviceValue : serviced.service = service := by
        simpa only [service, ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity, Bandits.Support.CappedService.service,
          harrival] using hactionFields.2
      have hserviceOutput :
          ActiveFollowerQueueOperation.serviceOutput rate.n pre serviced.arrival =
            ActiveFollowerQueueOperation.serviceUpdate rate.n pre serviced.arrival := by
        cases hstatus : pre.status with
        | unoccupied => exact (hpreOccupied hstatus).elim
        | pending => simp [ActiveFollowerQueueOperation.serviceOutput,
            ActiveRoundActions.FollowerStatus.occupied, hstatus]
        | released => simp [ActiveFollowerQueueOperation.serviceOutput,
            ActiveRoundActions.FollowerStatus.occupied, hstatus]
      have hservicedUpdate :
          serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival := by
        calc
          serviced.output = ActiveFollowerQueueOperation.serviceOutput rate.n pre serviced.arrival :=
            hqueueUpdate
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n pre serviced.arrival := hserviceOutput
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival := by rw [harrival]

      have hreleasedFields :
          next.lastDown = post.lastDown ∧ next.S = post.S ∧ next.delta = post.delta ∧
            next.backlog = post.backlog ∧ next.downBatch = post.downBatch ∧
              next.buffer = post.buffer := by
        classical
        unfold DeclaredFollowerLocalRound.releaseAndFinish at hreleaseFinish
        cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta
            prepared.follower prepared.time
            (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
            (preparedRound.feedback.observations player) pre post with
        | error reason =>
            simp only [hrelease] at hreleaseFinish
            cases hreleaseFinish
        | ok released =>
            cases hround : ActiveFollowerLifecycle.finishRound rate.eta prepared.time prepared.row
                released mu with
            | error reason =>
                simp only [hrelease, hround] at hreleaseFinish
                cases hreleaseFinish
            | ok result =>
                simp only [hrelease, hround] at hreleaseFinish
                have hpair : result = (next, nextMemory) := Except.ok.inj hreleaseFinish
                rcases result with ⟨final, finalMemory⟩
                have hstate : final = next := congrArg Prod.fst hpair
                have hfinishFrame := ActiveFollowerLifecycle.finishRound_frame rate.eta
                  prepared.time prepared.row released final mu finalMemory hround
                have hreleaseFrames := releaseAfterService_success_frames prepared.follower
                  prepared.time
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
                  (preparedRound.feedback.observations player) pre post released hrelease
                have hnextReleased : next = released := hstate.symm.trans hfinishFrame
                rcases hreleaseFrames with ⟨hlast, hS, hdelta, hbacklog, hbatch, hbuffer⟩
                exact ⟨by simpa only [hnextReleased] using hlast,
                  by simpa only [hnextReleased] using hS,
                  by simpa only [hnextReleased] using hdelta,
                  by simpa only [hnextReleased] using hbacklog,
                  by simpa only [hnextReleased] using hbatch,
                  by simpa only [hnextReleased] using hbuffer⟩
      have hnextFields := hreleasedFields
      have hnextEqualsPost :
          next.lastDown = post.lastDown ∧ next.S = post.S ∧ next.delta = post.delta ∧
          next.backlog = post.backlog ∧ next.downBatch = post.downBatch ∧
          next.buffer = post.buffer := hnextFields
      have hserviceUpdateFrames :=
        ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers rate.n pre arrival
      have hupdateScore :
          (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).S =
            pre.S + service := by
        simp [ActiveFollowerQueueOperation.serviceUpdate,
          ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity,
          Bandits.Support.CappedService.service, service]
      have hupdateDelta :
          (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).delta = service := by
        simp [ActiveFollowerQueueOperation.serviceUpdate,
          ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity,
          Bandits.Support.CappedService.service, service]
      have hupdateBacklog :
          (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).backlog =
            pre.backlog + arrival - service := by
        simp [ActiveFollowerQueueOperation.serviceUpdate,
          ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity,
          Bandits.Support.CappedService.residual,
          Bandits.Support.CappedService.service, service]
      have hnextScore : next.S = pre.S + service := by
        calc
          next.S = post.S := hnextEqualsPost.2.1
          _ = serviced.output.S := congrArg ReferencePrelaunchFollower.State.S hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).S :=
            congrArg ReferencePrelaunchFollower.State.S hservicedUpdate
          _ = pre.S + service := hupdateScore
      have hnextDelta : next.delta = service := by
        calc
          next.delta = post.delta := hnextEqualsPost.2.2.1
          _ = serviced.output.delta := congrArg ReferencePrelaunchFollower.State.delta hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).delta :=
            congrArg ReferencePrelaunchFollower.State.delta hservicedUpdate
          _ = service := hupdateDelta
      have hnextBacklog : next.backlog = pre.backlog + arrival - service := by
        calc
          next.backlog = post.backlog := hnextEqualsPost.2.2.2.1
          _ = serviced.output.backlog := congrArg ReferencePrelaunchFollower.State.backlog hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).backlog :=
            congrArg ReferencePrelaunchFollower.State.backlog hservicedUpdate
          _ = pre.backlog + arrival - service := hupdateBacklog
      have hnextTransition :
          (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
            (pre.S, pre.backlog) (true, arrival) := by
        have hstatePair : (next.S, next.backlog) =
            ((ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).S,
              (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).backlog) := by
          apply Prod.ext
          · exact hnextScore.trans hupdateScore.symm
          · exact hnextBacklog.trans hupdateBacklog.symm
        calc
          (next.S, next.backlog) =
              ((ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).S,
                (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).backlog) := hstatePair
          _ = QueueReplay.transition (4 * rate.n) (pre.S, pre.backlog) (true, arrival) := by
            simpa only [ActiveFollowerQueueOperation.serviceCapacity] using
              ActiveFollowerQueueOperation.serviceUpdate_eq_queueTransition rate.n pre arrival
      have hnextLast : next.lastDown = pre.lastDown := by
        calc
          next.lastDown = post.lastDown := hnextEqualsPost.1
          _ = serviced.output.lastDown := congrArg ReferencePrelaunchFollower.State.lastDown hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).lastDown :=
            congrArg ReferencePrelaunchFollower.State.lastDown hservicedUpdate
          _ = pre.lastDown := hserviceUpdateFrames.1
      have hnextBuffer : next.buffer = pre.buffer := by
        calc
          next.buffer = post.buffer := hnextEqualsPost.2.2.2.2.2
          _ = serviced.output.buffer := congrArg ReferencePrelaunchFollower.State.buffer hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).buffer :=
            congrArg ReferencePrelaunchFollower.State.buffer hservicedUpdate
          _ = pre.buffer := hserviceUpdateFrames.2.2.1
      have hnextBatch : next.downBatch = pre.downBatch := by
        calc
          next.downBatch = post.downBatch := hnextEqualsPost.2.2.2.2.1
          _ = serviced.output.downBatch := congrArg ReferencePrelaunchFollower.State.downBatch hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).downBatch :=
            congrArg ReferencePrelaunchFollower.State.downBatch hservicedUpdate
          _ = pre.downBatch := hserviceUpdateFrames.2.1
      have hnextScoreBound : next.S ≤ p.T * D p := by
        calc
          next.S = serviced.output.S := by
            calc
              next.S = post.S := hnextEqualsPost.2.1
              _ = serviced.output.S := by rw [hpost]
          _ ≤ p.T * D p := hscoreBound
      have hnextDeltaBound : next.delta ≤ D p := by
        calc
          next.delta = serviced.service := hnextDelta.trans hserviceValue.symm
          _ ≤ D p := hserviceBound
      have hnextBacklogBound : next.backlog ≤ p.T * D p := by
        calc
          next.backlog = serviced.output.backlog := by
            calc
              next.backlog = post.backlog := hnextEqualsPost.2.2.2.1
              _ = serviced.output.backlog := by rw [hpost]
          _ ≤ p.T * D p := hbacklogBound
      have hdownInput : (record.output.followers i).downInput = none ∧
          (record.output.followers i).down = none := by
        rw [hfeedbackFollower]
        exact finishFollower_occupied_noDown preparedRound.coordinator.downView prepared
          (preparedRound.feedback.observations player) pre mu hpreparedConfiguration hpreOccupied
      refine ⟨serviced, next, nextMemory, rfl, halign.2.1, halign.1,
        halign.2.2.2, halign.2.2.1, hpreDown, harrival, hserviceValue, hservicedUpdate,
        hrecordFollower, hnext, hfailure, hdownInput.1, hdownInput.2,
        hnextScore, hnextDelta, hnextBacklog, hnextTransition, hnextLast, hnextBuffer,
        hnextBatch, harrivalBound, hserviceBound, hnextScoreBound, hnextDeltaBound,
        hnextBacklogBound⟩

end Bandits.Support.ReferenceFirstLiveOccupiedService

end
