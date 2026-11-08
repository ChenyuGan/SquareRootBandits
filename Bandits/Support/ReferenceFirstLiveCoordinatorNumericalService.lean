/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCoordinatorArrivals

/-!
# Actual coordinator numerical service on the first-live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

For every generated first-live record, the literal FIRST chosen branch or
continuing LIVE chosen branch performs the actual bridge recording, capped
complement service, confirmation, and clock finish. The recorded arrival is
identified with the whole numerical cell on coordinator-owned complement
arms, including the zero-arrival case. The exact finished clock, pending set,
base score, and service outputs form the actual next live coordinator storage.
This result concerns the coordinator complement only; follower service and
the common all-arm queue induction remain separate.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstWindowRecordingTruth
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCoordinatorLiveRecording
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceFirstLiveCoordinatorNumericalService

variable {p : ConstructorDimensions.Parameters}

private theorem source_arrival_zero_on_complement_of_other_source
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
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
    (hsrc : (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan)[k.val]).input.row.2
            (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
              rate source rewards C_star C_h hc count hspan)[k.val].input.time).1) ≠
        ActiveRoundActions.coordinator p.two_le_m)
    (a : FastArm (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).selected.view.payload.slowSet) :
    RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan k).input a.1 = 0 := by
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  let payload := cell.selected.view.payload
  let src := PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
    ((record.input.row.2 record.input.time).1)
  let regime : SnapshotRecordingKernel.Regime p :=
    .live payload.assignment
      { missing := cell.selected.view.pendingAtChoice
        status := fun i => (cell.states i).status }
  have hsourceScalar :
      CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            ((record.input.row.2 record.input.time).1)) = src := by
    rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate p.two_le_m p.m_lt_K]
  have hsourceMap :
      ReferenceFirstWindowNumericalStream.sourceArm record payload
        cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
        cell.selected.view.cutoff cell.choiceInputsValid ≠ some a.1 := by
    intro hrecorded
    have hrecordedRoot :
        ReferenceFirstWindowNumericalStream.sourceArm
            ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
              rate source rewards C_star C_h hc count hspan)[k.val])
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).selected.view.payload
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).selected.view.pendingAtChoice
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).states
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).selected.view.complementWeights
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).selected.view.cutoff
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
              rate source rewards C_star C_h hc count hspan k).choiceInputsValid = some a.1 := by
      simpa [record, cell, payload] using hrecorded
    have howner :=
      ReferenceFirstLiveCoordinatorArrivals.actual_first_live_source_owner
        source rewards C_star C_h hc count hspan k a.1 hrecordedRoot
    have hownerEq : src = SnapshotRecordingKernel.ownerSource p regime a.1 :=
      hsourceScalar.symm.trans (by simpa [record, cell, regime] using howner)
    have hownerNe : SnapshotRecordingKernel.ownerSource p regime a.1 ≠
        ActiveRoundActions.coordinator p.two_le_m := by
      intro heq
      have hsrc' : src ≠ ActiveRoundActions.coordinator p.two_le_m := by
        simpa [src, record] using hsrc
      exact hsrc' (hownerEq.trans heq)
    have howns : SnapshotRecordingKernel.owns p regime
        (SnapshotRecordingKernel.ownerSource p regime a.1) a.1 :=
      SnapshotRecordingKernel.owns_ownerSource p regime a.1
    have hassigned :
        a.1 = payload.assignment.assigned
          (ActiveRoundActions.followerIndex p.two_le_m
            (SnapshotRecordingKernel.ownerSource p regime a.1) hownerNe) := by
      simpa [regime, SnapshotRecordingKernel.owns, hownerNe] using howns
    have himage : a.1 ∈ Finset.univ.image payload.assignment.assigned :=
      Finset.mem_image.mpr
        ⟨ActiveRoundActions.followerIndex p.two_le_m
            (SnapshotRecordingKernel.ownerSource p regime a.1) hownerNe,
          Finset.mem_univ _, hassigned.symm⟩
    have hslowSet :
        Finset.univ.image payload.assignment.assigned = payload.slowSet.1 := by
      have h := CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload payload
      exact congrArg Subtype.val h
    have hnotSlow : a.1 ∉ payload.slowSet.1 :=
      (Finset.mem_sdiff.mp a.property).2
    have hslow : a.1 ∈ payload.slowSet.1 := by
      have hmemEq := congrArg (fun S : Finset (Fin p.K) => a.1 ∈ S) hslowSet
      exact hmemEq.mp himage
    exact hnotSlow hslow
  have hsourceMap' :
      ReferenceFirstWindowNumericalStream.sourceArm
        ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan)[k.val])
        cell.selected.view.payload cell.selected.view.pendingAtChoice cell.states
        cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid ≠
          some a.1 := by
    simpa [record, cell, payload] using hsourceMap
  rw [cell.quantizedArrival_eq a.1]
  by_cases hsource : ReferenceFirstWindowNumericalStream.sourceArm
      ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[k.val])
      cell.selected.view.payload cell.selected.view.pendingAtChoice cell.states
      cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid =
        some a.1
  · exact False.elim (hsourceMap' hsource)
  · simp only [ite_eq_right hsource]

private theorem coordinator_complement_service_equations
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (src : Fin p.m)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (hpass : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (hpayload : r.payload = cell.selected.view.payload)
    (hother : ∀ a : FastArm cell.selected.view.payload.slowSet,
      src ≠ ActiveRoundActions.coordinator p.two_le_m →
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 = 0)
    (htraceCell : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if src = ActiveRoundActions.coordinator p.two_le_m then
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input arm else 0))
    (htraceRecording : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if recording.gateArm = some arm then recording.rawArrival else 0)) :
    (∀ a : FastArm r.payload.slowSet,
      serviced.arrival a =
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.service a = min (4 * rate.n)
        (q.queue a + RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1)) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.score a = r.complementScores a + serviced.service a) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.queue a = q.queue a +
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
          serviced.service a) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.previousService a = serviced.service a) ∧
    (∀ a : FastArm r.payload.slowSet,
      QueueReplay.transition (4 * rate.n) (r.complementScores a, q.queue a)
        (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
        (serviced.score a, serviced.queue a)) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
        serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
        serviced.previousService a ≤ D p) ∧
    (∀ a : FastArm r.payload.slowSet, serviced.arrival a = 0 →
      serviced.service a = min (4 * rate.n) (q.queue a + 0)) := by
  have hservicedRecording : serviced.recording = recording := by
    classical
    have hpass' := hpass
    unfold CoordinatorLiveServiceFinish.servicePass at hpass'
    by_cases hqueue : q.queueDomainValid
    · rw [dite_eq_left hqueue] at hpass'
      by_cases hprevious : q.previousServiceDomainValid
      · rw [dite_eq_left hprevious] at hpass'
        let arrival : FastArm r.payload.slowSet → ℕ :=
          fun j => CoordinatorLiveServiceFinish.complementArrival r.payload recording j
        by_cases harrival : ∀ j, arrival j ≤ D p
        · rw [dite_eq_left harrival] at hpass'
          let service : FastArm r.payload.slowSet → ℕ :=
            fun j => CappedService.service (4 * r.payload.n) (q.queue j) (arrival j)
          by_cases hservice : ∀ j, service j ≤ D p
          · rw [dite_eq_left hservice] at hpass'
            let score : FastArm r.payload.slowSet → ℕ :=
              fun j => r.complementScores j + service j
            by_cases hscore : ∀ j, score j ≤ p.T * D p
            · rw [dite_eq_left hscore] at hpass'
              let queue : FastArm r.payload.slowSet → ℕ :=
                fun j => CappedService.residual (4 * r.payload.n) (q.queue j) (arrival j)
              by_cases hqueueOut : ∀ j, queue j ≤ p.T * D p
              · rw [dite_eq_left hqueueOut] at hpass'
                cases hpass'
                rfl
              · rw [dite_eq_right hqueueOut] at hpass'
                cases hpass'
            · rw [dite_eq_right hscore] at hpass'
              cases hpass'
          · rw [dite_eq_right hservice] at hpass'
            cases hpass'
        · rw [dite_eq_right harrival] at hpass'
          cases hpass'
      · rw [dite_eq_right hprevious] at hpass'
        cases hpass'
    · rw [dite_eq_right hqueue] at hpass'
      cases hpass'
  have hn : r.payload.n = rate.n := by
    exact ReferenceActivePhysicalStep.payload_n_eq r.payload
  have harrival : ∀ a : FastArm r.payload.slowSet,
      serviced.arrival a =
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 := by
    intro a
    have hrecordingProjection :
        (if recording.gateArm = some a.1 then recording.rawArrival else 0) =
          if src = ActiveRoundActions.coordinator p.two_le_m then
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1
          else 0 := by
      have hleft := htraceRecording a.1
      rw [htraceCell a.1] at hleft
      exact (Option.some.inj hleft).symm
    let acell : FastArm cell.selected.view.payload.slowSet :=
      ⟨a.1, by simpa [hpayload] using a.2⟩
    rw [serviced.arrival_eq a, hservicedRecording]
    unfold CoordinatorLiveServiceFinish.complementArrival
    change (if recording.gateArm = some a.1 then recording.rawArrival else 0) = _
    by_cases hsrc : src = ActiveRoundActions.coordinator p.two_le_m
    · simpa [hsrc] using hrecordingProjection
    · have hzero := hother acell hsrc
      have hzero' : RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input acell.1 = 0 := hzero
      have hval : acell.1 = a.1 := rfl
      calc
        (if recording.gateArm = some a.1 then recording.rawArrival else 0) = 0 := by
          simpa [hsrc] using hrecordingProjection
        _ = RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 :=
          by rw [← hval]; exact hzero'.symm
  have hservice : ∀ a : FastArm r.payload.slowSet,
      serviced.service a = min (4 * rate.n)
        (q.queue a + RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) := by
    intro a
    calc
      serviced.service a = CappedService.service (4 * r.payload.n) (q.queue a)
          (serviced.arrival a) := serviced.service_eq a
      _ = min (4 * rate.n) (q.queue a +
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) := by
        simp [CappedService.service, hn, harrival a]
  have hqueue : ∀ a : FastArm r.payload.slowSet,
      serviced.queue a = q.queue a +
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
          serviced.service a := by
    intro a
    calc
      serviced.queue a = CappedService.residual (4 * r.payload.n) (q.queue a)
          (serviced.arrival a) := serviced.queue_eq a
      _ = q.queue a + RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
            serviced.service a := by
        simp [CappedService.residual, hn, harrival a, serviced.service_eq a]
  have hscore : ∀ a : FastArm r.payload.slowSet,
      serviced.score a = r.complementScores a + serviced.service a :=
    fun a => serviced.score_eq a
  have hprevious : ∀ a : FastArm r.payload.slowSet,
      serviced.previousService a = serviced.service a :=
    fun a => serviced.previousService_eq a
  have hqueueReplay : ∀ a : FastArm r.payload.slowSet,
      QueueReplay.transition (4 * rate.n) (r.complementScores a, q.queue a)
        (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
        (serviced.score a, serviced.queue a) := by
    intro a
    simpa [hn, harrival a] using
      CoordinatorLiveServiceFinish.serviced_queueReplay_transition r q serviced a
  refine ⟨harrival, hservice, hscore, hqueue, hprevious, hqueueReplay, ?_, ?_⟩
  · intro a
    exact ⟨serviced.arrivalDomain a, serviced.serviceDomain a,
      serviced.queueDomain a, serviced.scoreDomain a, serviced.previousServiceDomain a⟩
  · intro a hzero
    calc
      serviced.service a = min (4 * rate.n)
          (q.queue a + RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) :=
        hservice a
      _ = min (4 * rate.n) (q.queue a + 0) := by rw [← harrival a, hzero]

/- The premise is a literal successful physical tail, supplied from safety
inside each generated branch. No service or clock success is assumed at the root. -/
private theorem live_post_choice_success_of_no_failure
    {rate : ReferenceFirstWindowNumericalStream.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (h : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure = none) :
    ∃ recording serviced pending finished,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording ∧
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some pending ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
        .ok finished := by
  unfold ReferenceActivePhysicalStep.livePostChoice at h
  split at h
  · cases h
  · rename_i recording hrecord
    split at h
    · cases h
    · rename_i serviced hservice
      split at h
      · cases h
      · rename_i pending hconfirmation
        split at h
        · cases h
        · rename_i finished hfinish
          exact ⟨recording, serviced, pending, finished,
            hrecord, hservice, hconfirmation, hfinish⟩

private theorem actual_live_post_choice_storage
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (prepared : ReferenceActivePhysicalStep.PreparedRound record.input)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (pending : Finset (Fin (p.m - 1)))
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hprepared : prepared = record.output.preparation)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      record.input.time record.input.row prepared.coordinatorObservation = some pending)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time started.clock
      pending record.input.row = .ok finished)
    (hobserve : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started) :
    record.output.coordinator =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩ ∧
    record.output.next.coordinator =
      .live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base := by
  have hstepPrepared : prepared = ReferenceActivePhysicalStep.prepare record.input := by
    calc
      prepared = record.output.preparation := hprepared
      _ = (ReferenceActivePhysicalStep.step record.input).preparation := by rw [record.output_eq]
      _ = ReferenceActivePhysicalStep.prepare record.input := rfl
  have hpost := ReferenceActivePhysicalStep.livePostChoice_success prepared r q base started
    recording serviced pending finished hrecord hservice hconfirmation hfinish
  have hcoordinatorObserve : record.output.coordinator = prepared.observeCoordinator := by
    calc
      record.output.coordinator = (ReferenceActivePhysicalStep.step record.input).coordinator := by
        rw [record.output_eq]
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := rfl
      _ = prepared.observeCoordinator := by rw [← hstepPrepared]
  have hcoordinator : record.output.coordinator =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩ := by
    calc
      record.output.coordinator = prepared.observeCoordinator := hcoordinatorObserve
      _ = ReferenceActivePhysicalStep.livePostChoice prepared r q base started := hobserve
      _ = _ := hpost
  have hstepNext := (ReferenceActivePhysicalStep.step_next_fields record.input).1
  rw [← hstepPrepared] at hstepNext
  have hnext : record.output.next.coordinator =
      .live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base := by
    calc
      record.output.next.coordinator = (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
        rw [record.output_eq]
      _ = prepared.observeCoordinator.configuration := hstepNext
      _ = (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := by
        rw [hobserve]
      _ = _ := by rw [hpost]
  exact ⟨hcoordinator, hnext⟩

/- Every input below is conditional: the actual observation equation, its
no-failure fact, C's retained recording and raw projection, the selected payload
identity, and the other-source complement-zero fact. The generated root proves
or obtains all of them; none is added to its telescope. -/
private theorem coordinator_numerical_transition
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (src : Fin p.m)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hobserve : record.output.preparation.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice record.output.preparation r q base started)
    (hfailure : record.output.coordinator.failure = none)
    (sourceRecording : CoordinatorRecordingOperation.Output p)
    (hsourceRecording : record.output.coordinator.recording = some sourceRecording)
    (hpayload : r.payload = cell.selected.view.payload)
    (hother : ∀ a : FastArm cell.selected.view.payload.slowSet,
      src ≠ ActiveRoundActions.coordinator p.two_le_m →
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 = 0)
    (htraceCell : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if src = ActiveRoundActions.coordinator p.two_le_m then
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input arm else 0)) :
  ∃ recording serviced pending finished,
    CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
        r started) = some recording ∧
    record.output.coordinator.recording = some recording ∧
    CoordinatorLiveServiceFinish.servicePass r
      q recording = .ok serviced ∧
    r.payload = cell.selected.view.payload ∧
    cell.input.enabled = true ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.service a = min (4 * rate.n) (q.queue a +
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
      serviced.score a = r.complementScores a + serviced.service a ∧
      serviced.queue a = q.queue a +
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
        serviced.service a ∧
      serviced.previousService a = serviced.service a ∧
      QueueReplay.transition (4 * rate.n)
        (r.complementScores a, q.queue a)
        (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
        (serviced.score a, serviced.queue a)) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
        serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
        serviced.previousService a ≤ D p) ∧
    (∀ a : FastArm r.payload.slowSet,
      serviced.arrival a = 0 → serviced.service a =
        min (4 * rate.n) (q.queue a + 0)) ∧
    CoordinatorLocalArmChoice.confirmationUpdate r.payload
      started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      record.input.time record.input.row record.output.preparation.coordinatorObservation =
        some pending ∧
    CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
      started.clock pending record.input.row = .ok finished ∧
    finished.pending = pending ∧
    record.output.coordinator.failure = none ∧
    record.output.coordinator.up = none ∧
    record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank ∧
    record.output.next.coordinator =
      .live {
        payload := r.payload
        priorClock := finished.clock
        pendingAtChoice := finished.pending
        time := record.input.time
        gridBoundary := finished.clock.g
        complementScores := serviced.score }
      { queue := serviced.queue, previousService := serviced.previousService }
      base := by
  have hactual : record.output.coordinator = record.output.preparation.observeCoordinator := by
    rw [record.output_eq]
    rfl
  have htailFailure : (ReferenceActivePhysicalStep.livePostChoice
      record.output.preparation r q base started).failure = none := by
    rw [← hobserve, ← hactual]
    exact hfailure
  obtain ⟨recording, serviced, pending, finished, hrun, hservice, hconfirmation, hfinish⟩ :=
    live_post_choice_success_of_no_failure record.output.preparation r q base started htailFailure
  obtain ⟨hcoordinator, hnext⟩ := actual_live_post_choice_storage rate
    record.output.preparation r q base started recording serviced pending finished
    rfl hrun hservice hconfirmation hfinish hobserve
  have hrecording : record.output.coordinator.recording = some recording := by
    rw [hcoordinator]
  have hsame : recording = sourceRecording :=
    Option.some.inj (hrecording.symm.trans hsourceRecording)
  subst recording
  have htraceRecording : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if sourceRecording.gateArm = some arm then sourceRecording.rawArrival else 0) := by
    intro arm
    rw [ReferenceCoordinatorRecorderCallTrace.coordinatorRaw,
      ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
    change record.output.coordinator.recording.map _ = _
    rw [hsourceRecording]
    rfl
  have hcoordinates := coordinator_complement_service_equations rate record cell src
    r q sourceRecording serviced hservice hpayload hother htraceCell htraceRecording
  have hfinishedPending := CoordinatorPhaseClock.finishRound_pending_frame
    p rate.eta.val record.input.time started.clock pending record.input.row finished hfinish
  refine ⟨sourceRecording, serviced, pending, finished, hrun, hsourceRecording,
    hservice, hpayload, cell.enabled, hcoordinates.1, ?_,
    hcoordinates.2.2.2.2.2.2.1, hcoordinates.2.2.2.2.2.2.2,
    hconfirmation, hfinish, hfinishedPending, hfailure, ?_, ?_, hnext⟩
  · intro a
    exact ⟨hcoordinates.2.1 a, hcoordinates.2.2.1 a,
      hcoordinates.2.2.2.1 a, hcoordinates.2.2.2.2.1 a,
      hcoordinates.2.2.2.2.2.1 a⟩
  · rw [hcoordinator]
  · rw [hcoordinator]

/- This helper eliminates only the two successful branch witnesses. Its
record, cell, failure, recording, projection, and complement-zero inputs are
all explicit. The generated theorem below supplies each from the same run. -/
private theorem record_numerical_service
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (src : Fin p.m)
    (hfailure : record.output.coordinator.failure = none)
    (sourceRecording : CoordinatorRecordingOperation.Output p)
    (hsourceRecording : record.output.coordinator.recording = some sourceRecording)
    (hother : ∀ a : FastArm cell.selected.view.payload.slowSet,
      src ≠ ActiveRoundActions.coordinator p.two_le_m →
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 = 0)
    (htraceCell : ∀ arm : Fin p.K,
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) arm =
        some (if src = ActiveRoundActions.coordinator p.two_le_m then
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input arm else 0))
    (hbranches :
      (∃ installed arm,
        record.output.preparation.coordinator = .first (.chosen installed arm) ∧
        installed.registers.time = record.input.time) ∨
      (∃ r q base dispatched hstart continuation arm,
        record.output.preparation.coordinator =
          .live r q base (.continuingChosen dispatched hstart continuation arm))) :
    match record.output.preparation.coordinator with
    | .first (.chosen installed _selection) =>
        ∃ recording serviced pending finished,
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
              installed.registers installed.startRoundResult) = some recording ∧
          record.output.coordinator.recording = some recording ∧
          CoordinatorLiveServiceFinish.servicePass installed.registers
            installed.ownedRegisters recording = .ok serviced ∧
          installed.registers.payload = cell.selected.view.payload ∧
          cell.input.enabled = true ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a = RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.service a = min (4 * rate.n) (installed.ownedRegisters.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
            serviced.score a = installed.registers.complementScores a + serviced.service a ∧
            serviced.queue a = installed.ownedRegisters.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
              serviced.service a ∧
            serviced.previousService a = serviced.service a ∧
            QueueReplay.transition (4 * rate.n)
              (installed.registers.complementScores a, installed.ownedRegisters.queue a)
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
              (serviced.score a, serviced.queue a)) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
              serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
              serviced.previousService a ≤ D p) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a = 0 → serviced.service a =
              min (4 * rate.n) (installed.ownedRegisters.queue a + 0)) ∧
          CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
            installed.startRoundResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
            record.input.time record.input.row record.output.preparation.coordinatorObservation =
              some pending ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
            installed.startRoundResult.clock pending record.input.row = .ok finished ∧
          finished.pending = pending ∧
          record.output.coordinator.failure = none ∧
          record.output.coordinator.up = none ∧
          record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank ∧
          record.output.next.coordinator =
            .live {
              payload := installed.registers.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService }
            installed.followerBaseScore
    | .live r q base (.continuingChosen dispatched _hstart _continuation _selection) =>
        let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
        let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time
        ∃ recording serviced pending finished,
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
              actualRegisters dispatched.startResult) = some recording ∧
          record.output.coordinator.recording = some recording ∧
          CoordinatorLiveServiceFinish.servicePass actualRegisters actualOwned recording =
            .ok serviced ∧
          actualRegisters.payload = cell.selected.view.payload ∧
          cell.input.enabled = true ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a = RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.service a = min (4 * rate.n) (actualOwned.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
            serviced.score a = actualRegisters.complementScores a + serviced.service a ∧
            serviced.queue a = actualOwned.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
              serviced.service a ∧
            serviced.previousService a = serviced.service a ∧
            QueueReplay.transition (4 * rate.n)
              (actualRegisters.complementScores a, actualOwned.queue a)
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
              (serviced.score a, serviced.queue a)) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
              serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
              serviced.previousService a ≤ D p) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a = 0 → serviced.service a =
              min (4 * rate.n) (actualOwned.queue a + 0)) ∧
          CoordinatorLocalArmChoice.confirmationUpdate actualRegisters.payload
            dispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
            record.input.time record.input.row record.output.preparation.coordinatorObservation =
              some pending ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
            dispatched.startResult.clock pending record.input.row = .ok finished ∧
          finished.pending = pending ∧
          record.output.coordinator.failure = none ∧
          record.output.coordinator.up = none ∧
          record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank ∧
          record.output.next.coordinator =
            .live {
              payload := actualRegisters.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService } base
    | _ => False := by
  classical
  rcases hbranches with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, hbranch, htime⟩
    have hselectionActual := cell.selection_actual
    rw [hbranch] at hselectionActual
    have hselected : some (ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights arm htime) =
          some cell.selected := by
      exact (ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        record.input installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights arm htime).symm.trans
          hselectionActual
    have hpayload : (installed.registers.payload : ReferenceActivePhysicalStep.Payload rate) =
        cell.selected.view.payload :=
      congrArg (fun selected : ReferenceActivePhysicalStep.Selection record.input =>
        selected.view.payload) (Option.some.inj hselected)
    have hobserve : record.output.preparation.observeCoordinator =
        ReferenceActivePhysicalStep.livePostChoice record.output.preparation
          installed.registers installed.ownedRegisters installed.followerBaseScore
          installed.startRoundResult := by
      rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
        record.output.preparation (.chosen installed arm) hbranch]
      have hnonempty : (ReferenceActivePhysicalStep.DispatchCut.first
          (.chosen installed arm)).selection ≠ none := by
        intro hempty
        exact (Option.some_ne_none cell.selected) (hselectionActual.symm.trans hempty)
      exact ite_eq_right hnonempty
    rw [hbranch]
    exact coordinator_numerical_transition rate record cell src installed.registers
      installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
      hobserve hfailure sourceRecording hsourceRecording hpayload hother htraceCell
  · rcases hcontinuing with ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch⟩
    have hselectionActual := cell.selection_actual
    rw [hbranch] at hselectionActual
    have hselected : some (ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input r.payload dispatched.startResult record.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
        arm rfl) = some cell.selected := by
      exact (ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
        record.input r.payload dispatched.startResult record.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
        arm rfl).symm.trans hselectionActual
    have hpayload : r.payload = cell.selected.view.payload :=
      congrArg (fun selected : ReferenceActivePhysicalStep.Selection record.input =>
        selected.view.payload) (Option.some.inj hselected)
    have hobserve : record.output.preparation.observeCoordinator =
        ReferenceActivePhysicalStep.livePostChoice record.output.preparation
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
          base dispatched.startResult := by
      rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
        record.output.preparation r q base
        (.continuingChosen dispatched hstart continuation arm) hbranch]
      have hnonempty : (ReferenceActivePhysicalStep.DispatchCut.live r q base
          (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
        intro hempty
        exact (Option.some_ne_none cell.selected) (hselectionActual.symm.trans hempty)
      exact ite_eq_right hnonempty
    rw [hbranch]
    exact coordinator_numerical_transition rate record cell src
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base dispatched.startResult
      hobserve hfailure sourceRecording hsourceRecording hpayload hother htraceCell

/-- On the exact generated root, FIRST chosen and LIVE continuingChosen
exhaust the actual first-live window. No caller supplies a branch or state. -/
theorem actual_first_live_coordinator_service_branches
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    (∃ installed arm,
      record.output.preparation.coordinator = .first (.chosen installed arm) ∧
      installed.registers.time = record.input.time) ∨
    (∃ r q base dispatched hstart continuation arm,
      record.output.preparation.coordinator =
        .live r q base (.continuingChosen dispatched hstart continuation arm)) := by
  classical
  dsimp only
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let physicalRun := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow physicalRun.records
  let record := W[k.val]
  have hwindow := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hentry := hwindow k
  rcases hentry with ⟨_hinputs, _hrecordFailure, states, memories, hordinary, hbranch⟩
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with
      ⟨installed, arm, hbranch, _hfields, htime, _selected, _hselected,
        _hselectionEq, _hinputSelection, _hselectedFields, _branchRecording,
        _hbranchRecording, _hidentity, _hlive, _hdata⟩
    exact Or.inl ⟨installed, arm, hbranch, htime⟩
  · rcases hcontinuing with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, _hfields,
        _selected, _hselected, _hselectionEq, _hinputSelection, _hselectedFields,
        _branchRecording, _hbranchRecording, _hidentity, _hlive, _hdata⟩
    exact Or.inr ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch⟩

/-- The two literal successful dispatch branches exhaust the generated live
window. In each branch the complete numerical transition reaches the actual
next coordinator registers through confirmation and the original clock finish.
This is an internal coordinator-complement result, not a manuscript closure. -/
theorem actual_first_live_coordinator_numerical_service
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k
    match record.output.preparation.coordinator with
    | .first (.chosen installed _selection) =>
        ∃ recording serviced pending finished,
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
              installed.registers installed.startRoundResult) = some recording ∧
          record.output.coordinator.recording = some recording ∧
          CoordinatorLiveServiceFinish.servicePass installed.registers
            installed.ownedRegisters recording = .ok serviced ∧
          installed.registers.payload = cell.selected.view.payload ∧
          cell.input.enabled = true ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a = RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.service a = min (4 * rate.n) (installed.ownedRegisters.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
            serviced.score a = installed.registers.complementScores a + serviced.service a ∧
            serviced.queue a = installed.ownedRegisters.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
              serviced.service a ∧
            serviced.previousService a = serviced.service a ∧
            QueueReplay.transition (4 * rate.n)
              (installed.registers.complementScores a, installed.ownedRegisters.queue a)
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
              (serviced.score a, serviced.queue a)) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
              serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
              serviced.previousService a ≤ D p) ∧
          (∀ a : FastArm installed.registers.payload.slowSet,
            serviced.arrival a = 0 → serviced.service a =
              min (4 * rate.n) (installed.ownedRegisters.queue a + 0)) ∧
          CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
            installed.startRoundResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
            record.input.time record.input.row record.output.preparation.coordinatorObservation =
              some pending ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
            installed.startRoundResult.clock pending record.input.row = .ok finished ∧
          finished.pending = pending ∧
          record.output.coordinator.failure = none ∧
          record.output.coordinator.up = none ∧
          record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank ∧
          record.output.next.coordinator =
            .live {
              payload := installed.registers.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService }
            installed.followerBaseScore
    | .live r q base (.continuingChosen dispatched _hstart _continuation _selection) =>
        let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
        let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time
        ∃ recording serviced pending finished,
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
              actualRegisters dispatched.startResult) = some recording ∧
          record.output.coordinator.recording = some recording ∧
          CoordinatorLiveServiceFinish.servicePass actualRegisters actualOwned recording =
            .ok serviced ∧
          actualRegisters.payload = cell.selected.view.payload ∧
          cell.input.enabled = true ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a = RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.service a = min (4 * rate.n) (actualOwned.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
            serviced.score a = actualRegisters.complementScores a + serviced.service a ∧
            serviced.queue a = actualOwned.queue a +
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 -
              serviced.service a ∧
            serviced.previousService a = serviced.service a ∧
            QueueReplay.transition (4 * rate.n)
              (actualRegisters.complementScores a, actualOwned.queue a)
              (true, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) =
              (serviced.score a, serviced.queue a)) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a ≤ D p ∧ serviced.service a ≤ D p ∧
              serviced.queue a ≤ p.T * D p ∧ serviced.score a ≤ p.T * D p ∧
              serviced.previousService a ≤ D p) ∧
          (∀ a : FastArm actualRegisters.payload.slowSet,
            serviced.arrival a = 0 → serviced.service a =
              min (4 * rate.n) (actualOwned.queue a + 0)) ∧
          CoordinatorLocalArmChoice.confirmationUpdate actualRegisters.payload
            dispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
            record.input.time record.input.row record.output.preparation.coordinatorObservation =
              some pending ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
            dispatched.startResult.clock pending record.input.row = .ok finished ∧
          finished.pending = pending ∧
          record.output.coordinator.failure = none ∧
          record.output.coordinator.up = none ∧
          record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank ∧
          record.output.next.coordinator =
            .live {
              payload := actualRegisters.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := record.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService } base
    | _ => False := by
  classical
  dsimp only
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let physicalRun := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow physicalRun.records
  let record := W[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  let src := PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
    ((record.input.row.2 record.input.time).1)
  have hsafe := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
  have hfailure : record.output.coordinator.failure = none := (hsafe.1 k).1
  obtain ⟨sourceRecording, hsourceRecording, _hsourceGate, htraceCell, _hzeroReward⟩ :=
    ReferenceFirstLiveCoordinatorArrivals.actual_first_live_coordinator_source_arrivals
      rate source rewards C_star C_h hc count hspan k
  have hother : ∀ a : FastArm cell.selected.view.payload.slowSet,
      src ≠ ActiveRoundActions.coordinator p.two_le_m →
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 = 0 := by
    intro a hsrc
    exact source_arrival_zero_on_complement_of_other_source rate source rewards
      C_star C_h hc count hspan k hsrc a
  apply record_numerical_service rate record cell src hfailure sourceRecording
    hsourceRecording hother htraceCell
  exact actual_first_live_coordinator_service_branches
    rate source rewards C_star C_h hc count hspan k

end Bandits.Support.ReferenceFirstLiveCoordinatorNumericalService

end
