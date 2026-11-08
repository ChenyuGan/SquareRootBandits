/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementBirthNumericalReplay
public import Bandits.Support.ReferenceFirstReplacementAcceptedTailNumericalReplay

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# Actual continuing follower replay after the first replacement

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The proof consumes the accepted first-birth and accepted-tail numerical
producers. It follows the original complete physical records and serves every
calendar date in the continuing prefix, including dates with zero arrivals.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.RecordedQueueRun
open Bandits.Support.QueueReplay
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support

namespace Bandits.Support.ReferenceFirstReplacementContinuingNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_suffix_adjacent
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : ℕ)
    (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state = (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
      (R.get ⟨k + 1, hk⟩).input.time.val =
        (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, h0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, h1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [h0, h1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem finishFollower_ordinary_inv
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (i : Fin (p.m - 1)) (pre : ReferencePrelaunchFollower.State p rate.eta)
    (preMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepare : (record.output.preparation.followers.followers i).configuration =
      .ordinary pre preMemory)
    (houtput : (record.output.followers i).configuration = .ordinary next nextMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.followers.followers i).active
        (record.output.preparation.followers.followers i).arm
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) pre).result = .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) pre preMemory post =
        .ok (next, nextMemory) ∧
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i)
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).downInput =
        (ReferenceActivePhysicalStep.recordFollower
          record.output.preparation.coordinator.downView
          (record.output.preparation.followers.followers i).follower
          (record.output.preparation.followers.followers i).row
          (record.output.preparation.followers.followers i).activation
          (record.output.preparation.followers.followers i).time
          (record.output.preparation.followers.followers i).active
          (record.output.preparation.followers.followers i).arm
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) pre).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i)
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).down =
        (ReferenceActivePhysicalStep.recordFollower
          record.output.preparation.coordinator.downView
          (record.output.preparation.followers.followers i).follower
          (record.output.preparation.followers.followers i).row
          (record.output.preparation.followers.followers i).activation
          (record.output.preparation.followers.followers i).time
          (record.output.preparation.followers.followers i).active
          (record.output.preparation.followers.followers i).arm
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) pre).down := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinish : (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView prepared
      observation).configuration = .ordinary next nextMemory := by
    have he : record.output.followers i = ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared observation := by
      dsimp only [prepared, observation]
      rw [record.output_eq]
      rfl
    exact (congrArg ReferenceActivePhysicalStep.FollowerObservation.configuration he).symm.trans houtput
  obtain ⟨choice, memory, post, hconfiguration, hrecord, hrelease, hdownInput, hdown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      record.output.preparation.coordinator.downView prepared observation next nextMemory hfinish
  have hsame : DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice memory =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary pre preMemory :=
    hconfiguration.symm.trans (by simpa only [prepared] using hprepare)
  rcases DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hsame with ⟨rfl, rfl⟩
  have halign := record.output.preparation.follower_alignment i
  refine ⟨post, ?_, ?_⟩
  · simpa only [prepared, observation, halign.1, halign.2.1,
      halign.2.2.1] using hrecord
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [prepared, observation, halign.1, halign.2.1,
        halign.2.2.1] using hrelease
    · simpa only [prepared, observation, halign.1, halign.2.1,
        halign.2.2.1] using hdownInput
    · simpa only [prepared, observation, halign.1, halign.2.1,
        halign.2.2.1] using hdown

private theorem replay_take_succ (capacity : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) (n : ℕ) (hn : n < records.length) :
    QueueReplay.replay capacity initial (records.take (n + 1)) =
      QueueReplay.transition capacity (QueueReplay.replay capacity initial (records.take n))
        records[n] := by
  rw [← List.take_concat_get' records n hn, QueueReplay.replay_append]
  simp [QueueReplay.replay]

/-- At an actually occupied PREPARE boundary, the real local follower call
performs its checked enabled service, and the actual state after release and
finish keeps those queue registers. `harrival` is supplied by the actual
source cell at this same record, not by a desired trace. -/
private theorem actual_occupied_queue_step
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (pre : ReferencePrelaunchFollower.State p rate.eta)
    (preMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (arrival : ℕ)
    (hprepare : (record.output.preparation.followers.followers i).configuration =
      .ordinary pre preMemory)
    (houtput : (record.output.followers i).configuration = .ordinary next nextMemory)
    (hpersist : pre.status ≠ .unoccupied → next.status ≠ .unoccupied)
    (hbusy : pre.status ≠ .unoccupied)
    (hlast : pre.lastDown = some M)
    (harrival : ActiveFollowerQueueOperation.rawArrival rate.eta
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time M
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = arrival) :
    next.status ≠ .unoccupied ∧ next.lastDown = some M ∧
      next.S = pre.S + min (4 * rate.n) (pre.backlog + arrival) ∧
      next.delta = min (4 * rate.n) (pre.backlog + arrival) ∧
      next.backlog = pre.backlog + arrival - min (4 * rate.n) (pre.backlog + arrival) ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        (pre.S, pre.backlog) (true, arrival) ∧
      (record.output.followers i).downInput = none ∧
      (record.output.followers i).down = none := by
  classical
  let preparedRound := record.output.preparation
  let prepared := preparedRound.followers.followers i
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let own := record.output.ownEntries player
  let observation := preparedRound.feedback.observations player
  have hfeedback : (record.output.followers i) =
      ReferenceActivePhysicalStep.finishFollower preparedRound.coordinator.downView
        prepared observation := by
    dsimp only [preparedRound, prepared, observation]
    rw [record.output_eq]
    rfl
  obtain ⟨post, hrecord, hrelease, hfinishDownInput, hfinishDown⟩ :=
    finishFollower_ordinary_inv i pre preMemory
    next nextMemory hprepare houtput
  have hownPrepared : own = preparedRound.feedback.ownEntries player := by
    dsimp only [own, preparedRound]
    rw [record.output_eq]
    rfl
  have hownObservation : own.2 = observation := by
    rw [hownPrepared]
    exact congrArg Prod.snd (preparedRound.feedback.ownEntries_eq player)
  have hrecordStage :
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm own.2 pre = .ok post := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hbusy,
      hownObservation] using hrecord
  rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
    rate prepared.follower prepared.row prepared.activation prepared.time prepared.active
    prepared.arm own.2 pre hbusy] at hrecordStage
  cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale prepared.follower prepared.row prepared.activation prepared.time
      own.2 pre with
  | failure => simp only [hservice] at hrecordStage; cases hrecordStage
  | success serviced =>
      simp only [hservice] at hrecordStage
      have hpost : post = serviced.output := (Except.ok.inj hrecordStage).symm
      have hserviceActual : ActiveFollowerQueueOperation.checkedService rate.eta
          rate.sourceCap rate.n rate.n_scale prepared.follower prepared.row
          prepared.activation prepared.time own.2 pre = .success serviced := hservice
      rcases ActiveFollowerQueueOperation.serviceSuccess_equations serviced with
        ⟨hqueueUpdate, _, _, _, _, haction⟩
      have hactionFields :
          serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
              prepared.follower prepared.row prepared.time M own.2 ∧
          serviced.service = ActiveFollowerQueueOperation.localService rate.n
              pre.backlog serviced.arrival := by
        cases hstatus : pre.status with
        | unoccupied => exact (hbusy hstatus).elim
        | pending =>
            simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
            rcases haction with ⟨_, accepted, haccepted, _, hraw, hserved⟩
            have hM : accepted = M := Option.some.inj (haccepted.symm.trans hlast)
            subst accepted
            exact ⟨hraw, hserved⟩
        | released =>
            simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
            rcases haction with ⟨_, accepted, haccepted, _, hraw, hserved⟩
            have hM : accepted = M := Option.some.inj (haccepted.symm.trans hlast)
            subst accepted
            exact ⟨hraw, hserved⟩
      have harrival' : serviced.arrival = arrival := by
        calc
          serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
              prepared.follower prepared.row prepared.time M own.2 := hactionFields.1
          _ = arrival := by
            rw [hownObservation]
            simpa only [prepared, preparedRound, own, observation] using harrival
      have hserviceValue : serviced.service = min (4 * rate.n) (pre.backlog + arrival) := by
        simpa only [ActiveFollowerQueueOperation.localService,
          ActiveFollowerQueueOperation.serviceCapacity,
          Bandits.Support.CappedService.service, harrival'] using hactionFields.2
      have hserviceOutput : serviced.output = ActiveFollowerQueueOperation.serviceUpdate
          rate.n pre arrival := by
        have hqueue : serviced.output = ActiveFollowerQueueOperation.serviceOutput
            rate.n pre serviced.arrival := hqueueUpdate
        calc
          serviced.output = ActiveFollowerQueueOperation.serviceOutput rate.n pre serviced.arrival := hqueue
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n pre serviced.arrival := by
            cases hstatus : pre.status with
            | unoccupied => exact (hbusy hstatus).elim
            | pending => simp [ActiveFollowerQueueOperation.serviceOutput,
                ActiveRoundActions.FollowerStatus.occupied, hstatus]
            | released => simp [ActiveFollowerQueueOperation.serviceOutput,
                ActiveRoundActions.FollowerStatus.occupied, hstatus]
          _ = ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival := by rw [harrival']
      have hreply := (ReferenceFollowerReplyChronology.releaseAndFinish_frame
        i record.input.row record.input.time observation pre post next preMemory nextMemory
        hrelease).1
      have hframes : next.lastDown = post.lastDown ∧ next.S = post.S ∧
          next.delta = post.delta ∧ next.backlog = post.backlog := by
        simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply
      have hpreserve := ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
        rate.n pre arrival
      have hnextLast : next.lastDown = some M := by
        calc
          next.lastDown = post.lastDown := hframes.1
          _ = serviced.output.lastDown := congrArg ReferencePrelaunchFollower.State.lastDown hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).lastDown :=
            congrArg ReferencePrelaunchFollower.State.lastDown hserviceOutput
          _ = pre.lastDown := hpreserve.1
          _ = some M := hlast
      have hservice : min (4 * rate.n) (pre.backlog + arrival) = serviced.service :=
        hserviceValue.symm
      have hnextS : next.S = pre.S + min (4 * rate.n) (pre.backlog + arrival) := by
        calc
          next.S = post.S := hframes.2.1
          _ = serviced.output.S := congrArg ReferencePrelaunchFollower.State.S hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).S :=
            congrArg ReferencePrelaunchFollower.State.S hserviceOutput
          _ = pre.S + min (4 * rate.n) (pre.backlog + arrival) := by
            simp [ActiveFollowerQueueOperation.serviceUpdate,
              ActiveFollowerQueueOperation.localService,
              ActiveFollowerQueueOperation.serviceCapacity,
              Bandits.Support.CappedService.service]
      have hnextDelta : next.delta = min (4 * rate.n) (pre.backlog + arrival) := by
        calc
          next.delta = post.delta := hframes.2.2.1
          _ = serviced.output.delta := congrArg ReferencePrelaunchFollower.State.delta hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).delta :=
            congrArg ReferencePrelaunchFollower.State.delta hserviceOutput
          _ = min (4 * rate.n) (pre.backlog + arrival) := by
            simp [ActiveFollowerQueueOperation.serviceUpdate,
              ActiveFollowerQueueOperation.localService,
              ActiveFollowerQueueOperation.serviceCapacity,
              Bandits.Support.CappedService.service]
      have hnextBacklog : next.backlog = pre.backlog + arrival -
          min (4 * rate.n) (pre.backlog + arrival) := by
        calc
          next.backlog = post.backlog := hframes.2.2.2
          _ = serviced.output.backlog := congrArg ReferencePrelaunchFollower.State.backlog hpost
          _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n pre arrival).backlog :=
            congrArg ReferencePrelaunchFollower.State.backlog hserviceOutput
          _ = pre.backlog + arrival - min (4 * rate.n) (pre.backlog + arrival) := by
            simp [ActiveFollowerQueueOperation.serviceUpdate,
              ActiveFollowerQueueOperation.localService,
              ActiveFollowerQueueOperation.serviceCapacity,
              Bandits.Support.CappedService.residual,
              Bandits.Support.CappedService.service]
      have hpair : (next.S, next.backlog) =
          QueueReplay.transition (4 * rate.n) (pre.S, pre.backlog) (true, arrival) := by
        rw [hnextS, hnextBacklog]
        rfl
      have hdownNone : (record.output.followers i).downInput = none ∧
          (record.output.followers i).down = none := by
        have hrecordDiag :
            (ReferenceActivePhysicalStep.recordFollower preparedRound.coordinator.downView
              prepared.follower prepared.row prepared.activation prepared.time prepared.active
              prepared.arm observation pre).downInput = none ∧
            (ReferenceActivePhysicalStep.recordFollower preparedRound.coordinator.downView
              prepared.follower prepared.row prepared.activation prepared.time prepared.active
              prepared.arm observation pre).down = none := by
          simp [ReferenceActivePhysicalStep.recordFollower, prepared, preparedRound, hbusy]
        have hfinishDiag :
            (ReferenceActivePhysicalStep.finishFollower preparedRound.coordinator.downView
              prepared observation).downInput = none ∧
            (ReferenceActivePhysicalStep.finishFollower preparedRound.coordinator.downView
              prepared observation).down = none :=
          ⟨hfinishDownInput.trans hrecordDiag.1, hfinishDown.trans hrecordDiag.2⟩
        exact ⟨(congrArg (fun follower => follower.downInput) hfeedback).trans hfinishDiag.1,
          (congrArg (fun follower => follower.down) hfeedback).trans hfinishDiag.2⟩
      have hnextBusy : next.status ≠ .unoccupied := hpersist hbusy
      exact ⟨hnextBusy, hnextLast, hnextS, hnextDelta, hnextBacklog, hpair,
        hdownNone.1, hdownNone.2⟩

private theorem pending_reference_down_cut_is_accepted
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (feedback : ReferencePrelaunchFollower.Observation p)
    (state after : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer)
    (hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).outcome =
        .ok after)
    (hpending : after.status = .pending) :
    ∃ M scan registers lastService,
      (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).outcome =
        .accepted state
          { state with
            lastDown := some M
            S := registers.1
            delta := lastService
            backlog := registers.2
            status := if scan.endpoint = t.val + 2 then .pending else .unoccupied
            downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
              p i row t feedback rate state).1
            buffer := [] }
          (ActiveFollowerDownAcceptance.currentDecodeStep p i row t feedback rate state).2
          M scan registers lastService := by
  classical
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t feedback rate state
  let expected := ReferenceDownReception.expectedDownFlatWord view i row t
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
  · by_cases hmatches : decoded.2 = expected
    · cases hparsed : ReferenceDownReception.ordinaryParse p rate decoded.2 with
      | none =>
          have hparsedExpected : ReferenceDownReception.ordinaryParse p rate expected = none := by
            simpa only [hmatches] using hparsed
          have hafter : { state with downBatch := decoded.1 } = after := by
            simpa [ReferenceDownReception.referenceDownCut, hselected, hstatus,
              hregisters, hbatch, hbuffer, decoded, expected, hmatches, hparsedExpected,
              DeclaredFollowerLocalRound.consumeDownResult] using hconsume
          have hafterStatus : after.status = .unoccupied := by
            rw [← hafter]
            exact hstatus
          exact (by rw [hafterStatus] at hpending; cases hpending)
      | some M =>
          have hparsedExpected : ReferenceDownReception.ordinaryParse p rate expected = some M := by
            simpa only [hmatches] using hparsed
          by_cases haccepted : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M
          · let hstart := ActiveFollowerDownAcceptance.acceptedDownStartLE
              p rate M t state haccepted
            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t hstart row
            cases hchecked : ActiveFollowerDownAcceptance.checkedRecovery
                p rate M state scan.endpoint with
            | error failure =>
                simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                  hregisters, hbatch, hbuffer, decoded, expected, hmatches, hparsedExpected,
                  haccepted, scan, hchecked,
                  DeclaredFollowerLocalRound.consumeDownResult] at hconsume
            | ok recovered =>
                refine ⟨M, scan, recovered.registers, recovered.lastService, ?_⟩
                simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                  hregisters, hbatch, hbuffer, decoded, expected, hmatches, hparsedExpected,
                  haccepted, scan, hchecked]
          · have hafter : { state with downBatch := decoded.1 } = after := by
              simpa [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                hregisters, hbatch, hbuffer, decoded, expected, hmatches, hparsedExpected,
                haccepted, DeclaredFollowerLocalRound.consumeDownResult] using hconsume
            have hafterStatus : after.status = .unoccupied := by
              rw [← hafter]
              exact hstatus
            exact (by rw [hafterStatus] at hpending; cases hpending)
    · have hafter : { state with downBatch := decoded.1 } = after := by
        simpa [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregisters, hbatch, hbuffer, decoded, expected, hmatches,
          DeclaredFollowerLocalRound.consumeDownResult] using hconsume
      have hafterStatus : after.status = .unoccupied := by
        rw [← hafter]
        exact hstatus
      exact (by rw [hafterStatus] at hpending; cases hpending)
  · have hafter : state = after := by
      simpa [ReferenceDownReception.referenceDownCut, hselected,
        DeclaredFollowerLocalRound.consumeDownResult] using hconsume
    have hafterStatus : after.status = .unoccupied := by
      rw [← hafter]
      exact hstatus
    exact (by rw [hafterStatus] at hpending; cases hpending)

/-- The actual first replacement's followers follow the transmitted DOWN
queue through every original record in the continuing prefix. Each enabled
calendar round is retained in the replay, including a zero arrival. -/
theorem complete_first_replacement_continuing_follower_numerical_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        C.length = X.length ∧
        X = birth :: tail ∧
        ∀ j : Fin X.length, ∀ i : Fin (p.m - 1),
          let x := X.get j
          let M := payload.downRecord i
          let a := payload.assignment.assigned i
          let A := fun b => (C.take b).map (fun c =>
            (true, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
          let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
          ∃ pre preMemory next nextMemory,
            (x.output.preparation.followers.followers i).configuration =
              .ordinary pre preMemory ∧
            (x.output.followers i).configuration = .ordinary next nextMemory ∧
            (x.output.followers i).failure = none ∧
            (pre.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
              pre.lastDown = some M ∧
              (pre.S, pre.backlog) = Q j.val ∧
              pre.delta = (Q j.val).1 - (Q (j.val - 1)).1) ∧
            (next.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
              next.lastDown = some M ∧
              (next.S, next.backlog) = Q (j.val + 1) ∧
              next.delta = (Q (j.val + 1)).1 - (Q j.val).1 ∧
              ∃ k : Fin X.length, k.val ≤ j.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get k) i M)
      | _ => True := by
  classical
  have hsource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  have hgeometry :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
      rate source rewards C_star C_h
  have hboundary :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
      rate source rewards C_star C_h
  have hbirth :=
    ReferenceFirstReplacementBirthNumericalReplay.complete_first_replacement_birth_numerical_replay
      rate source rewards C_star C_h
  have htailReplay :=
    ReferenceFirstReplacementAcceptedTailNumericalReplay.complete_first_replacement_accepted_tail_numerical_replay
      rate source rewards C_star C_h
  dsimp only at hsource hgeometry hboundary hbirth htailReplay ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hsource hgeometry hboundary hbirth htailReplay ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hc] at hsource hgeometry hboundary hbirth htailReplay
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hinstruction output hcons clockData installed arm
      dsimp only [ReferenceActivePhysicalStep.collectionInput]
        at hsource hgeometry hboundary hbirth htailReplay ⊢
      let payloadRoot : ReferenceActivePhysicalStep.Payload rate :=
        installed.registers.payload
      have payloadRootEq : payloadRoot = installed.registers.payload := rfl
      let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      obtain ⟨hSourceLength, hcells, hrecoveries⟩ := hsource
      obtain ⟨hBirthLength, hstream, birthCell, hBirthCell, hBirthReadout,
        hbirthFollowers⟩ := hbirth
      change X = birth :: tail at hstream
      have hXlength : X.length = tail.length + 1 := by rw [hstream]; simp
      have hClength : C.length = X.length := hSourceLength
      have hsourceAt : ∀ j : Fin X.length,
          ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (X.get j),
            C[j.val]? = some cell.input ∧
            ReferenceLaterLiveNumericalReadout.laterLiveReadout s (X.get j) =
              some cell.input ∧
            cell.selected.view.payload = installed.registers.payload ∧
            cell.input.enabled = true := by
        intro j
        exact (hcells j).imp fun cell h =>
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      have hindexAt : ∀ q : ℕ, ∀ hq : q < X.length,
          ∃ hqR : v + q < R.length,
            R.get ⟨v + q, hqR⟩ = X.get ⟨q, hq⟩ := by
        intro q hq
        by_cases hq0 : q = 0
        · subst q
          have hv : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
          have hRvalue : R[v] = birth := (List.getElem?_eq_some_iff.mp hb).2
          have hRget : R.get ⟨v, hv⟩ = birth := by
            simpa only [List.get_eq_getElem] using hRvalue
          have hXoption : X[0]? = some birth := by rw [hstream]; rfl
          have hXget : X.get ⟨0, hq⟩ = birth := by
            simpa only [List.get_eq_getElem] using
              (List.getElem?_eq_some_iff.mp hXoption).2
          exact ⟨hv, hRget.trans hXget.symm⟩
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (Nat.pos_of_ne_zero hq0))
          have hm : m < tail.length := by rw [hXlength] at hq; omega
          let k : Fin tail.length := ⟨m, hm⟩
          have htailGet := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
          have hRbound : v + 1 + m < R.length := by
            exact (List.getElem?_eq_some_iff.mp htailGet).1
          have hRvalue : R[v + 1 + m] = tail.get k :=
            (List.getElem?_eq_some_iff.mp htailGet).2
          have hXoption : X[m + 1]? = some (tail.get k) := by
            rw [hstream]
            simp [k, List.get_eq_getElem]
          have hXvalue : X[m + 1] = tail.get k :=
            (List.getElem?_eq_some_iff.mp hXoption).2
          have hRbound' : v + (m + 1) < R.length := by omega
          have hRget : R.get ⟨v + (m + 1), hRbound'⟩ = tail.get k := by
            have hRget' : R.get ⟨v + 1 + m, hRbound⟩ = tail.get k := by
              simpa only [List.get_eq_getElem] using hRvalue
            simpa only [List.get_eq_getElem, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hRget'
          have hXget : X.get ⟨m + 1, hq⟩ = tail.get k := by
            simpa only [List.get_eq_getElem] using hXvalue
          have hindexEq : v + (m + 1) = v + (m + 1) := rfl
          rw [hindexEq]
          exact ⟨hRbound', hRget.trans hXget.symm⟩
      have hstep : ∀ n : ℕ, ∀ hn : n < X.length, ∀ i : Fin (p.m - 1),
          let x := X.get ⟨n, hn⟩
          let M := installed.registers.payload.downRecord i
          let a := installed.registers.payload.assignment.assigned i
          let A := fun b => (C.take b).map (fun c =>
            (true, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
          let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
          ∃ pre preMemory next nextMemory,
            (x.output.preparation.followers.followers i).configuration =
              .ordinary pre preMemory ∧
            (x.output.followers i).configuration = .ordinary next nextMemory ∧
            (x.output.followers i).failure = none ∧
            (pre.status ≠ .unoccupied →
              pre.lastDown = some M ∧ (pre.S, pre.backlog) = Q n ∧
              pre.delta = (Q n).1 - (Q (n - 1)).1) ∧
            (next.status ≠ .unoccupied →
              next.lastDown = some M ∧ (next.S, next.backlog) = Q (n + 1) ∧
              next.delta = (Q (n + 1)).1 - (Q n).1 ∧
              ∃ k : Fin X.length, k.val ≤ n ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get k) i M) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro hn i
          by_cases hn0 : n = 0
          · subst n
            have hbIndexOption : X[0]? = some birth := by rw [hstream]; rfl
            have hbIndex : X.get ⟨0, hn⟩ = birth :=
              (List.getElem?_eq_some_iff.mp hbIndexOption).2
            obtain ⟨pre, preMemory, next, nextMemory, hpreparedBirth,
              houtputBirth, hfailureBirth, hpreUnoccupied, hnextBirth⟩ := hbirthFollowers i
            let M := installed.registers.payload.downRecord i
            let A := fun b => (C.take b).map (fun c => (true,
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                (installed.registers.payload.assignment.assigned i)))
            let Q := fun b => QueueReplay.replay (4 * rate.n)
              (0, M.val.q) (A b)
            have hpreFields : pre.status ≠ .unoccupied →
                pre.lastDown = some M ∧ (pre.S, pre.backlog) = Q 0 ∧
                  pre.delta = (Q 0).1 - (Q (0 - 1)).1 := by
              intro hbusy
              exact (hbusy hpreUnoccupied).elim
            have hnextFields : next.status ≠ .unoccupied →
                next.lastDown = some M ∧ (next.S, next.backlog) = Q 1 ∧
                  next.delta = (Q 1).1 - (Q 0).1 ∧
                  ∃ k : Fin X.length, k.val ≤ 0 ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get k) i M := by
              intro hbusy
              obtain ⟨hlast, hregisters, hdelta, hretained⟩ := hnextBirth hbusy
              refine ⟨hlast, ?_, ?_, ?_⟩
              · exact hregisters
              · exact hdelta
              · refine ⟨⟨0, hn⟩, Nat.zero_le _, ?_⟩
                rw [hbIndex]
                exact hretained
            refine ⟨pre, preMemory, next, nextMemory, ?_, ?_, ?_, hpreFields, hnextFields⟩
            · rw [hbIndex]
              exact hpreparedBirth
            · rw [hbIndex]
              exact houtputBirth
            · rw [hbIndex]
              exact hfailureBirth
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
            have hkval : m < tail.length := by rw [hXlength] at hn; omega
            let k : Fin tail.length := ⟨m, hkval⟩
            have hxOption : X[m + 1]? = some (tail.get k) := by
              rw [hstream]
              simp [k, List.get_eq_getElem]
            have hx : X.get ⟨m + 1, hn⟩ = tail.get k :=
              (List.getElem?_eq_some_iff.mp hxOption).2
            have hpreviousBound : m < X.length := by omega
            obtain ⟨pp, ppm, pn, pnm, hpprep, hppout, hppfail, hppre, hppnext⟩ :=
              ih m (by omega) hpreviousBound i
            obtain ⟨hindex, htime, hrows, hselected, hrewards,
              selected, hsel, hpay, hlive, hgrid, hbits⟩ := hgeometry.2 k
            have hpayRoot : selected.view.payload = payloadRoot :=
              hpay.trans payloadRootEq.symm
            have hbk := hboundary k
            obtain ⟨_hindexBoundary, _hrowsBoundary, _hselectedBoundary,
              _hrewardsBoundary, _selectedBoundary, _hselBoundary, _hpayBoundary,
              _hliveBoundary, _hgridBoundary, _hbitsBoundary, hfollowers⟩ := hbk
            obtain ⟨state, memory, next, nextMemory, hinput, hdomain, hmass,
              hzero, hstrict, hbusy, hpair, hbefore, hstamp, hstart, hcredit,
              hdecision, hprep, hout, hfailure, hinit, hnextDomain, hnextMass,
              hnextDelta, hnextZero, hnextStrict, hnextBusy, hpersist⟩ := hfollowers i
            have hcurrentStart : (payloadRoot.downRecord i).val.sigma ≤
                (tail.get k).input.time.val + 1 := by
              rw [payloadRootEq]
              exact Nat.le_succ_of_le hstart
            obtain ⟨hprevR, hprevValue⟩ := hindexAt m hpreviousBound
            obtain ⟨hcurrentR, hcurrentValue⟩ := hindexAt (m + 1) hn
            have hadjBound : v + m + 1 < R.length := by
              simpa only [Nat.add_assoc] using hcurrentR
            have hadj := complete_suffix_adjacent source rewards C_star C_h
              (v + m) hadjBound
            have hcurrentValue' :
                R.get ⟨v + m + 1, hadjBound⟩ = X.get ⟨m + 1, hn⟩ := by
              have hindexEq : v + (m + 1) = v + m + 1 := by omega
              simpa only [hindexEq] using hcurrentValue
            dsimp only [R] at hadj hprevValue hcurrentValue'
            rw [hprevValue, hcurrentValue'] at hadj
            have hprevNext :
                (X.get ⟨m, hpreviousBound⟩).output.next.followers i = .ordinary pn pnm := by
              have hnextConfig :
                  (X.get ⟨m, hpreviousBound⟩).output.next.followers i =
                    ((X.get ⟨m, hpreviousBound⟩).output.followers i).configuration := by
                rw [(X.get ⟨m, hpreviousBound⟩).output_eq]
                rfl
              rw [hnextConfig, hppout]
            have hcurrentInputX :
                (X.get ⟨m + 1, hn⟩).input.state.followers i = .ordinary state memory := by
              simpa only [hx] using hinput
            have hstateAdj := congrArg (fun st => st.followers i) hadj.1
            have hconfig :
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory =
                  .ordinary pn pnm := by
              calc
                .ordinary state memory =
                    (X.get ⟨m + 1, hn⟩).input.state.followers i := hcurrentInputX.symm
                _ = (X.get ⟨m, hpreviousBound⟩).output.next.followers i := hstateAdj
                _ = .ordinary pn pnm := hprevNext
            have hstateEq : state = pn :=
              (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
            have hmemoryEq : memory = pnm :=
              (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).2
            subst state
            subst memory
            let state := pn
            let memory := pnm
            let M := installed.registers.payload.downRecord i
            let assignmentArm := installed.registers.payload.assignment.assigned i
            let records := C.map (fun c => (true,
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c assignmentArm))
            let queuePrefix := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((C.take b).map (fun c => (true,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c assignmentArm)))
            let queuePrefixList := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q)
              (records.take b)
            have hmapTake (b : ℕ) :
                (C.take b).map (fun c => (true,
                  RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c assignmentArm)) =
                  records.take b := by
              simp only [records, List.map_take]
            have hqueuePrefixEq (b : ℕ) : queuePrefix b = queuePrefixList b := by
              dsimp only [queuePrefix, queuePrefixList]
              exact congrArg (QueueReplay.replay (4 * rate.n) (0, M.val.q)) (hmapTake b)
            have hpreFields : state.status ≠ .unoccupied →
                state.lastDown = some M ∧ (state.S, state.backlog) = queuePrefix (m + 1) ∧
                  state.delta = (queuePrefix (m + 1)).1 - (queuePrefix m).1 := by
              intro hstateBusy
              have hpreviousBusy : pn.status ≠ .unoccupied := by
                simpa only [state] using hstateBusy
              rcases hppnext hpreviousBusy with ⟨hlast, hregisters, hdelta, _hretained⟩
              simpa only [state, M, queuePrefix, assignmentArm] using
                ⟨hlast, hregisters, hdelta⟩
            have hCdata := hsourceAt ⟨m + 1, hn⟩
            obtain ⟨sourceCell, hCget, hread, hcellPayload, _hcellEnabled⟩ := hCdata
            let recordIndex : Fin R.length := ⟨v + (m + 1), hcurrentR⟩
            have hreadOriginal : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                (R.get recordIndex) = some sourceCell.input := by
              rw [hcurrentValue]
              exact hread
            have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
              rate rewards C_star C_h source recordIndex sourceCell.input hreadOriginal
            rw [hcurrentValue] at hphysical
            obtain ⟨physicalCell, hinputEq, _henabled, _hlive, _henabledTrace,
              _hrowsPhysical, _hselectedPhysical, _hrewardsPhysical, _hmarker,
              _hdownLast, _howners, harrivals, _hunoccupied, _hlogging, _hcoord,
              _hlaterChosen⟩ := hphysical
            have hphysicalPayload : physicalCell.selected.view.payload =
                installed.registers.payload := by
              have hselSame := physicalCell.selection_actual.symm.trans
                sourceCell.selection_actual
              have hselEq : physicalCell.selected = sourceCell.selected :=
                Option.some.inj hselSame
              rw [hselEq]
              exact hcellPayload
            have hphysicalState : physicalCell.states i = state := by
              have hordinary := physicalCell.ordinary i
              have hprepared :
                  ((X.get ⟨m + 1, hn⟩).output.preparation.followers.followers i).configuration =
                    .ordinary state memory := by
                rw [hx]
                exact hprep
              have heq := hordinary.symm.trans hprepared
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj heq).1
            let x := X.get ⟨m + 1, hn⟩
            have hownObservation : (x.output.ownEntries
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
                x.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
              have ho : x.output.ownEntries = x.output.preparation.feedback.ownEntries := by
                rw [x.output_eq]
                rfl
              rw [ho, x.output.preparation.feedback.ownEntries_eq]
            have hrawInstalled : state.status ≠ .unoccupied →
                ActiveFollowerQueueOperation.rawArrival rate.eta i
                  (tail.get k).input.row (tail.get k).input.time
                  (installed.registers.payload.downRecord i)
                  ((tail.get k).output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  sourceCell.input
                  (installed.registers.payload.assignment.assigned i) := by
              intro hstateBusy
              have hbusyCell : (physicalCell.states i).status ≠ .unoccupied := by
                rw [hphysicalState]
                exact hstateBusy
              have h := (harrivals i hbusyCell).2
              rw [hphysicalPayload] at h
              have hownObservation' := hownObservation
              dsimp only [x] at hownObservation'
              rw [hownObservation'] at h
              have hobs := congrArg
                (fun record : ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate) =>
                  record.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) hx
              have hrow := congrArg
                (fun record : ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate) => record.input.row) hx
              have htimeRecord := congrArg
                (fun record : ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate) => record.input.time) hx
              rw [hrow, htimeRecord, hobs] at h
              exact h
            have hrawQuantized := hrawInstalled
            have hmappedOption : records[m + 1]? = some (true,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  sourceCell.input assignmentArm) := by
              dsimp only [records]
              simpa using congrArg (Option.map (fun c => (true,
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c assignmentArm))) hCget
            have hmappedValue := (List.getElem?_eq_some_iff.mp hmappedOption).2
            have hreplayStep : queuePrefix (m + 2) =
                QueueReplay.transition (4 * rate.n) (queuePrefix (m + 1))
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                    sourceCell.input assignmentArm) := by
              have hlength : m + 1 < records.length := by
                simp only [records, List.length_map]
                rw [hClength, hXlength]
                omega
              have hstep' := replay_take_succ (4 * rate.n)
                (0, M.val.q) records (m + 1) hlength
              have hstepList : queuePrefixList (m + 2) =
                  QueueReplay.transition (4 * rate.n) (queuePrefixList (m + 1))
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      sourceCell.input assignmentArm) := by
                simpa [queuePrefixList, records, hmappedValue] using hstep'
              rw [← hqueuePrefixEq (m + 2), ← hqueuePrefixEq (m + 1)] at hstepList
              exact hstepList
            have hnextFields : next.status ≠ .unoccupied →
                next.lastDown = some M ∧ (next.S, next.backlog) = queuePrefix (m + 2) ∧
                  next.delta = (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 ∧
                  ∃ j : Fin X.length, j.val ≤ m + 1 ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get j) i M := by
              intro hnextBusy
              by_cases hpreBusy : state.status ≠ .unoccupied
              · have hpre := hpreFields hpreBusy
                have harrival : ActiveFollowerQueueOperation.rawArrival rate.eta
                    ((tail.get k).output.preparation.followers.followers i).follower
                    ((tail.get k).output.preparation.followers.followers i).row
                    ((tail.get k).output.preparation.followers.followers i).time M
                    ((tail.get k).output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      sourceCell.input assignmentArm := by
                  have halign := (tail.get k).output.preparation.follower_alignment i
                  simpa only [halign.1, halign.2.1, halign.2.2.1, M, assignmentArm] using
                    hrawQuantized hpreBusy
                have hstep := actual_occupied_queue_step (tail.get k) i state memory
                  next nextMemory M
                  (RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                    sourceCell.input assignmentArm)
                  hprep hout hpersist hpreBusy hpre.1 harrival
                rcases hstep with ⟨_hnextOccupied, hlast, _hS, hdelta, _hbacklog,
                  hpair, _hdownInput, _hdown⟩
                have hpairReplay : (next.S, next.backlog) = queuePrefix (m + 2) := by
                  calc
                    (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
                        (state.S, state.backlog) (true,
                          RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            sourceCell.input assignmentArm) := hpair
                    _ = QueueReplay.transition (4 * rate.n)
                        (queuePrefix (m + 1))
                        (true, RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          sourceCell.input assignmentArm) := by rw [hpre.2.1]
                    _ = queuePrefix (m + 2) := hreplayStep.symm
                have hdeltaReplay : next.delta =
                    (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 := by
                  calc
                    next.delta = min (4 * rate.n) (state.backlog +
                        RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                          sourceCell.input assignmentArm) := hdelta
                    _ = (QueueReplay.transition (4 * rate.n) (state.S, state.backlog)
                          (true, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            sourceCell.input assignmentArm)).1 - state.S := by
                      simp [QueueReplay.transition]
                    _ = (QueueReplay.transition (4 * rate.n) (queuePrefix (m + 1))
                          (true, RecordedQueueRun.quantizedArrival
                            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                            sourceCell.input assignmentArm)).1 -
                          (queuePrefix (m + 1)).1 := by rw [← hpre.2.1]
                    _ = (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 := by
                      rw [hreplayStep]
                obtain ⟨_, _, _, hretained⟩ := hppnext hpreBusy
                rcases hretained with ⟨retainedIndex, hretainedLe, hretainedProof⟩
                exact ⟨hlast, hpairReplay, hdeltaReplay,
                  ⟨retainedIndex, Nat.le_succ_of_le hretainedLe, hretainedProof⟩⟩
              · have hstateUnoccupied : state.status = .unoccupied := by
                  by_contra hne
                  exact hpreBusy hne
                obtain ⟨logged, acceptedState, hlogging, _hbuffer, _hlastLog,
                  hlogDomain, _hlogPair, _hlogTime, hstrictLog, hf⟩ :=
                  @ReferenceFirstReplacementLiveFollowerPrefix.unoccupied_actual_follower_finish
                    p rate (tail.get k) payloadRoot selected hsel hpayRoot i state memory
                    hprep hstateUnoccupied hdomain hmass hpair hbefore hcurrentStart
                    (hstrict hstateUnoccupied) hcredit hgrid hbits
                dsimp only at hf
                obtain ⟨hconsume, _hrelease, hfinish, _hdomainNext, _hmassNext,
                  _hdeltaNext, _hflagNext, hshape⟩ := hf
                have hfinishConfig := congrArg
                  (fun follower : ReferenceActivePhysicalStep.FollowerObservation p rate =>
                    follower.configuration) hfinish
                have hacceptedStateEq : acceptedState = next :=
                  (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                    (hfinishConfig.symm.trans hout)).1
                have hacceptedStateBusy : acceptedState.status ≠ .unoccupied := by
                  rw [hacceptedStateEq]
                  exact hnextBusy
                obtain ⟨hpending, _hacceptedDown, _hacceptedBuffer⟩ :=
                  (hshape.resolve_left
                    (by intro hUnoccupied; exact hacceptedStateBusy hUnoccupied.1))
                have hlogFrame := ActiveFollowerLogging.checkedLogging_success_frame
                  i (tail.get k).input.row ((tail.get k).input.state.activations i)
                  (tail.get k).input.time
                  (((tail.get k).output.preparation.followers.followers i).arm,
                    (tail.get k).output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  state logged hlogging
                rcases hlogFrame with ⟨_, _, _, _, hloggedStatus, _, _⟩
                have hloggedStatus' : logged.status = .unoccupied :=
                  hloggedStatus.trans hstateUnoccupied
                have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged :=
                  hlogDomain.1
                have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch :=
                  hlogDomain.2.2
                have hbufferInput : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
                  refine ⟨?_, hlogDomain.2.1.2.1⟩
                  intro saved hsaved
                  obtain ⟨q, hq, hvalue⟩ := hlogDomain.2.1.2.2 saved hsaved
                  exact ⟨(hlogDomain.2.1.1 saved hsaved).1,
                    (hlogDomain.2.1.1 saved hsaved).2, ⟨⟨q, by omega⟩, hvalue⟩⟩
                let cut := ReferenceDownReception.referenceDownCut p
                  (tail.get k).output.preparation.coordinator.downView i
                  (tail.get k).input.row (tail.get k).input.time
                  ((tail.get k).output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                have hconsumeCut : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome =
                    .ok acceptedState := by
                  simpa only [cut] using hconsume
                obtain ⟨acceptedMessage, acceptedScan, acceptedRegisters,
                  acceptedLastService, hcutAccepted⟩ :=
                  pending_reference_down_cut_is_accepted
                    (tail.get k).output.preparation.coordinator.downView i
                    (tail.get k).input.row (tail.get k).input.time
                    ((tail.get k).output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                    logged acceptedState hloggedStatus' hregisters hbatch hbufferInput
                    hconsumeCut hpending
                have hdown : ((tail.get k).output.followers i).down = some cut := by
                  simpa only [cut] using congrArg
                    (fun follower : ReferenceActivePhysicalStep.FollowerObservation p rate =>
                      follower.down) hfinish
                have htailPoint := htailReplay k i
                rw [hdown] at htailPoint
                have hcutAcceptedLocal := hcutAccepted
                change cut.outcome = .accepted logged
                    { logged with
                      lastDown := some acceptedMessage
                      S := acceptedRegisters.1
                      delta := acceptedLastService
                      backlog := acceptedRegisters.2
                      status := if acceptedScan.endpoint = (tail.get k).input.time.val + 2
                        then .pending else .unoccupied
                      downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
                        (tail.get k).input.row (tail.get k).input.time
                        ((tail.get k).output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1
                      buffer := [] }
                    (ActiveFollowerDownAcceptance.currentDecodeStep p i
                      (tail.get k).input.row (tail.get k).input.time
                      ((tail.get k).output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).2
                    acceptedMessage acceptedScan acceptedRegisters acceptedLastService
                  at hcutAcceptedLocal
                cases hcutCase : cut.outcome with
                | skipped before reason => simp [hcutCase] at hcutAcceptedLocal
                | inputFailure before reason => simp [hcutCase] at hcutAcceptedLocal
                | decodeOrParseRejected before after raw => simp [hcutCase] at hcutAcceptedLocal
                | parsedButUnaccepted before after raw reply => simp [hcutCase] at hcutAcceptedLocal
                | outputFailure before reason => simp [hcutCase] at hcutAcceptedLocal
                | accepted before after raw message scan registers lastService =>
                    simp only [hcutCase] at htailPoint
                    obtain ⟨_hmessage, _hinput, _hendpoint, _hcount, _hregisters,
                      hlastService, _hafterLast, _hafterPair, _hafterDelta, _hafterBuffer,
                      acceptedNext, acceptedNextMemory, _houtputAccepted, _hfailureAccepted,
                      _hoccupiedAccepted, hlastAccepted, hpairAccepted, hdeltaAccepted,
                      hretainedAccepted⟩ := htailPoint
                    have hacceptedNextEq : acceptedNext = next :=
                      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                        (_houtputAccepted.symm.trans hout)).1
                    have hkvalEq : k.val = m := rfl
                    have hlastAcceptedM : acceptedNext.lastDown = some M := by
                      change acceptedNext.lastDown =
                        some (installed.registers.payload.downRecord i)
                      exact hlastAccepted
                    have hlastFinal : next.lastDown = some M := by
                      rw [← hacceptedNextEq]
                      exact hlastAcceptedM
                    have hpairAcceptedMap :
                        (acceptedNext.S, acceptedNext.backlog) = queuePrefix (m + 2) := by
                      rw [← hkvalEq]
                      dsimp only [queuePrefix, C, X, tail, M, assignmentArm]
                      exact hpairAccepted
                    have hpairFinal : (next.S, next.backlog) = queuePrefix (m + 2) := by
                      calc
                        (next.S, next.backlog) =
                            (acceptedNext.S, acceptedNext.backlog) := by
                          rw [hacceptedNextEq]
                        _ = queuePrefix (m + 2) := hpairAcceptedMap
                    have hlastServiceMap : lastService =
                        (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 := by
                      rw [← hkvalEq]
                      dsimp only [queuePrefix, C, X, tail, M, assignmentArm]
                      exact hlastService
                    have hdeltaFinal : next.delta =
                        (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 := by
                      calc
                        next.delta = acceptedNext.delta := by rw [hacceptedNextEq]
                        _ = lastService := hdeltaAccepted
                        _ = (queuePrefix (m + 2)).1 - (queuePrefix (m + 1)).1 := by
                          exact hlastServiceMap
                    refine ⟨hlastFinal, hpairFinal, hdeltaFinal, ?_⟩
                    refine ⟨⟨m + 1, hn⟩, Nat.le_refl _, ?_⟩
                    rw [hx]
                    exact hretainedAccepted
            have hprepX :
                ((X.get ⟨m + 1, hn⟩).output.preparation.followers.followers i).configuration =
                  .ordinary state memory := by rw [hx]; exact hprep
            have houtX : ((X.get ⟨m + 1, hn⟩).output.followers i).configuration =
                .ordinary next nextMemory := by rw [hx]; exact hout
            have hfailureX : ((X.get ⟨m + 1, hn⟩).output.followers i).failure = none := by
              rw [hx]
              exact hfailure
            simpa only [Nat.succ_eq_add_one, Nat.succ_sub_one] using
              (⟨state, memory, next, nextMemory, hprepX, houtX, hfailureX,
                hpreFields, hnextFields⟩ : _)
      refine ⟨hClength, hstream, ?_⟩
      intro j i
      exact hstep j.val j.isLt i

end Bandits.Support.ReferenceFirstReplacementContinuingNumericalReplay

end
