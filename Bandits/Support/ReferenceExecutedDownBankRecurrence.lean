/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedBoundaryMeasurability
public import Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
public import Bandits.Support.ReferenceSourceAffineHashHalf

import Lean.Elab.Tactic.Omega

/-!
# Executed DOWN calls and their physical decoder bank

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module identifies actual logged DOWN execution with the existing decoder
and studies postlaunch reset intervals on one retained physical run. Its
arbitrary-state helpers keep every local endpoint and gate visible. They do not
assert a global ordinary trace, a no-error law, a source event, or a regret
bound.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceActiveAffinePositiveTest

namespace Bandits.Support.ReferenceExecutedDownBankRecurrence

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record := ReferenceFollowerDownDecoderReplay.Record

variable {p : Parameters} {rate : RateInput p}

private theorem referenceDownCut_success_bank
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hbatch : ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch)
    (hout : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .ok post) :
    post.downBatch =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 := by
  classical
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row time
  · have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state := by
      by_contra hbad
      have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
          .inputFailure state .registers := by
        simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hbad]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
      cases hout
    have hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch := by
      simpa [ReferenceFollowerDecoderChronology.downBatchWellFormed,
        ActiveFollowerDownAcceptance.decoderInputDomain] using hbatch
    have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
      by_contra hbad
      have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
          .inputFailure state .sparseBuffer := by
        simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregisters, hdecoder, hbad]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
      cases hout
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state
    by_cases hmatches : decoded.2 =
        ReferenceDownReception.expectedDownFlatWord view i row time
    · by_cases hparsed : ReferenceDownReception.ordinaryParse p rate decoded.2 = none
      · have hparsedExpected : ReferenceDownReception.ordinaryParse p rate
            (ReferenceDownReception.expectedDownFlatWord view i row time) = none := by
          simpa [hmatches] using hparsed
        have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
            .decodeOrParseRejected state { state with downBatch := decoded.1 } decoded.2 := by
          simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
            hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected]
        rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
        have hpost := Except.ok.inj hout
        exact (congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm
      · obtain ⟨message, hparsed⟩ : ∃ message,
            ReferenceDownReception.ordinaryParse p rate decoded.2 = some message := by
          cases h : ReferenceDownReception.ordinaryParse p rate decoded.2 with
          | none => exact (hparsed h).elim
          | some message => exact ⟨message, rfl⟩
        have hparsedExpected : ReferenceDownReception.ordinaryParse p rate
            (ReferenceDownReception.expectedDownFlatWord view i row time) = some message := by
          simpa [hmatches] using hparsed
        by_cases haccepted : OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ReferencePrelaunchFollower.acceptedStart state) (time.val + 1) message
        · let hstart := ActiveFollowerDownAcceptance.acceptedDownStartLE
            p rate message time state haccepted
          let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan
            p rate message time hstart row
          cases hchecked : ActiveFollowerDownAcceptance.checkedRecovery p rate message state scan.endpoint with
          | error failure =>
              have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
                  .outputFailure state (.replay failure) := by
                simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                  hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected,
                  haccepted, scan, hchecked]
              rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
              cases hout
          | ok recovered =>
              have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
                  .accepted state
                    { state with
                      lastDown := some message
                      S := recovered.registers.1
                      delta := recovered.lastService
                      backlog := recovered.registers.2
                      status := if scan.endpoint = time.val + 2 then .pending else .unoccupied
                      downBatch := decoded.1
                      buffer := [] }
                    decoded.2 message scan recovered.registers recovered.lastService := by
                simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                  hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected,
                  haccepted, scan, hchecked]
              rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
              have hpost := Except.ok.inj hout
              exact (congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm
        · have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
              .parsedButUnaccepted state { state with downBatch := decoded.1 }
                decoded.2 message := by
            simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
              hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected, haccepted]
          rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
          have hpost := Except.ok.inj hout
          exact (congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm
    · have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
          .decodeOrParseRejected state { state with downBatch := decoded.1 } decoded.2 := by
        simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregisters, hdecoder, hbuffer, decoded, hmatches]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
      have hpost := Except.ok.inj hout
      exact (congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm
  · have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .skipped state .notSelectedDown := by
      simp [ReferenceDownReception.referenceDownCut, hselected]
    have hnotEligible : ¬ AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state) := by
      intro he
      exact hselected
        ((ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i row time observation rate state).mp he).1
    have hdecode := AffineBatchDecoder.decodeStep_ineligible p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state))
      state.downBatch time hbatch.1 (by
        simpa [ActiveFollowerDownAcceptance.currentInputExtension] using hnotEligible)
    rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
    have hpost : state = post := Except.ok.inj hout
    calc
      post.downBatch = state.downBatch := by
        exact (congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm
      _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 := by
        simpa only [ActiveFollowerDownAcceptance.currentDecodeStep] using
          (congrArg Prod.fst hdecode).symm

private theorem recordFollower_actualDecode_bank
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (hbatch : ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch)
    (hresult : (ReferenceActivePhysicalStep.recordFollower view i row activation time
      hactive arm observation state).result = .ok post) :
    post.downBatch =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 := by
  classical
  by_cases hunoccupied : state.status = .unoccupied
  · cases hlogging : ActiveFollowerLogging.checkedLogging i row activation time
      (arm, observation) state with
    | error failure =>
        simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging] at hresult
    | ok logged =>
        have hframe := ActiveFollowerLogging.checkedLogging_success_frame
          i row activation time (arm, observation) state logged hlogging
        rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
        have hloggedUnoccupied : logged.status = .unoccupied := hloggedStatus.trans hunoccupied
        have hcutResult : DeclaredFollowerLocalRound.consumeDownResult rate
            (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
              .ok post := by
          simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging] using hresult
        have hloggedWell : ReferenceFollowerDecoderChronology.downBatchWellFormed logged.downBatch := by
          rw [hloggedBatch]
          exact hbatch
        have hcutBatch := referenceDownCut_success_bank view i row time observation logged post
          hloggedUnoccupied hloggedWell hcutResult
        have hsame :
            ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged =
              ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state := by
          simp [ActiveFollowerDownAcceptance.currentDecodeStep,
            ActiveFollowerDownAcceptance.currentRoundInput, hloggedBatch, hloggedStatus]
        exact hcutBatch.trans (congrArg Prod.fst hsame)
  · have hserviceResult : DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row
        activation time hactive arm observation state = .ok post := by
      have hrecordEq := ReferenceActivePhysicalStep.recordFollower_result view i row activation
        time hactive arm observation state
      rw [hrecordEq] at hresult
      simpa [ReferenceDownReception.loggingThenReferenceDown, hunoccupied] using hresult
    unfold DeclaredFollowerLocalRound.recordOrServiceThenDown at hserviceResult
    simp only [dite_eq_right hunoccupied] at hserviceResult
    cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale i row activation time observation state with
    | failure => simp [hservice] at hserviceResult
    | success result =>
        simp only [hservice] at hserviceResult
        have hpost : result.output = post := Except.ok.inj hserviceResult
        have hframe := ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
          rate.n state result.arrival
        have hbatchOut : result.output.downBatch = state.downBatch := by
          rw [result.queueUpdate]
          exact hframe.2.1
        have hbatchPost : post.downBatch = state.downBatch := by
          rw [← hpost]
          exact hbatchOut
        have hnotEligible : ¬ AffineBatchDecoder.eligible
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state) := by
          intro he
          exact hunoccupied ((ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff
            p i row time observation rate state).mp he).2.1
        have hdecode := AffineBatchDecoder.decodeStep_ineligible p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state))
          state.downBatch time hbatch.1 (by
            simpa [ActiveFollowerDownAcceptance.currentInputExtension] using hnotEligible)
        rw [hbatchPost]
        change state.downBatch =
          (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1
        simpa only [ActiveFollowerDownAcceptance.currentDecodeStep] using
          (congrArg Prod.fst hdecode).symm

private theorem releaseAndFinish_downBatch_frame
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post : ReferencePrelaunchFollower.State p rate.eta)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : DeclaredFollowerLocalRound.releaseAndFinish rate i row time observation
      choice memory post = .ok (next, nextMemory)) :
    next.downBatch = post.downBatch := by
  classical
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hout
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) observation choice post with
  | error failure => simp [hrelease] at hout
  | ok released =>
      cases hfinish : ActiveFollowerLifecycle.finishRound rate.eta time row released memory with
      | error failure => simp [hrelease, hfinish] at hout
      | ok result =>
          have hreleaseEq := hrelease
          have hstate := ActiveFollowerLifecycle.finishRound_frame rate.eta time row
            released result.1 memory result.2 hfinish
          have hreleased : released.downBatch = post.downBatch := by
            cases hstatus : choice.status with
            | unoccupied =>
                rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i time
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) observation choice post
                  hstatus] at hrelease
                exact congrArg ReferencePrelaunchFollower.State.downBatch
                  (Except.ok.inj hrelease).symm
            | released =>
                have hnot : choice.status ≠ ActiveRoundActions.FollowerStatus.pending := by
                  simp [hstatus]
                rw [ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta i time
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) observation choice post
                  hnot] at hrelease
                exact congrArg ReferencePrelaunchFollower.State.downBatch
                  (Except.ok.inj hrelease).symm
            | pending =>
                by_cases hregs : ActiveFollowerLifecycle.localStateDomainValid choice
                · cases hlast : choice.lastDown with
                  | none =>
                      simp [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs,
                        hlast] at hrelease
                  | some M =>
                      by_cases htime : M.val.sigma ≤ time.val
                      · by_cases hpostRegs : ActiveFollowerLifecycle.localStateDomainValid post
                        · let releasedState := if ActiveFollowerLifecycle.releaseCondition rate.eta i
                              (ActiveFollowerLifecycle.publicRowOfCompleteRow row time) observation M then
                                { post with status := .released } else post
                          by_cases houtput : releasedState.status = .unoccupied ∨
                              ∃ M', releasedState.lastDown = some M' ∧ M'.val.sigma ≤ time.val + 1
                          · have heq : releasedState = released := by
                              simpa [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs,
                                hlast, htime, hpostRegs, houtput, releasedState] using hrelease
                            calc
                              released.downBatch = releasedState.downBatch :=
                                congrArg ReferencePrelaunchFollower.State.downBatch heq.symm
                              _ = post.downBatch := by
                                simp only [releasedState]
                                split_ifs <;> rfl
                          · simp [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs,
                              hlast, htime, hpostRegs, houtput, releasedState] at hrelease
                        · simp [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs,
                            hlast, htime, hpostRegs] at hrelease
                      · simp [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs,
                          hlast, htime] at hrelease
                · simp [ActiveFollowerLifecycle.releaseAfterService, hstatus, hregs] at hrelease
          rw [hreleaseEq] at hout
          simp [hfinish] at hout
          have hresult := Prod.mk.inj hout
          calc
            next.downBatch = result.1.downBatch :=
              congrArg ReferencePrelaunchFollower.State.downBatch hresult.1.symm
            _ = released.downBatch :=
              congrArg ReferencePrelaunchFollower.State.downBatch hstate
            _ = post.downBatch := hreleased

private theorem finishFollower_ordinary_projection
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ choice choiceMemory postRecord,
      prepared.configuration = .ordinary choice choiceMemory ∧
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok postRecord ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
        observation choice choiceMemory postRecord = .ok (next, nextMemory) := by
  cases hconfiguration : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hout
  | ordinary choice choiceMemory =>
      cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm observation
          choice).result with
      | error failure =>
          simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord] at hout
      | ok postRecord =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation choice choiceMemory postRecord with
          | error failure =>
              simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord,
                hfinish] at hout
          | ok result =>
              cases result with
              | mk final finalMemory =>
                  simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord,
                    hfinish] at hout
                  rcases hout with ⟨rfl, rfl⟩
                  exact ⟨choice, choiceMemory, postRecord, rfl, hrecord, hfinish⟩

private theorem record_downBatch_actual_replay_step
    (record : Record p rate) (i : Fin (p.m - 1))
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = []) :
    ∃ choice choiceMemory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary choice choiceMemory ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record = some
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) ∧
      after.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  let view := record.output.preparation.coordinator.downView
  have hstep : record.output = ReferenceActivePhysicalStep.step record.input := record.output_eq
  have hobserve :
      (record.output.preparation.observeFollower i).configuration = .ordinary after afterMemory := by
    have hafter' := hafter
    rw [hstep] at hafter'
    rw [hstep]
    simpa [ReferenceActivePhysicalStep.step] using hafter'
  have hfinish : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary after afterMemory := by
    simpa [view, prepared, observation,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hobserve
  obtain ⟨preparedState, preparedMemory, postRecord, hpreparedProjection, hrecord, hrelease⟩ :=
    finishFollower_ordinary_projection view prepared observation after afterMemory hfinish
  let choice := preparedState
  let choiceMemory := preparedMemory
  have hprepared : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
      .ordinary choice choiceMemory := hpreparedProjection
  have hframe := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i before choice memory choiceMemory hinput hprepared hoccupied
  have hprep := ReferenceFollowerDecoderChronology.run_prepared_follower_downBatch_spec
    record i before choice memory choiceMemory bound hinput hprepared hbefore hoccupied
  have hpreparedAlignment := record.output.preparation.follower_alignment i
  have hpreparedIndex : prepared.follower = i := hpreparedAlignment.2.1
  have hrecordBank := recordFollower_actualDecode_bank view prepared.follower prepared.row
    prepared.activation prepared.time prepared.active prepared.arm observation choice postRecord
    hprep.1.1 hrecord
  rw [hpreparedIndex] at hrecordBank
  have hreleaseBank := releaseAndFinish_downBatch_frame prepared.follower prepared.row prepared.time
    observation choice choiceMemory postRecord after afterMemory hrelease
  have hbatch : choice.downBatch = before.downBatch := hframe.1
  have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i choice
    choiceMemory hprepared
  refine ⟨choice, choiceMemory, hprepared, hcall, ?_⟩
  have hnext : after.downBatch =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
        observation rate choice).1 := by
    calc
      after.downBatch = postRecord.downBatch := hreleaseBank
      _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
          observation rate choice).1 := hrecordBank
  have hcallStep :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
        observation rate choice).1 =
      ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
        (prepared.time, ActiveFollowerDownAcceptance.currentRoundInput p i prepared.row
          prepared.time observation rate choice) := by
    unfold ActiveFollowerDownAcceptance.currentDecodeStep
      ReferenceFollowerDownDecoderReplay.replayDownCall
    rw [← hbatch]
  calc
    after.downBatch =
        (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
          observation rate choice).1 := hnext
    _ = ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
        (prepared.time, ActiveFollowerDownAcceptance.currentRoundInput p i prepared.row
          prepared.time observation rate choice) := hcallStep

/-- At an actual ordinary successor, the physical bank is the literal decoder
step on the same PREPARE choice. This local selector exposes the successful
ordinary-output branch; all receiver failures remain visible in the stored
diagnostics and are not assumed away. -/
theorem record_downBatch_after_ordinary
    (record : Record p rate) (i : Fin (p.m - 1))
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = []) :
    ∃ choice choiceMemory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary choice choiceMemory ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record = some
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) ∧
      after.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
  exact record_downBatch_actual_replay_step record i before after memory afterMemory bound
    hinput hafter hbefore hoccupied

/-- An ineligible administrative projection does not update the physical
bank. The equivalence defining eligibility includes disabled, occupied, and
zero-feedback cases. -/
theorem record_downBatch_after_ordinary_of_ineligible
    (record : Record p rate) (i : Fin (p.m - 1))
    (before after choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = [])
    (hchoice : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
      .ordinary choice choiceMemory)
    (hineligible : ¬ AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice)) :
    after.downBatch = before.downBatch := by
  obtain ⟨selected, selectedMemory, hselected, hcall, hstep⟩ :=
    record_downBatch_after_ordinary record i before after memory afterMemory bound
      hinput hafter hbefore hoccupied
  have hconfig :
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary selected selectedMemory :
        DeclaredFollowerLocalRound.LocalConfiguration p rate) = .ordinary choice choiceMemory :=
    hselected.symm.trans hchoice
  injection hconfig with hstate hmemory
  subst selected
  subst selectedMemory
  have hdecode := AffineBatchDecoder.decodeStep_ineligible p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice))
    before.downBatch (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
    hbefore.1.1 hineligible
  rw [ReferenceFollowerDownDecoderReplay.replayDownCall, hdecode] at hstep
  exact hstep

private theorem record_logged_choice
    (record : Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogged : (record.output.followers i).downInput = some logged) :
    ∃ state memory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary state memory ∧
      state.status = .unoccupied ∧
      logged.status = state.status ∧ logged.downBatch = state.downBatch := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hdiagnostic := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
    record i
  have hlogged' : (record.output.preparation.observeFollower i).downInput = some logged := by
    rw [hdiagnostic]
    exact hlogged
  have hfinish :
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared observation).downInput =
        some logged := by
    simpa only [prepared, observation,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hlogged'
  cases hconfiguration : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hfinish
  | ordinary state memory =>
      by_cases hstatus : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, observation) state with
        | error failure =>
            simp [ReferenceActivePhysicalStep.finishFollower,
              ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
              hlogging] at hfinish
        | ok actualLogged =>
            cases hresult : DeclaredFollowerLocalRound.consumeDownResult rate
                (ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView prepared.follower prepared.row
                  prepared.time observation rate actualLogged).outcome with
            | error failure =>
                have hloggedEq : actualLogged = logged := by
                  simpa [ReferenceActivePhysicalStep.finishFollower,
                    ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                    hlogging, hresult] using hfinish
                subst actualLogged
                have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                  prepared.follower prepared.row prepared.activation prepared.time
                  (prepared.arm, observation) state logged hlogging
                rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                exact ⟨state, memory, by simp [prepared,
                  ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                  hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
            | ok post =>
                cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                    prepared.follower prepared.row prepared.time observation state memory post with
                | error failure =>
                    have hloggedEq : actualLogged = logged := by
                      simpa [ReferenceActivePhysicalStep.finishFollower,
                        ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                        hlogging, hresult, hrelease] using hfinish
                    subst actualLogged
                    have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                      prepared.follower prepared.row prepared.activation prepared.time
                      (prepared.arm, observation) state logged hlogging
                    rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                    exact ⟨state, memory, by simp [prepared,
                      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                      hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
                | ok next =>
                    have hloggedEq : actualLogged = logged := by
                      simpa [ReferenceActivePhysicalStep.finishFollower,
                        ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                        hlogging, hresult, hrelease] using hfinish
                    subst actualLogged
                    have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                      prepared.follower prepared.row prepared.activation prepared.time
                      (prepared.arm, observation) state logged hlogging
                    rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                    exact ⟨state, memory, by simp [prepared,
                      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                      hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
      · cases hrecord : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
            prepared.follower prepared.row prepared.activation prepared.time prepared.active
            prepared.arm observation state with
        | error failure =>
            simp [ReferenceActivePhysicalStep.finishFollower,
              ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
              hrecord] at hfinish
        | ok post =>
            cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                prepared.follower prepared.row prepared.time observation state memory post with
            | error failure =>
                simp [ReferenceActivePhysicalStep.finishFollower,
                  ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                  hrecord, hrelease] at hfinish
            | ok next =>
                simp [ReferenceActivePhysicalStep.finishFollower,
                  ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                  hrecord, hrelease] at hfinish

/-- The retained diagnostics prove that the decoder actually ran: logged
input, raw comparison (either Boolean value), and positive own grid feedback
yield the real call, its original affine sample, and its exact expected
`Option Word`. The raw-comparison premise records execution even if a later
parse, recovery, release, or finish step failed. -/
theorem record_executed_down_call_fields
    (record : Record p rate) (i : Fin (p.m - 1))
    (callCode : ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
    let call := ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode
    ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
    call.1 = record.input.time ∧
    call.2.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample record.input ∧
    call.2.selected = true ∧ call.2.receiverEnabled = true ∧
    call.2.roundedReward =
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
    AffineBatchDecoder.eligible call.2 ∧
    cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input ∧
    ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
  classical
  dsimp only
  obtain ⟨state, memory, hconfiguration, hstatus, hloggedStatus, hloggedBatch⟩ :=
    record_logged_choice record i logged hlogged
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hcomparisonActual :
      ((ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged)).rawComparison.isSome =
        true := by
    rw [← hcutActual]
    exact hcomparison
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
      record.input.time logged := by
    rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call] at hcomparisonActual
    exact of_decide_eq_true hcomparisonActual
  have hactualCall : ReferenceFollowerDownDecoderReplay.actualDownCall i record =
      some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
    rw [← ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i record,
      hcall]
    rfl
  have hactualFields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
    record i _ hactualCall
  have hchoiceStatus : state.status = .unoccupied := by
    exact hloggedStatus.symm.trans hgate.2.1
  have hcallEq : ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode =
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate state) := by
    exact (Option.some.inj
      ((ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i state memory
        hconfiguration).symm.trans hactualCall)).symm
  have hselected : (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.selected = true := by
    exact hactualFields.2.2.mpr hgate.1
  have henabled :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.receiverEnabled = true := by
    rw [hcallEq]
    simp [ActiveFollowerDownAcceptance.currentRoundInput, hchoiceStatus]
  have hrounding : (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.roundedReward =
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [hcallEq]
    rfl
  have heligible : AffineBatchDecoder.eligible
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 := by
    exact ⟨hselected, henabled, by rw [hrounding]; exact hpositive⟩
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hsender : i = ReferenceActivePhysicalStep.upSenderIndex record.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    exact hgate.1.2.symm
  have hview : record.output.preparation.coordinator.downView =
      (ReferenceActivePhysicalStep.dispatch record.input).downView := by
    rw [hprepared]
    rfl
  have hexpected : cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input := by
    calc
      cut.expectedWord =
          (ReferenceDownReception.referenceDownCut p
            record.output.preparation.coordinator.downView i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).expectedWord :=
        congrArg ReferenceDownReception.ReferenceDownCutOutput.expectedWord hcutActual
      _ = ReferenceDownReception.expectedDownFlatWord
          record.output.preparation.coordinator.downView i record.input.row record.input.time := by
        classical
        unfold ReferenceDownReception.referenceDownCut
        split
        · split
          · split
            · split
              · split
                · dsimp only
                  split <;> rfl
                · rfl
              · rfl
            · rfl
          · rfl
        · rfl
      _ = ReferenceActiveAffinePositiveTest.downSent record.input := by
        simp [ReferenceActiveAffinePositiveTest.downSent, hview, hsender]
  have hdiag : ReferenceActiveAffinePositiveTest.downDiagnosticCall
      ((ReferenceActivePhysicalStep.prepare record.input).observeFollower
        (ReferenceActivePhysicalStep.upSenderIndex record.input)) = true := by
    have hobs : (ReferenceActivePhysicalStep.prepare record.input).observeFollower
        (ReferenceActivePhysicalStep.upSenderIndex record.input) = record.output.followers i := by
      calc
        _ = record.output.preparation.observeFollower
            (ReferenceActivePhysicalStep.upSenderIndex record.input) := by rw [hprepared]
        _ = record.output.preparation.observeFollower i := by rw [hsender]
        _ = record.output.followers i :=
          ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i
    simp [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hobs, hcut, hcomparison]
  have hown : ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ReferenceActivePhysicalStep.upSenderIndex record.input))).val.val =
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [← hprepared, hsender]
    rfl
  have hdownPositive : ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_diagnostic, hdiag, hown]
    simp [hpositive]
  have hsampleOriginal :=
    ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_sample_original_of_eligible
      record i _ hactualCall heligible
  exact ⟨hactualCall, hactualFields.1, hactualFields.2.1, hsampleOriginal, hselected, henabled,
    hrounding, heligible, hexpected, hdownPositive⟩

/-- On a computed ordinary successor, a retained executed diagnostic is the
actual decoder transition applied to the bank written in that diagnostic.
The ordinary successor is selected locally; the diagnostic itself remains
valid through later parse, recovery, release, or finish failures. -/
theorem record_executed_down_bank_after_ordinary
    (record : Record p rate) (i : Fin (p.m - 1))
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = [])
    (callCode : ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
    let call := ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode
    ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
    after.downBatch =
      (AffineBatchDecoder.decodeStep p
        (ActiveFollowerDownAcceptance.currentInputExtension p call.2)
        logged.downBatch call.1).1 ∧
    cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input ∧
    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample record.input ∧
    call.2.selected = true ∧ call.2.receiverEnabled = true ∧
    call.2.roundedReward = (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
  classical
  dsimp only
  obtain ⟨choice, choiceMemory, hchoice, hpreparedCall, hphysicalStep⟩ :=
    record_downBatch_after_ordinary record i before after memory afterMemory bound
      hinput hafter hbefore hoccupied
  obtain ⟨hactual, _, _, hsampleOriginal, hselected, henabled, hrounded, _, hexpected, _⟩ :=
    record_executed_down_call_fields record i callCode logged cut hcall hlogged hcut
      hcomparison hpositive
  have hcallEq : ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode =
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
    exact Option.some.inj (hactual.symm.trans hpreparedCall)
  have hchoiceFrame := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i before choice memory choiceMemory hinput (by
      simpa [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hchoice)
      hoccupied
  obtain ⟨loggedChoice, loggedMemory, hloggedChoice, _, hloggedStatus, hloggedBatch⟩ :=
    record_logged_choice record i logged hlogged
  have hchoiceEq :
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice choiceMemory :
        DeclaredFollowerLocalRound.LocalConfiguration p rate) =
      .ordinary loggedChoice loggedMemory := hchoice.symm.trans hloggedChoice
  injection hchoiceEq with hstateEq hmemoryEq
  subst loggedChoice
  subst loggedMemory
  have hbank : after.downBatch =
      (AffineBatchDecoder.decodeStep p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
        logged.downBatch
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).1).1 := by
    calc
      after.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
            ActiveFollowerDownAcceptance.currentRoundInput p i
              (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
              (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) :=
        hphysicalStep
      _ = ReferenceFollowerDownDecoderReplay.replayDownCall before.downBatch
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
        rw [hcallEq]
      _ = (AffineBatchDecoder.decodeStep p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
          logged.downBatch
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).1).1 := by
        have hloggedBefore : logged.downBatch = before.downBatch :=
          hloggedBatch.trans hchoiceFrame.1
        simp [ReferenceFollowerDownDecoderReplay.replayDownCall, hloggedBefore]
  exact ⟨hactual, hbank, hexpected, hsampleOriginal, hselected, henabled, hrounded⟩

/-- At a genuinely executed quota completion, any surviving computed ordinary
successor has empty pending storage.  Completion is the decoder's size test;
no unique parse or accepted message is needed for this reset. -/
theorem record_executed_down_completion_resets_pending
    (record : Record p rate) (i : Fin (p.m - 1))
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary before memory)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (hbefore : ReferenceFollowerDecoderChronology.downBatchEndpoint before bound)
    (hoccupied : before.status ≠ .unoccupied → before.downBatch.pending = [])
    (callCode : ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val)
    (hquota : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p) :
    after.downBatch.pending = [] := by
  obtain ⟨_, hbank, _, _, _, _, _⟩ := record_executed_down_bank_after_ordinary
    record i before after memory afterMemory bound hinput hafter hbefore hoccupied
    callCode logged cut hcall hlogged hcut hcomparison hpositive
  obtain ⟨_, _, _, _, _, _, _, heligible, _, _⟩ :=
    record_executed_down_call_fields record i callCode logged cut hcall hlogged hcut
      hcomparison hpositive
  have hcompleteEligible : AffineBatchDecoder.eligible
      ((ActiveFollowerDownAcceptance.currentInputExtension p
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).1) := by
    simpa [ActiveFollowerDownAcceptance.currentInputExtension] using heligible
  have hcomplete := AffineBatchDecoder.decodeStep_complete p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
    logged.downBatch (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).1
    hcompleteEligible hquota
  rw [hbank, hcomplete]

/-- With fewer than a quota of positives after the supplied boundary bank,
the literal decoder fold cannot complete another batch: it appends exactly
those positives and preserves the completed history. -/
private theorem foldDownCalls_below_quota
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hbound : bank.pending.length +
      (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length <
        AffineBatchDecoder.quota p) :
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls bank =
      ⟨bank.pending ++ ReferenceFollowerDownDecoderReplay.positiveCallEntries calls,
        bank.completed⟩ := by
  induction calls generalizing bank with
  | nil => simp [ReferenceFollowerDownDecoderReplay.foldDownCalls,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries]
  | cons call rest ih =>
      let trace := ActiveFollowerDownAcceptance.currentInputExtension p call.2
      let first := ReferenceFollowerDownDecoderReplay.positiveCallEntries [call]
      let later := ReferenceFollowerDownDecoderReplay.positiveCallEntries rest
      have hsplit : ReferenceFollowerDownDecoderReplay.positiveCallEntries (call :: rest) =
          first ++ later := by
        simp [ReferenceFollowerDownDecoderReplay.positiveCallEntries, first, later]
      have hbound' : bank.pending.length + first.length + later.length <
          AffineBatchDecoder.quota p := by
        simpa [hsplit, List.length_append, Nat.add_assoc] using hbound
      have hfirst : first = AffineBatchDecoder.positiveAt p trace call.1 := by
        simp [first, ReferenceFollowerDownDecoderReplay.positiveCallEntries, trace,
          ActiveFollowerDownAcceptance.currentInputExtension]
      have hnext : ReferenceFollowerDownDecoderReplay.replayDownCall bank call =
          ⟨bank.pending ++ first, bank.completed⟩ := by
        by_cases heligible : AffineBatchDecoder.eligible (trace call.1)
        · have hfirstEq : first = [AffineBatchDecoder.entry p trace call.1] := by
            rw [hfirst]
            simp [AffineBatchDecoder.positiveAt, heligible]
          have hsmall : (bank.pending ++ [AffineBatchDecoder.entry p trace call.1]).length <
              AffineBatchDecoder.quota p := by
            have hlt : bank.pending.length + 1 + later.length <
                AffineBatchDecoder.quota p := by
              simpa [hfirstEq] using hbound'
            simp only [List.length_append, List.length_singleton]
            omega
          have hsmall' : (bank.pending ++ AffineBatchDecoder.positiveAt p trace call.1).length <
              AffineBatchDecoder.quota p := by
            simpa [AffineBatchDecoder.positiveAt, heligible] using hsmall
          unfold ReferenceFollowerDownDecoderReplay.replayDownCall
          change AffineBatchDecoder.step p trace bank call.1 = _
          unfold AffineBatchDecoder.step
          rw [if_pos hsmall']
          simp [AffineBatchDecoder.positiveAt, heligible, hfirstEq]
        · have hfirstEq : first = [] := by
            rw [hfirst]
            simp [AffineBatchDecoder.positiveAt, heligible]
          have hpending : bank.pending.length < AffineBatchDecoder.quota p := by
            have hlt : bank.pending.length + first.length + later.length <
                AffineBatchDecoder.quota p := hbound'
            rw [hfirstEq] at hlt
            omega
          have hdecode := AffineBatchDecoder.decodeStep_ineligible p trace bank call.1
            hpending (by simpa [trace, ActiveFollowerDownAcceptance.currentInputExtension]
              using heligible)
          unfold ReferenceFollowerDownDecoderReplay.replayDownCall
          rw [hdecode]
          simp [hfirstEq]
      have hboundRest : (bank.pending ++ first).length + later.length <
          AffineBatchDecoder.quota p := by
        rw [List.length_append]
        omega
      change ReferenceFollowerDownDecoderReplay.foldDownCalls rest
          (ReferenceFollowerDownDecoderReplay.replayDownCall bank call) = _
      rw [hnext, ih ⟨bank.pending ++ first, bank.completed⟩ hboundRest]
      simp [hsplit, first, later, List.append_assoc]

private theorem foldCalendar_records_extend
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ suffix,
      (entries.foldl (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        origin hmode) acc).records = acc.records ++ suffix := by
  classical
  induction entries generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      obtain ⟨suffix, hsuffix⟩ := ih
        (acc := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
          origin hmode acc entry)
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        origin hmode acc entry
      let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
      have hround :
          (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
            origin hmode acc entry).records = acc.records ++ [record] := rfl
      refine ⟨record :: suffix, ?_⟩
      rw [hsuffix, hround]
      simp [List.append_assoc]

private theorem connected_split_append
    {initial middle final : ReferenceActivePhysicalHorizon.State p rate}
    {left : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hwhole : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final)
    (hleft : ReferenceActivePhysicalHorizon.Connected initial left middle) :
    ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial middle final with
  | nil =>
      simp only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] at hwhole hleft ⊢
      subst middle
      exact hwhole
  | cons record rest ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hwhole hleft ⊢
      rcases hwhole with ⟨_, hwhole⟩
      rcases hleft with ⟨_, hleft⟩
      exact ih hwhole hleft

private theorem record_downCallObservation_none_of_dagger_internal
    (record : Record p rate) (i : Fin (p.m - 1))
    (hdagger : record.input.state.followers i = .dagger) :
    ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = none := by
  apply (ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_eq_none_iff i record).2
  unfold ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration
  rw [record.output_eq]
  change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
    .dagger
  rw [(ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i]
  rw [ReferenceActiveFeedbackCut.prepareFollowers_apply]
  change (DeclaredFollowerLocalRound.prepare rate i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)).configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.dagger
  rw [hdagger]
  exact (DeclaredFollowerLocalRound.prepare_dagger rate i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)).2

/-- If a follower is daggered at an internal prefix boundary, H's connected
physical suffix keeps every later input daggered; therefore every later
record on that same full run has no executed DOWN call. -/
theorem run_suffix_downCallObservation_none_of_dagger
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (hdagger :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
        (by omega) hmode).finalState.followers i = .dagger) :
    ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start (left + right) hspan hmode).records.drop left,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = none := by
  let runLeft := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
    (by omega) hmode
  let runWhole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (left + right) hspan hmode
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start left right hspan hmode
  have happend' : runWhole = ReferenceActivePhysicalHorizon.foldCalendar initial rows
      selected rewards start (start + left) right (by omega) (by omega) hmode runLeft := by
    simpa [runWhole, runLeft] using happend
  let entries := ReferenceActivePhysicalHorizon.calendarEntries (p := p) start
    (start + left) right (by omega) (by omega)
  obtain ⟨suffix, hrecordsFold⟩ := foldCalendar_records_extend initial rows selected rewards
    start hmode entries runLeft
  have hrecordsFold' :
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
        start (start + left) right (by omega) (by omega) hmode runLeft).records =
        runLeft.records ++ suffix := by
    simpa [ReferenceActivePhysicalHorizon.foldCalendar, entries] using hrecordsFold
  have hrecords : runWhole.records = runLeft.records ++ suffix := by
    rw [happend']
    exact hrecordsFold'
  have hlenLeft := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start left (by omega) hmode
  have hlenLeft' : runLeft.records.length = left := by simpa [runLeft] using hlenLeft
  have hinterval : runWhole.records.drop left = suffix := by
    rw [hrecords, List.drop_append, hlenLeft']
    have hdropLeft : runLeft.records.drop left = [] :=
      List.drop_eq_nil_of_le (le_of_eq hlenLeft')
    simp [hdropLeft]
  have hconnectedWhole := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start (left + right) hspan hmode
  have hconnectedLeft := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start left (by omega) hmode
  have hconnectedSuffix : ReferenceActivePhysicalHorizon.Connected runLeft.finalState suffix
      runWhole.finalState := by
    apply connected_split_append (middle := runLeft.finalState) (left := runLeft.records)
    · rw [← hrecords]
      simpa [runWhole] using hconnectedWhole
    · exact hconnectedLeft
  obtain ⟨_, hrecordDagger⟩ := hconnectedSuffix.follower_dagger i hdagger
  intro record hrecord
  apply record_downCallObservation_none_of_dagger_internal record i
  apply hrecordDagger record
  rw [← hinterval]
  exact hrecord

/-- Between ordinary computed endpoints of one physical run, an empty pending
bank followed by fewer than quota new positives stays pending exactly as the
literal executed-positive suffix; completed batches retain the boundary
history. The initial bank and both endpoints belong to the same run. -/
theorem run_interval_fresh_downBatch_identity
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1))
    (stateA : ReferencePrelaunchFollower.State p rate.eta)
    (memoryA : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryA :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start a (by omega) hmode).finalState.followers i = .ordinary stateA memoryA)
    (stateB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (hordinaryB :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).finalState.followers i = .ordinary stateB memoryB)
    (hreset : stateA.downBatch.pending = [])
    (hsmall : (ReferenceFollowerDownDecoderReplay.actualDownPositives i
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).records.drop a)).length < AffineBatchDecoder.quota p) :
    stateB.downBatch.pending = ReferenceFollowerDownDecoderReplay.actualDownPositives i
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start b hspan hmode).records.drop a) ∧
    stateB.downBatch.completed = stateA.downBatch.completed ∧
    ReferenceFollowerDecoderChronology.downBatchEndpoint stateA (start + a) ∧
    ReferenceFollowerDecoderChronology.downBatchEndpoint stateB (start + b) ∧
    (stateB.status ≠ .unoccupied → stateB.downBatch.pending = []) := by
  let runA := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let runB := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  have hsum : a + (b - a) = b := by omega
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start a (b - a) (by omega) hmode
  have happend' : runB = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + a) (b - a) (by omega) (by omega) hmode runA := by
    simpa [runA, runB, hsum] using happend
  let entries := ReferenceActivePhysicalHorizon.calendarEntries (p := p) start
    (start + a) (b - a) (by omega) (by omega)
  obtain ⟨suffix, hrecordsFold⟩ := foldCalendar_records_extend initial rows selected rewards
    start hmode entries runA
  have hrecordsFold' :
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
        start (start + a) (b - a) (by omega) (by omega) hmode runA).records =
        runA.records ++ suffix := by
    simpa [ReferenceActivePhysicalHorizon.foldCalendar, entries] using hrecordsFold
  have hrecords : runB.records = runA.records ++ suffix := by
    rw [happend']
    exact hrecordsFold'
  have hlenA := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start a (by omega) hmode
  have hlenA' : runA.records.length = a := by simpa [runA] using hlenA
  have hprefix : runA.records = runB.records.take a := by
    rw [hrecords, List.take_append]
    have htaken : runA.records.take a = runA.records :=
      List.take_of_length_le (le_of_eq hlenA')
    simp [htaken, hlenA']
  have hinterval : runB.records.drop a = suffix := by
    rw [hrecords, List.drop_append, hlenA']
    have hdropA : runA.records.drop a = [] := List.drop_eq_nil_of_le (le_of_eq hlenA')
    simp [hdropA]
  obtain ⟨initialFollower, initialMemory, hinitial, _, _, _, _⟩ := hseed i
  have hreplayA := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    initial rows selected rewards start a (by omega) hmode hseed i initialFollower initialMemory
    hinitial stateA memoryA (by simpa [runA] using hordinaryA)
  have hreplayB := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    initial rows selected rewards start b hspan hmode hseed i initialFollower initialMemory
    hinitial stateB memoryB (by simpa [runB] using hordinaryB)
  have hspecA := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial rows selected rewards start a (by omega) hmode hseed i stateA memoryA
    (by simpa [runA] using hordinaryA)
  have hspecB := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial rows selected rewards start b hspan hmode hseed i stateB memoryB
    (by simpa [runB] using hordinaryB)
  have hbank : stateB.downBatch =
      ReferenceFollowerDownDecoderReplay.foldDownCalls
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) stateA.downBatch := by
    calc
      stateB.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i runB.records
          initialFollower.downBatch := hreplayB.1
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix)
            (ReferenceFollowerDownDecoderReplay.replayDownCalls i runA.records
              initialFollower.downBatch) := by
            simp [ReferenceFollowerDownDecoderReplay.replayDownCalls,
              ReferenceFollowerDownDecoderReplay.actualDownCalls, hrecords,
              ReferenceFollowerDownDecoderReplay.foldDownCalls, List.filterMap_append,
              List.foldl_append]
      _ = ReferenceFollowerDownDecoderReplay.foldDownCalls
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) stateA.downBatch := by
            rw [← hreplayA.1]
  have hsmall' : stateA.downBatch.pending.length +
      (ReferenceFollowerDownDecoderReplay.positiveCallEntries
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix)).length <
        AffineBatchDecoder.quota p := by
    have hsmallSuffix :
        (ReferenceFollowerDownDecoderReplay.actualDownPositives i suffix).length <
          AffineBatchDecoder.quota p := by
      rw [← hinterval]
      exact hsmall
    rw [hreset]
    simpa [ReferenceFollowerDownDecoderReplay.actualDownPositives,
      ReferenceFollowerDownDecoderReplay.actualDownCalls,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries] using hsmallSuffix
  have hfold := foldDownCalls_below_quota
    (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) stateA.downBatch hsmall'
  have hfinalBank : stateB.downBatch =
      ⟨stateA.downBatch.pending ++
          ReferenceFollowerDownDecoderReplay.positiveCallEntries
            (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix),
        stateA.downBatch.completed⟩ := hbank.trans hfold
  have hpending : stateB.downBatch.pending =
      stateA.downBatch.pending ++
        ReferenceFollowerDownDecoderReplay.positiveCallEntries
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i suffix) :=
    congrArg (fun batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
      batch.pending) hfinalBank
  have hcompletedProjected :=
    congrArg (fun batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
      batch.completed) hfinalBank
  have hcompleted : stateB.downBatch.completed = stateA.downBatch.completed := by
    simpa using hcompletedProjected
  have hpending' : stateB.downBatch.pending =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i (runB.records.drop a) := by
    rw [hpending, hreset]
    rw [← hinterval]
    rfl
  exact ⟨hpending', hcompleted, hspecA.1, hspecB.1, hspecB.2⟩

/-- On B's retained launch-start fibre, the incoming bank at a genuine
completion boundary is reset by the same generated physical run. The source
rows, original selected index, and whole reward grid are carried unchanged;
the local diagnostic package records execution and quota completion, while
the incoming ordinary branch is selected explicitly. -/
theorem retainedGenerated_completion_pending_empty
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (qJ : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha)
    (halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h qJ r s hsr control0) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2).2.1
    let physicalRun := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (alpha - s)
      (by omega) hmode
    let priorCount := alpha - s - 1
    let priorRun := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s priorCount
      (by omega) hmode
    let calendarEntry : ReferenceActivePhysicalHorizon.CalendarEntry p s :=
      ⟨s + priorCount, by omega, by omega⟩
    let roundInput := ReferenceActivePhysicalHorizon.roundInputAt seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hmode priorRun
      calendarEntry
    let record : Record p rate :=
      ⟨roundInput, ReferenceActivePhysicalStep.step roundInput, rfl⟩
    (∃ after afterMemory,
      physicalRun.finalState.followers i = .ordinary after afterMemory) →
    (∃ callCode logged cut,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = some callCode ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p) →
    ∃ after afterMemory,
      physicalRun.finalState.followers i = .ordinary after afterMemory ∧
      after.downBatch.pending = [] := by
  classical
  dsimp only
  intro hordinary hcompletion
  rcases hordinary with ⟨after, afterMemory, hafter⟩
  obtain ⟨callCode, hcompletion⟩ := hcompletion
  obtain ⟨logged, hcompletion⟩ := hcompletion
  obtain ⟨cut, hcompletion⟩ := hcompletion
  rcases hcompletion with ⟨hcall, hlogged, hcut, hcomparison, hpositive, hquota⟩
  let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  let hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hspec.2.1
  have hseed : ReferenceFollowerDecoderChronology.downBatchSeed seed s := hspec.2.2
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let priorCount := alpha - s - 1
  let priorRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s priorCount
    (by omega) hmode
  let calendarEntry : ReferenceActivePhysicalHorizon.CalendarEntry p s :=
    ⟨s + priorCount, by omega, by omega⟩
  let roundInput := ReferenceActivePhysicalHorizon.roundInputAt seed rows selected rewards s
    hmode priorRun calendarEntry
  let record : Record p rate :=
    ⟨roundInput, ReferenceActivePhysicalStep.step roundInput, rfl⟩
  have hspan : s + (priorCount + 1) ≤ p.T := by omega
  have hsuccessor := ReferenceActivePhysicalHorizon.run_successor_step seed rows selected
    rewards s priorCount hspan hmode
  have hrecordNext : record.output.next.followers i = .ordinary after afterMemory := by
    have hfinal :
        (ReferenceActivePhysicalHorizon.run seed rows selected rewards s
          (priorCount + 1) hspan hmode).finalState.followers i = .ordinary after afterMemory := by
      simpa [show alpha - s = priorCount + 1 by omega] using hafter
    rw [hsuccessor] at hfinal
    simpa [record, roundInput, priorRun, calendarEntry,
      ReferenceActivePhysicalHorizon.foldRound,
      ReferenceActivePhysicalHorizon.roundInputAt] using hfinal
  have hprevOrdinary : ∃ before beforeMemory,
      priorRun.finalState.followers i = .ordinary before beforeMemory := by
    cases hbefore : priorRun.finalState.followers i with
    | dagger =>
        have hnextDagger : record.output.next.followers i = .dagger := by
          rw [record.output_eq]
          exact ReferenceActivePhysicalStep.step_follower_dagger roundInput i (by
            simpa [roundInput, ReferenceActivePhysicalHorizon.roundInputAt, priorRun] using hbefore)
        rw [hnextDagger] at hrecordNext
        cases hrecordNext
    | ordinary before beforeMemory => exact ⟨before, beforeMemory, rfl⟩
  obtain ⟨before, beforeMemory, hbefore⟩ := hprevOrdinary
  have hinput : record.input.state.followers i = .ordinary before beforeMemory := by
    simp [record, roundInput, ReferenceActivePhysicalHorizon.roundInputAt, priorRun, hbefore]
  have hbeforeSpec := ReferenceFollowerDecoderChronology.run_downBatch_spec
    seed rows selected rewards s priorCount (by omega) hmode hseed i before beforeMemory
    (by simpa [priorRun] using hbefore)
  have hreset := record_executed_down_completion_resets_pending record i before after
    beforeMemory afterMemory (s + priorCount) hinput hrecordNext hbeforeSpec.1
    hbeforeSpec.2 callCode logged cut hcall hlogged hcut hcomparison hpositive hquota
  exact ⟨after, afterMemory, hafter, hreset⟩

/-- The retained generated seed supports a fresh pending-store interval on one
and the same source run.  The completion diagnostics name the literal record
at alpha - 1; the ordinary endpoint selectors remain explicit local inputs. -/
theorem retainedGenerated_fresh_downBatch_interval_identity
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (qJ : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha beta : ℕ)
    (halpha : s < alpha) (hab : alpha ≤ beta) (hbetaR : beta ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h qJ r s hsr control0) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2).2.1
    let runAlpha := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (alpha - s)
      (by omega) hmode
    let runBeta := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (beta - s)
      (by omega) hmode
    let priorCount := alpha - s - 1
    let priorRun := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s priorCount
      (by omega) hmode
    let calendarEntry : ReferenceActivePhysicalHorizon.CalendarEntry p s :=
      ⟨s + priorCount, by omega, by omega⟩
    let roundInput := ReferenceActivePhysicalHorizon.roundInputAt seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hmode priorRun
      calendarEntry
    let record : Record p rate :=
      ⟨roundInput, ReferenceActivePhysicalStep.step roundInput, rfl⟩
    (∃ stateA memoryA,
      runAlpha.finalState.followers i = .ordinary stateA memoryA) →
    (∃ stateB memoryB,
      runBeta.finalState.followers i = .ordinary stateB memoryB) →
    (∃ callCode logged cut,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
        some callCode ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p) →
    (ReferenceFollowerDownDecoderReplay.actualDownPositives i
      (runBeta.records.drop (alpha - s))).length < AffineBatchDecoder.quota p →
    ∃ stateA memoryA stateB memoryB,
      runAlpha.finalState.followers i = .ordinary stateA memoryA ∧
      runBeta.finalState.followers i = .ordinary stateB memoryB ∧
      stateB.downBatch.pending = ReferenceFollowerDownDecoderReplay.actualDownPositives i
        (runBeta.records.drop (alpha - s)) ∧
      stateB.downBatch.completed = stateA.downBatch.completed ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateA alpha ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateB beta ∧
      (stateB.status ≠ .unoccupied → stateB.downBatch.pending = []) := by
  classical
  dsimp only
  intro hordinaryA hordinaryB hcompletion hsmall
  rcases hordinaryA with ⟨stateA, memoryA, hordinaryA⟩
  rcases hordinaryB with ⟨stateB, memoryB, hordinaryB⟩
  have hreset := retainedGenerated_completion_pending_empty
    rewards C_star C_h qJ r s hsr control0 i alpha halpha (by omega) x
    ⟨stateA, memoryA, hordinaryA⟩ hcompletion
  rcases hreset with ⟨resetState, resetMemory, hresetOrdinary, hresetPending⟩
  have hsameReset : resetState = stateA ∧ resetMemory = memoryA := by
    have heq := hresetOrdinary.symm.trans hordinaryA
    injection heq with hstate hmemory
    exact ⟨hstate, hmemory⟩
  rcases hsameReset with ⟨hstateEq, hmemoryEq⟩
  have hresetPendingA : stateA.downBatch.pending = [] := by
    rw [← hstateEq]
    exact hresetPending
  let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  let hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hspec.2.1
  have hseed : ReferenceFollowerDecoderChronology.downBatchSeed seed s := hspec.2.2
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let runAlpha := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (alpha - s) (by omega) hmode
  let runBeta := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (beta - s) (by omega) hmode
  have hinterval := run_interval_fresh_downBatch_identity seed rows selected rewards s
    (alpha - s) (beta - s) (by omega) (by omega) hmode hseed i stateA memoryA
    (by simpa [runAlpha, rows, selected] using hordinaryA) stateB memoryB
    (by simpa [runBeta, rows, selected] using hordinaryB) hresetPendingA
    (by simpa [runBeta, rows, selected] using hsmall)
  rcases hinterval with ⟨hpending, hcompleted, hendpointA, hendpointB, hoccupiedB⟩
  have hendpointA' :
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateA alpha := by
    simpa only [show s + (alpha - s) = alpha by omega] using hendpointA
  have hendpointB' :
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateB beta := by
    simpa only [show s + (beta - s) = beta by omega] using hendpointB
  exact ⟨stateA, memoryA, stateB, memoryB, hordinaryA, hordinaryB,
    hpending, hcompleted, hendpointA', hendpointB', hoccupiedB⟩

/-- A physical round entered by a daggered follower prepares dagger absence in
the actual retained code, so it has no administrative call either. -/
theorem record_downCallObservation_none_of_dagger
    (record : Record p rate) (i : Fin (p.m - 1))
    (hdagger : record.input.state.followers i = .dagger) :
    ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = none := by
  exact record_downCallObservation_none_of_dagger_internal record i hdagger

/-- Every actual record after a run starts daggered has no DOWN diagnostic
call; the conclusion follows from H's retained connected-run dagger chain. -/
theorem run_downCallObservation_none_of_dagger
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) (hdagger : initial.followers i = .dagger) :
    ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = none := by
  obtain ⟨_, hrecords⟩ := ReferenceActivePhysicalHorizon.run_follower_dagger
    initial rows selected rewards start count hspan hmode i hdagger
  intro record hrecord
  exact record_downCallObservation_none_of_dagger record i (hrecords record hrecord)

end Bandits.Support.ReferenceExecutedDownBankRecurrence

end
