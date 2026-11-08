/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerDecoderChronology

import Lean.Elab.Tactic.Omega

/-!
# Actual DOWN decoder calls in the postlaunch physical run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-48,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:248-275,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`.

Each retained call below is formed from the actual prepared follower choice,
row, time, and own quantized physical observation in a
`ReferenceActivePhysicalHorizon.RoundRecord`.  A missing ordinary choice is
represented by `none`.  The replay uses the existing affine decoder and its
current-input extension; it supplies no separate observation trace.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceFollowerDecoderChronology

namespace Bandits.Support.ReferenceFollowerDownDecoderReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Call (p : Parameters) := Fin p.T ×
  AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p)

variable {p : Parameters} {rate : RateInput p}

/-- The actual choice configuration retained by PREPARE for follower `i`. -/
def preparedChoiceConfiguration
    (record : Record p rate) (i : Fin (p.m - 1)) :=
  (record.output.preparation.followers.followers i).configuration

/-- The actual row retained by PREPARE for follower `i`. -/
def preparedChoiceRow
    (record : Record p rate) (i : Fin (p.m - 1)) :=
  (record.output.preparation.followers.followers i).row

/-- The actual calendar coordinate retained by PREPARE for follower `i`. -/
def preparedChoiceTime
    (record : Record p rate) (i : Fin (p.m - 1)) :=
  (record.output.preparation.followers.followers i).time

/-- The follower's own physical observation, taken from the computed feedback
vector at its actual player coordinate. -/
def preparedOwnObservation
    (record : Record p rate) (i : Fin (p.m - 1)) :=
  record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)

/-- The actual prepared DOWN input, when PREPARE retained an ordinary choice
configuration.  Its fields are exactly those of
`ActiveFollowerDownAcceptance.currentRoundInput`; in particular the sample,
selection bit, enable bit, and quantized reward are not reconstructed from a
separate trace. -/
def actualDownCall (i : Fin (p.m - 1))
    (record : Record p rate) : Option (Call p) :=
  match preparedChoiceConfiguration record i with
  | .dagger => none
  | .ordinary choice _ =>
      some (preparedChoiceTime record i,
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (preparedChoiceRow record i) (preparedChoiceTime record i)
          (preparedOwnObservation record i) rate choice)

/-- Filter the actual retained records only by the honest optional prepared
configuration above.  The endpoint theorem below proves this omits no record
whenever the computed endpoint is ordinary. -/
def actualDownCalls (i : Fin (p.m - 1))
    (records : List (Record p rate)) : List (Call p) :=
  records.filterMap (actualDownCall i)

/-- Replay a stamped actual input by calling the existing affine decoder. -/
def replayDownCall (batch : AffineBatchDecoder.State p.T
    (AffineBatchDecoder.width p)) (call : Call p) :=
  (AffineBatchDecoder.decodeStep p
    (ActiveFollowerDownAcceptance.currentInputExtension p call.2) batch call.1).1

/-- The fold operation on a literal list of stamped decoder inputs. -/
def foldDownCalls (calls : List (Call p))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :=
  calls.foldl replayDownCall initial

/-- The whole-bank fold over the actual optional calls retained in records. -/
def replayDownCalls (i : Fin (p.m - 1))
    (records : List (Record p rate))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :=
  foldDownCalls (actualDownCalls i records) initial

/-- The exact stamped positive entries contributed by a literal list of calls. -/
def positiveCallEntries (calls : List (Call p)) :
    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
  calls.flatMap fun call =>
    AffineBatchDecoder.positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1

/-- The exact stamped positive entries contributed by the retained calls. -/
def actualDownPositives (i : Fin (p.m - 1))
    (records : List (Record p rate)) :=
  positiveCallEntries (actualDownCalls i records)

/-- A call made from an actual ordinary prepared configuration retains exactly
the four current-round fields supplied by the accepted local input adapter. -/
theorem actualDownCall_ordinary
    (record : Record p rate) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : preparedChoiceConfiguration record i = .ordinary choice memory) :
    actualDownCall i record = some
      (preparedChoiceTime record i,
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (preparedChoiceRow record i) (preparedChoiceTime record i)
          (preparedOwnObservation record i) rate choice) := by
  simp [actualDownCall, hchoice]

/-- The eligibility test of the retained actual input is the literal selected
DOWN, unoccupied-at-choice, positive-own-feedback condition. -/
theorem actualDownCall_eligible_iff
    (record : Record p rate) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta) :
    AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i
          (preparedChoiceRow record i) (preparedChoiceTime record i)
          (preparedOwnObservation record i) rate choice) ↔
      ActiveFollowerDownAcceptance.downSelected p i
          (preparedChoiceRow record i) (preparedChoiceTime record i) ∧
        choice.status = .unoccupied ∧
        0 < (preparedOwnObservation record i).val.val := by
  exact ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i
    (preparedChoiceRow record i) (preparedChoiceTime record i)
    (preparedOwnObservation record i) rate choice

/-- A successful reference DOWN cut stores the complete state returned by its
literal current decoder call.  The rejection, ambiguity, mismatch, and
accepted-recovery branches all preserve this same returned bank. -/
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

/-- A successful local record stage advances the exact decoder call on an
unoccupied choice and frames the bank through occupied service. -/
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

/-- A successful release and end-of-round stage changes no decoder bank. -/
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

/-- If an actual follower observer returns an ordinary configuration, its
PREPARE, record, release, and finish calls all succeeded. -/
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

/-- Exact one-record whole-bank identity from the actual ordinary physical
prestate to its actual ordinary successor. PREPARE preserves the whole bank;
the literal prepared current input drives the existing decoder on an
unoccupied choice, while occupied service and all other ineligible calls
frame it. -/
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
      preparedChoiceConfiguration record i = .ordinary choice choiceMemory ∧
      actualDownCall i record = some
        (preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (preparedChoiceRow record i) (preparedChoiceTime record i)
            (preparedOwnObservation record i) rate choice) ∧
      after.downBatch = replayDownCall before.downBatch
        (preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (preparedChoiceRow record i) (preparedChoiceTime record i)
            (preparedOwnObservation record i) rate choice) := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := preparedOwnObservation record i
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
    simpa [view, prepared, observation, preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hobserve
  obtain ⟨preparedState, preparedMemory, postRecord, hpreparedProjection, hrecord, hrelease⟩ :=
    finishFollower_ordinary_projection view prepared observation after afterMemory hfinish
  let choice := preparedState
  let choiceMemory := preparedMemory
  have hprepared : preparedChoiceConfiguration record i = .ordinary choice choiceMemory := by
    exact hpreparedProjection
  have hframe := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i before choice memory choiceMemory hinput hprepared hoccupied
  have hprep := ReferenceFollowerDecoderChronology.run_prepared_follower_downBatch_spec
    record i before choice memory choiceMemory bound hinput hprepared hbefore hoccupied
  have hpreparedAlignment := record.output.preparation.follower_alignment i
  have hpreparedIndex : prepared.follower = i := by
    exact hpreparedAlignment.2.1
  have hrecordBank := recordFollower_actualDecode_bank view prepared.follower prepared.row
    prepared.activation prepared.time prepared.active prepared.arm observation choice postRecord
    hprep.1.1 hrecord
  rw [hpreparedIndex] at hrecordBank
  have hreleaseBank := releaseAndFinish_downBatch_frame prepared.follower prepared.row prepared.time
    observation choice choiceMemory postRecord after afterMemory hrelease
  have hbatch : choice.downBatch = before.downBatch := hframe.1
  have hcall := actualDownCall_ordinary record i choice choiceMemory hprepared
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
      replayDownCall before.downBatch
        (prepared.time, ActiveFollowerDownAcceptance.currentRoundInput p i prepared.row
          prepared.time observation rate choice) := by
    unfold ActiveFollowerDownAcceptance.currentDecodeStep replayDownCall
    rw [← hbatch]
  calc
    after.downBatch =
        (ActiveFollowerDownAcceptance.currentDecodeStep p i prepared.row prepared.time
          observation rate choice).1 := hnext
    _ = replayDownCall before.downBatch
        (prepared.time, ActiveFollowerDownAcceptance.currentRoundInput p i prepared.row
          prepared.time observation rate choice) := hcallStep

/-- The prepared time is the exact physical input time retained by the
canonical RoundRecord. -/
theorem preparedChoiceTime_eq_recordTime
    (record : Record p rate) (i : Fin (p.m - 1)) :
    preparedChoiceTime record i = record.input.time := by
  have htime := (record.output.preparation.follower_alignment i).2.2.1
  simpa only [preparedChoiceTime] using htime

/-- If the actual round successor is ordinary, its retained prepared follower
configuration is ordinary, so the optional projection really has a call. -/
private theorem preparedChoiceConfiguration_of_ordinary_successor
    (record : Record p rate) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary state memory) :
    ∃ choice choiceMemory,
      preparedChoiceConfiguration record i = .ordinary choice choiceMemory := by
  let prepared := record.output.preparation.followers.followers i
  let observation := preparedOwnObservation record i
  let view := record.output.preparation.coordinator.downView
  have hstep : record.output = ReferenceActivePhysicalStep.step record.input := record.output_eq
  have hobserve :
      (record.output.preparation.observeFollower i).configuration = .ordinary state memory := by
    have hnext' := hnext
    rw [hstep] at hnext'
    rw [hstep]
    simpa [ReferenceActivePhysicalStep.step] using hnext'
  have hfinish : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary state memory := by
    simpa [view, prepared, observation, preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hobserve
  obtain ⟨choice, choiceMemory, _, hchoice, _, _⟩ :=
    finishFollower_ordinary_projection view prepared observation state memory hfinish
  exact ⟨choice, choiceMemory, hchoice⟩

/-- Dagger absorption along the actual connected horizon means an ordinary
endpoint has ordinary prepared choice configurations at every retained round.
This proves that `actualDownCalls` omits no round in this endpoint scope. -/
private theorem connected_ordinary_configurations
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (Record p rate)} (i : Fin (p.m - 1))
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfinal : ∃ state memory,
      final.followers i = .ordinary state memory) :
    (∃ state memory, initial.followers i = .ordinary state memory) ∧
      ∀ record ∈ records,
        ∃ choice choiceMemory,
          preparedChoiceConfiguration record i = .ordinary choice choiceMemory := by
  induction records generalizing initial final with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hconnected
      subst final
      exact ⟨hfinal, by simp⟩
  | cons record rest ih =>
      rcases hconnected with ⟨hinput, htail⟩
      have htailResult := ih htail hfinal
      rcases htailResult with ⟨hmiddleExists, htailChoices⟩
      obtain ⟨middle, middleMemory, hmiddle⟩ := hmiddleExists
      have hinputOrdinary : ∃ state memory,
          initial.followers i = .ordinary state memory := by
        cases hbefore : record.input.state.followers i with
        | dagger =>
            have hdagger : record.output.next.followers i = .dagger := by
              rw [record.output_eq]
              exact ReferenceActivePhysicalStep.step_follower_dagger record.input i hbefore
            rw [hdagger] at hmiddle
            cases hmiddle
        | ordinary state memory =>
            refine ⟨state, memory, ?_⟩
            rw [← hinput]
            exact hbefore
      have hrecordChoice := preparedChoiceConfiguration_of_ordinary_successor
        record i middle middleMemory hmiddle
      refine ⟨hinputOrdinary, ?_⟩
      intro current hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hrecordChoice
      · exact htailChoices current hmem

/-- The actual prepared-call list keeps the physical time at each record's
real input coordinate. -/
private theorem actualDownCalls_time_values
    (i : Fin (p.m - 1)) (records : List (Record p rate))
    (hordinary : ∀ record ∈ records,
      ∃ choice memory,
        preparedChoiceConfiguration record i = .ordinary choice memory) :
    (actualDownCalls i records).map Prod.fst =
      records.map (fun record => record.input.time) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      obtain ⟨choice, memory, hchoice⟩ := hordinary record (by simp)
      have hcall := actualDownCall_ordinary record i choice memory hchoice
      have htail : ∀ current ∈ rest,
          ∃ choice memory,
            preparedChoiceConfiguration current i = .ordinary choice memory := by
        intro current hmem
        exact hordinary current (by simp [hmem])
      have htailMap :
          (List.filterMap (actualDownCall i) rest).map Prod.fst =
            rest.map (fun current => current.input.time) := by
        simpa only [actualDownCalls] using ih htail
      simp only [actualDownCalls, List.filterMap_cons, hcall, List.map_cons]
      rw [htailMap]
      simp only [preparedChoiceTime_eq_recordTime]

/-- Every literal affine fold preserves the decoder size domain and appends
exactly the positive stamped entries of its own current inputs. -/
private theorem foldDownCalls_spec
    (calls : List (Call p))
    (initial : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hinitial : ReferenceFollowerDecoderChronology.downBatchWellFormed initial) :
    ReferenceFollowerDecoderChronology.downBatchWellFormed (foldDownCalls calls initial) ∧
      AffineBatchDecoder.collected (foldDownCalls calls initial) =
        AffineBatchDecoder.collected initial ++ positiveCallEntries calls := by
  induction calls generalizing initial with
  | nil =>
      exact ⟨hinitial, by simp [foldDownCalls, positiveCallEntries]⟩
  | cons call rest ih =>
      let next := replayDownCall initial call
      have hstep := AffineBatchDecoder.step_spec p
        (ActiveFollowerDownAcceptance.currentInputExtension p call.2)
        initial call.1 hinitial.1 hinitial.2
      have hnext : ReferenceFollowerDecoderChronology.downBatchWellFormed next ∧
          AffineBatchDecoder.collected next =
            AffineBatchDecoder.collected initial ++
              AffineBatchDecoder.positiveAt p
                (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
        refine ⟨?_, ?_⟩
        · exact ⟨by simpa [next, replayDownCall, AffineBatchDecoder.decodeStep] using hstep.1,
            by simpa [next, replayDownCall, AffineBatchDecoder.decodeStep] using hstep.2.1⟩
        · simpa [next, replayDownCall, AffineBatchDecoder.decodeStep] using hstep.2.2
      obtain ⟨hrestWell, hrestCollected⟩ := ih next hnext.1
      refine ⟨hrestWell, ?_⟩
      change AffineBatchDecoder.collected (foldDownCalls rest next) =
        AffineBatchDecoder.collected initial ++
          (AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 ++
            positiveCallEntries rest)
      rw [hrestCollected, hnext.2]
      exact List.append_assoc _ _ _

/-- The actual connected horizon's ordinary endpoint guarantees that every
record contributes exactly one honest optional call. This also gives complete
calendar correspondence; no trace is supplied or reconstructed. -/
theorem run_downCall_calendar_correspondence
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.followers i = .ordinary state memory) :
    (actualDownCalls i
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records).map
          Prod.fst =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          (fun record => record.input.time) ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          (fun record => record.input.time.val) = ReferenceActivePhysicalHorizon.calendar start count ∧
      ∀ record ∈
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
        ∃ choice choiceMemory,
          preparedChoiceConfiguration record i = .ordinary choice choiceMemory ∧
          (AffineBatchDecoder.eligible
              (ActiveFollowerDownAcceptance.currentRoundInput p i
                (preparedChoiceRow record i) (preparedChoiceTime record i)
                (preparedOwnObservation record i) rate choice) ↔
            ActiveFollowerDownAcceptance.downSelected p i
              (preparedChoiceRow record i) (preparedChoiceTime record i) ∧
            choice.status = .unoccupied ∧
            0 < (preparedOwnObservation record i).val.val) := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected
    rewards start count hspan hmode
  have hordinaryFinal : ∃ choice choiceMemory,
      execution.finalState.followers i = .ordinary choice choiceMemory :=
    ⟨state, memory, by simpa [execution] using hordinary⟩
  obtain ⟨_, hchoices⟩ := connected_ordinary_configurations i hconnected hordinaryFinal
  refine ⟨?_, ?_, ?_⟩
  · simpa [execution] using actualDownCalls_time_values i execution.records hchoices
  · exact ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
      start count hspan hmode
  · intro record hrecord
    obtain ⟨choice, choiceMemory, hchoice⟩ := hchoices record hrecord
    exact ⟨choice, choiceMemory, hchoice,
      actualDownCall_eligible_iff record i choice⟩

/-- Exact replay identity for the entire follower DOWN bank at any ordinary
computed endpoint. The initial bank is taken from the fixed actual initial
configuration certified by `downBatchSeed`; calls come only from this run's
retained records. -/
theorem run_downBatch_replay
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1))
    (initialFollower : ReferencePrelaunchFollower.State p rate.eta)
    (initialMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinitial : initial.followers i = .ordinary initialFollower initialMemory)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.followers i = .ordinary state memory) :
    state.downBatch = replayDownCalls i
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records
        initialFollower.downBatch ∧
      AffineBatchDecoder.collected state.downBatch =
        AffineBatchDecoder.collected initialFollower.downBatch ++
          actualDownPositives i
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological state.downBatch ∧
      ∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
        entry.time.val < start + count := by
  obtain ⟨seedState, seedMemory, hseedConfig, hseedStatus, hseedWell,
      hseedChronological, hseedTimes⟩ := hseed i
  have hseedConfigEq :
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary seedState seedMemory :
        DeclaredFollowerLocalRound.LocalConfiguration p rate) =
        .ordinary initialFollower initialMemory := hseedConfig.symm.trans hinitial
  injection hseedConfigEq with hseedStateEq hseedMemoryEq
  subst seedState
  subst seedMemory
  induction count generalizing state memory with
  | zero =>
      have hzero := ReferenceActivePhysicalHorizon.run_zero_final initial rows selected
        rewards start hspan hmode
      have hzeroRecords := ReferenceActivePhysicalHorizon.run_zero_records initial rows selected
        rewards start hspan hmode
      have hstateEq : state = initialFollower := by
        have hconfigEq :
            (DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory :
              DeclaredFollowerLocalRound.LocalConfiguration p rate) =
              .ordinary initialFollower initialMemory := by
          calc
            _ = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                start 0 hspan hmode).finalState.followers i := hordinary.symm
            _ = initial.followers i := by rw [hzero]
            _ = .ordinary initialFollower initialMemory := hinitial
        injection hconfigEq with hstateEq hmemoryEq
      subst state
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hzeroRecords, replayDownCalls, actualDownCalls, foldDownCalls]
      · simp [hzeroRecords, actualDownPositives, actualDownCalls,
          positiveCallEntries]
      · simpa [ReferenceFollowerDecoderChronology.downCollectedChronological] using
          hseedChronological
      · intro entry hentry
        exact lt_of_lt_of_le (hseedTimes entry hentry) (Nat.le_refl _)
  | succ count ih =>
      have hprevSpan : start + count ≤ p.T := by omega
      let acc := ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hprevSpan hmode
      let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
        ⟨start + count, by omega, by omega⟩
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        start hmode acc entry
      let record : Record p rate :=
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
      have hsuccessor := ReferenceActivePhysicalHorizon.run_successor_step initial rows
        selected rewards start count hspan hmode
      have hrecordNext : record.output.next.followers i = .ordinary state memory := by
        have hfinal := hordinary
        rw [hsuccessor] at hfinal
        simpa [record, input, acc, entry, ReferenceActivePhysicalHorizon.foldRound,
          ReferenceActivePhysicalHorizon.roundInputAt] using hfinal
      cases hbefore : acc.finalState.followers i with
      | dagger =>
          have hnextDagger : record.output.next.followers i = .dagger := by
            rw [record.output_eq]
            exact ReferenceActivePhysicalStep.step_follower_dagger input i (by
              simpa [input, ReferenceActivePhysicalHorizon.roundInputAt, acc] using hbefore)
          rw [hnextDagger] at hrecordNext
          cases hrecordNext
      | ordinary before beforeMemory =>
          have hbeforeOrdinary :
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                start count hprevSpan hmode).finalState.followers i =
                  .ordinary before beforeMemory := by
            simpa [acc] using hbefore
          have hprefix := ih hprevSpan before beforeMemory hbeforeOrdinary
          have hbeforeEndpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
            initial rows selected rewards start count hprevSpan hmode hseed i before beforeMemory
            hbeforeOrdinary
          have hinput : record.input.state.followers i = .ordinary before beforeMemory := by
            simp [record, input, ReferenceActivePhysicalHorizon.roundInputAt, acc, hbefore]
          obtain ⟨choice, choiceMemory, hchoice, hcall, hstepBank⟩ :=
            record_downBatch_actual_replay_step record i before state beforeMemory memory
              (start + count) hinput hrecordNext
              hbeforeEndpoint.1 hbeforeEndpoint.2
          have hrecords :
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                start (count + 1) hspan hmode).records = acc.records ++ [record] := by
            have hfold := ReferenceActivePhysicalHorizon.foldRound_equations
              initial rows selected rewards start hmode acc entry
            rw [hsuccessor]
            exact hfold.2
          have hcalls : actualDownCalls i
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                start (count + 1) hspan hmode).records =
                actualDownCalls i acc.records ++
                  [(preparedChoiceTime record i,
                    ActiveFollowerDownAcceptance.currentRoundInput p i
                      (preparedChoiceRow record i) (preparedChoiceTime record i)
                      (preparedOwnObservation record i) rate choice)] := by
            rw [hrecords]
            simp only [actualDownCalls, List.filterMap_append,
              List.filterMap_cons, hcall, List.filterMap_nil]
          have hidentity : state.downBatch =
              replayDownCalls i
                (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                  start (count + 1) hspan hmode).records initialFollower.downBatch := by
            calc
              state.downBatch = replayDownCall before.downBatch
                  (preparedChoiceTime record i,
                    ActiveFollowerDownAcceptance.currentRoundInput p i
                      (preparedChoiceRow record i) (preparedChoiceTime record i)
                      (preparedOwnObservation record i) rate choice) := hstepBank
              _ = replayDownCall
                  (replayDownCalls i acc.records initialFollower.downBatch)
                  (preparedChoiceTime record i,
                    ActiveFollowerDownAcceptance.currentRoundInput p i
                      (preparedChoiceRow record i) (preparedChoiceTime record i)
                      (preparedOwnObservation record i) rate choice) := by
                    rw [← hprefix.1]
              _ = replayDownCalls i
                  (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                    start (count + 1) hspan hmode).records initialFollower.downBatch := by
                    change replayDownCall
                        (foldDownCalls (actualDownCalls i acc.records) initialFollower.downBatch)
                        (preparedChoiceTime record i,
                          ActiveFollowerDownAcceptance.currentRoundInput p i
                            (preparedChoiceRow record i) (preparedChoiceTime record i)
                            (preparedOwnObservation record i) rate choice) =
                      foldDownCalls (actualDownCalls i
                        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                          start (count + 1) hspan hmode).records) initialFollower.downBatch
                    rw [hcalls]
                    simp [foldDownCalls, List.foldl_append]
          have hbatchSpec := foldDownCalls_spec
            (actualDownCalls i
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards
                start (count + 1) hspan hmode).records)
            initialFollower.downBatch hseedWell
          have hendpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
            initial rows selected rewards start (count + 1) hspan hmode hseed i state memory
            hordinary
          refine ⟨hidentity, ?_, hendpoint.1.2.1, hendpoint.1.2.2⟩
          rw [hidentity]
          simpa [actualDownPositives, replayDownCalls] using hbatchSpec.2

/-- At every ordinary computed prefix, all entries already pending are
strictly earlier than the next physical calendar coordinate. This is the
old-batch/new-input ordering needed when applying the next actual call. -/
theorem run_downBatch_pending_before_next_input
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.followers i = .ordinary state memory) :
    ∀ entry ∈ state.downBatch.pending, entry.time.val < start + count := by
  have hendpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial rows selected rewards start count hspan hmode hseed i state memory hordinary
  intro entry hentry
  apply hendpoint.1.2.2
  rw [AffineBatchDecoder.collected]
  exact List.mem_append_right _ hentry

/-- Specialization to the actual launched initial state.  It consumes the
accepted launch seed for the whole decoder bank and derives the horizon's
activation condition from the launch adapter's clipped `blockStop` bound.
Every in-range prefix, including count zero and an endpoint at `p.T`, is
covered by `hspan`. -/
theorem run_downBatch_replay_ofActualLaunchedBoundary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (rows : CompletePublicTable.CompleteRows p)
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + count ≤ p.T)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
      count hspan (by
        intro j
        exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
          hlaunched j)).finalState.followers i = .ordinary state memory) :
    ∃ initialFollower initialMemory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary initialFollower initialMemory ∧
      state.downBatch = replayDownCalls i
        (ReferenceActivePhysicalHorizon.run
          (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
            b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
          rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
          count hspan (by
            intro j
            exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
              source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
              hlaunched j)).records initialFollower.downBatch ∧
      AffineBatchDecoder.collected state.downBatch =
        AffineBatchDecoder.collected initialFollower.downBatch ++
          actualDownPositives i
            (ReferenceActivePhysicalHorizon.run
              (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star
                C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
              rows (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
              count hspan (by
                intro j
                exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
                  source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
                  learnerSeed hlaunched j)).records ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological state.downBatch ∧
      ∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
        entry.time.val < BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h) + count := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
  have hseed := ReferenceFollowerDecoderChronology.ofActualLaunchedBoundary_downBatchSeed
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro j
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched j
  obtain ⟨initialFollower, initialMemory, hinitial, _, _, _, _⟩ := hseed i
  have hreplay := run_downBatch_replay initial rows
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    hseed i initialFollower initialMemory hinitial state memory (by simpa [initial, start] using hordinary)
  refine ⟨initialFollower, initialMemory, hinitial, hreplay.1, ?_, hreplay.2.2.1, ?_⟩
  · simpa [initial, start] using hreplay.2.1
  · simpa [start] using hreplay.2.2.2

end Bandits.Support.ReferenceFollowerDownDecoderReplay

end
