/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOccupiedServiceForward

import Lean.Elab.Tactic.Omega

/-!
# Actual complete-suffix unoccupied nonaccepting transition

From an ordinary actual CHOICE with an unoccupied follower and the literal
nonaccepting branch test, construct the complete logging, decoder, receiver,
release, and finish transition on that same physical round.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceDownReception
open Bandits.Support.AffineBatchDecoder

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

namespace Bandits.Support.ReferenceCompleteUnoccupiedNonacceptingForward

/-- The actual complete-suffix unoccupied-at-choice nonaccepting receiver
branch performs one successful sparse log, keeps the exact ordinary decoder
diagnostics, and successfully completes the no-release/no-proposal-read tail.
The sole logical branch input is the negation of the literal selected/raw/
ordinary-acceptance conjunction; all local domains and chronology are derived
from this record's actual input and PREPARE transition. -/
theorem complete_ordinary_unoccupied_nonaccepting_forward
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
    let r := R[k.val]
    ∀ (i : Fin (p.m - 1)),
    let f := ReferenceFollowerFixedReply.actualChoice r i
    ∀ (choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    f.configuration = .ordinary choice memory →
    choice.status = .unoccupied →
    let t := r.input.time
    let e := t.val
    let row := r.input.row
    let activation := r.input.state.activations i
    let own := r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := r.output.preparation.coordinator.downView
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
    let expected := ReferenceDownReception.expectedDownFlatWord view i row t
    let parsed := ReferenceDownReception.ordinaryParse p rate decoded.2
    ¬ (ActiveFollowerDownAcceptance.downSelected p i row t ∧
      decoded.2 = expected ∧
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed) →
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i row activation t (f.arm, own) choice =
        .ok logged ∧
      logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i row activation t
        (f.arm, own) ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
      ActiveFollowerLifecycle.localStateDomainValid logged ∧
      (logged.lastDown = choice.lastDown ∧ logged.S = choice.S ∧
        logged.delta = choice.delta ∧ logged.backlog = choice.backlog ∧
        logged.status = choice.status ∧ logged.downBatch = choice.downBatch ∧
        logged.initializationFailure = choice.initializationFailure) ∧
      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ logged.buffer, saved.calendarRound ≤ e + 1) ∧
      (let cut := ReferenceDownReception.referenceDownCut p view i row t own rate logged
       let next := @ite _ (ActiveFollowerDownAcceptance.downSelected p i row t)
         (Classical.propDecidable _) {logged with downBatch := decoded.1} logged
       DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
       DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice memory next =
         .ok (next, memory) ∧
       next.status = .unoccupied ∧
       next.lastDown = choice.lastDown ∧ next.S = choice.S ∧
       next.delta = choice.delta ∧ next.backlog = choice.backlog ∧
       next.buffer = logged.buffer ∧
       next.initializationFailure = choice.initializationFailure ∧
       ActiveFollowerLifecycle.localStateDomainValid next ∧
       ReferenceFollowerDecoderChronology.downBatchEndpoint next (e + 1) ∧
       (ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 ∧
        AffineBatchDecoder.collected decoded.1 =
          AffineBatchDecoder.collected choice.downBatch ++
            AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p
                (ActiveFollowerDownAcceptance.currentRoundInput p i row t own rate choice)) t) ∧
       (∀ _hselected : ActiveFollowerDownAcceptance.downSelected p i row t,
          own.val.val = 0 → decoded = (choice.downBatch, none)) ∧
       cut.expectedWord = expected ∧
       (cut.outcome = .skipped logged .notSelectedDown ∧
          cut.raw = none ∧ cut.filteredRaw = none ∧ cut.ordinaryParse = none ∧
          ¬ cut.ordinaryAcceptance ∧ cut.rawComparison = none ∨
        (ActiveFollowerDownAcceptance.downSelected p i row t ∧
          ((decoded.2 ≠ expected ∧
              cut.outcome = .decodeOrParseRejected logged
                {logged with downBatch := decoded.1} decoded.2 ∧
              cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
              cut.ordinaryParse = parsed ∧
              cut.ordinaryAcceptance =
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged parsed ∧
              cut.rawComparison = some false) ∨
            (decoded.2 = expected ∧ parsed = none ∧
              cut.outcome = .decodeOrParseRejected logged
                {logged with downBatch := decoded.1} decoded.2 ∧
              cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
              cut.ordinaryParse = none ∧ ¬ cut.ordinaryAcceptance ∧
              cut.rawComparison = some true) ∨
            (decoded.2 = expected ∧ ∃ M,
              parsed = some M ∧
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed ∧
              cut.outcome = .parsedButUnaccepted logged
                {logged with downBatch := decoded.1} decoded.2 M ∧
              cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
              cut.ordinaryParse = parsed ∧ ¬ cut.ordinaryAcceptance ∧
              cut.rawComparison = some true)))) ∧
       r.output.followers i = ⟨.ordinary next memory, none, some logged, some cut⟩ ∧
       r.output.next.followers i = .ordinary next memory) := by
  classical
  dsimp only
  intro k i choice memory hchoice hu hn
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let r := R[k.val]
  let f := ReferenceFollowerFixedReply.actualChoice r i
  let t := r.input.time
  let e := t.val
  let row := r.input.row
  let activation := r.input.state.activations i
  let own := r.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := r.output.preparation.coordinator.downView
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
  let expected := ReferenceDownReception.expectedDownFlatWord view i row t
  let parsed := ReferenceDownReception.ordinaryParse p rate decoded.2
  change f.configuration = .ordinary choice memory at hchoice
  change ¬ (ActiveFollowerDownAcceptance.downSelected p i row t ∧
    decoded.2 = expected ∧
    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed) at hn
  let hprepared := hchoice
  change (r.output.preparation.followers.followers i).configuration =
    .ordinary choice memory at hprepared
  have hprepare :
      (DeclaredFollowerLocalRound.prepare rate i row activation t (r.input.active i)
        (r.input.state.followers i)).configuration = .ordinary choice memory := by
    have h := hprepared
    rw [r.output_eq] at h
    change (DeclaredFollowerLocalRound.prepare rate i row activation t (r.input.active i)
      (r.input.state.followers i)).configuration = .ordinary choice memory at h
    exact h
  obtain ⟨before, beforeMemory, hinput, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i row activation t
      (r.input.active i) (r.input.state.followers i) choice memory hprepare
  have hdomains := ReferenceCarriedDownForwardTransition.actual_prepare_local_domains
    rate r i choice memory hprepared
  rcases hdomains with ⟨hchoiceDomain, hchoiceOperation⟩
  obtain ⟨hbufferBefore, hpairBefore, htimeBefore⟩ :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_input_buffer_chronological
      rate source rewards C_star C_h k i before beforeMemory hinput
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta t before choice
    beforeMemory memory hstart
  rcases hstartFrame with
    ⟨_, _, _, _, hstartBatch, hstartBuffer, _, _⟩
  have hchoicePair : choice.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound) := by
    rw [hstartBuffer]
    exact hpairBefore
  have hchoiceStamps : ∀ saved ∈ choice.buffer, saved.calendarRound < e + 1 := by
    rw [hstartBuffer]
    exact htimeBefore
  obtain ⟨logged, hlogging, hlogBuffer, _, _, hlogBufferValid⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i row activation t
      (f.arm, own) choice hchoiceDomain.2.1 hchoiceStamps hu
  rcases ActiveFollowerLogging.checkedLogging_success_frame i row activation t
      (f.arm, own) choice logged hlogging with
    ⟨hlogLastDown, hlogS, hlogDelta, hlogBacklog, hlogStatus, hlogBatch, hlogMarker⟩
  have hloggedDomain : ActiveFollowerLifecycle.localStateDomainValid logged := by
    unfold ActiveFollowerLifecycle.localStateDomainValid at hchoiceDomain ⊢
    rcases hchoiceDomain with ⟨hregisters, _, hdecoder⟩
    refine ⟨?_, hlogBufferValid, ?_⟩
    · simpa only [ActiveFollowerLifecycle.serviceRegistersValid,
        hlogS, hlogDelta, hlogBacklog] using hregisters
    · simpa only [ActiveFollowerLifecycle.downDecoderStateValid, hlogBatch] using hdecoder
  have hloggedOperation :=
    ReferenceCarriedDownForwardTransition.operationInputDomain_of_localStateDomainValid
      rate logged hloggedDomain
  have hdecoderSpec := ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
    i row t own choice hchoiceOperation.2.1
  have hdecodedDomain : ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 := by
    simpa only [decoded] using hdecoderSpec.1
  have hdecodedLogged : ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate logged =
      decoded := by
    simp only [decoded, ActiveFollowerDownAcceptance.currentDecodeStep,
      ActiveFollowerDownAcceptance.currentRoundInput, hlogStatus, hlogBatch]
  have hparsedLogged :
      ReferenceDownReception.ordinaryParse p rate
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate logged).2 = parsed := by
    rw [hdecodedLogged]
  have hacceptanceLogged :
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged parsed =
        ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed := by
    simp [ReferenceDownReception.ordinaryLocalAcceptanceTest,
      ReferencePrelaunchFollower.acceptedStart, hlogLastDown]
  let cut := ReferenceDownReception.referenceDownCut p view i row t own rate logged
  let postDecode := {logged with downBatch := decoded.1}
  let next := if ActiveFollowerDownAcceptance.downSelected p i row t then postDecode else logged
  have hnotSelected : ¬ ActiveFollowerDownAcceptance.downSelected p i row t →
      cut.outcome = .skipped logged .notSelectedDown ∧
      cut.raw = none ∧ cut.filteredRaw = none ∧ cut.ordinaryParse = none ∧
      ¬ cut.ordinaryAcceptance ∧ cut.rawComparison = none := by
    intro hselected
    simp [cut, ReferenceDownReception.referenceDownCut, hselected]
  have hselectedCases :
      ∀ hselected : ActiveFollowerDownAcceptance.downSelected p i row t,
        (decoded.2 ≠ expected ∧
            cut.outcome = .decodeOrParseRejected logged postDecode decoded.2 ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
            cut.ordinaryParse = parsed ∧
            cut.ordinaryAcceptance =
              ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged parsed ∧
            cut.rawComparison = some false) ∨
          (decoded.2 = expected ∧ parsed = none ∧
            cut.outcome = .decodeOrParseRejected logged postDecode decoded.2 ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
            cut.ordinaryParse = none ∧ ¬ cut.ordinaryAcceptance ∧
            cut.rawComparison = some true) ∨
          (decoded.2 = expected ∧ ∃ M,
            parsed = some M ∧
            ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed ∧
            cut.outcome = .parsedButUnaccepted logged postDecode decoded.2 M ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
            cut.ordinaryParse = parsed ∧ ¬ cut.ordinaryAcceptance ∧
            cut.rawComparison = some true) := by
    intro hselected
    by_cases hmatches : decoded.2 = expected
    · cases hparse : parsed with
      | none =>
          have hparseExpected : ReferenceDownReception.ordinaryParse p rate expected = none := by
            simpa only [parsed, hmatches] using hparse
          right
          left
          refine ⟨hmatches, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [cut, postDecode, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
            change False → False
            exact fun h => h
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
      | some M =>
          have hnotAcceptedSome :
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice
                (some M) := by
            intro haccept
            apply hn
            exact ⟨hselected, hmatches, by simpa only [hparse] using haccept⟩
          have hparseExpected : ReferenceDownReception.ordinaryParse p rate expected = some M := by
            simpa only [parsed, hmatches] using hparse
          have hparseWire : ReferenceDownReception.ordinaryParse p rate
              (ReferenceDownReception.expectedDownFlatWord view i row t) = some M := by
            simpa only [expected] using hparseExpected
          have hnotAccepted :
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice
                parsed := by
            simpa only [hparse] using hnotAcceptedSome
          have hnotAcceptedLogged :
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged
                parsed := by
            rw [hacceptanceLogged]
            exact hnotAccepted
          have hnotAcceptedLoggedSome :
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged
                (some M) := by
            have hacceptEq := hacceptanceLogged
            rw [hparse] at hacceptEq
            intro haccept
            apply hnotAcceptedSome
            rw [← hacceptEq]
            exact haccept
          have hcutReject : ¬ OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged) (t.val + 1) M := by
            simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest] using hnotAcceptedLoggedSome
          right
          right
          refine ⟨hmatches, M, rfl, hnotAcceptedSome, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [cut, postDecode, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected, hnotAcceptedLoggedSome, hcutReject]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged, hparseExpected,
              hnotAcceptedLoggedSome]
          · simp [cut, ReferenceDownReception.referenceDownCut,
              hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
              hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged,
              hparseExpected]
    · left
      refine ⟨hmatches, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [cut, postDecode, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged]
      · simp [cut, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged]
      · simp [cut, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged]
      · simp [cut, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, parsed, expected, hdecodedLogged]
      · simp [cut, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, parsed, expected, hdecodedLogged,
          hacceptanceLogged]
      · simp [cut, ReferenceDownReception.referenceDownCut,
          hselected, hlogStatus, hu, hloggedOperation.1, hloggedOperation.2.1,
          hloggedOperation.2.2, hmatches, decoded, expected, hdecodedLogged]
  have hcutExpected : cut.expectedWord = expected := by
    unfold cut ReferenceDownReception.referenceDownCut
    repeat' split_ifs
    all_goals
      by_cases hcmp :
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate logged).2 =
          ReferenceDownReception.expectedDownFlatWord view i row t
      <;> simp [hcmp, expected]
  have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next := by
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
    · rcases hselectedCases hselected with hmis | hmatched
      · rcases hmis with ⟨_, houtcome, _, _, _, _, _⟩
        rw [houtcome]
        simp [DeclaredFollowerLocalRound.consumeDownResult, next, postDecode, hselected]
      · rcases hmatched with hnone | hunaccepted
        · rcases hnone with ⟨_, _, houtcome, _, _, _, _, _⟩
          rw [houtcome]
          simp [DeclaredFollowerLocalRound.consumeDownResult, next, postDecode, hselected]
        · rcases hunaccepted with ⟨_, M, _, _, houtcome, _, _, _, _, _⟩
          rw [houtcome]
          simp [DeclaredFollowerLocalRound.consumeDownResult, next, postDecode, hselected]
    · have hskip := hnotSelected hselected
      rcases hskip with ⟨houtcome, _, _, _, _, _⟩
      rw [houtcome]
      simp [DeclaredFollowerLocalRound.consumeDownResult, next, hselected]
  have hnextDomain : ActiveFollowerLifecycle.localStateDomainValid next := by
    classical
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
    · unfold next
      rw [ite_eq_left hselected]
      unfold ActiveFollowerLifecycle.localStateDomainValid
      rcases hloggedDomain with ⟨hregisters, hbuffer, _⟩
      refine ⟨hregisters, hbuffer, ?_⟩
      change ActiveFollowerDownAcceptance.decoderInputDomain p decoded.1
      simpa only [ActiveFollowerDownAcceptance.decoderInputDomain,
        ActiveFollowerLifecycle.downDecoderStateValid,
        ReferenceFollowerDecoderChronology.downBatchWellFormed] using hdecodedDomain
    · unfold next
      rw [ite_eq_right hselected]
      exact hloggedDomain
  have hnextStatus : next.status = .unoccupied := by
    classical
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
    · simp [next, postDecode, hselected, hu, hlogStatus]
    · simp [next, hselected, hu, hlogStatus]
  have hnextFrame : next.lastDown = choice.lastDown ∧ next.S = choice.S ∧
      next.delta = choice.delta ∧ next.backlog = choice.backlog ∧
      next.buffer = logged.buffer ∧
      next.initializationFailure = choice.initializationFailure := by
    classical
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
    · unfold next
      rw [ite_eq_left hselected]
      simp [postDecode, hlogLastDown, hlogS, hlogDelta, hlogBacklog, hlogMarker]
    · unfold next
      rw [ite_eq_right hselected]
      simp [hlogLastDown, hlogS, hlogDelta, hlogBacklog, hlogMarker]
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i t
    (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) own choice next hu
  have hfinish := ActiveFollowerLifecycle.finishRound_unoccupied rate.eta t row next memory
    hnextDomain hnextStatus
  have hreleaseFinish : DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice
      memory next = .ok (next, memory) := by
    rw [DeclaredFollowerLocalRound.releaseAndFinish_final_equation rate i row t own choice
      memory next next hrelease]
    rw [hfinish]
  have hloggedPair : logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    have hem : ReferenceFollowerBufferProvenance.logEmission i r =
        ReferencePrelaunchFollower.logAt i row activation t (f.arm, own) := by
      simp only [ReferenceFollowerBufferProvenance.logEmission, hprepared, hu, dite_true]
      rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
      rfl
    rw [hlogBuffer, ← hem, List.pairwise_append]
    refine ⟨hchoicePair, ReferenceFollowerBufferProvenance.logEmission_pairwise i r, ?_⟩
    intro a ha b hb
    have haTime := hchoiceStamps a ha
    have hbTime := ReferenceFollowerBufferProvenance.logEmission_source_timestamp i r b hb
    omega
  have hloggedStamps : ∀ saved ∈ logged.buffer, saved.calendarRound ≤ e + 1 := by
    have hem : ReferenceFollowerBufferProvenance.logEmission i r =
        ReferencePrelaunchFollower.logAt i row activation t (f.arm, own) := by
      simp only [ReferenceFollowerBufferProvenance.logEmission, hprepared, hu, dite_true]
      rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
      rfl
    rw [hlogBuffer, ← hem]
    intro saved hsaved
    rcases List.mem_append.mp hsaved with hold | hnew
    · exact Nat.le_of_lt (hchoiceStamps saved hold)
    · rw [ReferenceFollowerBufferProvenance.logEmission_source_timestamp i r saved hnew]
  obtain ⟨hrowRaw, hfollowerRaw, htimeRaw, hactivationRaw⟩ :=
    r.output.preparation.follower_alignment i
  have hfollower : f.follower = i := by
    simpa only [f, ReferenceFollowerFixedReply.actualChoice] using hfollowerRaw
  have hrow : f.row = row := by
    simpa only [f, ReferenceFollowerFixedReply.actualChoice, row] using hrowRaw
  have hactivation : f.activation = activation := by
    simpa only [f, ReferenceFollowerFixedReply.actualChoice, activation] using hactivationRaw
  have htime : f.time = t := by
    simpa only [f, ReferenceFollowerFixedReply.actualChoice, t] using htimeRaw
  have hloggingF : ActiveFollowerLogging.checkedLogging f.follower f.row f.activation f.time
      (f.arm, own) choice = .ok logged := by
    rw [hfollower, hrow, hactivation, htime]
    exact hlogging
  have hconsumeF : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view f.follower f.row f.time own rate logged).outcome =
        .ok next := by
    simpa only [hfollower, hrow, htime] using hconsume
  have hcutF : ReferenceDownReception.referenceDownCut p view f.follower f.row f.time own rate logged = cut := by
    rw [hfollower, hrow, htime]
  have hrecordResultF :
      (ReferenceActivePhysicalStep.recordFollower
        view f.follower f.row f.activation f.time f.active f.arm own choice).result =
          .ok next := by
    simp [ReferenceActivePhysicalStep.recordFollower, hu, hloggingF,
      hconsumeF]
  have hreleaseFinishF : DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row
      f.time own choice memory next = .ok (next, memory) := by
    rw [hfollower, hrow, htime]
    exact hreleaseFinish
  have hrecordLogged := ReferenceActivePhysicalStep.recordFollower_logged
    view f.follower f.row f.activation f.time f.active f.arm own choice logged hu hloggingF
  have hfollowers : r.output.followers i = ⟨.ordinary next memory, none, some logged, some cut⟩ := by
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower]
    change ReferenceActivePhysicalStep.finishFollower view f own =
      ⟨.ordinary next memory, none, some logged, some cut⟩
    simp [ReferenceActivePhysicalStep.finishFollower, hchoice, hrecordResultF,
      hreleaseFinishF, hrecordLogged.1, hrecordLogged.2, hcutF]
  have hfinishOrd :
      (ReferenceActivePhysicalStep.finishFollower view f own).configuration =
        .ordinary next memory :=
    (ReferenceActivePhysicalStep.finishFollower_success view f own choice next next memory memory
      hchoice hrecordResultF hreleaseFinishF).1
  have hstepConfig : ((ReferenceActivePhysicalStep.step r.input).followers i).configuration =
      .ordinary next memory := by
    have h := congrArg (fun out : ReferenceActivePhysicalStep.FollowerObservation p rate =>
      out.configuration) hfollowers
    rw [r.output_eq] at h
    exact h
  have hnextOutput : r.output.next.followers i = .ordinary next memory := by
    rw [r.output_eq]
    calc
      (ReferenceActivePhysicalStep.step r.input).next.followers i =
          ((ReferenceActivePhysicalStep.step r.input).followers i).configuration :=
        (ReferenceActivePhysicalStep.step_next_fields r.input).2.2.2 i
      _ = .ordinary next memory := hstepConfig
  have hc := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rcases hc with ⟨hc, hspan, hrecordAt⟩
  have hrecordAt' : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      k.val hspan
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc).activeAtStart := by
    simpa only [r, R, List.get_eq_getElem] using hrecordAt
  obtain ⟨active, hlaunch, hseed⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
      rate source rewards C_star C_h hc
  have hlaunchState := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hc
  have hactiveEq : active = ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hc := by
    rw [hlaunchState] at hlaunch
    exact (Option.some.inj hlaunch).symm
  subst active
  have hseedStart : ReferenceFollowerDecoderChronology.downBatchSeed
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hseed
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc).activeAtStart
  have hrunOrdinary :
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        k.val (by omega) hmode).finalState.followers i = .ordinary before beforeMemory := by
    have h := hinput
    rw [hrecordAt'] at h
    dsimp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt] at h
    exact h
  have htimeBound : e =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
    change (r.input.time.val) =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val
    rw [hrecordAt']
    rfl
  have hprefix := ReferenceFollowerDecoderChronology.run_downBatch_spec
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    k.val (by omega) hmode hseedStart i before beforeMemory hrunOrdinary
  have hbeforeEndpoint : ReferenceFollowerDecoderChronology.downBatchEndpoint before e := by
    simpa [htimeBound] using hprefix.1
  have hbeforeOccupied : before.status ≠ .unoccupied → before.downBatch.pending = [] := hprefix.2
  have hpreparedPrefix := ReferenceFollowerDecoderChronology.run_prepared_follower_downBatch_spec
    r i before choice beforeMemory memory e hinput hprepared hbeforeEndpoint hbeforeOccupied
  have hpreparedTime : f.time.val = e := by
    have hf := r.output.preparation.follower_alignment i
    exact congrArg Fin.val hf.2.2.1
  have hnextEndpoint := ReferenceFollowerDecoderChronology.preparedFollower_downBatch_spec
    view f own choice memory next memory e hprepared hpreparedPrefix.1
    (by intro h; exact (h hu).elim) hpreparedTime hfinishOrd
  have hcutCases :
      (cut.outcome = .skipped logged .notSelectedDown ∧ cut.raw = none ∧
        cut.filteredRaw = none ∧ cut.ordinaryParse = none ∧
        ¬ cut.ordinaryAcceptance ∧ cut.rawComparison = none) ∨
      (ActiveFollowerDownAcceptance.downSelected p i row t ∧
        ((decoded.2 ≠ expected ∧
            cut.outcome = .decodeOrParseRejected logged postDecode decoded.2 ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
            cut.ordinaryParse = parsed ∧
            cut.ordinaryAcceptance =
              ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged parsed ∧
            cut.rawComparison = some false) ∨
          (decoded.2 = expected ∧ parsed = none ∧
            cut.outcome = .decodeOrParseRejected logged postDecode decoded.2 ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
            cut.ordinaryParse = none ∧ ¬ cut.ordinaryAcceptance ∧
            cut.rawComparison = some true) ∨
          (decoded.2 = expected ∧ ∃ M, parsed = some M ∧
            ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed ∧
            cut.outcome = .parsedButUnaccepted logged postDecode decoded.2 M ∧
            cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
            cut.ordinaryParse = parsed ∧ ¬ cut.ordinaryAcceptance ∧
            cut.rawComparison = some true))) := by
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
    · exact Or.inr ⟨hselected, hselectedCases hselected⟩
    · exact Or.inl (hnotSelected hselected)
  have hresult :
      ActiveFollowerLogging.checkedLogging i row activation t (f.arm, own) choice = .ok logged ∧
      logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i row activation t (f.arm, own) ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
      ActiveFollowerLifecycle.localStateDomainValid logged ∧
      (logged.lastDown = choice.lastDown ∧ logged.S = choice.S ∧ logged.delta = choice.delta ∧
        logged.backlog = choice.backlog ∧ logged.status = choice.status ∧
        logged.downBatch = choice.downBatch ∧
        logged.initializationFailure = choice.initializationFailure) ∧
      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ logged.buffer, saved.calendarRound ≤ e + 1) ∧
      (let cut := ReferenceDownReception.referenceDownCut p view i row t own rate logged
       let next := @ite _ (ActiveFollowerDownAcceptance.downSelected p i row t)
         (Classical.propDecidable _) {logged with downBatch := decoded.1} logged
       DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
       DeclaredFollowerLocalRound.releaseAndFinish rate i row t own choice memory next =
         .ok (next, memory) ∧
       next.status = .unoccupied ∧ next.lastDown = choice.lastDown ∧ next.S = choice.S ∧
       next.delta = choice.delta ∧ next.backlog = choice.backlog ∧ next.buffer = logged.buffer ∧
       next.initializationFailure = choice.initializationFailure ∧
       ActiveFollowerLifecycle.localStateDomainValid next ∧
       ReferenceFollowerDecoderChronology.downBatchEndpoint next (e + 1) ∧
       (ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 ∧
        AffineBatchDecoder.collected decoded.1 =
          AffineBatchDecoder.collected choice.downBatch ++ AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i row t own rate choice)) t) ∧
       (∀ hselected : ActiveFollowerDownAcceptance.downSelected p i row t,
          own.val.val = 0 → decoded = (choice.downBatch, none)) ∧
       cut.expectedWord = expected ∧
       ((cut.outcome = .skipped logged .notSelectedDown ∧ cut.raw = none ∧
           cut.filteredRaw = none ∧ cut.ordinaryParse = none ∧ ¬ cut.ordinaryAcceptance ∧
           cut.rawComparison = none) ∨
         (ActiveFollowerDownAcceptance.downSelected p i row t ∧
           ((decoded.2 ≠ expected ∧ cut.outcome = .decodeOrParseRejected logged
              {logged with downBatch := decoded.1} decoded.2 ∧ cut.raw = decoded.2 ∧
              cut.filteredRaw = none ∧ cut.ordinaryParse = parsed ∧
              cut.ordinaryAcceptance =
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t logged parsed ∧
              cut.rawComparison = some false) ∨
            (decoded.2 = expected ∧ parsed = none ∧
              cut.outcome = .decodeOrParseRejected logged
                {logged with downBatch := decoded.1} decoded.2 ∧ cut.raw = decoded.2 ∧
              cut.filteredRaw = decoded.2 ∧ cut.ordinaryParse = none ∧
              ¬ cut.ordinaryAcceptance ∧ cut.rawComparison = some true) ∨
            (decoded.2 = expected ∧ ∃ M, parsed = some M ∧
              ¬ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed ∧
              cut.outcome = .parsedButUnaccepted logged
                {logged with downBatch := decoded.1} decoded.2 M ∧ cut.raw = decoded.2 ∧
              cut.filteredRaw = decoded.2 ∧ cut.ordinaryParse = parsed ∧
              ¬ cut.ordinaryAcceptance ∧ cut.rawComparison = some true)))) ∧
       r.output.followers i = ⟨.ordinary next memory, none, some logged, some cut⟩ ∧
       r.output.next.followers i = .ordinary next memory) := by
    exact ⟨hlogging, hlogBuffer, hchoiceDomain, hchoiceOperation, hloggedDomain,
      ⟨hlogLastDown, hlogS, hlogDelta, hlogBacklog, hlogStatus, hlogBatch, hlogMarker⟩,
      hloggedPair, hloggedStamps, hconsume, hreleaseFinish, hnextStatus,
      hnextFrame.1, hnextFrame.2.1, hnextFrame.2.2.1, hnextFrame.2.2.2.1,
      hnextFrame.2.2.2.2.1, hnextFrame.2.2.2.2.2, hnextDomain,
      hnextEndpoint.1, ⟨hdecodedDomain, hdecoderSpec.2⟩,
      by
        intro hselected hzero
        have heligible : ¬ AffineBatchDecoder.eligible
            (ActiveFollowerDownAcceptance.currentRoundInput p i row t own rate choice) := by
          rw [ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff]
          exact fun h => by simpa [hzero] using h.2.2
        have hpending := hchoiceOperation.2.1.1
        simpa [decoded, ActiveFollowerDownAcceptance.currentDecodeStep,
          ActiveFollowerDownAcceptance.currentInputExtension] using
          AffineBatchDecoder.decodeStep_ineligible p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i row t own rate choice))
            choice.downBatch t hpending heligible,
      hcutExpected, hcutCases, hfollowers, hnextOutput⟩
  exact ⟨logged, hresult⟩

end Bandits.Support.ReferenceCompleteUnoccupiedNonacceptingForward

end
