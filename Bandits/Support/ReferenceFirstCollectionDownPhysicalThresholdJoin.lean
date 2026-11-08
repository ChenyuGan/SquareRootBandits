/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownPhysicalBoundary
public import Bandits.Support.ReferenceFirstCollectionDownPhysicalThreshold


/-!
# First-collection DOWN physical threshold join

Join the actual initialized pure bank to the successful physical follower
callback at each positive collection coordinate. At the inclusive second-bank
threshold the same cut accepts the fixed word or has two distinct solutions.
No threshold-attainment or probability assertion is made.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionDownPhysicalThresholdJoin

variable {p : Parameters}

/-- The actual follower's prepared local snapshot, before observation. -/
def localPrepared {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1)) :
    DeclaredFollowerLocalRound.PreparedRound p rate :=
  record.output.preparation.followers.followers i

/-- The actual collision-zeroed physical observation of this follower. -/
def localObservation {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1)) :
    ReferencePrelaunchFollower.Observation p :=
  record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)

/-- The actual stored follower output, including its failure and DOWN data. -/
def localOutput {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1)) :
    ReferenceActivePhysicalStep.FollowerObservation p rate :=
  record.output.followers i

/-- The reference cut evaluated on the actual view, row, time and observation. -/
def localCut {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceDownReception.ReferenceDownCutOutput p rate :=
  ReferenceDownReception.referenceDownCut p
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (localObservation record i) rate logged

/-- The actual checked physical callback on the given incoming local state. -/
def localPhysicalCall {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceActivePhysicalStep.FollowerRecord (rate := rate) :=
  ReferenceActivePhysicalStep.recordFollower
    record.output.preparation.coordinator.downView i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (localPrepared record i).arm (localObservation record i) before

/-- The real successful callback fixes the rejected next state, including the
returned decoder bank. This helper assumes no recovery success. -/
private theorem physical_rejected_update
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (before logged post after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hstatus : before.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation time
      (arm, own) before = .ok logged)
    (hrejected : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).outcome =
      .decodeOrParseRejected logged after raw)
    (hresult : (ReferenceActivePhysicalStep.recordFollower view i row activation time
      hactive arm own before).result = .ok post) : post = after := by
  have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time own rate logged).outcome =
        .ok post := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hlogging] using hresult
  rw [hrejected, DeclaredFollowerLocalRound.consumeDownResult_rejected] at hconsume
  exact (Except.ok.inj hconsume).symm

/-- Conditional per-record join. All domain, diagnostic and success inputs
are supplied by the actual prefix and physical-boundary producers below. -/
private theorem threshold_physical_dichotomy
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (before logged post : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (pureSecond : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hstatus : before.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((localPrepared record i).arm, localObservation record i) before = .ok logged)
    (hcut : cut = localCut record i logged)
    (hresult : (localPhysicalCall record i before).result = .ok post)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time)
    (hregister : ActiveFollowerDownAcceptance.registerInputDomain p rate logged)
    (hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer)
    (hrawCurrent : cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
      record.input.row record.input.time (localObservation record i) rate logged).2)
    (hexpected : cut.expectedWord = some word)
    (hreject : cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected logged
      { logged with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
        record.input.row record.input.time (localObservation record i) rate logged).1 } cut.raw)
    (hbank : (ActiveFollowerDownAcceptance.currentDecodeStep p i
      record.input.row record.input.time (localObservation record i) rate logged).1 = bank)
    (hcases : (cut.raw = some word ∧ cut.ordinaryParse = some message ∧ cut.ordinaryAcceptance) ∨
      (cut.raw = none ∧ cut.rawComparison = some false ∧
        ∃ other, other ≠ word ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pureSecond) other)) :
    (cut.raw = some word ∧ ∃ after scan registers lastService,
      cut.outcome = .accepted logged after (some word) message scan registers lastService ∧
      post = after ∧ post.lastDown = some message) ∨
    (cut.raw = none ∧ cut.rawComparison = some false ∧
      ∃ other, other ≠ word ∧
        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pureSecond) other ∧
        post.downBatch = bank) := by
  classical
  rcases hcases with ⟨hraw, hparse, haccept⟩ | ⟨hraw, hcomparison, other, hne, hsolves⟩
  · left
    refine ⟨hraw, ?_⟩
    have haccepted :=
      ReferenceFirstCollectionDownPhysicalThreshold.actual_physical_result_forces_accepted_cut
        rate record.output.preparation.coordinator.downView i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (localPrepared record i).arm (localObservation record i) before logged post word message
        hselected hstatus hlogging hregister hdecoder hbuffer
        (by simpa only [hcut, localCut] using hrawCurrent)
        (by simpa only [hcut, localCut] using hraw)
        (by simpa only [hcut, localCut] using hexpected)
        (by simpa only [hcut, localCut] using hparse)
        (by simpa only [hcut, localCut] using haccept) hresult
    simpa only [hcut, localCut] using haccepted
  · right
    refine ⟨hraw, hcomparison, other, hne, hsolves, ?_⟩
    have hneq : cut.raw ≠ cut.expectedWord := by
      intro h
      rw [hraw, hexpected] at h
      cases h
    have hpost : post = { logged with downBatch :=
        (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
          (localObservation record i) rate logged).1 } :=
      physical_rejected_update rate record.output.preparation.coordinator.downView i
        record.input.row (record.input.state.activations i) record.input.time (record.input.active i)
        (localPrepared record i).arm (localObservation record i) before logged post _ cut.raw
        hstatus hlogging (by simpa only [hcut, localCut] using hreject hneq) hresult
    rw [hpost]
    exact hbank

/-- Transport diagnostics by whole-record equality and identify the logged
state from the same actual follower output. -/
private theorem diagnostics_of_same_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : ReferenceCollectionPhaseHistory.Record p rate) (heq : left = right)
    (i : Fin (p.m - 1)) (choice logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hinput : (localOutput left i).downInput = some choice)
    (hactual : (localOutput right i).downInput = some logged)
    (hregister : ActiveFollowerDownAcceptance.registerInputDomain p rate choice)
    (hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer)
    (hraw : (localCut left i choice).raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
      left.input.row left.input.time (localObservation left i) rate choice).2)
    (hreject : (localCut left i choice).raw ≠ (localCut left i choice).expectedWord →
      (localCut left i choice).outcome = .decodeOrParseRejected choice
        { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
          left.input.row left.input.time (localObservation left i) rate choice).1 }
        (localCut left i choice).raw)
    (hcut : cut = localCut right i logged)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i left.input.row left.input.time) :
    ActiveFollowerDownAcceptance.downSelected p i right.input.row right.input.time ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
      right.input.row right.input.time (localObservation right i) rate logged).2 ∧
    (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected logged
      { logged with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
        right.input.row right.input.time (localObservation right i) rate logged).1 } cut.raw) := by
  cases heq
  have hstates : choice = logged := Option.some.inj (hinput.symm.trans hactual)
  cases hstates
  exact ⟨hselected, hregister, hdecoder, hbuffer,
    by simpa only [hcut] using hraw,
    by simpa only [hcut] using hreject⟩

/-- Equality of the logged state preserves the literal decoder bank. -/
private theorem decoder_bank_of_state_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (choice logged : ReferencePrelaunchFollower.State p rate.eta) (heq : choice = logged)
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hbank : (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
      (localObservation record i) rate choice).1 = bank) :
    (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
      (localObservation record i) rate logged).1 = bank := by
  cases heq
  exact hbank

/-- Keep precisely the diagnostics needed from the produced selected call.
The input is P's literal per-record selected branch, not a new root premise. -/
private theorem selected_call_diagnostics
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (payload : ReferenceFirstCollectionReadyStream.Payload rate) (s : ℕ)
    (hcall :
              ∃ (selected : ReferenceActivePhysicalStep.Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = payload ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                (record.output.preparation.followers.followers i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let cut := ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView i record.input.row record.input.time own rate choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
                (record.output.followers i).downInput = some choice ∧
                (record.output.followers i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) = some (payload.downRecord i) ∧
                ReferencePrelaunchFollower.acceptedStart choice = 0 ∧ (payload.downRecord i).val.sigma = s + 1 ∧
                (payload.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (payload.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord payload i) = 1)) :
    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
      (localOutput record i).downInput = some choice ∧
      ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
      ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
      ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
      (localCut record i choice).raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i
        record.input.row record.input.time (localObservation record i) rate choice).2 ∧
      ((localCut record i choice).raw ≠ (localCut record i choice).expectedWord →
        (localCut record i choice).outcome = .decodeOrParseRejected choice
          { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
            record.input.row record.input.time (localObservation record i) rate choice).1 }
          (localCut record i choice).raw) := by
  rcases hcall with ⟨_selected, choice, _memory, _hselection, _hpayload, _hpending,
    _hsent, _hconfig, _hstatus, _hlast, _hdomain, _hlogging,
    hinput, _hcut, hregister, hdecoder, hbuffer, _hexpected,
    _hcompSome, hraw, _hfiltered, _hparse, _haccept, _hcomparison,
    hreject, _houtcome, _hparseWord, _hstart, _hsigma, _htime,
    _hlocal, _hhash⟩
  exact ⟨choice, hinput, hregister, hdecoder, hbuffer, hraw, hreject⟩

/-- Extract the actual callback from the source-independent boundary
conjunction. No success, state or bank premise is introduced at the root. -/
private theorem callback_from_boundary_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (s w n : ℕ)
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hrest :
        ActiveFollowerLifecycle.localStateDomainValid before ∧
        ActiveFollowerLifecycle.localBufferValid before ∧
        ActiveFollowerLifecycle.downDecoderStateValid before ∧
        before.S ≤ p.T * D p ∧ before.delta ≤ D p ∧ before.backlog ≤ p.T * D p ∧
        before.S + before.backlog ≤ w * D p ∧
        (∀ saved ∈ before.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
        (before.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
        (∀ saved ∈ before.buffer, ∃ q : ℕ, q ≤ D p ∧
          saved.observation = (q : ℝ) / (D p : ℝ)) ∧
        before.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ before.buffer, saved.calendarRound < s + w + n + 1) ∧
        before.downBatch.pending.length < AffineBatchDecoder.quota p ∧
        (∀ batch ∈ before.downBatch.completed, batch.length = AffineBatchDecoder.quota p) ∧
        ((before.lastDown = none ∧ before.S = 0 ∧ before.delta = 0 ∧ before.backlog = 0) ∨
          before.lastDown = some (message)) ∧
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (before, memory) ∧
        ∃ logged cut post,
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time
            ((record.output.preparation.followers.followers i).arm,
              record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before =
              .ok logged ∧
          logged.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
            record.input.row (record.input.state.activations i) record.input.time
            ((record.output.preparation.followers.followers i).arm,
              record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
          cut = ReferenceDownReception.referenceDownCut p
            record.output.preparation.coordinator.downView i record.input.row
            record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).result =
              .ok post ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).downInput =
              some logged ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).down =
              some cut ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before memory post =
              .ok (post, memory) ∧
          (record.output.followers i).configuration = .ordinary post memory ∧
          (record.output.followers i).failure = none ∧
          (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some cut ∧
          post.status = .unoccupied ∧
          ActiveFollowerLifecycle.localStateDomainValid post ∧
          ActiveFollowerLifecycle.localBufferValid post ∧
          ActiveFollowerLifecycle.downDecoderStateValid post ∧ post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧
          post.backlog ≤ p.T * D p ∧ post.S + post.backlog ≤ w * D p ∧
          (∀ saved ∈ post.buffer,
            1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
          (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
          (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
            saved.observation = (q : ℝ) / (D p : ℝ)) ∧
          post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ post.buffer, saved.calendarRound < s + w + n + 2) ∧
          post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          (∀ batch ∈ post.downBatch.completed,
            batch.length = AffineBatchDecoder.quota p) ∧
          ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
            post.lastDown = some (message)) ∧
          post.initializationFailure = before.initializationFailure) :
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (before, memory) ∧
        ∃ logged cut post,
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) before =
              .ok logged ∧
          logged.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
            record.input.row (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) ∧
          cut = localCut record i logged ∧
          (localPhysicalCall record i before).result =
              .ok post ∧
          (localPhysicalCall record i before).downInput =
              some logged ∧
          (localPhysicalCall record i before).down =
              some cut ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time
            (localObservation record i) before memory post =
              .ok (post, memory) ∧
          (localOutput record i).configuration = .ordinary post memory ∧
          (localOutput record i).failure = none ∧
          (localOutput record i).downInput = some logged ∧
          (localOutput record i).down = some cut ∧
          post.status = .unoccupied ∧
          post.initializationFailure = before.initializationFailure := by
  rcases hrest with ⟨_hdomain, _hbuffer, _hdecoder, _hS, _hdelta, _hbacklog, _hmass,
    _hcalendar, _hkeys, _hquant, _hpair, _hstamps, _hpending, _hcompleted,
    _hlast, hstart, logged, cut, post, hlogging, hlogBuffer, hcut,
    hresult, hcallInput, hcallCut, hfinish, houtConfig, hfailure,
    houtInput, houtCut, hpostStatus, _hpostDomain, _hpostBuffer, _hpostDecoder,
    _hpostS, _hpostDelta, _hpostBacklog, _hpostMass, _hpostCalendar, _hpostKeys,
    _hpostQuant, _hpostPair, _hpostStamps, _hpostPending, _hpostCompleted,
    _hpostLast, hinitFlag⟩
  exact ⟨hstart, logged, cut, post, hlogging, hlogBuffer, hcut,
    hresult, hcallInput, hcallCut, hfinish, houtConfig, hfailure,
    houtInput, houtCut, hpostStatus, hinitFlag⟩

/-- The actual boundary producer, with its full successful physical callback
projected to the fields consumed by the join. -/
private theorem actual_physical_callback_family :
    ∀ {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (_hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count),
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    ∃ (hB : 0 < B.length)
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      (B[0]'hB).input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      ∀ (n : Fin B.length), 0 < n.val → ∀ i : Fin (p.m - 1),
      ∃ (hRun : s + (w + n.val) ≤ p.T)
        (hNext : s + (w + n.val + 1) ≤ p.T),
      let record := B[n.val]
      record.input.state = (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState ∧
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val + 1) hNext
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState = record.output.next ∧
      ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        record.input.state.followers i = .ordinary before memory ∧
        (localPrepared record i).configuration =
          .ordinary before memory ∧
        before.status = .unoccupied ∧
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (before, memory) ∧
        ∃ loggedB cutB post,
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) before =
              .ok loggedB ∧
          loggedB.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
            record.input.row (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) ∧
          cutB = localCut record i loggedB ∧
          (localPhysicalCall record i before).result =
              .ok post ∧
          (localPhysicalCall record i before).downInput =
              some loggedB ∧
          (localPhysicalCall record i before).down =
              some cutB ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time
            (localObservation record i) before memory post =
              .ok (post, memory) ∧
          (localOutput record i).configuration = .ordinary post memory ∧
          (localOutput record i).failure = none ∧
          (localOutput record i).downInput = some loggedB ∧
          (localOutput record i).down = some cutB ∧
          post.status = .unoccupied ∧
          post.initializationFailure = before.initializationFailure := by
  intro p rate source rewards C_star C_h count hcross hspan hshort s epoch w B
  obtain ⟨hB, r, q, base, hcoord, hsigma, hzero, hboundary⟩ :=
    ReferenceFirstCollectionDownPhysicalBoundary.actual_first_collection_down_physical_boundary
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨hB, r, q, base, hcoord, hsigma, hzero, ?_⟩
  intro n hn i
  obtain ⟨hRun, hNext, hprefixIn, hprefixOut, before, memory, hinput, hprep,
    hstatus, hrest⟩ := hboundary n hn i
  obtain ⟨hstart, logged, cut, post, hphysical⟩ :=
    callback_from_boundary_record rate B[n.val] i before memory s w n.val
      (r.payload.downRecord i) hrest
  exact ⟨hRun, hNext, hprefixIn, hprefixOut, before, memory, hinput, hprep,
    hstatus, hstart, logged, cut, post, hphysical⟩

/-- Strengthen P's produced OLD prefix using the same actual physical
callback. Its explicit local conjunction is supplied by P in the public proof. -/
private theorem join_old_prefix :
    ∀ {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (n : Fin d.stream.ell) (hn : 0 < n.val) (i : Fin (p.m - 1))
    (hwindow : d.stream.window = ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length),
    let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let Q := AffineBatchDecoder.quota p
    let out := d.stream
    let P0 := out.payload
    let nB : Fin B.length := ⟨n.val, by
      have hwindowLocal : out.window = B := hwindow
      rw [← hwindowLocal]
      exact Nat.lt_of_lt_of_le n.isLt out.withinWindow⟩
    let record := B[nB.val]
    ∀ (before : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (loggedB : ReferencePrelaunchFollower.State p rate.eta)
      (cutB : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (post : ReferencePrelaunchFollower.State p rate.eta),
      (localPrepared record i).configuration = .ordinary before memory →
      before.status = .unoccupied →
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        ((localPrepared record i).arm, localObservation record i) before = .ok loggedB →
      cutB = localCut record i loggedB →
      (localPhysicalCall record i before).result = .ok post →
      (localOutput record i).downInput = some loggedB →
      (localOutput record i).down = some cutB →
      ((∀ k : Fin (n.val + 1),
          let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
            out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
              (Nat.lt_of_lt_of_le n.isLt out.withinWindow))
          ∃ prior priorMemory,
            record.input.state.followers i = .ordinary prior priorMemory ∧ prior.lastDown = none ∧
            (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
              ∃ (selected : ReferenceActivePhysicalStep.Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P0 ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                (record.output.preparation.followers.followers i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let cut := ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView i record.input.row record.input.time own rate choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((record.output.preparation.followers.followers i).arm, own) choice = .ok choice ∧
                (record.output.followers i).downInput = some choice ∧
                (record.output.followers i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i)) = some (P0.downRecord i) ∧
                ReferencePrelaunchFollower.acceptedStart choice = 0 ∧ (P0.downRecord i).val.sigma = s + 1 ∧
                (P0.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (P0.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) = 1))) ∧
        ∃ hBlen : 0 < (B).length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          ((B)[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          (let W0 := cutoffState.downBatch
            let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
            before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
            AffineBatchDecoder.collected before.downBatch =
              AffineBatchDecoder.collected W0 ++ P ∧
            W0.pending.length < Q ∧
            (∀ entry ∈ W0.pending, entry.time.val < s + w) ∧
            (C.map Prod.fst).map Fin.val =
              ReferenceActivePhysicalHorizon.calendar (s + w) n.val ∧
            P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ P, s + w ≤ entry.time.val ∧ entry.time.val < s + w + n.val) ∧
            (∀ entry ∈ P, entry.sample =
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                entry.time).2 (0, i)) ∧
            (∀ completed ∈ W0.completed,
              completed.length = Q) ∧
            (AffineBatchDecoder.collected W0).Pairwise
              (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < s + w) ∧
            before.downBatch.completed =
              (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed) ∧
          let W0 := cutoffState.downBatch
          let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i ((B).take n.val)
          ∀ (hdown : ActiveFollowerDownAcceptance.downSelected p i
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.row
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time),
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
            ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
            ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              let record : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) :=
                B[nB.val]
              let prep := record.output.preparation.followers.followers i
              let own := record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let fixedWord := CoordinatorLocalArmChoice.storedDownFlatWord P0 i
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((B).take n.val)
              let currentEntry : AffineBatchDecoder.Entry p.T
                  (AffineBatchDecoder.width p) :=
                ⟨prep.time, (prep.row.2 prep.time).2 (0, i)⟩
              prep.configuration = .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              (record.output.followers i).downInput = some choice ∧
              (record.output.followers i).down = some cut ∧
              cut.expectedWord = some fixedWord ∧
              cut.rawComparison.isSome = true ∧
              cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
              logged = choice ∧
              logged.downBatch = before.downBatch ∧
              logged.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
              cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                p i record.input.row record.input.time own rate choice).2 ∧
              (∀ (hpositive : 0 < own.val.val),
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  ((B).take (n.val + 1))).length =
                    Q - W0.pending.length + Q →
                ∃ contaminatedFirst pureSecond :
                    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                  contaminatedFirst = W0.pending ++ P.take (Q - W0.pending.length) ∧
                  pureSecond = P.drop (Q - W0.pending.length) ++ [currentEntry] ∧
                  contaminatedFirst.length = Q ∧ pureSecond.length = Q ∧
                  (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 =
                    ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩ ∧
                  cut.raw = AffineBatchDecoder.batchOutput pureSecond ∧
                  (∀ entry ∈ pureSecond,
                    AffineChannelLaw.affineHash entry.sample fixedWord = 1) ∧
                  AffineBatchDecoder.satisfies
                    (AffineBatchDecoder.samples pureSecond) fixedWord ∧
                  pureSecond.Pairwise (fun earlier later =>
                    earlier.time.val < later.time.val) ∧
                  (∀ entry ∈ pureSecond,
                    s + w ≤ entry.time.val ∧
                    entry.time.val ≤ s + w + n.val) ∧
                  (∀ entry ∈ pureSecond,
                    entry.sample =
                      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex
                        p source)).2 entry.time).2 (0, i)) ∧
                  ((cut.raw = some fixedWord ∧
                    cut.ordinaryParse = some (P0.downRecord i) ∧
                    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                      record.input.time choice cut.ordinaryParse ∧
                    cut.ordinaryAcceptance) ∨
                   (cut.raw = none ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      cut.rawComparison = some false)))) →
        (∀ k : Fin (n.val + 1),
          let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
            out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
              (Nat.lt_of_lt_of_le n.isLt out.withinWindow))
          ∃ prior priorMemory,
            record.input.state.followers i = .ordinary prior priorMemory ∧ prior.lastDown = none ∧
            (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
              ∃ (selected : ReferenceActivePhysicalStep.Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P0 ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                (localPrepared record i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := localObservation record i
                let cut := localCut record i choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((localPrepared record i).arm, own) choice = .ok choice ∧
                (localOutput record i).downInput = some choice ∧
                (localOutput record i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i)) = some (P0.downRecord i) ∧
                ReferencePrelaunchFollower.acceptedStart choice = 0 ∧ (P0.downRecord i).val.sigma = s + 1 ∧
                (P0.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (P0.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) = 1))) ∧
        ∃ hBlen : 0 < (B).length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          ((B)[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          (let W0 := cutoffState.downBatch
            let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
            before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
            AffineBatchDecoder.collected before.downBatch =
              AffineBatchDecoder.collected W0 ++ P ∧
            W0.pending.length < Q ∧
            (∀ entry ∈ W0.pending, entry.time.val < s + w) ∧
            (C.map Prod.fst).map Fin.val =
              ReferenceActivePhysicalHorizon.calendar (s + w) n.val ∧
            P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ P, s + w ≤ entry.time.val ∧ entry.time.val < s + w + n.val) ∧
            (∀ entry ∈ P, entry.sample =
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                entry.time).2 (0, i)) ∧
            (∀ completed ∈ W0.completed,
              completed.length = Q) ∧
            (AffineBatchDecoder.collected W0).Pairwise
              (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < s + w) ∧
            before.downBatch.completed =
              (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed) ∧
          let W0 := cutoffState.downBatch
          let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i ((B).take n.val)
          ∀ (hdown : ActiveFollowerDownAcceptance.downSelected p i
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.row
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time),
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
            ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
            ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              let record : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) :=
                B[nB.val]
              let prep := localPrepared record i
              let own := localObservation record i
              let fixedWord := CoordinatorLocalArmChoice.storedDownFlatWord P0 i
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((B).take n.val)
              let currentEntry : AffineBatchDecoder.Entry p.T
                  (AffineBatchDecoder.width p) :=
                ⟨prep.time, (prep.row.2 prep.time).2 (0, i)⟩
              prep.configuration = .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              (localOutput record i).downInput = some choice ∧
              (localOutput record i).down = some cut ∧
              cut.expectedWord = some fixedWord ∧
              cut.rawComparison.isSome = true ∧
              cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
              logged = choice ∧
              logged.downBatch = before.downBatch ∧
              logged.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
              cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                p i record.input.row record.input.time own rate choice).2 ∧
              choice = before ∧ choiceMemory = memory ∧
              logged = loggedB ∧ cut = cutB ∧
              (∀ (hpositive : 0 < own.val.val),
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  ((B).take (n.val + 1))).length =
                    Q - W0.pending.length + Q →
                ∃ contaminatedFirst pureSecond :
                    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                  contaminatedFirst = W0.pending ++ P.take (Q - W0.pending.length) ∧
                  pureSecond = P.drop (Q - W0.pending.length) ++ [currentEntry] ∧
                  contaminatedFirst.length = Q ∧ pureSecond.length = Q ∧
                  (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 =
                    ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩ ∧
                  cut.raw = AffineBatchDecoder.batchOutput pureSecond ∧
                  (∀ entry ∈ pureSecond,
                    AffineChannelLaw.affineHash entry.sample fixedWord = 1) ∧
                  AffineBatchDecoder.satisfies
                    (AffineBatchDecoder.samples pureSecond) fixedWord ∧
                  pureSecond.Pairwise (fun earlier later =>
                    earlier.time.val < later.time.val) ∧
                  (∀ entry ∈ pureSecond,
                    s + w ≤ entry.time.val ∧
                    entry.time.val ≤ s + w + n.val) ∧
                  (∀ entry ∈ pureSecond,
                    entry.sample =
                      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex
                        p source)).2 entry.time).2 (0, i)) ∧
                  ((cut.raw = some fixedWord ∧
                    cut.ordinaryParse = some (P0.downRecord i) ∧
                    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                      record.input.time choice cut.ordinaryParse ∧
                    cut.ordinaryAcceptance) ∨
                   (cut.raw = none ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      cut.rawComparison = some false)) ∧
                  ((cut.raw = some fixedWord ∧
                    ∃ after scan registers lastService,
                      cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                        loggedB after (some fixedWord) (P0.downRecord i) scan registers lastService ∧
                      post = after ∧ post.lastDown = some (P0.downRecord i)) ∨
                   (cut.raw = none ∧ cut.rawComparison = some false ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      post.downBatch =
                        ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩))) := by
  intro p rate source rewards C_star C_h count hcross hspan hshort d n hn i hwindow s epoch w B Q
    out P0 nB record before memory loggedB cutB post hprep hstatus hlogging hcut hresult houtInput houtCut hOld
  have hrecordAtN : out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow) = record :=
    getElem_congr_coll hwindow
  rcases hOld with ⟨hcalls, hBlen, cutoffState, cutoffMemory, hcutOrd, hbank, hselected⟩
  refine ⟨hcalls, hBlen, cutoffState, cutoffMemory, hcutOrd, hbank, ?_⟩
  intro W0 C hdown
  obtain ⟨choice, choiceMemory, logged, cut, hconfigP, hstatusP,
    hinputP, hcutP, hexpectedP, hcompSomeP, hcomparisonP,
    hloggedP, hloggedBankP, hfoldP, hrawP, hthreshold⟩ := hselected hdown
  change (localPrepared record i).configuration = .ordinary choice choiceMemory at hconfigP
  change (localOutput record i).downInput = some choice at hinputP
  change (localOutput record i).down = some cut at hcutP
  have hchoices := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hconfigP.symm.trans hprep)
  have hchoice : choice = before := hchoices.1
  have hmemory : choiceMemory = memory := hchoices.2
  have hloggedB : logged = loggedB := hloggedP.trans
    (Option.some.inj (hinputP.symm.trans houtInput))
  have hcutB : cut = cutB := Option.some.inj (hcutP.symm.trans houtCut)
  refine ⟨choice, choiceMemory, logged, cut, hconfigP, hstatusP,
    hinputP, hcutP, hexpectedP, hcompSomeP, hcomparisonP,
    hloggedP, hloggedBankP, hfoldP, hrawP, hchoice, hmemory, hloggedB, hcutB, ?_⟩
  intro hpositive hcount
  obtain ⟨contaminatedFirst, pureSecond, hfirst, hsecond, hfirstSize,
    hsecondSize, hdecodeBank, hbatchRaw, hhashes, hsolves,
    hdates, hdateRange, hsamples, hcases⟩ := hthreshold hpositive hcount
  refine ⟨contaminatedFirst, pureSecond, hfirst, hsecond, hfirstSize,
    hsecondSize, hdecodeBank, hbatchRaw, hhashes, hsolves,
    hdates, hdateRange, hsamples, hcases, ?_⟩
  obtain ⟨prior, priorMemory, _hpriorInput, _hpriorNone, hbranch⟩ :=
    hcalls ⟨n.val, Nat.lt_succ_self n.val⟩
  obtain ⟨choiceC, hinputC, hregisterC, hdecoderC, hbufferC, hrawC, hrejectC⟩ :=
    selected_call_diagnostics rate
      (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)) i P0 s (hbranch hdown)
  have hcutJoined : cut = localCut record i loggedB := hcutB.trans hcut
  obtain ⟨hdownB, hregister, hdecoderLogged, hbufferLogged, hrawCurrent, hrejectLocal⟩ :=
    diagnostics_of_same_record rate
      (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)) record hrecordAtN
      i choiceC loggedB cut hinputC houtInput hregisterC hdecoderC hbufferC
      hrawC hrejectC hcutJoined hdown
  have hchoiceLogged : choice = loggedB := hloggedP.symm.trans hloggedB
  have hbankLogged := decoder_bank_of_state_eq rate record i choice loggedB hchoiceLogged
    ⟨[], cutoffState.downBatch.completed ++ [contaminatedFirst, pureSecond]⟩ hdecodeBank
  have hcasesLocal :
      (cut.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
        cut.ordinaryParse = some (P0.downRecord i) ∧ cut.ordinaryAcceptance) ∨
      (cut.raw = none ∧ cut.rawComparison = some false ∧
        ∃ other, other ≠ CoordinatorLocalArmChoice.storedDownFlatWord P0 i ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pureSecond) other) := by
    rcases hcases with ⟨hraw, hparse, _hlocal, haccept⟩ |
      ⟨hraw, other, hne, hsolvesOther, hcomparison⟩
    · exact Or.inl ⟨hraw, hparse, haccept⟩
    · exact Or.inr ⟨hraw, hcomparison, other, hne, hsolvesOther⟩
  exact threshold_physical_dichotomy rate record i before loggedB post cut
    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) (P0.downRecord i) pureSecond
    ⟨[], cutoffState.downBatch.completed ++ [contaminatedFirst, pureSecond]⟩
    hstatus hlogging hcutJoined hresult hdownB hregister hdecoderLogged hbufferLogged
    hrawCurrent hexpectedP hrejectLocal hbankLogged hcasesLocal


/-- The same actual initialized dispatcher supplies both the inherited pure
bank and the successful physical callback. Local OLD, DOWN, positivity and
inclusive-count selectors occur only after the physical witnesses. -/
theorem actual_first_collection_down_physical_threshold_join :
    ∀ {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count),
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let Q := AffineBatchDecoder.quota p
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let P0 := out.payload
      out.window = B ∧
      P0.sigma.val = s ∧
      (∀ i, (P0.downRecord i).val.sigma = s + 1 ∧ (P0.downRecord i).val.q = 0) ∧
    ∃ (hB : 0 < B.length)
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      (B[0]'hB).input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      P0 = r.payload ∧
      ∀ (n : Fin out.ell), 0 < n.val → ∀ i : Fin (p.m - 1),
      ∃ nB : Fin B.length, nB.val = n.val ∧
      ∃ (hRun : s + (w + n.val) ≤ p.T)
        (hNext : s + (w + n.val + 1) ≤ p.T),
      let record := B[nB.val]
      record.input.state = (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState ∧
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val + 1) hNext
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState = record.output.next ∧
      ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        record.input.state.followers i = .ordinary before memory ∧
        (localPrepared record i).configuration =
          .ordinary before memory ∧
        before.status = .unoccupied ∧
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (before, memory) ∧
        ∃ loggedB cutB post,
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) before =
              .ok loggedB ∧
          loggedB.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
            record.input.row (record.input.state.activations i) record.input.time
            ((localPrepared record i).arm,
              localObservation record i) ∧
          cutB = localCut record i loggedB ∧
          (localPhysicalCall record i before).result =
              .ok post ∧
          (localPhysicalCall record i before).downInput =
              some loggedB ∧
          (localPhysicalCall record i before).down =
              some cutB ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time
            (localObservation record i) before memory post =
              .ok (post, memory) ∧
          (localOutput record i).configuration = .ordinary post memory ∧
          (localOutput record i).failure = none ∧
          (localOutput record i).downInput = some loggedB ∧
          (localOutput record i).down = some cutB ∧
          post.status = .unoccupied ∧
          post.initializationFailure = before.initializationFailure ∧
          (before.lastDown = none →
        (∀ k : Fin (n.val + 1),
          let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
            out.window[k.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt)
              (Nat.lt_of_lt_of_le n.isLt out.withinWindow))
          ∃ prior priorMemory,
            record.input.state.followers i = .ordinary prior priorMemory ∧ prior.lastDown = none ∧
            (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
              ∃ (selected : ReferenceActivePhysicalStep.Selection record.input)
                (choice : ReferencePrelaunchFollower.State p rate.eta)
                (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                record.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P0 ∧ i ∈ selected.view.pendingAtChoice ∧
                ReferenceActiveAffinePositiveTest.downSent record.input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                (localPrepared record i).configuration =
                  .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧ choice.lastDown = none ∧
                ActiveFollowerLifecycle.localStateDomainValid choice ∧
                let own := localObservation record i
                let cut := localCut record i choice
                ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
                  record.input.time ((localPrepared record i).arm, own) choice = .ok choice ∧
                (localOutput record i).downInput = some choice ∧
                (localOutput record i).down = some cut ∧
                ActiveFollowerDownAcceptance.registerInputDomain p rate choice ∧
                ActiveFollowerDownAcceptance.decoderInputDomain p choice.downBatch ∧
                ActiveFollowerDownAcceptance.bufferInputDomain p choice.buffer ∧
                cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) ∧
                cut.rawComparison.isSome = true ∧
                cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i record.input.row record.input.time own rate choice).2 ∧
                cut.filteredRaw = (if cut.raw = cut.expectedWord then cut.raw else none) ∧
                cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
                (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                  p rate record.input.time choice cut.ordinaryParse) ∧
                cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
                (cut.raw ≠ cut.expectedWord → cut.outcome = .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 }
                  cut.raw) ∧
                (cut.outcome = if cut.raw = cut.expectedWord then
                  ActiveFollowerDownAcceptance.downTransition p i record.input.row
                    record.input.time own rate choice
                else .decodeOrParseRejected choice
                  { choice with downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 } cut.raw) ∧
                ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord P0 i)) = some (P0.downRecord i) ∧
                ReferencePrelaunchFollower.acceptedStart choice = 0 ∧ (P0.downRecord i).val.sigma = s + 1 ∧
                (P0.downRecord i).val.sigma ≤ record.input.time.val + 1 ∧
                ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time choice
                  (some (P0.downRecord i)) ∧
                (0 < own.val.val →
                  AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                    (CoordinatorLocalArmChoice.storedDownFlatWord P0 i) = 1))) ∧
        ∃ hBlen : 0 < (B).length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          ((B)[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          (let W0 := cutoffState.downBatch
            let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i (B.take n.val)
            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take n.val)
            before.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
            AffineBatchDecoder.collected before.downBatch =
              AffineBatchDecoder.collected W0 ++ P ∧
            W0.pending.length < Q ∧
            (∀ entry ∈ W0.pending, entry.time.val < s + w) ∧
            (C.map Prod.fst).map Fin.val =
              ReferenceActivePhysicalHorizon.calendar (s + w) n.val ∧
            P.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ P, s + w ≤ entry.time.val ∧ entry.time.val < s + w + n.val) ∧
            (∀ entry ∈ P, entry.sample =
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                entry.time).2 (0, i)) ∧
            (∀ completed ∈ W0.completed,
              completed.length = Q) ∧
            (AffineBatchDecoder.collected W0).Pairwise
              (fun earlier later => earlier.time.val < later.time.val) ∧
            (∀ entry ∈ AffineBatchDecoder.collected W0, entry.time.val < s + w) ∧
            before.downBatch.completed =
              (ReferenceFollowerDownDecoderReplay.foldDownCalls C W0).completed) ∧
          let W0 := cutoffState.downBatch
          let C := ReferenceFollowerDownDecoderReplay.actualDownCalls i ((B).take n.val)
          ∀ (hdown : ActiveFollowerDownAcceptance.downSelected p i
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.row
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time),
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
            ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
            ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              let record : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) :=
                B[nB.val]
              let prep := localPrepared record i
              let own := localObservation record i
              let fixedWord := CoordinatorLocalArmChoice.storedDownFlatWord P0 i
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((B).take n.val)
              let currentEntry : AffineBatchDecoder.Entry p.T
                  (AffineBatchDecoder.width p) :=
                ⟨prep.time, (prep.row.2 prep.time).2 (0, i)⟩
              prep.configuration = .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              (localOutput record i).downInput = some choice ∧
              (localOutput record i).down = some cut ∧
              cut.expectedWord = some fixedWord ∧
              cut.rawComparison.isSome = true ∧
              cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) ∧
              logged = choice ∧
              logged.downBatch = before.downBatch ∧
              logged.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls C W0 ∧
              cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep
                p i record.input.row record.input.time own rate choice).2 ∧
              choice = before ∧ choiceMemory = memory ∧
              logged = loggedB ∧ cut = cutB ∧
              (∀ (hpositive : 0 < own.val.val),
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  ((B).take (n.val + 1))).length =
                    Q - W0.pending.length + Q →
                ∃ contaminatedFirst pureSecond :
                    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                  contaminatedFirst = W0.pending ++ P.take (Q - W0.pending.length) ∧
                  pureSecond = P.drop (Q - W0.pending.length) ++ [currentEntry] ∧
                  contaminatedFirst.length = Q ∧ pureSecond.length = Q ∧
                  (ActiveFollowerDownAcceptance.currentDecodeStep
                    p i record.input.row record.input.time own rate choice).1 =
                    ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩ ∧
                  cut.raw = AffineBatchDecoder.batchOutput pureSecond ∧
                  (∀ entry ∈ pureSecond,
                    AffineChannelLaw.affineHash entry.sample fixedWord = 1) ∧
                  AffineBatchDecoder.satisfies
                    (AffineBatchDecoder.samples pureSecond) fixedWord ∧
                  pureSecond.Pairwise (fun earlier later =>
                    earlier.time.val < later.time.val) ∧
                  (∀ entry ∈ pureSecond,
                    s + w ≤ entry.time.val ∧
                    entry.time.val ≤ s + w + n.val) ∧
                  (∀ entry ∈ pureSecond,
                    entry.sample =
                      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex
                        p source)).2 entry.time).2 (0, i)) ∧
                  ((cut.raw = some fixedWord ∧
                    cut.ordinaryParse = some (P0.downRecord i) ∧
                    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                      record.input.time choice cut.ordinaryParse ∧
                    cut.ordinaryAcceptance) ∨
                   (cut.raw = none ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      cut.rawComparison = some false)) ∧
                  ((cut.raw = some fixedWord ∧
                    ∃ after scan registers lastService,
                      cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                        loggedB after (some fixedWord) (P0.downRecord i) scan registers lastService ∧
                      post = after ∧ post.lastDown = some (P0.downRecord i)) ∨
                   (cut.raw = none ∧ cut.rawComparison = some false ∧
                    ∃ other, other ≠ fixedWord ∧
                      AffineBatchDecoder.satisfies
                        (AffineBatchDecoder.samples pureSecond) other ∧
                      post.downBatch =
                        ⟨[], W0.completed ++ [contaminatedFirst, pureSecond]⟩)))) := by
  intro p rate source rewards C_star C_h count hcross hspan hshort
  change ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) source rewards C_star C_h + count ≤ p.T at hspan
  change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count at hshort
  classical
  intro s epoch w B Q
  have hBResult :=
    actual_physical_callback_family
      rate source rewards C_star C_h count hcross hspan hshort
  have hPResult :=
    ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
      rate source rewards C_star C_h count hcross hspan hshort
  rcases hPResult with ⟨d, hPResult⟩
  let out := d.stream
  let P0 := out.payload
  rcases hPResult with ⟨hwindowRaw, hsigma, hqueues, hprefix⟩
  have hwindow : out.window = B := hwindowRaw
  rcases hBResult with ⟨hB, r, q, base, hcoord, hsigmaB, hzero, hboundary⟩
  change 0 < B.length at hB
  obtain ⟨ce⟩ := out.cutoffExecution
  have houtPos : 0 < out.window.length := by
    rw [hwindow]
    exact hB
  have hhead : out.cutoff.cut = B[0]'hB := by
    calc
      out.cutoff.cut = out.window[0]'houtPos := out.cutoffIsHead.symm
      _ = B[0]'hB := getElem_congr_coll hwindow
  have hlive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      ce.live ce.owned ce.base = .live r q base := by
    calc
      .live ce.live ce.owned ce.base = out.cutoff.cut.input.state.coordinator := ce.actualLive.symm
      _ = (B[0]'hB).input.state.coordinator := congrArg
        (fun record : ReferenceCollectionPhaseHistory.Record p rate => record.input.state.coordinator) hhead
      _ = .live r q base := hcoord
  have hregs : ce.live = r := by
    injection hlive with hregs howned hbase
  have hpayload : P0 = r.payload := by
    calc
      P0 = out.cutoff.payload := out.payloadMatchesCutoff
      _ = ce.live.payload := ce.payloadIsLive
      _ = r.payload := congrArg
        (fun regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => regs.payload) hregs
  have hwindowLocal : out.window = B := hwindow
  refine ⟨d, hwindow, hsigma, hqueues, hB, r, q, base, hcoord, hsigmaB, hzero, hpayload, ?_⟩
  intro n hn i
  let nB : Fin B.length := ⟨n.val, by
    rw [← hwindowLocal]
    exact Nat.lt_of_lt_of_le n.isLt out.withinWindow⟩
  let record : ReferenceCollectionPhaseHistory.Record p rate := B[nB.val]
  refine ⟨nB, rfl, ?_⟩
  have hrecordAtN : out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow) =
      record := getElem_congr_coll hwindowLocal
  obtain ⟨hRun, hNext, hprefixIn, hprefixOut, before, memory, hinput, hprep,
    hstatus, hstart, loggedB, cutB, post, hlogging, hlogBuffer, hcut,
    hresult, hcallInput, hcallCut, hfinish, houtConfig, hfailure,
    houtInput, houtCut, hpostStatus, hinitFlag⟩ := hboundary nB hn i
  refine ⟨hRun, hNext, hprefixIn, hprefixOut, before, memory, hinput, hprep,
    hstatus, hstart, loggedB, cutB, post, hlogging, hlogBuffer, hcut,
    hresult, hcallInput, hcallCut, hfinish, houtConfig, hfailure,
    houtInput, houtCut, hpostStatus, hinitFlag, ?_⟩
  intro hnone
  have hinputOut :
      (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
        .ordinary before memory := by
    rw [hrecordAtN]
    exact hinput
  have hOld := hprefix n hn i before memory hinputOut hnone
  exact join_old_prefix rate source rewards C_star C_h count hcross hspan hshort
    d n hn i hwindowLocal before memory loggedB cutB post
    hprep hstatus hlogging hcut hresult houtInput houtCut hOld

/-- Identify the initialized pure-bank dispatcher with the actual physical
cutoff boundary. This pins the physical live payload to the exact payload used
by the pure-bank threshold witness. -/
theorem actual_first_collection_down_physical_threshold_join_head
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    ∃ hB : 0 < B.length,
    ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
    ∃ q : CoordinatorLiveServiceFinish.OwnedRegisters r,
    ∃ base : Fin (p.m - 1) → ℕ,
      (B[0]'hB).input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
          (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let P0 := out.payload
      out.window = B ∧ P0.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (P0.downRecord i).val.q = 0) ∧
      P0 = r.payload := by
  classical
  intro s epoch w B
  obtain ⟨d, hwindow, hsigma, hqueues, hB, r, q, base, hcoord, hsigmaB,
    hzero, hpayload, _hjoin⟩ := actual_first_collection_down_physical_threshold_join
      rate source rewards C_star C_h count hcross hspan hshort
  exact ⟨hB, r, q, base, hcoord, hsigmaB, hzero, d,
    hwindow, hsigma, (fun i => (hqueues i).2), hpayload⟩

end Bandits.Support.ReferenceFirstCollectionDownPhysicalThresholdJoin

end
