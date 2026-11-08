/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

import Lean.Elab.Tactic.Omega

/-!
# Actual follower DOWN decoder chronology

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-42,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:248-275,290-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,131-138`.

This module follows the literal postlaunch `ReferenceActivePhysicalHorizon.run`
and its `ReferenceActivePhysicalStep.step` records.  Its seed predicate keeps
the ordinary unoccupied follower states, decoder size bounds, chronological
collected entries, and their strict pre-start stamps explicit.  No arbitrary
trace, sent-word condition, decoder-success condition, or global physical
history premise is supplied.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActualInitializationLaunchState
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceFollowerDecoderChronology

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The actual decoder's pre-call size domain. -/
def downBatchWellFormed (batch : AffineBatchDecoder.State p.T
    (AffineBatchDecoder.width p)) : Prop :=
  batch.pending.length < AffineBatchDecoder.quota p ∧
    ∀ completed ∈ batch.completed,
      completed.length = AffineBatchDecoder.quota p

/-- The accumulated positive equations have their actual strict chronological
order, including entries in completed batches and the pending suffix. -/
def downCollectedChronological (batch : AffineBatchDecoder.State p.T
    (AffineBatchDecoder.width p)) : Prop :=
  (AffineBatchDecoder.collected batch).Pairwise
    (fun earlier later => earlier.time.val < later.time.val)

/-- Source-facing local initialization data for one actual postlaunch run.
Each follower starts ordinary and unoccupied; all decoder and chronology
conditions are visible as fields of this predicate. -/
def downBatchSeed (initial : ReferenceActivePhysicalStep.State p rate)
    (start : ℕ) : Prop :=
  ∀ i, ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p),
    initial.followers i = .ordinary state memory ∧
    state.status = .unoccupied ∧
    downBatchWellFormed state.downBatch ∧
    downCollectedChronological state.downBatch ∧
    ∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
      entry.time.val < start

/-- The complete state projection required at an ordinary computed endpoint.
The strict bound is in physical calendar coordinates, with no terminal action
at `start + count`. -/
def downBatchEndpoint (state : ReferencePrelaunchFollower.State p rate.eta)
    (bound : ℕ) : Prop :=
  downBatchWellFormed state.downBatch ∧
  downCollectedChronological state.downBatch ∧
  ∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
    entry.time.val < bound

/-- Initial ordinary followers have empty, well-formed, chronological DOWN
batches. Their collected entries are vacuously before any run origin. -/
theorem initial_downBatchEndpoint (bound : ℕ) :
    downBatchEndpoint (ReferencePrelaunchFollower.initial p rate.eta) bound := by
  refine ⟨?_, ?_, ?_⟩
  · simp [downBatchWellFormed, ReferencePrelaunchFollower.initial,
      AffineBatchDecoder.initial, AffineBatchDecoder.quota_pos]
  · simp [downCollectedChronological, ReferencePrelaunchFollower.initial,
      AffineBatchDecoder.initial, AffineBatchDecoder.collected]
  · simp [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
      AffineBatchDecoder.collected]

/-- A source replay starts unoccupied with a well-formed DOWN batch and a
chronological equation list. Its time stamps are strictly before the replay
horizon `n`. -/
theorem replay_downBatchEndpoint {n : ℕ} (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p)
    (history : ReferencePrelaunchFollower.LocalHistory p n)
    (hn : n ≤ p.T) :
    (ReferencePrelaunchFollower.replay rate.eta i row activation history hn).status =
        .unoccupied ∧
      downBatchWellFormed
        (ReferencePrelaunchFollower.replay rate.eta i row activation history hn).downBatch ∧
      downCollectedChronological
        (ReferencePrelaunchFollower.replay rate.eta i row activation history hn).downBatch ∧
      ∀ entry ∈ AffineBatchDecoder.collected
          (ReferencePrelaunchFollower.replay rate.eta i row activation history hn).downBatch,
        entry.time.val < n := by
  have hstatus :=
    (ReferencePrelaunchFollower.replay_registers rate.eta i row activation history hn).2.2.2.2.2
  obtain ⟨hk, hc, _⟩ := ReferencePrelaunchFollower.replay_batch_spec
    rate.eta i row activation history hn
  refine ⟨hstatus, ⟨hk, hc⟩,
    ReferencePrelaunchFollower.replay_collected_pairwise rate.eta i row activation history hn,
    ?_⟩
  intro entry hentry
  obtain ⟨u, _, _, _, _, htime, _⟩ :=
    (ReferencePrelaunchFollower.replay_collected_mem_iff rate.eta i row activation
      history hn entry).mp hentry
  rw [htime]
  exact u.isLt

/-- Appending this round's decoder input preserves its literal batch size
domain and appends exactly its eligible positive sample. -/
theorem currentDecodeStep_batch_spec (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hbatch : downBatchWellFormed state.downBatch) :
    downBatchWellFormed
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 ∧
      AffineBatchDecoder.collected
          (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 =
        AffineBatchDecoder.collected state.downBatch ++
          AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state))
            time := by
  obtain ⟨hpending, hcompleted, hcollected⟩ := AffineBatchDecoder.step_spec p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state))
    state.downBatch time hbatch.1 hbatch.2
  refine ⟨?_, ?_⟩
  · change (AffineBatchDecoder.step p _ state.downBatch time).pending.length < _ ∧ _
    exact ⟨hpending, hcompleted⟩
  · simpa only [ActiveFollowerDownAcceptance.currentDecodeStep,
      AffineBatchDecoder.decodeStep] using hcollected

/-- A returned word can only come from a completed quota batch, whose pending
suffix is cleared by the literal decoder step. -/
private theorem currentDecodeStep_pending_empty_of_some
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hbatch : downBatchWellFormed state.downBatch)
    (hword : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).2 =
      some word) :
    (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1.pending = [] := by
  let trace := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state)
  have houtput : AffineBatchDecoder.stepOutput p trace state.downBatch time = some word := by
    simpa [ActiveFollowerDownAcceptance.currentDecodeStep, trace,
      AffineBatchDecoder.decodeStep] using hword
  have hquota := (AffineBatchDecoder.stepOutput_eq_some_iff p trace state.downBatch time word).mp
    houtput
  have hlen : (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace time).length ≤
      AffineBatchDecoder.quota p := by
    have hpending := hbatch.1
    by_cases heligible : AffineBatchDecoder.eligible (trace time)
    · simp [AffineBatchDecoder.positiveAt, heligible]
      omega
    · simp [AffineBatchDecoder.positiveAt, heligible]
      exact hbatch.1.le
  have heq : (state.downBatch.pending ++ AffineBatchDecoder.positiveAt p trace time).length =
      AffineBatchDecoder.quota p := by omega
  change (AffineBatchDecoder.step p trace state.downBatch time).pending = []
  simp [AffineBatchDecoder.step, heq]

/-- One actual eligible-input-or-no-op decoder call preserves the batch bounds
and appends only entries stamped at the supplied physical round. -/
private theorem currentDecodeStep_downBatchEndpoint
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (bound : ℕ)
    (hbound : time.val = bound) (hbefore : downBatchEndpoint state bound) :
    downBatchEndpoint
      {state with downBatch :=
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1}
      (bound + 1) := by
  have hbatch := currentDecodeStep_batch_spec i row time observation state hbefore.1
  let trace := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate state)
  have hpositivePair : (AffineBatchDecoder.positiveAt p trace time).Pairwise
      (fun earlier later => earlier.time.val < later.time.val) := by
    unfold AffineBatchDecoder.positiveAt
    split_ifs <;> simp
  have hpositiveTime : ∀ entry ∈ AffineBatchDecoder.positiveAt p trace time,
      entry.time.val = time.val := by
    intro entry hentry
    unfold AffineBatchDecoder.positiveAt at hentry
    split_ifs at hentry <;> simp_all [AffineBatchDecoder.entry]
  have hpair :
      (AffineBatchDecoder.collected state.downBatch ++
        AffineBatchDecoder.positiveAt p trace time).Pairwise
          (fun earlier later => earlier.time.val < later.time.val) := by
    rw [List.pairwise_append]
    refine ⟨hbefore.2.1, hpositivePair, ?_⟩
    intro earlier hearlier later hlater
    have htime := hpositiveTime later hlater
    have hold := hbefore.2.2 earlier hearlier
    omega
  refine ⟨hbatch.1, ?_, ?_⟩
  · simpa [downCollectedChronological, hbatch.2] using hpair
  · intro entry hentry
    rw [hbatch.2] at hentry
    rcases List.mem_append.mp hentry with hold | hnew
    · exact lt_trans (hbefore.2.2 entry hold) (Nat.lt_succ_self bound)
    · have heq := hpositiveTime entry hnew
      omega

/-- Bounds remain true while a physical follower is being serviced: service
does not edit any collected equation or decoder size field. -/
private theorem downBatchEndpoint_mono
    (state : ReferencePrelaunchFollower.State p rate.eta) {oldBound newBound : ℕ}
    (hbound : oldBound ≤ newBound) (hbefore : downBatchEndpoint state oldBound) :
    downBatchEndpoint state newBound := by
  refine ⟨hbefore.1, hbefore.2.1, ?_⟩
  intro entry hentry
  exact lt_of_lt_of_le (hbefore.2.2 entry hentry) hbound

/-- Every successful actual DOWN cut on an unoccupied choice state retains
the exact decoder state. This includes a suppressed wrong unique word, parser
rejection, local acceptance rejection, and completed ambiguity; all of them
retain the decoder's returned batch. A skipped unselected call is the literal
decoder no-op. -/
private theorem referenceDownCut_success_batch
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hbatch : downBatchWellFormed state.downBatch)
    (hout : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
        .ok post) :
    post.downBatch =
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 ∧
      (post.status ≠ .unoccupied →
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1.pending = []) := by
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
      simpa [downBatchWellFormed, ActiveFollowerDownAcceptance.decoderInputDomain] using hbatch
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
        refine ⟨(congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm, ?_⟩
        intro hoccupied
        have hstatusPost : post.status = state.status := by
          exact (congrArg ReferencePrelaunchFollower.State.status hpost).symm
        rw [hstatusPost, hstatus] at hoccupied
        exact (hoccupied rfl).elim
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
              refine ⟨(congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm, ?_⟩
              intro hoccupied
              have hraw : decoded.2 ≠ none := by
                intro hnone
                rw [hnone] at hparsed
                change OrdinaryMessageCodec.parseDown
                  (ReferencePrelaunchFollower.codecParams p rate.eta) none = some message at hparsed
                rw [OrdinaryMessageCodec.parseDown] at hparsed
                simp at hparsed
              by_cases hend : scan.endpoint = time.val + 2
              · cases hword : decoded.2 with
                | none => exact (hraw hword).elim
                | some word =>
                    exact currentDecodeStep_pending_empty_of_some i row time observation state word
                      hbatch (by simpa [decoded] using hword)
              · have hstatusPost : post.status = .unoccupied := by
                  have hstatusEq := congrArg ReferencePrelaunchFollower.State.status hpost
                  simpa [hend] using hstatusEq.symm
                exact (hoccupied hstatusPost).elim
        · have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
              .parsedButUnaccepted state { state with downBatch := decoded.1 }
                decoded.2 message := by
            simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
              hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected, haccepted]
          rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
          have hpost := Except.ok.inj hout
          refine ⟨(congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm, ?_⟩
          intro hoccupied
          have hstatusPost : post.status = state.status :=
            (congrArg ReferencePrelaunchFollower.State.status hpost).symm
          rw [hstatusPost, hstatus] at hoccupied
          exact (hoccupied rfl).elim
    · have hcut : (ReferenceDownReception.referenceDownCut p view i row time observation rate state).outcome =
          .decodeOrParseRejected state { state with downBatch := decoded.1 } decoded.2 := by
        simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregisters, hdecoder, hbuffer, decoded, hmatches]
      rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
      have hpost := Except.ok.inj hout
      refine ⟨(congrArg ReferencePrelaunchFollower.State.downBatch hpost).symm, ?_⟩
      intro hoccupied
      have hstatusPost : post.status = state.status :=
        (congrArg ReferencePrelaunchFollower.State.status hpost).symm
      rw [hstatusPost, hstatus] at hoccupied
      exact (hoccupied rfl).elim
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
        intro h
        exact hnotEligible (by simpa [ActiveFollowerDownAcceptance.currentInputExtension] using h))
    rw [hcut, DeclaredFollowerLocalRound.consumeDownResult] at hout
    have hpost : state = post := Except.ok.inj hout
    have hdecoded := congrArg Prod.fst hdecode
    refine ⟨?_, ?_⟩
    · rw [← hpost, ActiveFollowerDownAcceptance.currentDecodeStep, hdecoded]
    · intro hoccupied
      rw [← hpost, hstatus] at hoccupied
      exact (hoccupied rfl).elim

/-- A successful local PREPARE keeps the entire DOWN batch across its
beginning-of-round interruption. The actual wrapper's follower projection is
the `DeclaredFollowerLocalRound.prepare` call. -/
private theorem startRound_unoccupied_status
    (time : Fin p.T) (state choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time state memory =
      .ok (choice, choiceMemory))
    (hunoccupied : state.status = .unoccupied) :
    choice.status = .unoccupied := by
  classical
  unfold ActiveFollowerLifecycle.startRound at hstart
  cases hdecision : ActiveFollowerLifecycle.interruptionDecision rate.eta time state memory with
  | error failure => simp [hdecision] at hstart
  | ok interrupted =>
      simp [hdecision] at hstart
      rcases hstart with ⟨hstate, _⟩
      rw [← hstate]
      simp [hunoccupied]

private theorem local_prepare_downBatch_frame
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1)
    (state choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (DeclaredFollowerLocalRound.prepare rate i row activation time hactive
      (.ordinary state memory)).configuration = .ordinary choice choiceMemory) :
    choice.downBatch = state.downBatch ∧
      (state.status = .unoccupied → choice.status = .unoccupied) := by
  classical
  unfold DeclaredFollowerLocalRound.prepare at hprep
  cases hstart : ActiveFollowerLifecycle.startRound rate.eta time state memory with
  | error reason => simp [hstart] at hprep
  | ok pair =>
    cases pair with
    | mk choiceState choiceMem =>
      cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time
          choiceState with
      | failure => simp [hstart, hoff] at hprep
      | noOffer =>
        cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time i none with
        | none => simp [hstart, hoff, hchoice] at hprep
        | some arm =>
          simp [hstart, hoff, hchoice] at hprep
          rcases hprep with ⟨rfl, rfl⟩
          exact ⟨(ActiveFollowerLifecycle.startRound_frame rate.eta time state choiceState
            memory choiceMem hstart).2.2.2.2.1,
            startRound_unoccupied_status time state choiceState memory choiceMem hstart⟩
      | offer offered =>
        cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time i
            (some offered) with
        | none => simp [hstart, hoff, hchoice] at hprep
        | some arm =>
          simp [hstart, hoff, hchoice] at hprep
          rcases hprep with ⟨rfl, rfl⟩
          exact ⟨(ActiveFollowerLifecycle.startRound_frame rate.eta time state choiceState
            memory choiceMem hstart).2.2.2.2.1,
            startRound_unoccupied_status time state choiceState memory choiceMem hstart⟩

/-- The interruption frame specialized to an actual successful prepared
follower. If it was already unoccupied, its full partial batch is retained. If
it becomes unoccupied from an occupied state, the occupied invariant transfers
the empty pending bank through the same frame. -/
theorem run_interruption_downBatch_frame
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hoccupied : state.status ≠ .unoccupied → state.downBatch.pending = []) :
    choice.downBatch = state.downBatch ∧
      (state.status ≠ .unoccupied → choice.status = .unoccupied →
        choice.downBatch.pending = []) ∧
      (state.status = .unoccupied → choice.status = .unoccupied) := by
  have hstep : record.output = ReferenceActivePhysicalStep.step record.input := record.output_eq
  have hlocal := record.output.preparation.followers.followers_eq i
  rw [hstep] at hlocal
  simp only [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.followerInput,
    ReferenceActiveFeedbackCut.prepareFollowers] at hlocal
  have hprojection := congrArg
    (fun prepared : DeclaredFollowerLocalRound.PreparedRound p rate => prepared.configuration) hlocal
  have hprep : (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (.ordinary state memory)).configuration = .ordinary choice choiceMemory := by
    have hprepared' := hprepared
    rw [hstep] at hprepared'
    simp only [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput] at hprepared'
    rw [hprojection, hinput] at hprepared'
    exact hprepared'
  have hframe := local_prepare_downBatch_frame i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    state choice memory choiceMemory hprep
  refine ⟨hframe.1, ?_, hframe.2⟩
  intro hwasOccupied _hnowUnoccupied
  rw [hframe.1]
  exact hoccupied hwasOccupied

/-- Actual PREPARE projection: the computed prepared follower retains the
whole batch, and its pending bank is empty whenever it remains occupied. -/
theorem run_prepared_follower_downBatch_spec
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hbefore : downBatchEndpoint state bound)
    (hoccupied : state.status ≠ .unoccupied → state.downBatch.pending = []) :
    downBatchEndpoint choice bound ∧
      (choice.status ≠ .unoccupied → choice.downBatch.pending = []) := by
  have hframe := run_interruption_downBatch_frame record i state choice memory choiceMemory
    hinput hprepared hoccupied
  refine ⟨?_, ?_⟩
  · simpa [downBatchEndpoint, hframe.1] using hbefore
  · intro hchoiceOccupied
    by_cases hstateOccupied : state.status = .unoccupied
    · exact (hchoiceOccupied (hframe.2.2 hstateOccupied)).elim
    · rw [hframe.1]
      exact hoccupied hstateOccupied

/-- The reference-only DOWN decoder receives the same single current row
input as the accepted follower replay adapter when the actual round is active
and the follower is unoccupied. -/
private theorem currentDecodeStep_eq_decodeAt_fst
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hunoccupied : state.status = .unoccupied)
    (hbatch : downBatchWellFormed state.downBatch) :
    (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own.2 rate state).1 =
      (ReferencePrelaunchFollower.decodeAt i row activation time own state.downBatch).1 := by
  classical
  let selected := PublicDiscreteDraws.slotDraw (row.2 time).1 =
      PublicDiscreteDraws.downSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = i
  have hselected : decide selected =
      decide (activation.val ≤ time.val + 1 ∧ selected) := by
    by_cases hs : selected <;> simp [hs, hactive]
  have hinput : ActiveFollowerDownAcceptance.currentRoundInput p i row time own.2 rate state =
      ReferencePrelaunchFollower.downInput i row activation time own := by
    simp only [ActiveFollowerDownAcceptance.currentRoundInput,
      ReferencePrelaunchFollower.downInput, hunoccupied]
    rw [hselected]
    rfl
  have hcurrent :
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time own.2 rate state)) time =
        (ReferencePrelaunchFollower.traceAt i row activation time own) time := by
    simpa only [ActiveFollowerDownAcceptance.currentInputExtension,
      ReferencePrelaunchFollower.traceAt] using hinput
  have hdecode := ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i row time own.2 rate state))
    (ReferencePrelaunchFollower.traceAt i row activation time own) state.downBatch time hcurrent
  calc
    (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own.2 rate state).1 =
        (AffineBatchDecoder.decodeStep p
          (ReferencePrelaunchFollower.traceAt i row activation time own) state.downBatch time).1 := by
            simpa only [ActiveFollowerDownAcceptance.currentDecodeStep] using
              congrArg Prod.fst hdecode
    _ = (AffineBatchDecoder.step p
          (ReferencePrelaunchFollower.traceAt i row activation time own) state.downBatch time) := by
            rfl
    _ = (ReferencePrelaunchFollower.decodeAt i row activation time own state.downBatch).1 := by
          symm
          exact ReferencePrelaunchFollower.decodeAt_fst i row activation time own
            state.downBatch hbatch.1

/-- A successful post-observation logging/DOWN operation advances exactly the
same follower decoder call as the accepted replay adapter. Every DOWN outcome
that returns an ordinary state is included, including suppressed mismatches. -/
private theorem recordFollower_downBatch_eq_step
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (hbatch : downBatchWellFormed state.downBatch)
    (hoccupied : state.status ≠ .unoccupied → state.downBatch.pending = [])
    (hresult : (ReferenceActivePhysicalStep.recordFollower view i row activation time
      hactive arm observation state).result = .ok post) :
    post.downBatch =
      (ReferencePrelaunchFollower.step i row activation time (arm, observation) state).downBatch ∧
    (post.status ≠ .unoccupied → post.downBatch.pending = []) := by
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
        have hloggedWell : downBatchWellFormed logged.downBatch := by
          rw [hloggedBatch]
          exact hbatch
        have hcutBatch := referenceDownCut_success_batch view i row time observation logged post
          hloggedUnoccupied hloggedWell hcutResult
        have hdecode := currentDecodeStep_eq_decodeAt_fst i row activation time hactive
          (arm, observation) logged hloggedUnoccupied hloggedWell
        have hsame :
            (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).1 =
              (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 := by
          simp [ActiveFollowerDownAcceptance.currentDecodeStep,
            ActiveFollowerDownAcceptance.currentRoundInput, hloggedBatch, hloggedStatus]
        refine ⟨?_, ?_⟩
        · calc
            post.downBatch =
                (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).1 :=
              hcutBatch.1
            _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state).1 :=
              hsame
            _ = (ReferencePrelaunchFollower.decodeAt i row activation time (arm, observation)
                  state.downBatch).1 :=
              currentDecodeStep_eq_decodeAt_fst i row activation time hactive
                (arm, observation) state hunoccupied hbatch
            _ = (ReferencePrelaunchFollower.step i row activation time (arm, observation)
                  state).downBatch := by
              simp [ReferencePrelaunchFollower.step, hunoccupied]
        · intro hpostOccupied
          rw [hcutBatch.1]
          exact hcutBatch.2 hpostOccupied
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
          (rate.n) state result.arrival
        have hbatchOut : result.output.downBatch = state.downBatch := by
          rw [result.queueUpdate]
          exact hframe.2.1
        have hbatchPost : post.downBatch = state.downBatch := by
          rw [← hpost]
          exact hbatchOut
        have hstatusPost : post.status = state.status := by
          rw [← hpost]
          rw [result.queueUpdate]
          exact hframe.2.2.2.1
        refine ⟨?_, ?_⟩
        · simpa [ReferencePrelaunchFollower.step, hunoccupied] using hbatchPost
        · intro hpostOccupied
          have hstateOccupied : state.status ≠ .unoccupied := by
            simpa [hstatusPost] using hpostOccupied
          rw [hbatchPost]
          exact hoccupied hstateOccupied

/-- If the actual observer returns an ordinary configuration, both its
recording and release/finish stages were successful on the literal calls. -/
private theorem finishFollower_ordinary_projection
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
      (postRecord : ReferencePrelaunchFollower.State p rate.eta),
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

/-- The release test can change status, and EndRound can change proposal
memory; neither changes a decoder bank on a successful physical call. -/
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
    next.downBatch = post.downBatch ∧
      (choice.status = .unoccupied → next = post) := by
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
          refine ⟨?_, ?_⟩
          · calc
              next.downBatch = result.1.downBatch :=
                congrArg ReferencePrelaunchFollower.State.downBatch hresult.1.symm
              _ = released.downBatch :=
                congrArg ReferencePrelaunchFollower.State.downBatch hstate
              _ = post.downBatch := hreleased
          · intro hunoccupied
            have hreleaseUnoccupied := ActiveFollowerLifecycle.releaseAfterService_unoccupied
              rate.eta i time (ActiveFollowerLifecycle.publicRowOfCompleteRow row time)
              observation choice post hunoccupied
            have hreleasedPost : released = post := by
              rw [hreleaseUnoccupied] at hreleaseEq
              exact (Except.ok.inj hreleaseEq).symm
            calc
              next = result.1 := hresult.1.symm
              _ = released := hstate
              _ = post := hreleasedPost

/-- Exact post-observation projection for a successful actual prepared
follower. An unoccupied choice appends only this round's eligible positive
equation; occupied service preserves the whole decoder state. -/
theorem preparedFollower_downBatch_spec
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hprepared : prepared.configuration = .ordinary choice choiceMemory)
    (hbefore : downBatchEndpoint choice bound)
    (hoccupied : choice.status ≠ .unoccupied → choice.downBatch.pending = [])
    (hbound : prepared.time.val = bound)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    downBatchEndpoint next (bound + 1) ∧
      (next.status ≠ .unoccupied → next.downBatch.pending = []) := by
  obtain ⟨actualChoice, actualMemory, postRecord, hactualPrepared, hrecord, hfinish⟩ :=
    finishFollower_ordinary_projection view prepared observation next nextMemory hout
  have hconfig :
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary actualChoice actualMemory :
        DeclaredFollowerLocalRound.LocalConfiguration p rate) = .ordinary choice choiceMemory :=
    hactualPrepared.symm.trans hprepared
  injection hconfig with hchoiceState hchoiceMemory
  subst actualChoice
  subst actualMemory
  have hrecordBatch := recordFollower_downBatch_eq_step view prepared.follower prepared.row
    prepared.activation prepared.time prepared.active prepared.arm observation choice postRecord
    hbefore.1 hoccupied hrecord
  have hreleaseFrame := releaseAndFinish_downBatch_frame prepared.follower prepared.row
    prepared.time observation choice choiceMemory postRecord next nextMemory hfinish
  have hnextBatch : next.downBatch = postRecord.downBatch := hreleaseFrame.1
  have hpostEndpoint : downBatchEndpoint postRecord (bound + 1) := by
    by_cases hunoccupied : choice.status = .unoccupied
    · have hdecode := currentDecodeStep_downBatchEndpoint prepared.follower prepared.row
        prepared.time observation choice bound hbound hbefore
      have hsame :
          (ReferencePrelaunchFollower.step prepared.follower prepared.row prepared.activation
            prepared.time (prepared.arm, observation) choice).downBatch =
            (ActiveFollowerDownAcceptance.currentDecodeStep p prepared.follower prepared.row
              prepared.time observation rate choice).1 := by
        simp only [ReferencePrelaunchFollower.step, hunoccupied]
        symm
        exact currentDecodeStep_eq_decodeAt_fst prepared.follower prepared.row
          prepared.activation prepared.time prepared.active (prepared.arm, observation)
          choice hunoccupied hbefore.1
      have hpostBatch : postRecord.downBatch =
          (ActiveFollowerDownAcceptance.currentDecodeStep p prepared.follower prepared.row
            prepared.time observation rate choice).1 := hrecordBatch.1.trans hsame
      simpa [downBatchEndpoint, hpostBatch] using hdecode
    · have hsame :
          (ReferencePrelaunchFollower.step prepared.follower prepared.row prepared.activation
            prepared.time (prepared.arm, observation) choice).downBatch = choice.downBatch := by
        simp [ReferencePrelaunchFollower.step, hunoccupied]
      have hpostBatch : postRecord.downBatch = choice.downBatch := hrecordBatch.1.trans hsame
      have hmono := downBatchEndpoint_mono choice (Nat.le_succ bound) hbefore
      simpa [downBatchEndpoint, hpostBatch] using hmono
  have hbatchEndpoint : downBatchEndpoint next (bound + 1) := by
    simpa [downBatchEndpoint, hnextBatch] using hpostEndpoint
  refine ⟨hbatchEndpoint, ?_⟩
  intro hnextOccupied
  by_cases hunoccupied : choice.status = .unoccupied
  · have hsameState := hreleaseFrame.2 hunoccupied
    have hpostOccupied : postRecord.status ≠ .unoccupied := by
      simpa [hsameState] using hnextOccupied
    rw [hnextBatch]
    exact hrecordBatch.2 hpostOccupied
  · have hsame :
        (ReferencePrelaunchFollower.step prepared.follower prepared.row prepared.activation
          prepared.time (prepared.arm, observation) choice).downBatch = choice.downBatch := by
      simp [ReferencePrelaunchFollower.step, hunoccupied]
    rw [hnextBatch, hrecordBatch.1, hsame]
    exact hoccupied hunoccupied

/-- Actual RoundRecord projection across PREPARE, feedback, DOWN observation,
release, and EndRound. This reads the stored `record.input` and the actual
`RoundRecord.output`; the computed time remains an explicit calendar binder. -/
theorem run_round_follower_downBatch_spec
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (bound : ℕ)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hbefore : downBatchEndpoint state bound)
    (hoccupied : state.status ≠ .unoccupied → state.downBatch.pending = [])
    (hroundTime : (record.output.preparation.followers.followers i).time.val = bound)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    downBatchEndpoint next (bound + 1) ∧
      (next.status ≠ .unoccupied → next.downBatch.pending = []) := by
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := record.output.preparation.coordinator.downView
  have hstep : record.output = ReferenceActivePhysicalStep.step record.input := record.output_eq
  have hobserve :
      (record.output.preparation.observeFollower i).configuration = .ordinary next nextMemory := by
    have hout' := hout
    rw [hstep] at hout'
    rw [hstep]
    simpa [ReferenceActivePhysicalStep.step] using hout'
  have hfinish : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    simpa [view, prepared, observation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hobserve
  obtain ⟨choice, choiceMemory, _, hprepared, _, _⟩ :=
    finishFollower_ordinary_projection view prepared observation next nextMemory hfinish
  have hprep := run_prepared_follower_downBatch_spec record i state choice memory choiceMemory
    bound hinput hprepared hbefore hoccupied
  exact preparedFollower_downBatch_spec view prepared observation choice choiceMemory next nextMemory
    bound hprepared hprep.1 hprep.2 hroundTime hfinish

private theorem roundRecord_prepared_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    (record.output.preparation.followers.followers i).time = record.input.time := by
  have htime := (ReferenceActivePhysicalStep.prepare record.input).follower_alignment i
  rw [record.output_eq]
  simpa [ReferenceActivePhysicalStep.step] using htime.2.2.1

/-- The actual finite calendar preserves decoder validity, chronological
collection, strict pre-endpoint stamps, and occupied pending emptiness at each
ordinary final follower. The induction follows `run_successor_step`; its
one-round premise is the stored `RoundRecord`, not a separately supplied trace.
-/
theorem run_downBatch_spec
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : downBatchSeed initial start)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.followers i = .ordinary state memory) :
    downBatchEndpoint state (start + count) ∧
      (state.status ≠ .unoccupied → state.downBatch.pending = []) := by
  revert i state memory hspan hordinary
  induction count with
  | zero =>
      intro hspan i state memory hordinary
      have hrun := ReferenceActivePhysicalHorizon.run_zero_final initial rows selected
        rewards start hspan hmode
      rw [hrun] at hordinary
      obtain ⟨seedState, seedMemory, hconfig, hstatus, hwell, hchron, hstamp⟩ := hseed i
      have hstates : DeclaredFollowerLocalRound.LocalConfiguration.ordinary seedState seedMemory =
          DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory :=
        hconfig.symm.trans hordinary
      cases hstates
      refine ⟨⟨hwell, hchron, ?_⟩, ?_⟩
      · intro entry hentry
        exact lt_of_lt_of_le (hstamp entry hentry) (Nat.le_refl _)
      · intro hoccupied
        rw [hstatus] at hoccupied
        exact (hoccupied rfl).elim
  | succ count ih =>
      intro hspan i state memory hordinary
      have hprevSpan : start + count ≤ p.T := by omega
      let acc := ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hprevSpan hmode
      let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
        ⟨start + count, by omega, by omega⟩
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        start hmode acc entry
      let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
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
          have hbeforeEndpoint := ih hprevSpan i before beforeMemory (by
            simpa [acc] using hbefore)
          have hinput : record.input.state.followers i = .ordinary before beforeMemory := by
            simp [record, input, ReferenceActivePhysicalHorizon.roundInputAt, acc, hbefore]
          have hroundTime :
              (record.output.preparation.followers.followers i).time.val = start + count := by
            rw [roundRecord_prepared_time record i]
            simp [record, input, ReferenceActivePhysicalHorizon.roundInputAt, acc, entry]
          have hround := run_round_follower_downBatch_spec record i before state
            beforeMemory memory (start + count) hinput hbeforeEndpoint.1 hbeforeEndpoint.2
            hroundTime hrecordNext
          simpa [Nat.add_assoc] using hround

/-- The named occupied-empty projection of the actual run theorem. -/
theorem run_occupied_pending_empty
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : downBatchSeed initial start)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).finalState.followers i = .ordinary state memory) :
    state.status ≠ .unoccupied → state.downBatch.pending = [] :=
  (run_downBatch_spec initial rows selected rewards start count hspan hmode hseed
    i state memory hordinary).2

/-- The actual launch adapter supplies the seed required by the postlaunch
calendar theorem. Its full accepted-boundary context is retained. Existing
followers use the replay at the clipped completed-block stop; inactive and
forced-at-launch followers reduce to the literal initial state. -/
theorem ofActualLaunchedBoundary_downBatchSeed
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
        source rewards actual)).disposition = .launched launch learnerSeed) :
    downBatchSeed
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let finished := ReferenceInitializationRun.finishBlock x b h
  intro i
  obtain ⟨state, memory, hconfig, hstate, _, _, _, _, _, hstatus, _⟩ :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  have hordEndpoint : downBatchEndpoint
      (ReferenceInitializationRun.ordinary x finished
        (ActualReferenceInitializationBlock.refFollower i))
      (BootstrapObservedFollower.blockStop p block) := by
    let follower := ActualReferenceInitializationBlock.refFollower i
    by_cases hforced : finished.forcedFailure follower = true
    · have hinitial : ReferenceInitializationRun.ordinary x finished follower =
          ReferencePrelaunchFollower.initial p rate.eta := by
        simp [ReferenceInitializationRun.ordinary, hforced, x,
          ActualReferenceInitializationBlock.referenceInput,
          ReferencePrelaunchFollower.forcedAtLaunch]
      rw [hinitial]
      simpa [x, ActualReferenceInitializationBlock.referenceInput] using
        initial_downBatchEndpoint (BootstrapObservedFollower.blockStop p block)
    · have hforced' : finished.forcedFailure follower = false := by
        cases h : finished.forcedFailure follower <;> simp_all
      by_cases hunactivated : finished.activation follower = none
      · have hinitial : ReferenceInitializationRun.ordinary x finished follower =
            ReferencePrelaunchFollower.initial p rate.eta := by
          simp [ReferenceInitializationRun.ordinary, hforced', hunactivated, x,
            ActualReferenceInitializationBlock.referenceInput]
        rw [hinitial]
        simpa [x, ActualReferenceInitializationBlock.referenceInput] using
          initial_downBatchEndpoint (BootstrapObservedFollower.blockStop p block)
      · obtain ⟨activation, hactivation⟩ :
            ∃ activation, finished.activation follower = some activation := by
          cases h : finished.activation follower <;> simp_all
        let horizon := ReferenceInitializationRun.elapsed p (b.completed + 1)
        let history := finished.history
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        let replay := ReferencePrelaunchFollower.replay rate.eta
          (BootstrapPhysicalInput.sourceFollowerIndex p follower) x.row activation history
          (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        have hreplay := replay_downBatchEndpoint (p := p) (rate := rate)
          (BootstrapPhysicalInput.sourceFollowerIndex p follower) x.row activation history
          (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        have htime : horizon = BootstrapObservedFollower.blockStop p block := by
          simp [horizon, ReferenceInitializationRun.elapsed,
            BootstrapObservedFollower.blockStop, block,
            ReferenceInitializationRun.nextBlock]
        have hreplayEndpoint : downBatchEndpoint replay horizon := by
          exact ⟨hreplay.2.1, hreplay.2.2.1, hreplay.2.2.2⟩
        have hplayer : PublicDiscreteDraws.followerPlayer p.two_le_m follower =
            PublicDiscreteDraws.followerPlayer p.two_le_m i := by
          apply Fin.ext
          rfl
        have hordinary : ReferenceInitializationRun.ordinary x finished follower = replay := by
          simp [ReferenceInitializationRun.ordinary, hforced', hactivation,
            replay, history, x, ActualReferenceInitializationBlock.referenceInput,
            ReferencePrelaunchFollower.atLaunch, hplayer]
        rw [hordinary, ← htime]
        exact hreplayEndpoint
  refine ⟨state, memory, hconfig, hstatus, ?_, ?_, ?_⟩
  · rw [hstate]
    exact hordEndpoint.1
  · rw [hstate]
    exact hordEndpoint.2.1
  · intro entry hentry
    have hentry' : entry ∈ AffineBatchDecoder.collected
        (ReferenceInitializationRun.ordinary x finished
          (ActualReferenceInitializationBlock.refFollower i)).downBatch := by
      simpa [hstate] using hentry
    exact hordEndpoint.2.2 entry hentry'

end Bandits.Support.ReferenceFollowerDecoderChronology

end
