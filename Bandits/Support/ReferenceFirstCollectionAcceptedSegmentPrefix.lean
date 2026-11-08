/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCheckedSourcePrefix
public import Bandits.Support.ReferenceFirstCollectionAcceptedReadyStep

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# The actual first collection segment through an accepted current round

The current ready-domain selector and the effective parse/acceptance tests
are explicit inputs. The actual accepted-step producer supplies START,
reception and FINISH. The source-prefix producer supplies the cutoff and
strictly earlier completed operations. Their combination identifies the
current record in the existing segment extraction and initializes the checked
prefix through that record. Nothing here assumes survival of future records.

Mathematical evidence:
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This is internal operational mathematics. Segment membership alone gives no
calendar queue/score truth. The numerical splice using the accepted canonical
cutoff, queue continuation, the original source readouts and replay append
remains a separate producer.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCollectionAcceptedSegmentPrefix

variable {p : ConstructorDimensions.Parameters}

private theorem take_eq_of_prefix {α : Type*} (xs ys : List α)
    (hprefix : xs <+: ys) (k : ℕ) (hk : k ≤ xs.length) :
    xs.take k = ys.take k := by
  obtain ⟨rest, rfl⟩ := hprefix
  rw [List.take_append, Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]

/-- Only the finite inspected prefix is required to pass the continuation
test. The uninspected suffix may fail immediately. -/
private theorem take_takeWhile_of_prefix {α : Type*} (xs : List α)
    (test : α → Bool) (k : ℕ) (hk : k ≤ xs.length)
    (hall : ∀ i : Fin k, test (xs[i.val]'(Nat.lt_of_lt_of_le i.isLt hk)) = true) :
    (xs.takeWhile test).take k = xs.take k ∧
      k ≤ (xs.takeWhile test).length := by
  have hself : (xs.take k).takeWhile test = xs.take k := by
    apply List.takeWhile_eq_self_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hiK : i < k := by
      have hlen : (xs.take k).length = k := List.length_take_of_le hk
      omega
    have h := hall ⟨i, hiK⟩
    have hxi' : xs[i]'(by omega) = x := by
      simpa only [List.getElem_take] using hxi
    rw [← hxi']
    exact h
  have heq : (xs.takeWhile test).take k = xs.take k := by
    rw [List.take_takeWhile, hself]
  refine ⟨heq, ?_⟩
  have hlen := congrArg List.length heq
  simp only [List.length_take, Nat.min_eq_left hk] at hlen
  omega

/-- Append two successful calls of the existing checked fold. This lemma
does not introduce a second execution or any protocol invariant. -/
private theorem checked_rounds_append
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial middle final : ReferenceActivePhysicalStep.Ledger rate)
    (left right : List (CollectionCheckedExecution.RoundInput
      (p := p) (eta := rate.eta.val)))
    (acceptedLeft acceptedRight : List Bool)
    (hleft : CollectionCheckedExecution.checkedRounds initial left =
      some (acceptedLeft, middle))
    (hright : CollectionCheckedExecution.checkedRounds middle right =
      some (acceptedRight, final)) :
    CollectionCheckedExecution.checkedRounds initial (left ++ right) =
      some (acceptedLeft ++ acceptedRight, final) := by
  induction left generalizing initial acceptedLeft with
  | nil =>
      have hpair : ([], initial) = (acceptedLeft, middle) := Option.some.inj hleft
      cases hpair
      exact hright
  | cons input rest ih =>
      cases hs : CoordinatorCollectionLedger.startRound initial
          (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw with
      | invalid =>
          simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at hleft
      | rejected bad =>
          simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at hleft
      | success started =>
          cases hd : CoordinatorCollectionLedger.decodeUp started
              input.selectedFollower input.parsed with
          | invalid =>
              simp only [CollectionCheckedExecution.checkedRounds, hs, hd, reduceCtorEq] at hleft
          | success decoded | rejected decoded =>
              cases hf : CoordinatorCollectionLedger.finishRound decoded with
              | invalid =>
                  simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf,
                    reduceCtorEq] at hleft
              | rejected bad =>
                  simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf,
                    reduceCtorEq] at hleft
              | success finished =>
                  cases ht : CollectionCheckedExecution.checkedRounds finished rest with
                  | none =>
                      simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf,
                        ht, reduceCtorEq] at hleft
                  | some pair =>
                      simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf,
                        ht, Option.some.injEq, Prod.mk.injEq] at hleft
                      rcases hleft with ⟨rfl, hmiddle⟩
                      have htail := ih finished pair.1 (hmiddle ▸ ht)
                      simp only [List.cons_append, CollectionCheckedExecution.checkedRounds,
                        hs, hd, hf, htail]

/-- Invert the *actual* extraction after producing a successful receiver.
The receiver's success tag, rather than the local acceptance check alone,
identifies the extracted acceptance bit. Recorder and START uniqueness
identify the extracted parsed message and selected follower. -/
private theorem accepted_completed_round
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : Choice rate) (recording : CoordinatorRecordingOperation.Output p)
    (started decoded final : ReferenceActivePhysicalStep.Ledger rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (saved : Option (Fin p.T × Bool))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hc : choice record.input = some c)
    (hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) c.payload c.started c.weights) =
      some recording)
    (hstart : CoordinatorCollectionLedger.startRound c.preLedger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
      .success started)
    (hreceive : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) started).result =
      .success (decoded, bank))
    (hparse : effectiveParse record.input started = some M)
    (hnext : record.output.next.coordinator = .collection payload final saved) :
    ∃ completed : CompletedRound rate,
      extractRound record = some completed ∧ completed.context = c ∧
      completed.final = final ∧ completed.accepted = true ∧
      completed.input.parsed = some M ∧
      completed.input.selectedFollower = ReferenceActivePhysicalStep.upSenderIndex record.input ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
      CollectionCheckedExecution.checkedRounds c.preLedger [completed.input] =
        some ([true], final) := by
  obtain ⟨completed, he⟩ := actual_collection_round_complete
    record c payload final saved hc hnext
  obtain ⟨hcExtract, hround, hchecked, payload', saved', hnext'⟩ :=
    actual_collection_round_checked record completed he
  have hcontext : completed.context = c :=
    Option.some.inj (hcExtract.symm.trans hc)
  have hfinal : completed.final = final :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hnext'.symm.trans hnext)).2.1
  obtain ⟨recording', started', decoded', bank', _hdiag, hrec', hs', hin', hr', _hcheck⟩ :=
    actual_collection_round_inputs record completed he
  rw [hcontext] at hrec' hs' hin'
  have hrecEq : recording' = recording :=
    Option.some.inj (hrec'.symm.trans hrecording)
  subst recording'
  have hsEq : started' = started :=
    CoordinatorCollectionLedger.Checked.success.inj (hs'.symm.trans hstart)
  subst started'
  have haccepted : completed.accepted = true := by
    cases hb : completed.accepted with
    | true => rfl
    | false =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte, hreceive, reduceCtorEq] at hr'
  have hparsed : completed.input.parsed = some M := by
    rw [hin']
    exact hparse
  have hselected : completed.input.selectedFollower =
      ReferenceActivePhysicalStep.upSenderIndex record.input := by
    rw [hin']
    rfl
  have hraw :=
    (ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
      record completed he).1
  refine ⟨completed, he, hcontext, hfinal, haccepted, hparsed, hselected, hround, hraw, ?_⟩
  simpa only [hcontext, haccepted, hfinal] using hchecked

section ActualSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)

variable (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records).length < count)

include hshort

/-- A continuing ready input cannot be the cutoff input: the actual cutoff
input still has the LIVE constructor. This uses protocol constructors, not
an arithmetic inference about the two cursors. -/
private theorem ready_index_pos
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved) : 0 < n.val := by
  classical
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
  let live := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records live.length
  obtain ⟨cut, suffix, hsplit, _htime, r, q, base, hcut, hlive, _⟩ :=
    ReferenceFirstCollectionEpochAlignment.actual_first_collection_epoch_replay
      rate source rewards C_star C_h count hcross hspan hshort
  change epoch.records = live ++ cut :: suffix at hsplit
  have hwindow : window = cut :: suffix.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    have hdrop : epoch.records.drop live.length = cut :: suffix := by
      have hd := congrArg (fun records => records.drop live.length) hsplit
      simpa only [List.drop_left] using hd
    have hdropNext : epoch.records.drop (live.length + 1) = suffix := by
      rw [← List.drop_drop, hdrop]
      rfl
    simp only [window, ReferenceCollectionPhaseHistory.collectionWindow, hdrop, hdropNext,
      List.take_succ_cons, List.take_zero, List.singleton_append]
  by_contra hpos
  have hn : n.val = 0 := by omega
  have hcoord : window[n.val].input.state.coordinator = .collection payload ledger saved :=
    by
      unfold ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain at hReady
      exact hReady.1
  have hzero : window[n.val] = cut := by
    have hz := congrArg (fun records => records[n.val]?) hwindow
    rw [List.getElem?_eq_getElem n.isLt] at hz
    have hz' : some window[n.val] = some cut := by
      simpa only [hn, List.getElem?_cons_zero] using hz
    exact Option.some.inj hz'
  rw [hzero, hcut, hlive] at hcoord
  cases hcoord

/-- Produce the accepted current operation and locate it in the actual
initialized first-collection segment. The only local branch inputs are
readiness, the effective parse, and the actual candidate's UP check.

The exported checked prefix includes the cutoff, every strict earlier
operation, and the current operation. The segment itself may end at any
subsequent failed/noncontinuing record; equality with the whole window is
deliberately unnecessary.

The named numerical consumer is the accepted canonical-cutoff/queue-
continuation assembly at `h = n.val + 1`, followed by the original source
readout splice and `QueueReplay.replay_append`. That assembly stays open. -/
theorem actual_first_collection_accepted_segment_prefix
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : effectiveParse
      (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      (CoordinatorCollectionLedger.startRoundCandidate ledger
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val])) = some M)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val]))
      (ReferenceActivePhysicalStep.upSenderIndex
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input) M = true) :
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let live := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records live.length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let u := s + live.length + 1
    ∃ (c : Choice rate) (recording : CoordinatorRecordingOperation.Output p)
      (started f : ReferenceActivePhysicalStep.Ledger rate)
      (completed : CompletedRound rate)
      (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (head : Choice rate) (f0 : ReferenceActivePhysicalStep.Ledger rate)
      (initializer : Initializer p) (seg : Segment rate),
      0 < n.val ∧ choice window[n.val].input = some c ∧
      c.payload = payload ∧ c.preLedger = ledger ∧ c.initializer = none ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare window[n.val].input)
          c.payload c.started c.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound ledger (window[n.val].input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger window[n.val].input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started ∧
      started = CoordinatorCollectionLedger.startRoundCandidate ledger window[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger window[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val]) ∧
      (∃ decoded bank,
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare window[n.val].input) started).result =
          .success (decoded, bank) ∧
        CoordinatorCollectionLedger.decodeUp started
          (ReferenceActivePhysicalStep.upSenderIndex window[n.val].input) (some M) =
          .success decoded ∧
        CoordinatorCollectionLedger.finishRound decoded = .success f) ∧
      f.cursor = u + n.val + 1 ∧
      f.pending = ledger.pending.erase (ReferenceActivePhysicalStep.upSenderIndex window[n.val].input) ∧
      window[n.val].output.next.coordinator = .collection payload f saved ∧
      extractRound window[n.val] = some completed ∧ completed.context = c ∧
      completed.final = f ∧ completed.accepted = true ∧
      completed.input.parsed = some M ∧
      completed.input.selectedFollower = ReferenceActivePhysicalStep.upSenderIndex window[n.val].input ∧
      completed.input.round = window[n.val].input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val] ∧
      CollectionCheckedExecution.checkedRounds c.preLedger [completed.input] = some ([true], f) ∧
      cut = window[0]'(by exact Nat.lt_of_le_of_lt (Nat.zero_le n.val) n.isLt) ∧
      choice cut.input = some head ∧ head.initializer = some initializer ∧
      head.initializer.isSome = true ∧ initializer.checkedStart rate = .success head.preLedger ∧
      (∃ completed0 : CompletedRound rate,
        extractRound cut = some completed0 ∧ completed0.context = head ∧
        completed0.final = f0 ∧
        CollectionCheckedExecution.checkedRounds head.preLedger [completed0.input] =
          some ([completed0.accepted], f0)) ∧
      (∀ k : Fin n.val, 0 < k.val →
        ∃ earlier : CompletedRound rate,
          extractRound (window[k.val]'(Nat.lt_trans k.isLt n.isLt)) = some earlier ∧
          earlier.context.payload = c.payload ∧ earlier.context.initializer = none ∧
          CollectionBufferProvenance.collectionContext earlier.context.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          CollectionCheckedExecution.checkedRounds earlier.context.preLedger [earlier.input] =
            some ([earlier.accepted], earlier.final)) ∧
      CollectionCheckedExecution.checkedRounds f0
        (inputs ((window.take n.val).drop 1)) =
        some (acceptances ((window.take n.val).drop 1), c.preLedger) ∧
      segmentAt epoch.records live.length = some seg ∧ seg.entry = cut ∧ seg.context = head ∧
      ∃ retained : n.val < seg.records.length,
      seg.records.take (n.val + 1) = window.take (n.val + 1) ∧
      seg.records[n.val]'retained = window[n.val] ∧
      extractRound (seg.records[n.val]'retained) = some completed ∧
      CollectionCheckedExecution.checkedRounds head.preLedger
        (inputs (seg.records.take (n.val + 1))) =
        some (acceptances (seg.records.take (n.val + 1)), f) ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside (inputs (seg.records.take (n.val + 1))) =
        .success ⟨head.preLedger, acceptances (seg.records.take (n.val + 1)), f⟩ := by
  classical
  intro epoch live window s u
  have hnWindow : n.val < window.length := n.isLt
  have hn : 0 < n.val := ready_index_pos
    rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
  obtain ⟨_hstep, htime, c, recording, started, hc, hrecording,
      hpay, hledger, hinit, hstart, hcandidate, _hregisters, hmessages⟩ :=
    ReferenceFirstCollectionAcceptedReadyStep.actual_first_collection_accepted_finish_ready_step
      rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
  have hcandidateLedger : started = CoordinatorCollectionLedger.startRoundCandidate ledger
      window[n.val].input.time
      (ReferenceActivePhysicalStep.collectionEnabled ledger window[n.val].input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val]) := by
    simpa only [hledger] using hcandidate
  have hparseStarted : effectiveParse window[n.val].input started = some M := by
    rw [hcandidateLedger]
    exact hparse
  have hacceptStarted : CoordinatorCollectionLedger.acceptUpCheck started
      (ReferenceActivePhysicalStep.upSenderIndex window[n.val].input) M = true := by
    rw [hcandidateLedger]
    exact haccept
  obtain ⟨out⟩ := hmessages M hparseStarted hacceptStarted
  let f := out.finished
  have hnext : window[n.val].output.next.coordinator = .collection payload f saved := by
    simpa only [out.lastProposalIsSaved] using out.actualNextCoordinator
  have hcursor : f.cursor = u + n.val + 1 := by
    have hf := out.finishedCursor
    change f.cursor = window[n.val].input.time.val + 2 at hf
    change window[n.val].input.time.val + 1 = s + live.length + 1 + n.val at htime
    dsimp only [u]
    omega
  have hstartC : CoordinatorCollectionLedger.startRound c.preLedger
      (window[n.val].input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger window[n.val].input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
      .success started := by
    rw [hledger]
    exact hstart
  obtain ⟨completed, he, hcontext, hfinal, haccepted, hparsed,
      hselected, hround, hraw, hcheckedCurrent⟩ :=
    accepted_completed_round rate window[n.val] c recording started out.decoded f out.bank
      payload saved M hc hrecording hstartC out.receiveSuccess hparseStarted hnext

  -- A is instantiated at this very n and the B-produced actual choice.
  -- Its original source-cell/readout identities remain public in A.
  have hsource :=
    ReferenceFirstCollectionCheckedSourcePrefix.actual_first_collection_checked_source_prefix
      rate source rewards C_star C_h hcross count hspan hshort n hn c hc
  dsimp only at hsource
  obtain ⟨cut, suffix, r, q, base, head, f0, proposal, _hindex, hrecords, hwindow,
      _hstate, _hheadPayload, hinitializer, hhead, hcompleted0, _hcutNext,
      headValid, present, _hDlen, _hDzero, hcallPayload, _hcallInit,
      _hcontextF0, _hchain, hfold, _hHlen, _hInputLen, _hDtailLen,
      _hHAt, hAll, _hSourceRows⟩ := hsource
  change epoch.records = live ++ cut :: suffix at hrecords
  change window = cut :: suffix.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) at hwindow
  let initializer := cutoffInitializer
    (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
    (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time
  have hinitHead : head.initializer = some initializer := hinitializer
  have hcheckedInit : initializer.checkedStart rate = .success head.preLedger :=
    choice_initializer cut.input head initializer hhead hinitHead
  obtain ⟨completed0, he0, hc0, hf0, hchecked0⟩ := hcompleted0
  have hzero : cut = window[0]'(by exact Nat.lt_of_le_of_lt (Nat.zero_le n.val) n.isLt) := by
    have hz := congrArg (fun records => records[0]?) hwindow
    have hlen : 0 < window.length := Nat.lt_of_le_of_lt (Nat.zero_le n.val) n.isLt
    rw [List.getElem?_eq_getElem hlen, List.getElem?_cons_zero] at hz
    exact (Option.some.inj hz).symm

  have hearlier : ∀ k : Fin n.val, 0 < k.val →
      ∃ earlier : CompletedRound rate,
        extractRound (window[k.val]'(Nat.lt_trans k.isLt n.isLt)) = some earlier ∧
        earlier.context.payload = c.payload ∧ earlier.context.initializer = none ∧
        CollectionBufferProvenance.collectionContext earlier.context.preLedger =
          CollectionBufferProvenance.collectionContext head.preLedger ∧
        CollectionCheckedExecution.checkedRounds earlier.context.preLedger [earlier.input] =
          some ([earlier.accepted], earlier.final) := by
    intro k hk
    -- Use the final component of A's per-cell theorem, without replacing
    -- its full payload/context identities by a sigma-only match.
    have hcell := hAll ⟨k.val, by have hi := k.isLt; omega⟩
    obtain ⟨c'', valid'', hc'', hpay'', hctx'', hi'', _hcell,
      _hrows, _hselected, _hrewards, _htime, _henabled, _hclock, _hreward,
      _hrate, _hout, _hread, hcomplete⟩ := hcell
    obtain ⟨earlier, hextract, hctx, hchecked, _⟩ := hcomplete hk k.isLt
    refine ⟨earlier, hextract, ?_, ?_, ?_, ?_⟩
    · rw [hctx, hpay'', hcallPayload]
    · simpa only [hctx] using hi'' hk
    · simpa only [hctx] using hctx''
    · simpa only [hctx] using hchecked

  have hWprefix : window <+: cut :: suffix := by
    refine ⟨suffix.dropWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input), ?_⟩
    rw [hwindow, List.cons_append, List.takeWhile_append_dropWhile]
  have hsourceLength : n.val < (cut :: suffix).length :=
    Nat.lt_of_lt_of_le n.isLt hWprefix.length_le
  have htailLength : n.val ≤ suffix.length := by
    simp only [List.length_cons] at hsourceLength
    omega
  have htailContinuing : ∀ k : Fin n.val,
      continuing (suffix[k.val]'(Nat.lt_of_lt_of_le k.isLt htailLength)) = true := by
    intro k
    have hk : k.val + 1 ≤ n.val := by have hi := k.isLt; omega
    have hrecord : suffix[k.val]'(Nat.lt_of_lt_of_le k.isLt htailLength) =
        window[k.val + 1]'(by omega) := by
      have ht := hWprefix.getElem (i := k.val + 1) (by omega)
      simpa only [List.getElem_cons_succ] using ht.symm
    rw [hrecord]
    by_cases hcurrent : k.val + 1 = n.val
    · simp only [hcurrent, continuing, he, hcontext, hinit, Option.isNone_none]
    · have hklt : k.val + 1 < n.val := Nat.lt_of_le_of_ne hk hcurrent
      obtain ⟨earlier, hextract, _hpayEarlier, hiEarlier, _hctxEarlier, _hcheckEarlier⟩ :=
        hearlier ⟨k.val + 1, hklt⟩ (Nat.succ_pos k.val)
      simp only [continuing, hextract, hiEarlier, Option.isNone_none]
  obtain ⟨htailTake, htailRetained⟩ := take_takeWhile_of_prefix
    suffix continuing n.val htailLength htailContinuing
  let seg : Segment rate :=
    ⟨cut, head, cut :: suffix.takeWhile continuing, suffix.dropWhile continuing⟩
  have hsegment : segmentAt epoch.records live.length = some seg := by
    have hdrop : epoch.records.drop live.length = cut :: suffix := by
      have hd := congrArg (fun records => records.drop live.length) hrecords
      simpa only [List.drop_left] using hd
    unfold segmentAt
    rw [hdrop]
    simp only [ReferenceCollectionSegmentExtraction.segment, hhead, Option.map_some,
      he0, Option.isSome_some, ↓reduceIte, Option.bind_some, hinitHead, or_true, seg]
  have hretained : n.val < seg.records.length := by
    change n.val < (cut :: suffix.takeWhile continuing).length
    simp only [List.length_cons]
    omega
  have htakeSource : window.take (n.val + 1) = (cut :: suffix).take (n.val + 1) :=
    take_eq_of_prefix window (cut :: suffix) hWprefix (n.val + 1)
      (Nat.succ_le_of_lt n.isLt)
  have htake : seg.records.take (n.val + 1) = window.take (n.val + 1) := by
    rw [htakeSource]
    change (cut :: suffix.takeWhile continuing).take (n.val + 1) = _
    simp only [List.take_succ_cons, htailTake]
  have hcurrentRecord : seg.records[n.val]'hretained = window[n.val] := by
    have h := congrArg (fun records => records[n.val]?) htake
    simpa only [List.getElem?_take, Nat.lt_succ_self, ↓reduceIte,
      List.getElem?_eq_getElem hretained, List.getElem?_eq_getElem hnWindow,
      Option.some.injEq] using h

  -- The head is committed once. H contains only indices 1,...,n-1,
  -- and the produced accepted completion supplies index n.
  -- Thus this checked prefix covers cutoff through current inclusive.
  -- At n=1, H=[] and the composition still uses the actual head
  -- endpoint f0. No predecessor operation or future survival is
  -- assumed when assembling the two checked calls.
  let H := (window.take n.val).drop 1
  have hfoldH : CollectionCheckedExecution.checkedRounds f0 (inputs H) =
      some (acceptances H, c.preLedger) := hfold
  have hthroughCurrent := checked_rounds_append rate f0 c.preLedger f
    (inputs H) [completed.input] (acceptances H) [true] hfoldH hcheckedCurrent
  have hthroughHead := checkedRounds_cons head.preLedger f0 f completed0.input
    completed0.accepted (inputs H ++ [completed.input]) (acceptances H ++ [true])
    hchecked0 hthroughCurrent
  have hsplitPrefix : window.take (n.val + 1) = cut :: (H ++ [window[n.val]]) := by
    rw [List.take_succ_eq_append_getElem n.isLt]
    have htakeN : window.take n.val = cut :: H := by
      have ht := congrArg (fun records => records.take n.val) hwindow
      have hd := congrArg (fun records => (records.take n.val).drop 1) hwindow
      simp only [List.take_cons hn, List.drop_succ_cons, List.drop_zero] at ht hd
      exact ht.trans (congrArg (List.cons cut) hd.symm)
    rw [htakeN, List.cons_append]
  have hinputs : inputs (window.take (n.val + 1)) =
      completed0.input :: (inputs H ++ [completed.input]) := by
    rw [hsplitPrefix]
    simp only [inputs, ReferenceCollectionSegmentExtraction.completed,
      List.filterMap_cons, he0, List.map_cons,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he, List.map_append,
      List.map_cons, List.map_nil]
  have hacceptances : acceptances (window.take (n.val + 1)) =
      completed0.accepted :: (acceptances H ++ [true]) := by
    rw [hsplitPrefix]
    simp only [acceptances, ReferenceCollectionSegmentExtraction.completed,
      List.filterMap_cons, he0, List.map_cons,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he, List.map_append,
      List.map_cons, List.map_nil, haccepted]
  have hcheckedPrefix : CollectionCheckedExecution.checkedRounds head.preLedger
      (inputs (seg.records.take (n.val + 1))) =
      some (acceptances (seg.records.take (n.val + 1)), f) := by
    rw [htake, hinputs, hacceptances]
    exact hthroughHead
  have hinitialized : CollectionCheckedExecution.startAndRunChecked p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside (inputs (seg.records.take (n.val + 1))) =
      .success ⟨head.preLedger, acceptances (seg.records.take (n.val + 1)), f⟩ := by
    unfold CollectionCheckedExecution.startAndRunChecked
    dsimp only [Initializer.checkedStart] at hcheckedInit
    simp only [hcheckedInit, hcheckedPrefix]
  refine ⟨c, recording, started, f, completed, cut, head, f0, initializer, seg,
    hn, hc, hpay, hledger, hinit, hrecording, hstart, hcandidateLedger,
    ⟨out.decoded, out.bank, out.receiveSuccess, out.decodeSuccess, out.finishSuccess⟩,
    hcursor, out.finishedPending, hnext, he, hcontext, hfinal, haccepted, hparsed,
    hselected, hround, hraw, hcheckedCurrent, hzero, hhead, hinitHead, ?_,
    hcheckedInit, ⟨completed0, he0, hc0, hf0, hchecked0⟩, hearlier, hfoldH,
    hsegment, rfl, rfl, hretained, htake, hcurrentRecord, ?_, hcheckedPrefix, hinitialized⟩
  · rw [hinitHead]
    rfl
  · rw [hcurrentRecord]
    exact he

end ActualSource

end Bandits.Support.ReferenceFirstCollectionAcceptedSegmentPrefix
