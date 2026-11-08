/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

/-!
# Executed collection erasure history

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-21,41-70,277-284,327-348`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108`, and
`sources/zip4/manuscript/05_binary_transport.tex:60-78,180-191`.
Acceptance below means success of the executed filtered receiver and checked
replay. In particular, a locally admissible wrong raw word is not an event.
These are internal physical history results, not source statement approval,
global initialization correspondence, or score/queue authenticity.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceCollectionPhaseHistory

open ConstructorDimensions

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

abbrev Label (p : Parameters) := Fin (p.m - 1)
abbrev UpRecord (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val)

/-- The actual post-choice collection arguments selected by the dispatcher. -/
structure Tail (x : ReferenceActivePhysicalStep.RoundInput p rate) where
  payload : ReferenceActivePhysicalStep.Payload rate
  ledger : ReferenceActivePhysicalStep.Ledger rate
  started : CoordinatorPhaseClock.StartRoundResult p
  weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ

/-- Only the executed cutoff/continuing branch, after the actual choice guard. -/
def executedTail (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Tail x) :=
  let prepared := ReferenceActivePhysicalStep.prepare x
  if prepared.coordinator.selection = none then none else
  match prepared.coordinator with
  | .live r _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
      some ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights⟩
  | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
      some ⟨payload, ledger, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩
  | _ => none

/-- The filtered ordinary parser used by this very receiver call. -/
def filteredParsed (x : ReferenceActivePhysicalStep.RoundInput p rate) (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    Option (UpRecord p rate) :=
  CoordinatorUpReception.parseDecoderOutput (ReferenceUpReception.filterRawByExpected
    (CoordinatorUpReception.decoderTransition (ReferenceUpReception.receptionInputAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) ledger) x.time)).2 (ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)))

/-- Recorder and stage (1) must succeed before reception is executed. -/
def Tail.reception {x : ReferenceActivePhysicalStep.RoundInput p rate} (tail : Tail x) :
    Option (ReferenceActivePhysicalStep.Ledger rate × ReferenceActivePhysicalStep.UpCut p rate) :=
  match CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) tail.payload tail.started tail.weights) with
  | none => none
  | some recording =>
      match CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | .success started => some (started, ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started)
      | _ => none

/-- An event is determined by actual executed receiver success, not diagnostics. -/
def acceptedLabel (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Label p) :=
  (executedTail x).bind fun tail => tail.reception.bind fun received =>
    match received.2.result with
    | .success _ => some (ReferenceActivePhysicalStep.upSenderIndex x)
    | _ => none

/-- Literal witness, retaining every operation needed for checked acceptance. -/
def AcceptedUp (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Label p) (message : UpRecord p rate) : Prop :=
  ∃ (tail : Tail x) (recording : CoordinatorRecordingOperation.Output p)
    (started decoded : ReferenceActivePhysicalStep.Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p),
    executedTail x = some tail ∧
    CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) tail.payload tail.started tail.weights) =
        some recording ∧
    CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1) (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started ∧
    (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, bank) ∧
    filteredParsed x started = some message ∧ i = ReferenceActivePhysicalStep.upSenderIndex x

/-- Apply precisely the possible one-label erasure. -/
def eraseEvent (pending : Finset (Label p)) (event : Option (Label p)) : Finset (Label p) :=
  match event with | none => pending | some i => pending.erase i

private theorem start_frame (l out : ReferenceActivePhysicalStep.Ledger rate) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) (h : CoordinatorCollectionLedger.startRound l t enabled raw = .success out) :
    out.pending = l.pending ∧ out.sigma = l.sigma := by
  unfold CoordinatorCollectionLedger.startRound at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl⟩

private theorem finish_frame (l out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.finishRound l = .success out) :
    out.pending = l.pending ∧ out.sigma = l.sigma := by
  unfold CoordinatorCollectionLedger.finishRound at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl⟩

/-- This predicate is a case analysis of the literal checked decode result. -/
private def decodeSpec (l : ReferenceActivePhysicalStep.Ledger rate) (i : Label p) (parsed : Option (UpRecord p rate)) :
    CoordinatorCollectionLedger.Checked (ReferenceActivePhysicalStep.Ledger rate) → Prop
  | .invalid => True
  | .rejected out => out.pending = l.pending ∧ out.sigma = l.sigma
  | .success out => ∃ message, parsed = some message ∧ i ∈ l.pending ∧
      message.val.sigma = l.sigma ∧ out.pending = l.pending.erase i ∧ out.sigma = l.sigma

private theorem decode_spec (l : ReferenceActivePhysicalStep.Ledger rate) (i : Label p)
    (parsed : Option (UpRecord p rate)) : decodeSpec l i parsed (CoordinatorCollectionLedger.decodeUp l i parsed) := by
  unfold CoordinatorCollectionLedger.decodeUp
  split
  · cases parsed with
    | none =>
        dsimp only
        split
        · exact ⟨rfl, rfl⟩
        · trivial
    | some message =>
        dsimp only
        split
        · rename_i haccept
          have ha : i ∈ l.pending ∧ message.val.sigma = l.sigma := by
            have h := haccept
            simp only [CoordinatorCollectionLedger.acceptUpCheck,
              Bool.and_eq_true, decide_eq_true_eq] at h
            exact h.2
          split
          ·
            split
            · split
              · trivial
              ·
                split
                ·
                  split
                  · exact ⟨message, rfl, ha.1, ha.2, rfl, rfl⟩
                  · trivial
                · trivial
              · trivial
            · trivial
          · trivial
        ·
          split
          · exact ⟨rfl, rfl⟩
          · trivial
  · trivial

/-- Receiver success and rejection have distinct pending-set effects. -/
private def receptionSpec (l : ReferenceActivePhysicalStep.Ledger rate) (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    CoordinatorCollectionLedger.Checked (ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p) → Prop
  | .invalid => True
  | .rejected out => out.1.pending = l.pending ∧ out.1.sigma = l.sigma
  | .success out => ∃ message, filteredParsed x l = some message ∧
      ReferenceActivePhysicalStep.upSenderIndex x ∈ l.pending ∧ message.val.sigma = l.sigma ∧
      out.1.pending = l.pending.erase (ReferenceActivePhysicalStep.upSenderIndex x) ∧ out.1.sigma = l.sigma

private theorem receive_spec (x : ReferenceActivePhysicalStep.RoundInput p rate) (l : ReferenceActivePhysicalStep.Ledger rate) :
    receptionSpec l x (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) l).result := by
  change receptionSpec l x (if CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) l) x.time) = true then
    CoordinatorUpReception.packDecodeResult (CoordinatorCollectionLedger.decodeUp l (ReferenceActivePhysicalStep.upSenderIndex x) (filteredParsed x l))
      (CoordinatorUpReception.decoderBankAfter (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) l) x.time)) else .invalid)
  split
  · have hd := decode_spec l (ReferenceActivePhysicalStep.upSenderIndex x) (filteredParsed x l)
    cases he : CoordinatorCollectionLedger.decodeUp l (ReferenceActivePhysicalStep.upSenderIndex x) (filteredParsed x l) <;>
      rw [he] at hd <;> exact hd
  · trivial

def Tail.label {x : ReferenceActivePhysicalStep.RoundInput p rate} (tail : Tail x) : Option (Label p) :=
  tail.reception.bind fun received =>
    match received.2.result with | .success _ => some (ReferenceActivePhysicalStep.upSenderIndex x) | _ => none

private theorem acceptedLabel_of_tail {x : ReferenceActivePhysicalStep.RoundInput p rate} {tail : Tail x}
    (ht : executedTail x = some tail) : acceptedLabel x = tail.label := by
  simp only [acceptedLabel, ht, Option.bind_some, Tail.label]

/-- A successful checked reception supplies an ordinary parsed record and its
old-ledger start. No score identity is asserted. -/
theorem acceptedLabel_witness {x : ReferenceActivePhysicalStep.RoundInput p rate} {i : Label p}
    (h : acceptedLabel x = some i) :
    ∃ message, AcceptedUp x i message := by
  unfold acceptedLabel at h
  cases ht : executedTail x with
  | none => simp only [ht, Option.bind_none] at h; contradiction
  | some tail =>
      simp only [ht, Option.bind_some, Tail.reception] at h
      split at h
      · contradiction
      · rename_i recording hr
        split at h <;> try contradiction
        rename_i started hs
        cases hc : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
        | invalid => simp only [hc, Option.bind_some] at h; contradiction
        | rejected out => simp only [hc, Option.bind_some] at h; contradiction
        | success out =>
            simp only [hc, Option.bind_some, Option.some.injEq] at h
            have hd := receive_spec x started
            rw [hc] at hd
            obtain ⟨message, hp, _, _, _, _⟩ := hd
            exact ⟨message, tail, recording, started, out.1, out.2,
              ht, hr, hs, hc, hp, h.symm⟩

private theorem tail_label_mem {x : ReferenceActivePhysicalStep.RoundInput p rate} (tail : Tail x) (i : Label p)
    (h : tail.label = some i) : i ∈ tail.ledger.pending := by
  unfold Tail.label Tail.reception at h
  split at h
  · contradiction
  · split at h <;> try contradiction
    rename_i started hs
    cases hc : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
    | invalid => simp only [hc, Option.bind_some] at h; contradiction
    | rejected out => simp only [hc, Option.bind_some] at h; contradiction
    | success out =>
        simp only [hc, Option.bind_some, Option.some.injEq] at h
        have hd := receive_spec x started
        rw [hc] at hd
        rw [← h, ← (start_frame tail.ledger started _ _ _ hs).1]
        exact hd.choose_spec.2.1

private theorem collection_finish_frame {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate)
    (old : ReferenceActivePhysicalStep.Ledger rate) (hspec : receptionSpec old x cut.result)
    (outPayload : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration =
      .collection outPayload out proposal) :
    out.pending = eraseEvent old.pending
      (match cut.result with | .success _ => some (ReferenceActivePhysicalStep.upSenderIndex x) | _ => none) ∧
      out.sigma = old.sigma := by
  unfold ReferenceActivePhysicalStep.collectionFinish at h
  cases hc : cut.result <;> rw [hc] at h hspec
  · dsimp only at h
    split at h <;> try contradiction
    rename_i finished hf
    split at h <;> try contradiction
    cases h
    have hframe := finish_frame _ out hf
    exact ⟨hframe.1.trans hspec.choose_spec.2.2.2.1,
      hframe.2.trans hspec.choose_spec.2.2.2.2⟩
  · dsimp only at h
    split at h <;> try contradiction
    rename_i finished hf
    split at h <;> try contradiction
    cases h
    have hframe := finish_frame _ out hf
    exact ⟨hframe.1.trans hspec.1, hframe.2.trans hspec.2⟩
  · contradiction

private theorem post_choice_frame {x : ReferenceActivePhysicalStep.RoundInput p rate} (tail : Tail x)
    (payload : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
      tail.started tail.weights).configuration = .collection payload out proposal) :
    out.pending = eraseEvent tail.ledger.pending tail.label ∧ out.sigma = tail.ledger.sigma := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  split at h <;> try contradiction
  rename_i recording hr
  dsimp only at h
  split at h <;> try contradiction
  rename_i started hs
  have hf := collection_finish_frame tail.payload tail.started recording
    (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started) started (receive_spec x started) payload out proposal h
  have hstart := start_frame tail.ledger started _ _ _ hs
  have he : tail.label = (match (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).result with
      | .success _ => some (ReferenceActivePhysicalStep.upSenderIndex x) | _ => none) := by
    simp only [Tail.label, Tail.reception, hr, hs, Option.bind_some]
    rfl
  rw [he, ← hstart.1]
  exact ⟨hf.1, hf.2.trans hstart.2⟩

/-- Search tags are the actual retained dispatch constructors. -/
def cutoffChosen (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  match (ReferenceActivePhysicalStep.prepare x).coordinator with
  | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => true
  | _ => false

def laterChosen (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  match (ReferenceActivePhysicalStep.prepare x).coordinator with
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) => true
  | _ => false

/-- The origin information intrinsic to the actual dispatcher, not an
assumed physical invariant. -/
private def dispatchOrigin (x : ReferenceActivePhysicalStep.RoundInput p rate) : ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .live r q base _ => x.state.coordinator = .live r q base
  | .collection payload ledger _ _ _ =>
      ∃ proposal, x.state.coordinator = .collection payload ledger proposal
  | .first _ => x.state.coordinator = .first
  | .dagger => x.state.coordinator = .dagger
  | .invalidCollectionCutoff => ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal

private theorem dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    dispatchOrigin x (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change dispatchOrigin x (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      exact hc
  | collection payload ledger proposal =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨proposal, hc⟩
      · exact ⟨payload, ledger, proposal, hc⟩
  | dagger => exact hc

private theorem live_not_collection {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration ≠
      .collection payload ledger proposal := by
  intro h
  unfold ReferenceActivePhysicalStep.livePostChoice at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> contradiction

private theorem step_collection_tail (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection payload out proposal) :
    ∃ tail : Tail x, executedTail x = some tail ∧
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
        tail.started tail.weights).configuration = .collection payload out proposal := by
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = _ at h
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at h
  split at h
  · split at h <;> contradiction
  · rename_i hguard
    cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome =>
        cases outcome <;> simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h <;> try contradiction
        exact False.elim (live_not_collection _ _ _ _ _ _ _ _ h)
    | live r q base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
            simp only [he] at h
            let tail : Tail x := ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights⟩
            refine ⟨tail, ?_, h⟩
            simp only [executedTail]
            rw [ite_eq_right hguard, he]
        | continuingChosen dispatched hstart continuation selected =>
            simp only [he] at h
            exact False.elim (live_not_collection (ReferenceActivePhysicalStep.prepare x) (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult payload out proposal h)
        | clockFailure failure heq => simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction
        | initializerFailure dispatched hstart checked heq =>
            simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction
        | localFailure dispatched hstart reason =>
            simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction
    | collection oldPayload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            simp only [he] at h
            let tail : Tail x := ⟨oldPayload, ledger, snapshot.clockStarted,
              CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x oldPayload ledger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩
            refine ⟨tail, ?_, h⟩
            simp only [executedTail]
            rw [ite_eq_right hguard, he]
        | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
            simp only [he] at h
            exact False.elim (live_not_collection (ReferenceActivePhysicalStep.prepare x) installed.registers
              installed.ownedRegisters installed.retainedBaseScore started payload out proposal h)
        | _ => simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction
    | invalidCollectionCutoff => simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction
    | dagger => simp only [he, ReferenceActivePhysicalStep.coordinatorFailure] at h; contradiction

/-- A tail is either the first cutoff round, whose pending set is full, or
the continuation of the very collection ledger stored in the pre-state. -/
theorem executedTail_origin {x : ReferenceActivePhysicalStep.RoundInput p rate} {tail : Tail x}
    (ht : executedTail x = some tail) :
    laterChosen x = false ∧
    ((cutoffChosen x = true ∧ tail.ledger.pending = Finset.univ) ∨
      (cutoffChosen x = false ∧ ∃ payload ledger proposal,
        x.state.coordinator = .collection payload ledger proposal ∧ tail.ledger = ledger)) := by
  have ho := dispatch_origin x
  unfold executedTail at ht
  dsimp only at ht
  split at ht <;> try contradiction
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome => cases outcome <;> simp only [he] at ht <;> contradiction
  | live r q base outcome =>
      cases outcome <;> simp only [he] at ht <;> try contradiction
      rename_i dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected
      cases ht
      simp only [laterChosen, cutoffChosen, he, Bool.true_eq_false, false_and,
        true_and, or_false]
      rw [hledger]
      rfl
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [he] at ht <;> try contradiction
      cases ht
      rw [he] at ho
      exact ⟨by simp only [laterChosen, he], Or.inr
        ⟨by simp only [cutoffChosen, he], payload, ledger, ho.choose, ho.choose_spec, rfl⟩⟩
  | invalidCollectionCutoff => simp only [he] at ht; contradiction
  | dagger => simp only [he] at ht; contradiction

/-- Exact local erasure; all failures remain in the actual step. -/
theorem step_collection_frame (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (h : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection payload out proposal) :
    ∃ tail : Tail x, executedTail x = some tail ∧
      out.pending = eraseEvent tail.ledger.pending (acceptedLabel x) ∧
      out.sigma = tail.ledger.sigma := by
  obtain ⟨tail, ht, hp⟩ := step_collection_tail x payload out proposal h
  have hf := post_choice_frame tail payload out proposal hp
  rw [← acceptedLabel_of_tail ht] at hf
  exact ⟨tail, ht, hf⟩

/-- A literal later-choice occurrence requires the old stored pending set to
be empty, before this round's recorder or receiver runs. -/
theorem laterChosen_pending_empty (x : ReferenceActivePhysicalStep.RoundInput p rate) (h : laterChosen x = true) :
    ∃ payload ledger proposal, x.state.coordinator = .collection payload ledger proposal ∧
      ledger.pending = ∅ := by
  have ho := dispatch_origin x
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [laterChosen, he, Bool.false_eq_true] at h
      rename_i core consistent started hstart instruction hi output hcons data installed selected
      rw [he] at ho
      obtain ⟨proposal, hcoord⟩ := ho
      refine ⟨payload, ledger, proposal, hcoord, ?_⟩
      by_contra hp
      have hsigma : clock.sigma = some payload.sigma := core.clock_sigma_eq
      have hcutoff : clock.u = some cutoff := core.clock_cutoff_eq
      have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time clock :=
        core.clock_start_time_valid
      have hut : cutoff.val ≤ x.time.val := by
        have ht : payload.sigma.val < x.time.val ∧ cutoff.val ≤ x.time.val := by
          simpa only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hcutoff] using htime
        exact ht.2
      have hk := CoordinatorPhaseClock.startRound_collection_pending
        p rate.eta.val x.time payload.sigma cutoff clock ledger.pending
        core.clock_parameter_valid core.clock_registers_valid core.clock_sigma_eq
        core.clock_cutoff_eq hut hp
      change CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending =
        .ok started at hstart
      rw [hk] at hstart
      cases hstart
      cases hi
  | first outcome => simp only [laterChosen, he, Bool.false_eq_true] at h
  | live r q base outcome => simp only [laterChosen, he, Bool.false_eq_true] at h
  | invalidCollectionCutoff => simp only [laterChosen, he, Bool.false_eq_true] at h
  | dagger => simp only [laterChosen, he, Bool.false_eq_true] at h

private theorem event_at_tail {x : ReferenceActivePhysicalStep.RoundInput p rate} {tail : Tail x}
    (ht : executedTail x = some tail) {i : Label p} (hi : acceptedLabel x = some i) :
    ∃ message, AcceptedUp x i message ∧ message.val.sigma = tail.ledger.sigma := by
  obtain ⟨message, hm⟩ := acceptedLabel_witness hi
  refine ⟨message, hm, ?_⟩
  obtain ⟨other, recording, started, decoded, bank, ho, _, hs, hc, hp, _⟩ := hm
  have he : other = tail := Option.some.inj (ho.symm.trans ht)
  have hd := receive_spec x started
  rw [hc] at hd
  obtain ⟨parsed, hparsed, _, hsigma, _, _⟩ := hd
  have hm' : parsed = message := Option.some.inj (hparsed.symm.trans hp)
  subst parsed
  exact hsigma.trans ((start_frame other.ledger started _ _ _ hs).2.trans
    (congrArg (fun t => t.ledger.sigma) he))

abbrev Record (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- Successful labels, in execution order, including the cutoff record. -/
def acceptedLabels (records : List (Record p rate)) : List (Label p) :=
  records.filterMap fun record => acceptedLabel record.input

/-- A searched window starts at this cutoff and ends immediately before the
first later choice (or at list end). -/
def collectionWindow (records : List (Record p rate)) (a : ℕ) : List (Record p rate) :=
  (records.drop a).take 1 ++
    ((records.drop (a + 1)).takeWhile fun record => !laterChosen record.input)

/-- Source induction data: the current collection has a real cutoff in the
computed prefix; its accepted labels are distinct, and its pending set is
their exact complement. The witness property keeps ordinary parsed starts. -/
def History (records : List (Record p rate)) (state : ReferenceActivePhysicalStep.State p rate) : Prop :=
  ∀ payload ledger proposal, state.coordinator = .collection payload ledger proposal →
    ∃ before cutoff during, records = before ++ cutoff :: during ∧
      cutoffChosen cutoff.input = true ∧ laterChosen cutoff.input = false ∧
      (∀ record ∈ during, cutoffChosen record.input = false ∧ laterChosen record.input = false) ∧
      ledger.pending = Finset.univ \ (acceptedLabels (cutoff :: during)).toFinset ∧
      (acceptedLabels (cutoff :: during)).Nodup ∧
      ∀ record ∈ cutoff :: during, ∀ i, acceptedLabel record.input = some i →
        ∃ message, AcceptedUp record.input i message ∧ message.val.sigma = ledger.sigma

private theorem labels_append (xs ys : List (Record p rate)) :
    acceptedLabels (xs ++ ys) = acceptedLabels xs ++ acceptedLabels ys := by
  exact List.filterMap_append

private theorem erase_labels (xs : List (Label p)) (event : Option (Label p)) :
    eraseEvent (Finset.univ \ xs.toFinset) event =
      Finset.univ \ (xs ++ event.toList).toFinset := by
  cases event with
  | none => simp only [eraseEvent, Option.toList_none, List.append_nil]
  | some i =>
      simp only [eraseEvent, Option.toList_some, List.toFinset_append,
        List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
      exact (Finset.sdiff_insert (Finset.univ : Finset (Label p)) xs.toFinset i).symm

private theorem nodup_event (xs : List (Label p)) (event : Option (Label p))
    (hx : xs.Nodup) (he : ∀ i, event = some i → i ∈ Finset.univ \ xs.toFinset) :
    (xs ++ event.toList).Nodup := by
  cases event with
  | none => simpa only [Option.toList_none, List.append_nil] using hx
  | some i =>
      have hi : i ∉ xs := by
        have hm := (Finset.mem_sdiff.mp (he i rfl)).2
        simpa only [List.mem_toFinset] using hm
      simpa only [Option.toList_some] using (List.nodup_append.mpr
        ⟨hx, by simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self],
          by
            intro a ha b hb hab
            have hb' : b = i := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hb
            subst b
            subst a
            exact hi ha⟩)

private theorem history_first (state : ReferenceActivePhysicalStep.State p rate) (h : state.coordinator = .first) :
    History [] state := by
  intro payload ledger proposal hc
  rw [h] at hc
  contradiction

/-- The invariant is propagated by the full actual transition, including
frozen service, checked rejection, and every local failure branch. -/
theorem history_step {records : List (Record p rate)} {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (ih : History records x.state) :
    History (records ++ [⟨x, ReferenceActivePhysicalStep.step x, rfl⟩]) (ReferenceActivePhysicalStep.step x).next := by
  intro payload out proposal hout
  obtain ⟨tail, ht, hp, hs⟩ := step_collection_frame x payload out proposal hout
  obtain ⟨hlater, horigin⟩ := executedTail_origin ht
  let record : Record p rate := ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  have hmem : ∀ i, acceptedLabel x = some i → i ∈ tail.ledger.pending := by
    intro i hi
    exact tail_label_mem tail i ((acceptedLabel_of_tail ht).symm.trans hi)
  have hnew : ∀ i, acceptedLabel x = some i →
      ∃ message, AcceptedUp x i message ∧ message.val.sigma = out.sigma := by
    intro i hi
    obtain ⟨message, hm, hstart⟩ := event_at_tail ht hi
    exact ⟨message, hm, hstart.trans hs.symm⟩
  rcases horigin with ⟨hcut, hfull⟩ | ⟨hcut, oldPayload, old, oldProposal, hold, hledger⟩
  · refine ⟨records, record, [], rfl, hcut, hlater, ?_, ?_, ?_, ?_⟩
    · simp only [List.not_mem_nil, false_implies, implies_true]
    · rw [hp, hfull]
      change eraseEvent Finset.univ (acceptedLabel x) =
        Finset.univ \ (acceptedLabel x).toList.toFinset
      simpa only [List.toFinset_nil, Finset.sdiff_empty, List.nil_append] using
        erase_labels ([] : List (Label p)) (acceptedLabel x)
    · change (acceptedLabel x).toList.Nodup
      cases acceptedLabel x <;> simp only [Option.toList_none, Option.toList_some,
        List.nodup_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_self]
    · intro r hr i hi
      have hr' : r = record := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr
      subst r
      exact hnew i hi
  · obtain ⟨before, cutoff, during, heq, hc, hcl, hd, hexact, hnodup, hw⟩ :=
      ih oldPayload old oldProposal hold
    have hpend : tail.ledger.pending = Finset.univ \ (acceptedLabels (cutoff :: during)).toFinset := by
      rw [hledger]; exact hexact
    refine ⟨before, cutoff, during ++ [record], ?_, hc, hcl, ?_, ?_, ?_, ?_⟩
    · rw [heq, List.append_assoc, List.cons_append]
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hd r hr
      · have hr' : r = record := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr
        subst r
        exact ⟨hcut, hlater⟩
    · rw [hp, hpend]
      have he : acceptedLabels (cutoff :: (during ++ [record])) =
          acceptedLabels (cutoff :: during) ++ (acceptedLabel x).toList := by
        rw [← List.cons_append, labels_append]
        rfl
      rw [he]
      exact erase_labels _ _
    · have he : acceptedLabels (cutoff :: (during ++ [record])) =
          acceptedLabels (cutoff :: during) ++ (acceptedLabel x).toList := by
        rw [← List.cons_append, labels_append]
        rfl
      rw [he]
      exact nodup_event _ _ hnodup (by intro i hi; rw [← hpend]; exact hmem i hi)
    · intro r hr i hi
      have hr' : r ∈ (cutoff :: during) ++ [record] := by
        simpa only [List.cons_append] using hr
      rcases List.mem_append.mp hr' with hr | hr
      · obtain ⟨message, hm, hstart⟩ := hw r hr i hi
        exact ⟨message, hm, hstart.trans ((congrArg (fun l => l.sigma) hledger).symm.trans hs.symm)⟩
      · have hr' : r = record := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr
        subst r
        exact hnew i hi

/-- Horizon induction starts from the actual first phase; inherited collection
history is never postulated. -/
theorem run_history (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    History (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState := by
  induction count with
  | zero =>
      rw [ReferenceActivePhysicalHorizon.run_zero_records, ReferenceActivePhysicalHorizon.run_zero_final]
      exact history_first initial hfirst
  | succ count ih =>
      rw [ReferenceActivePhysicalHorizon.run_successor_step]
      exact history_step (x := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode)
        ⟨start + count, by omega, by omega⟩) (ih (by omega))

private theorem takeWhile_no_later (records : List (Record p rate))
    (h : ∀ record ∈ records, laterChosen record.input = false) :
    (records.takeWhile fun record => !laterChosen record.input) = records := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
      have hr := h r (by simp only [List.mem_cons, true_or])
      have hs : ∀ record ∈ rs, laterChosen record.input = false :=
        fun record hm => h record (List.mem_cons_of_mem r hm)
      simp only [List.takeWhile_cons, hr, Bool.not_false, ↓reduceIte, ih hs]

private theorem window_at_end (before : List (Record p rate)) (cutoff : Record p rate)
    (during : List (Record p rate))
    (h : ∀ r ∈ during, laterChosen r.input = false) :
    collectionWindow (before ++ cutoff :: during) before.length = cutoff :: during := by
  unfold collectionWindow
  rw [List.drop_append_length, List.drop_add_one_eq_tail_drop, List.drop_append_length]
  simp only [List.tail_cons, List.take_succ_cons, List.take_zero, takeWhile_no_later during h,
    List.singleton_append]

private theorem window_before_later (before : List (Record p rate)) (cutoff : Record p rate)
    (during : List (Record p rate)) (next : Record p rate)
    (h : ∀ r ∈ during, laterChosen r.input = false) (hn : laterChosen next.input = true) :
    collectionWindow ((before ++ cutoff :: during) ++ [next]) before.length = cutoff :: during := by
  rw [List.append_assoc, List.cons_append]
  unfold collectionWindow
  rw [List.drop_append_length, List.drop_add_one_eq_tail_drop, List.drop_append_length]
  have hall : ∀ r ∈ during, (!laterChosen r.input) = true := by
    intro r hr
    rw [h r hr]
    rfl
  simp only [List.tail_cons]
  rw [List.takeWhile_append_of_pos hall]
  simp only [List.take_succ_cons, List.take_zero, List.takeWhile_cons,
    hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.singleton_append]

/-- For each computed collection endpoint C_b, expose the actual cutoff a,
the exact record interval [a,b), its searched window, and distinct accepted
labels. The cutoff round itself is included. -/
theorem run_collection_pending_exact (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hc : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState.coordinator =
      .collection payload ledger proposal) :
    ∃ (before : List (Record p rate)) (cutoff : Record p rate) (during : List (Record p rate)),
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records =
        before ++ cutoff :: during ∧ before.length < count ∧
      cutoffChosen cutoff.input = true ∧
      collectionWindow (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records
        before.length = cutoff :: during ∧
      ledger.pending = Finset.univ \ (acceptedLabels (cutoff :: during)).toFinset ∧
      (acceptedLabels (cutoff :: during)).Nodup ∧
      ∀ r ∈ cutoff :: during, ∀ i, acceptedLabel r.input = some i →
        ∃ message, AcceptedUp r.input i message ∧ message.val.sigma = ledger.sigma := by
  obtain ⟨before, cutoff, during, he, hcut, _, hd, hp, hn, hw⟩ :=
    run_history initial rows selected rewards start count hspan hmode hfirst
      payload ledger proposal hc
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start count hspan hmode
  rw [he, List.length_append, List.length_cons] at hlength
  refine ⟨before, cutoff, during, he, by omega, hcut, ?_, hp, hn, hw⟩
  rw [he]
  exact window_at_end before cutoff during (fun r hr => (hd r hr).2)

/-- The next input uses the final state of the computed prefix and the
original complete rows, selected private row, and whole reward table. -/
def nextInput (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode)
    ⟨start + count, by omega, by omega⟩

/-- Every follower has an executed, successfully parsed UP witness strictly
before the later assignment's choice round j. The last acceptance cannot
start an assignment on its post-choice tail. -/
theorem run_laterStart_all_up_accepted (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (hlater : laterChosen (nextInput initial rows selected rewards start count hspan hmode) = true) :
    ∃ (before : List (Record p rate)) (cutoff : Record p rate)
      (during : List (Record p rate)) (payload : ReferenceActivePhysicalStep.Payload rate)
      (old : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode).records =
        before ++ cutoff :: during ∧ cutoffChosen cutoff.input = true ∧
      (nextInput initial rows selected rewards start count hspan hmode).state.coordinator =
        .collection payload old proposal ∧ old.pending = ∅ ∧
      collectionWindow
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode).records ++
          [⟨nextInput initial rows selected rewards start count hspan hmode,
            ReferenceActivePhysicalStep.step (nextInput initial rows selected rewards start count hspan hmode), rfl⟩])
        before.length = cutoff :: during ∧
      ∀ i : Label p, ∃ (k : ℕ) (r : Record p rate) (message : UpRecord p rate),
        before.length ≤ k ∧ k < count ∧
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode).records[k]? = some r ∧
        AcceptedUp r.input i message ∧ message.val.sigma = old.sigma := by
  let x := nextInput initial rows selected rewards start count hspan hmode
  obtain ⟨payload, old, proposal, hc, hempty⟩ := laterChosen_pending_empty x hlater
  obtain ⟨before, cutoff, during, he, hcut, _, hd, hp, _, hw⟩ :=
    run_history initial rows selected rewards start count (by omega) hmode hfirst
      payload old proposal hc
  refine ⟨before, cutoff, during, payload, old, proposal, he, hcut, hc, hempty, ?_, ?_⟩
  · rw [he]
    exact window_before_later before cutoff during ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
      (fun r hr => (hd r hr).2) hlater
  · intro i
    have hi : i ∈ acceptedLabels (cutoff :: during) := by
      apply List.mem_toFinset.mp
      by_contra hnot
      have hmem : i ∈ old.pending := by
        rw [hp]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnot⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty i hmem
    obtain ⟨r, hr, haccept⟩ := List.mem_filterMap.mp hi
    obtain ⟨message, hm, hstart⟩ := hw r hr i haccept
    obtain ⟨offset, hoffset, hget⟩ := List.mem_iff_getElem.mp hr
    have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start count (by omega) hmode
    rw [he, List.length_append] at hlen
    refine ⟨before.length + offset, r, message, by omega, by omega, ?_, hm, hstart⟩
    rw [he, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hoffset, hget]

/-- The two possible phases after a collection tail; finishing never installs. -/
def CollectionPhase (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Prop :=
  configuration = .dagger ∨ ∃ payload ledger proposal,
    configuration = .collection payload ledger proposal

theorem collectionFinish_no_installation {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    CollectionPhase (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases cut.result with
  | invalid => exact Or.inl rfl
  | success out =>
      dsimp only
      split
      · exact Or.inl rfl
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, _, _, rfl⟩
  | rejected out =>
      dsimp only
      split
      · exact Or.inl rfl
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, _, _, rfl⟩

theorem collectionPostChoice_no_installation {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate) (started)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CollectionPhase (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  split
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact collectionFinish_no_installation _ _ _ _

private theorem step_collection_phase (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hc : x.state.coordinator = .collection payload old proposal)
    (hn : laterChosen x = false) : CollectionPhase (ReferenceActivePhysicalStep.step x).next.coordinator := by
  have ho := dispatch_origin x
  change CollectionPhase (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
  split
  · split <;> exact Or.inl rfl
  · cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => rw [he] at ho; dsimp only [dispatchOrigin] at ho; rw [hc] at ho; contradiction
    | live r q base outcome => rw [he] at ho; dsimp only [dispatchOrigin] at ho; rw [hc] at ho; contradiction
    | collection cp cl clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            exact collectionPostChoice_no_installation (ReferenceActivePhysicalStep.prepare x) cp cl snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x cp cl clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
        | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
            simp only [laterChosen, he, Bool.true_eq_false] at hn
        | _ => exact Or.inl rfl
    | invalidCollectionCutoff => exact Or.inl rfl
    | dagger => exact Or.inl rfl

private theorem cutoff_false_in_collection (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hc : x.state.coordinator = .collection payload old proposal) : cutoffChosen x = false := by
  have ho := dispatch_origin x
  unfold cutoffChosen
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live r q base outcome =>
      rw [he] at ho
      dsimp only [dispatchOrigin] at ho
      rw [hc] at ho
      contradiction
  | first outcome => rfl
  | collection cp cl clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem step_pending_frame (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hc : x.state.coordinator = .collection payload old proposal)
    (hn : (ReferenceActivePhysicalStep.step x).next.coordinator = .collection cp out saved) :
    out.pending = eraseEvent old.pending (acceptedLabel x) ∧ out.sigma = old.sigma := by
  obtain ⟨tail, ht, hp, hs⟩ := step_collection_frame x cp out saved hn
  have hcut := cutoff_false_in_collection x payload old proposal hc
  obtain ⟨_, horigin⟩ := executedTail_origin ht
  rcases horigin with ⟨ha, _⟩ | ⟨_, op, ol, os, ho, he⟩
  · rw [hcut] at ha
    contradiction
  · rw [hc] at ho
    cases ho
    rw [he] at hp hs
    exact ⟨hp, hs⟩

private theorem connected_pending_nested {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (Record p rate)) (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hc : initial.coordinator = .collection payload old proposal)
    (hf : final.coordinator = .collection cp out saved)
    (hno : ∀ r ∈ records, laterChosen r.input = false) :
    out.pending ⊆ old.pending ∧ out.sigma = old.sigma := by
  induction records generalizing initial payload old proposal with
  | nil =>
      subst final
      rw [hc] at hf
      cases hf
      exact ⟨Finset.Subset.refl _, rfl⟩
  | cons r rs ih =>
      obtain ⟨hpre, hrest⟩ := hchain
      have hr : r.input.state.coordinator = .collection payload old proposal := by rw [hpre]; exact hc
      have hphase := step_collection_phase r.input payload old proposal hr
        (hno r (List.mem_cons_self))
      rw [← r.output_eq] at hphase
      rcases hphase with hd | ⟨np, nl, ns, hn⟩
      · have hdagger := (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hrest hd).1
        rw [hf] at hdagger
        contradiction
      · have hstep : (ReferenceActivePhysicalStep.step r.input).next.coordinator = .collection np nl ns := by
          rw [← r.output_eq]; exact hn
        have hframe := step_pending_frame r.input payload old proposal np nl ns hr hstep
        obtain ⟨hsub, hsig⟩ := ih hrest np nl ns hn
          (fun r hm => hno r (List.mem_cons_of_mem _ hm))
        constructor
        · apply Finset.Subset.trans hsub
          rw [hframe.1]
          cases acceptedLabel r.input with
          | none => exact Finset.Subset.refl _
          | some i => exact Finset.erase_subset i old.pending
        · exact hsig.trans hframe.2

/-- Pending sets are nested over an actual computed collection block until
its first later choice. Endpoint observations exclude preceding dagger using
the horizon absorption theorem; no no-dagger premise is supplied. -/
theorem run_collection_pending_nested_block (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hc : initial.coordinator = .collection payload old proposal)
    (hf : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState.coordinator =
      .collection cp out saved)
    (hno : ∀ r ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      laterChosen r.input = false) : out.pending ⊆ old.pending ∧ out.sigma = old.sigma :=
  connected_pending_nested _ (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count hspan hmode)
    payload old proposal cp out saved hc hf hno

/-- Actual prefix records occur at the beginning of the longer computed run. -/
theorem run_records_prefix (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ∃ suffix, (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (left + right) hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left (by omega) hmode).records ++ suffix := by
  induction right with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ right ih =>
      obtain ⟨suffix, he⟩ := ih (by omega)
      change ∃ suffix, (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        ((left + right) + 1) (by omega) hmode).records =
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left (by omega) hmode).records ++ suffix
      rw [ReferenceActivePhysicalHorizon.run_successor_step]
      change ∃ suffix', _ ++ [_] = _ ++ suffix'
      rw [he]
      exact ⟨suffix ++ [_], List.append_assoc _ _ _⟩

private theorem window_extension (before : List (Record p rate)) (cutoff : Record p rate)
    (during suffix : List (Record p rate))
    (h : ∀ r ∈ during, laterChosen r.input = false) :
    cutoff :: during <+: collectionWindow ((before ++ cutoff :: during) ++ suffix) before.length := by
  rw [List.append_assoc, List.cons_append]
  unfold collectionWindow
  rw [List.drop_append_length, List.drop_add_one_eq_tail_drop, List.drop_append_length]
  simp only [List.tail_cons, List.take_succ_cons, List.take_zero, List.singleton_append]
  rw [List.takeWhile_append_of_pos (fun r hr => by rw [h r hr]; rfl)]
  exact ⟨_, rfl⟩

/-- The exact interval [a,b) is a prefix of the collection window searched in
the entire longer computed run. Thus the endpoint result applies inside a
window, including when its first later choice is beyond b. -/
theorem run_collection_pending_exact_prefix (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start beforeCount afterCount : ℕ) (hspan : start + (beforeCount + afterCount) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (hc : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount (by omega) hmode).finalState.coordinator =
      .collection payload ledger proposal) :
    ∃ (a : ℕ) (cutoff : Record p rate),
      a < beforeCount ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (beforeCount + afterCount) hspan hmode).records[a]? =
        some cutoff ∧ cutoffChosen cutoff.input = true ∧
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount (by omega) hmode).records.drop a) <+:
        collectionWindow
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (beforeCount + afterCount) hspan hmode).records a ∧
      ledger.pending = Finset.univ \
        (acceptedLabels ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount
          (by omega) hmode).records.drop a)).toFinset ∧
      (acceptedLabels ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount
        (by omega) hmode).records.drop a)).Nodup := by
  obtain ⟨before, cutoff, during, he, hcut, _, hd, hp, hn, _⟩ :=
    run_history initial rows selected rewards start beforeCount (by omega) hmode hfirst
      payload ledger proposal hc
  obtain ⟨suffix, hfull⟩ := run_records_prefix initial rows selected rewards start
    beforeCount afterCount hspan hmode
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start beforeCount (by omega) hmode
  rw [he, List.length_append, List.length_cons] at hlength
  refine ⟨before.length, cutoff, by omega, ?_, hcut, ?_, ?_, ?_⟩
  · rw [hfull, he, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
    rfl
  · rw [he, List.drop_append_length, hfull, he]
    exact window_extension before cutoff during suffix (fun r hr => (hd r hr).2)
  · rw [he, List.drop_append_length]
    exact hp
  · rw [he, List.drop_append_length]
    exact hn

/-- Reception acceptance cannot coincide with an executed later assignment
choice; collection finishing above never installs an assignment either. -/
theorem acceptedLabel_no_later {x : ReferenceActivePhysicalStep.RoundInput p rate} {i : Label p}
    (hi : acceptedLabel x = some i) : laterChosen x = false := by
  obtain ⟨message, tail, recording, started, decoded, bank, ht, _⟩ := acceptedLabel_witness hi
  exact (executedTail_origin ht).1

private theorem connected_append_right {initial current final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (Record p rate))
    (hfull : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final)
    (hleft : ReferenceActivePhysicalHorizon.Connected initial left current) : ReferenceActivePhysicalHorizon.Connected current right final := by
  induction left generalizing initial with
  | nil =>
      subst current
      exact hfull
  | cons r rs ih =>
      exact ih hfull.2 hleft.2

/-- For C_b and C_c of one canonical run, pending is nested as long as the
actual records [b,c) contain no later choice. This is exactly the observation
defining a collection window, rather than an additional physical law. -/
theorem run_collection_pending_nested (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start beforeCount afterCount : ℕ) (hspan : start + (beforeCount + afterCount) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate) (proposal)
    (cp : ReferenceActivePhysicalStep.Payload rate) (out : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (hc : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount (by omega) hmode).finalState.coordinator =
      .collection payload old proposal)
    (hf : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (beforeCount + afterCount) hspan hmode).finalState.coordinator =
      .collection cp out saved)
    (hno : ∀ r ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (beforeCount + afterCount) hspan hmode).records.drop beforeCount,
      laterChosen r.input = false) : out.pending ⊆ old.pending ∧ out.sigma = old.sigma := by
  obtain ⟨suffix, he⟩ := run_records_prefix initial rows selected rewards start beforeCount afterCount hspan hmode
  have hfull := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start (beforeCount + afterCount) hspan hmode
  rw [he] at hfull
  have hchain := connected_append_right _ _ hfull
    (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start beforeCount (by omega) hmode)
  apply connected_pending_nested suffix hchain payload old proposal cp out saved hc hf
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start beforeCount (by omega) hmode
  have hdrop := List.drop_append_length
    (l₁ := (ReferenceActivePhysicalHorizon.run initial rows selected rewards start beforeCount (by omega) hmode).records)
    (l₂ := suffix)
  rw [hlen] at hdrop
  rw [he, hdrop] at hno
  exact hno

section LaunchInputs

variable
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
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
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

/-- Actual boundary specialization; all initialization conversion inputs remain explicit. -/
theorem ofActualLaunchedBoundary_history (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    History (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start count hspan hmode).records
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode).finalState := by
  dsimp only
  exact run_history _ _ _ _ _ count hspan _ (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

/-- Conditional actual-boundary specialization of the computed history theorem. -/
theorem ofActualLaunchedBoundary_pending_exact (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode).finalState.coordinator = .collection payload ledger proposal →
    ∃ (before : List (Record p rate)) (cutoff : Record p rate) (during : List (Record p rate)),
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode).records =
        before ++ cutoff :: during ∧ before.length < count ∧
      cutoffChosen cutoff.input = true ∧
      collectionWindow (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode).records
        before.length = cutoff :: during ∧
      ledger.pending = Finset.univ \ (acceptedLabels (cutoff :: during)).toFinset ∧
      (acceptedLabels (cutoff :: during)).Nodup ∧
      ∀ r ∈ cutoff :: during, ∀ i, acceptedLabel r.input = some i →
        ∃ message, AcceptedUp r.input i message ∧ message.val.sigma = ledger.sigma := by
  dsimp only
  intro payload ledger proposal hc
  exact run_collection_pending_exact _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) payload ledger proposal hc

/-- Conditional actual-boundary specialization of the computed history theorem. -/
theorem ofActualLaunchedBoundary_laterStart_all_up_accepted (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + (count + 1) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    laterChosen (nextInput initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start count hspan hmode) = true →
    ∃ (before : List (Record p rate)) (cutoff : Record p rate)
      (during : List (Record p rate)) (payload : ReferenceActivePhysicalStep.Payload rate)
      (old : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count (by omega) hmode).records =
        before ++ cutoff :: during ∧ cutoffChosen cutoff.input = true ∧
      (nextInput initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode).state.coordinator =
        .collection payload old proposal ∧ old.pending = ∅ ∧
      collectionWindow
        ((ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count (by omega) hmode).records ++
          [⟨nextInput initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode,
            ReferenceActivePhysicalStep.step (nextInput initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode), rfl⟩])
        before.length = cutoff :: during ∧
      ∀ i : Label p, ∃ (k : ℕ) (r : Record p rate) (message : UpRecord p rate),
        before.length ≤ k ∧ k < count ∧
        (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count (by omega) hmode).records[k]? = some r ∧
        AcceptedUp r.input i message ∧ message.val.sigma = old.sigma := by
  dsimp only
  intro hlater
  exact run_laterStart_all_up_accepted _ _ _ _ _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) hlater

/-- Actual launched constructor, with an interior endpoint of the longer run. -/
theorem ofActualLaunchedBoundary_pending_exact_prefix (beforeCount afterCount : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + (beforeCount + afterCount) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start beforeCount (by omega) hmode).finalState.coordinator = .collection payload ledger proposal →
    ∃ (a : ℕ) (cutoff : Record p rate),
      a < beforeCount ∧
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (beforeCount + afterCount) hspan hmode).records[a]? =
        some cutoff ∧ cutoffChosen cutoff.input = true ∧
      ((ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start beforeCount (by omega) hmode).records.drop a) <+:
        collectionWindow
          (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (beforeCount + afterCount) hspan hmode).records a ∧
      ledger.pending = Finset.univ \
        (acceptedLabels ((ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start beforeCount
          (by omega) hmode).records.drop a)).toFinset ∧
      (acceptedLabels ((ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start beforeCount
        (by omega) hmode).records.drop a)).Nodup := by
  dsimp only
  intro payload ledger proposal hc
  exact run_collection_pending_exact_prefix _ _ _ _ _ beforeCount afterCount hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) payload ledger proposal hc

/-- Nested pending sets at two computed prefixes of the actual launched suffix. -/
theorem ofActualLaunchedBoundary_pending_nested (beforeCount afterCount : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + (beforeCount + afterCount) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    ∀ (payload : ReferenceActivePhysicalStep.Payload rate) (old : ReferenceActivePhysicalStep.Ledger rate)
      (proposal : Option (Fin p.T × Bool)) (cp : ReferenceActivePhysicalStep.Payload rate)
      (out : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start beforeCount (by omega) hmode).finalState.coordinator = .collection payload old proposal →
      (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (beforeCount + afterCount) hspan hmode).finalState.coordinator = .collection cp out saved →
      (∀ r ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (beforeCount + afterCount) hspan hmode).records.drop beforeCount,
        laterChosen r.input = false) → out.pending ⊆ old.pending ∧ out.sigma = old.sigma := by
  dsimp only
  intro payload old proposal cp out saved hc hf hno
  exact run_collection_pending_nested _ _ _ _ _ beforeCount afterCount hspan _
    payload old proposal cp out saved hc hf hno

end LaunchInputs

end Bandits.Support.ReferenceCollectionPhaseHistory
end
