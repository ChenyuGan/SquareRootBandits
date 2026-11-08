/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.CollectionCheckedExecution

/-!
# Actual collection calendar inputs

Literal projections of the accepted physical dispatch, recorder, filtered UP
receiver and collection tail. Mathematical evidence:
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-165` and
`sources/zip4/manuscript/06_interruptions.tex:246-267,277-294,391-397`.
An incoming collection boundary is distinguished from a newly initialized
cutoff. Failed rounds retain their complete original physical record.
For a failed first round the checked prefix is empty: its ledger endpoint is
the pre-round initializer, while the failed partial successor stays in the
excluded suffix. A nonempty prefix also has an actual stored endpoint theorem.
These are internal execution identities, not a recording-history or score
truth theorem, a domain induction, or a manuscript closure assertion.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionSegmentExtraction


open ConstructorDimensions

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- Actual cutoff initializer arguments, without any true-score input. -/
structure Initializer (p : Parameters) where
  assignment : CoordinatorCollectionLedger.Assignment p
  sigma : ℕ
  cutoff : ℕ
  freezeAt : ℕ
  base : Fin (p.m - 1) → ℕ
  outside : Fin p.K → Option CoordinatorCollectionLedger.CutoffRegister

def Initializer.checkedStart (a : Initializer p) (rate : ReferenceActivePhysicalStep.RateInput p) :
    CoordinatorCollectionLedger.Checked (ReferenceActivePhysicalStep.Ledger rate) :=
  CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val rate.eta.property
    (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale a.assignment a.sigma
    a.cutoff a.freezeAt a.base a.outside

def cutoffInitializer (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T) : Initializer p :=
  ⟨CoordinatorStartRoundCutoffDispatch.ledgerAssignment r, r.payload.sigma.val + 1, time.val + 1,
    r.gridBoundary, base, CoordinatorStartRoundCutoffDispatch.outsideRegisters r q⟩

/-- A projection of a successful post-choice collection dispatch. `none`
denotes an incoming collection, not a source initializer. -/
structure Choice (rate : ReferenceActivePhysicalStep.RateInput p) where
  payload : ReferenceActivePhysicalStep.Payload rate
  preLedger : ReferenceActivePhysicalStep.Ledger rate
  started : CoordinatorPhaseClock.StartRoundResult p
  weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ
  initializer : Option (Initializer p)

def choiceOfCut {x : ReferenceActivePhysicalStep.RoundInput p rate} : ReferenceActivePhysicalStep.DispatchCut x → Option (Choice rate)
  | .live r q base (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
      some ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights,
        some (cutoffInitializer (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)⟩
  | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
      some ⟨payload, ledger, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
  | _ => none

/-- Include the cutoff round itself and every actual continuing collection
choice, also when service is disabled. No arrival-positivity test occurs. -/
def choice (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Choice rate) :=
  if (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none then none
  else choiceOfCut (ReferenceActivePhysicalStep.prepare x).coordinator

theorem choice_tail (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (h : choice x = some c) :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator = ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x)
      c.payload c.preLedger c.started c.weights := by
  unfold choice at h
  split at h
  · contradiction
  next hn =>
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    simp only [dite_eq_right hn]
    cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at h
    | live r q base outcome =>
        cases outcome <;> simp only [hc, choiceOfCut] at h
        all_goals first | contradiction | (cases Option.some.inj h; rfl)
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc, choiceOfCut] at h
        all_goals first | contradiction | (cases Option.some.inj h; rfl)
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at h
    | dagger => simp [hc, choiceOfCut] at h

theorem shared_initializer {n : ℕ}
    {hn : (n : ℝ) = rate.eta.val * (D p : ℝ)}
    {cap : CoordinatorCollectionLedger.sourceLearningCap p rate.eta.val}
    (a : Initializer p)
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property cap n hn)
    (h : CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val rate.eta.property cap n hn
      a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside = .success ledger) :
    a.checkedStart rate = .success (ReferenceActivePhysicalStep.sharedLedger ledger) := by
  have hn' : n = rate.n := ReferenceActivePhysicalStep.shared_n_eq hn
  subst n
  simpa only [Initializer.checkedStart, ReferenceActivePhysicalStep.sharedLedger] using h

/-- The initialization check is discharged from the actual cutoff constructor's
domain evidence and candidate equality, rather than assumed as a trace law. -/
theorem choice_initializer (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (a : Initializer p) (h : choice x = some c) (ha : c.initializer = some a) :
    a.checkedStart rate = .success c.preLedger := by
  unfold choice at h
  split at h
  · contradiction
  next =>
    cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at h
    | live r q base outcome =>
        cases outcome <;> simp only [hc, choiceOfCut] at h
        all_goals try contradiction
        next dispatched hstart ledger hinit heq hdomain hclock hpending hno selected =>
          cases Option.some.inj h
          cases Option.some.inj ha
          rw [heq]
          exact shared_initializer _ _
            (CoordinatorStartRoundCutoffDispatch.startCollectionChecked_success_of_domains _ _ _ _ hdomain)
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc, choiceOfCut] at h
        all_goals first | contradiction | (cases Option.some.inj h; contradiction)
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at h
    | dagger => simp [hc, choiceOfCut] at h

/-- The raw decoder transition is evaluated after this round's checked
start/service. The effective parse is filtered against the same prepared
choice-time UP offer. The diagnostic's unfiltered parse is never read. -/
def effectiveParse (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (started : ReferenceActivePhysicalStep.Ledger rate) :
    Option (OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val)) :=
  CoordinatorUpReception.parseDecoderOutput (ReferenceUpReception.filterRawByExpected
    (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time)).2
    (ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)))

def inputOf (x : ReferenceActivePhysicalStep.RoundInput p rate) (pre : ReferenceActivePhysicalStep.Ledger rate)
    (recording : CoordinatorRecordingOperation.Output p) (started : ReferenceActivePhysicalStep.Ledger rate) :
    CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val) :=
  ⟨x.time, ReferenceActivePhysicalStep.collectionEnabled pre x.time,
    CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording,
    ReferenceActivePhysicalStep.upSenderIndex x, effectiveParse x started⟩

theorem receiveUp_filtered (x : ReferenceActivePhysicalStep.RoundInput p rate) (started : ReferenceActivePhysicalStep.Ledger rate)
    (hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time) = true) :
    (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result = CoordinatorUpReception.packDecodeResult
      (CoordinatorCollectionLedger.decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x) (effectiveParse x started))
      (CoordinatorUpReception.decoderBankAfter
        (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time)) := by
  exact ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode rate x.row
    (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time
    ((ReferenceActivePhysicalStep.prepare x).followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl hcheck

theorem receiveUp_input_check (x : ReferenceActivePhysicalStep.RoundInput p rate) (started : ReferenceActivePhysicalStep.Ledger rate)
    (h : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result ≠ .invalid) :
    CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time) = true := by
  cases hc : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time) with
  | true => rfl
  | false =>
      apply False.elim
      apply h
      exact ReferenceUpReception.receiveUpFilteredAtRow_input_invalid rate x.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time
        ((ReferenceActivePhysicalStep.prepare x).followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl hc |>.1

/-- Proof-free fields extracted from one physically completed collection
round. Acceptance is the filtered receiver's constructor tag. -/
structure CompletedRound (rate : ReferenceActivePhysicalStep.RateInput p) where
  context : Choice rate
  input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val)
  accepted : Bool
  final : ReferenceActivePhysicalStep.Ledger rate

/-- Project only a collection endpoint. A failed tail is excluded here and
retained separately by the segment exit as its entire original record. -/
def extractWith (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) : Option (CompletedRound rate) :=
  match observation.configuration, observation.recording with
  | .collection _ final _, some recording =>
      match CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | .success started =>
          match (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
          | .success _ => some ⟨c, inputOf x c.preLedger recording started, true, final⟩
          | .rejected _ => some ⟨c, inputOf x c.preLedger recording started, false, final⟩
          | .invalid => none
      | _ => none
  | _, _ => none

def extractRound (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (CompletedRound rate) :=
  (choice record.input).bind fun c => extractWith record.input c record.output.coordinator


/-- The receiver's successful/rejected tag gives the corresponding literal
filtered ledger decode; invalid reception supplies no such conclusion. -/
theorem receiveUp_decode_result (x : ReferenceActivePhysicalStep.RoundInput p rate) (started : ReferenceActivePhysicalStep.Ledger rate) :
    match (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
    | .success (decoded, _) =>
        CoordinatorCollectionLedger.decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x) (effectiveParse x started) = .success decoded
    | .rejected (decoded, _) =>
        CoordinatorCollectionLedger.decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x) (effectiveParse x started) = .rejected decoded
    | .invalid => True := by
  by_cases hbad : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result = .invalid
  · rw [hbad]
    trivial
  · rw [receiveUp_filtered x started (receiveUp_input_check x started hbad)]
    cases CoordinatorCollectionLedger.decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x) (effectiveParse x started) <;> simp only [CoordinatorUpReception.packDecodeResult]

theorem extractWith_endpoint (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) (r : CompletedRound rate)
    (h : extractWith x c observation = some r) :
    r.context = c ∧ r.input.round = x.time ∧
      ∃ payload proposal, observation.configuration = .collection payload r.final proposal := by
  unfold extractWith at h
  split at h
  · split at h
    · split at h <;> first | contradiction | (cases Option.some.inj h; exact ⟨rfl, rfl, _, _, by assumption⟩)
    · contradiction
  · contradiction

/-- A physically completed tail executes the same checked ledger round.
The proof splits the actual recorder/start/receive/finish/clock calls, including
ordinary UP rejection. No success or domain invariant for a history is an input. -/
theorem collection_tail_checked (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (r : CompletedRound rate)
    (h : extractWith x c
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights) =
        some r) :
    CollectionCheckedExecution.checkedRounds c.preLedger [r.input] = some ([r.accepted], r.final) := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  cases hrec : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) with
  | none => simp only [hrec, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
  | some recording =>
      simp only [hrec] at h
      cases hs : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hs, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
      | rejected rejected => simp only [hs, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
      | success started =>
          simp only [hs] at h
          have hd := receiveUp_decode_result x started
          cases hr : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
          | invalid =>
              simp only [ReferenceActivePhysicalStep.collectionFinish, hr, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hr] at hd
              simp only [ReferenceActivePhysicalStep.collectionFinish, hr] at h
              cases hf : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp only [hf, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
              | rejected rejected => simp only [hf, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
              | success finished =>
                  simp only [hf] at h
                  cases hk : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => simp only [hk, ReferenceActivePhysicalStep.coordinatorFailure, extractWith, reduceCtorEq] at h
                  | ok clockFinished =>
                      simp only [hk, extractWith, hs, hr] at h
                      cases Option.some.inj h
                      simp only [CollectionCheckedExecution.checkedRounds, inputOf, CoordinatorCollectionLedger.sourceRound, hs, hd, hf]

/-- Physical origin of a single checked collection round, using the retained
input/output equality of the accepted horizon record. -/
theorem actual_collection_round_checked
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (r : CompletedRound rate)
    (h : extractRound record = some r) :
    choice record.input = some r.context ∧
      r.input.round = record.input.time ∧
      CollectionCheckedExecution.checkedRounds r.context.preLedger [r.input] = some ([r.accepted], r.final) ∧
      ∃ payload proposal,
        record.output.next.coordinator = .collection payload r.final proposal := by
  unfold extractRound at h
  cases hc : choice record.input with
  | none => simp only [hc, Option.bind_none, reduceCtorEq] at h
  | some c =>
      simp only [hc, Option.bind_some] at h
      obtain ⟨hcontext, hround, payload, proposal, hendpoint⟩ :=
        extractWith_endpoint record.input c record.output.coordinator r h
      have htail : record.output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare record.input)
            c.payload c.preLedger c.started c.weights := by
        rw [record.output_eq]
        exact choice_tail record.input c hc
      have hchecked := collection_tail_checked record.input c r (htail ▸ h)
      refine ⟨congrArg some hcontext.symm, hround, ?_, payload, proposal, ?_⟩
      · rw [hcontext]
        exact hchecked
      · rw [record.output_eq] at hendpoint ⊢
        exact hendpoint


/-- On a carried collection input the dispatch projection keeps the actual
pre-round ledger, rather than matching it to a separately supplied trace. -/
theorem choice_collection_pre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (c : Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (h : choice x = some c) :
    c.preLedger = ledger ∧ c.initializer = none := by
  unfold choice at h
  split at h
  · contradiction
  next =>
    change choiceOfCut (ReferenceActivePhysicalStep.dispatch x) = some c at h
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at h
    split at h
    next hcut =>
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
      change choiceOfCut (.collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))) = some c at h
      cases ho : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) <;>
        simp only [choiceOfCut, ho] at h
      all_goals first | contradiction | (cases Option.some.inj h; exact ⟨rfl, rfl⟩)
    · simp only [choiceOfCut, reduceCtorEq] at h

/-- Literal retained completed-round list; this does not filter on arrivals,
enabled bits or acceptance. -/
def completed (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    List (CompletedRound rate) :=
  records.filterMap extractRound

def inputs (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :=
  (completed records).map CompletedRound.input

def acceptances (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :=
  (completed records).map CompletedRound.accepted

/-- Endpoint ledger projection. The empty prefix ends at its incoming ledger. -/
def endpointLedger (initial : ReferenceActivePhysicalStep.Ledger rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) : ReferenceActivePhysicalStep.Ledger rate :=
  (completed records).foldl (fun _ r => r.final) initial

/-- Endpoint of the original physical records, including all original stores. -/
def endpointState (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) : ReferenceActivePhysicalStep.State p rate :=
  records.foldl (fun _ record => record.output.next) initial

/-- A continuing completed collection round. The first cutoff round is
handled separately, and no later cutoff is silently joined to this segment. -/
def continuing (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  match extractRound record with
  | none => false
  | some r => r.context.initializer.isNone

theorem completed_append
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    completed (left ++ right) = completed left ++ completed right :=
  List.filterMap_append

theorem endpointLedger_append (initial : ReferenceActivePhysicalStep.Ledger rate)
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    endpointLedger initial (left ++ right) =
      endpointLedger (endpointLedger initial left) right := by
  simp only [endpointLedger, completed_append, List.foldl_append]

/-- Composition of two actual checked calls. This is the existing ledger
fold's cons equation, not an alternative recurrence for physical execution. -/
theorem checkedRounds_cons (initial middle final : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (accepted : Bool) (rest : List (CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val)))
    (acceptedRest : List Bool)
    (hone : CollectionCheckedExecution.checkedRounds initial [input] = some ([accepted], middle))
    (hrest : CollectionCheckedExecution.checkedRounds middle rest = some (acceptedRest, final)) :
    CollectionCheckedExecution.checkedRounds initial (input :: rest) = some (accepted :: acceptedRest, final) := by
  cases hs : CoordinatorCollectionLedger.startRound initial (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw with
  | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at hone
  | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, reduceCtorEq] at hone
  | success started =>
      cases hd : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed with
      | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, reduceCtorEq] at hone
      | success decoded | rejected decoded =>
          cases hf : CoordinatorCollectionLedger.finishRound decoded with
          | invalid => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at hone
          | rejected bad => simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, reduceCtorEq] at hone
          | success finished =>
              simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, Option.some.injEq, Prod.mk.injEq,
                List.cons.injEq, and_true] at hone
              rcases hone with ⟨rfl, rfl⟩
              simp only [CollectionCheckedExecution.checkedRounds, hs, hd, hf, hrest]

/-- Every retained continuing input executes on the actual previous endpoint.
All chain evidence is the accepted physical horizon's literal linkage. -/
theorem continuing_checked
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (current final : ReferenceActivePhysicalStep.State p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hchain : ReferenceActivePhysicalHorizon.Connected current records final)
    (hcoord : current.coordinator = .collection payload ledger proposal) :
    CollectionCheckedExecution.checkedRounds ledger (inputs (records.takeWhile continuing)) =
        some (acceptances (records.takeWhile continuing),
          endpointLedger ledger (records.takeWhile continuing)) ∧
      ∃ payload' proposal',
        (endpointState current (records.takeWhile continuing)).coordinator =
          .collection payload' (endpointLedger ledger (records.takeWhile continuing)) proposal' := by
  induction records generalizing current payload ledger proposal with
  | nil =>
      exact ⟨rfl, payload, proposal, hcoord⟩
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hchain⟩
      cases he : extractRound record with
      | none =>
          simpa only [List.takeWhile_cons, continuing, he, Bool.false_eq_true,
            ↓reduceIte, inputs, acceptances, completed, List.filterMap_nil, List.map_nil,
            endpointLedger, List.foldl_nil, endpointState, CollectionCheckedExecution.checkedRounds]
            using And.intro (Eq.refl (some (([] : List Bool), ledger))) ⟨payload, proposal, hcoord⟩
      | some r =>
          cases hi : r.context.initializer with
          | some a =>
              simpa only [List.takeWhile_cons, continuing, he, hi, Option.isNone_some,
                Bool.false_eq_true, ↓reduceIte, inputs, acceptances, completed,
                List.filterMap_nil, List.map_nil, endpointLedger, List.foldl_nil,
                endpointState, CollectionCheckedExecution.checkedRounds]
                using And.intro (Eq.refl (some (([] : List Bool), ledger))) ⟨payload, proposal, hcoord⟩
          | none =>
              obtain ⟨hc, _, hone, nextPayload, nextProposal, hnext⟩ :=
                actual_collection_round_checked record r he
              have hledger := (choice_collection_pre record.input payload ledger proposal r.context
                (hpre ▸ hcoord) hc).1
              obtain ⟨htail, tailPayload, tailProposal, htailCoord⟩ :=
                ih record.output.next nextPayload r.final nextProposal hchain hnext
              have hboth := checkedRounds_cons ledger r.final
                (endpointLedger r.final (rest.takeWhile continuing)) r.input r.accepted
                (inputs (rest.takeWhile continuing)) (acceptances (rest.takeWhile continuing))
                (hledger ▸ hone) htail
              simpa only [List.takeWhile_cons, continuing, he, hi, Option.isNone_none,
                ↓reduceIte, inputs, acceptances, completed, List.filterMap_cons, he,
                List.map_cons, endpointLedger, List.foldl_cons, endpointState]
                using And.intro hboth ⟨tailPayload, tailProposal, htailCoord⟩


/-- The exact first excluded physical record is retained. Later chosen
marks a complete segment; an interval end or other stop leaves it open.
The stored record exposes the original dependent dispatch tag, recorder,
UP diagnostic, failure reason and partial successor, without recomputation. -/
inductive Exit (rate : ReferenceActivePhysicalStep.RateInput p) where
  | intervalEnd
  | laterChosen (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
  | stopped (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))

def exitOf (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) : Exit rate :=
  match records with
  | [] => .intervalEnd
  | record :: _ =>
      match (ReferenceActivePhysicalStep.prepare record.input).coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
          .laterChosen record
      | _ => .stopped record

/-- A segment is a literal prefix/suffix split of the original physical
records. The optional initializer distinguishes a real cutoff from an
arbitrary incoming collection boundary. -/
structure Segment (rate : ReferenceActivePhysicalStep.RateInput p) where
  entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
  context : Choice rate
  records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
  remaining : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))

def segment (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    Option (Segment rate) :=
  match records with
  | [] => none
  | entry :: rest =>
      (choice entry.input).map fun c =>
        if (extractRound entry).isSome then
          ⟨entry, c, entry :: rest.takeWhile continuing, rest.dropWhile continuing⟩
        else
          ⟨entry, c, [], entry :: rest⟩

def Segment.exit (s : Segment rate) : Exit rate := exitOf s.remaining

def Segment.inputs (s : Segment rate) := ReferenceCollectionSegmentExtraction.inputs s.records

def Segment.accepted (s : Segment rate) := acceptances s.records

def Segment.final (s : Segment rate) := endpointLedger s.context.preLedger s.records

/-- Every excluded round, including a failed first round, is retained in the
suffix. No failed physical operation becomes a successful checked input. -/
theorem segment_partition
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (s : Segment rate)
    (h : segment records = some s) :
    s.records ++ s.remaining = records := by
  cases records with
  | nil => simp only [segment, reduceCtorEq] at h
  | cons entry rest =>
      unfold segment at h
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at h
      | some c =>
          simp only [hc, Option.map_some] at h
          split at h
          · cases Option.some.inj h
            simp only [List.cons_append, List.takeWhile_append_dropWhile]
          · cases Option.some.inj h
            rfl

/-- The projected segment executes on its actual entry ledger and returns
the literal filtered acceptance list and last completed physical ledger.
The original carried arrays are not replaced by a matching local trace. -/
theorem connected_segment_checked
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (s : Segment rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) (h : segment records = some s) :
    CollectionCheckedExecution.checkedRounds s.context.preLedger s.inputs = some (s.accepted, s.final) := by
  cases records with
  | nil => simp only [segment, reduceCtorEq] at h
  | cons entry rest =>
      rcases hchain with ⟨_, hchain⟩
      unfold segment at h
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at h
      | some c =>
          simp only [hc, Option.map_some] at h
          cases he : extractRound entry with
          | none =>
              simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
              cases Option.some.inj h
              rfl
          | some r =>
              simp only [he, Option.isSome_some, ↓reduceIte] at h
              cases Option.some.inj h
              obtain ⟨hrc, _, hone, payload, proposal, hnext⟩ :=
                actual_collection_round_checked entry r he
              have hcontext : r.context = c := Option.some.inj (hrc.symm.trans hc)
              have htail := (continuing_checked rest entry.output.next final payload r.final
                proposal hchain hnext).1
              have hboth := checkedRounds_cons c.preLedger r.final
                (endpointLedger r.final (rest.takeWhile continuing)) r.input r.accepted
                (inputs (rest.takeWhile continuing)) (acceptances (rest.takeWhile continuing))
                (hcontext ▸ hone) htail
              simpa only [Segment.inputs, Segment.accepted, Segment.final, inputs,
                acceptances, endpointLedger, completed, List.filterMap_cons, he,
                List.map_cons, List.foldl_cons] using hboth

/-- Source initialization comes from the actual cutoff dispatch. An open
incoming collection has no initializer and cannot use this export.
The branch equation identifies the actual computed initializer projection. -/
theorem connected_segment_initialized
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (s : Segment rate) (a : Initializer p)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) (h : segment records = some s)
    (ha : s.context.initializer = some a) :
    CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside s.inputs =
        .success ⟨s.context.preLedger, s.accepted, s.final⟩ := by
  have hchoice : choice s.entry.input = some s.context := by
    cases records with
    | nil => simp only [segment, reduceCtorEq] at h
    | cons entry rest =>
        unfold segment at h
        cases hc : choice entry.input with
        | none => simp only [hc, Option.map_none, reduceCtorEq] at h
        | some c =>
            simp only [hc, Option.map_some] at h
            split at h <;> cases Option.some.inj h <;> exact hc
  have hinit := choice_initializer s.entry.input s.context a hchoice ha
  have hr := connected_segment_checked records initial final s hchain h
  unfold CollectionCheckedExecution.startAndRunChecked
  dsimp only [Initializer.checkedStart] at hinit
  simp only [hinit, hr]

/-- The accepted horizon supplies all linkage evidence. The original
all-active boundary is the only run-mode input. -/
theorem run_collection_checked_segment_from_boundary (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (s : Segment rate)
    (h : segment (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records = some s) :
    CollectionCheckedExecution.checkedRounds s.context.preLedger s.inputs = some (s.accepted, s.final) :=
  connected_segment_checked _ initial _
    s (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count span active) h

theorem run_collection_initialized_segment (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (s : Segment rate) (a : Initializer p)
    (h : segment (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records = some s)
    (ha : s.context.initializer = some a) :
    CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside s.inputs =
        .success ⟨s.context.preLedger, s.accepted, s.final⟩ :=
  connected_segment_initialized _ initial _ s a
    (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count span active) h ha


theorem continuing_isSome
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (h : continuing record = true) :
    (extractRound record).isSome = true := by
  cases he : extractRound record with
  | none => simp only [continuing, he, Bool.false_eq_true] at h
  | some r => rfl

theorem segment_all_completed
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (s : Segment rate)
    (h : segment records = some s) :
    ∀ record ∈ s.records, (extractRound record).isSome = true := by
  cases records with
  | nil => simp only [segment, reduceCtorEq] at h
  | cons entry rest =>
      unfold segment at h
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at h
      | some c =>
          simp only [hc, Option.map_some] at h
          split at h
          next hgood =>
            cases Option.some.inj h
            intro record hm
            rcases List.mem_cons.mp hm with rfl | hm
            · exact hgood
            · exact continuing_isSome record
                ((List.all_eq_true.mp List.all_takeWhile) record hm)
          next =>
            cases Option.some.inj h
            intro record hm
            exact False.elim (List.not_mem_nil hm)

/-- Calendar projection for a list of retained actual rounds. The only local
condition says the extractor retained each cell; it carries no recording law. -/
theorem inputs_calendar
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ record ∈ records, (extractRound record).isSome = true) :
    (inputs records).map (fun input => input.round.val) =
      records.map (fun record => record.input.time.val) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hhead := hgood record (List.mem_cons_self)
      have hrest : ∀ record ∈ rest, (extractRound record).isSome = true :=
        fun record hm => hgood record (List.mem_cons_of_mem _ hm)
      cases he : extractRound record with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hhead
      | some r =>
          have htime := (actual_collection_round_checked record r he).2.1
          simpa only [inputs, completed, List.filterMap_cons, he, List.map_cons,
            htime] using congrArg (List.cons record.input.time.val) (ih hrest)

/-- Every retained calendar cell appears once, including disabled rounds,
zero arrivals and rejected UP messages. -/
theorem segment_input_calendar
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (s : Segment rate)
    (h : segment records = some s) :
    s.inputs.map (fun input => input.round.val) =
      (records.map (fun record => record.input.time.val)).take s.records.length := by
  rw [Segment.inputs, inputs_calendar s.records (segment_all_completed records s h)]
  rw [← segment_partition records s h, List.map_append]
  exact (List.take_left' (List.length_map _)).symm

theorem run_collection_input_calendar_from_boundary (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (s : Segment rate)
    (h : segment (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records = some s) :
    s.inputs.map (fun input => input.round.val) =
      (ReferenceActivePhysicalHorizon.calendar start count).take s.records.length := by
  rw [← ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards start count span active]
  exact segment_input_calendar _ s h


/-- Physical suffix linkage derived solely from the original record chain.
Taking an offset changes neither rows, rewards nor stored predecessor states. -/
theorem connected_drop
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (offset : ℕ)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceActivePhysicalHorizon.Connected (endpointState initial (records.take offset)) (records.drop offset) final := by
  induction offset generalizing initial records with
  | zero => simpa only [List.take_zero, List.drop_zero, endpointState, List.foldl_nil] using hchain
  | succ offset ih =>
      cases records with
      | nil => exact hchain
      | cons record rest =>
          simpa only [List.take_succ_cons, List.drop_succ_cons, endpointState, List.foldl_cons]
            using ih rest record.output.next hchain.2

/-- Extract a cutoff at any calendar offset, allowing an open incoming
collection only at the supplied boundary itself. Mid-collection offsets
cannot be mistaken for newly initialized source segments. -/
def segmentAt (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (offset : ℕ) :
    Option (Segment rate) :=
  (segment (records.drop offset)).bind fun s =>
    if offset = 0 ∨ s.context.initializer.isSome = true then some s else none

/-- All actual cutoff entries, together with a possible incoming boundary.
The finite index enumeration is a list extraction, not another protocol run. -/
def segments (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) : List (Segment rate) :=
  (List.range records.length).filterMap (segmentAt records)

theorem segmentAt_branch
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (offset : ℕ)
    (s : Segment rate) (h : segmentAt records offset = some s) :
    segment (records.drop offset) = some s ∧
      (offset = 0 ∨ s.context.initializer.isSome = true) := by
  unfold segmentAt at h
  cases hs : segment (records.drop offset) with
  | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
  | some found =>
      simp only [hs, Option.bind_some] at h
      split at h
      next hbranch =>
        cases Option.some.inj h
        exact ⟨rfl, hbranch⟩
      next => contradiction

theorem choice_first_none (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) : choice x = none := by
  unfold choice
  split
  · rfl
  · change choiceOfCut (ReferenceActivePhysicalStep.dispatch x) = none
    rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
    rfl

theorem connected_first_segment_none
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfirst : initial.coordinator = .first) :
    segment records = none := by
  cases records with
  | nil => rfl
  | cons record rest =>
      have hc := choice_first_none record.input (hchain.1 ▸ hfirst)
      simp only [segment, hc, Option.map_none]

/-- From a first-assignment boundary, every extracted segment is an actual
cutoff. Arbitrary initial collection boundaries remain explicitly incoming. -/
theorem segmentAt_from_first_initialized
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfirst : initial.coordinator = .first) (offset : ℕ) (s : Segment rate)
    (h : segmentAt records offset = some s) :
    ∃ a, s.context.initializer = some a := by
  obtain ⟨hs, hz | ha⟩ := segmentAt_branch records offset s h
  · subst offset
    rw [List.drop_zero, connected_first_segment_none records initial final hchain hfirst] at hs
    contradiction
  · cases hi : s.context.initializer with
    | none => simp only [hi, Option.isSome_none, Bool.false_eq_true] at ha
    | some a => exact ⟨a, rfl⟩

theorem run_collection_checked_segment (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    CollectionCheckedExecution.checkedRounds s.context.preLedger s.inputs = some (s.accepted, s.final) :=
  connected_segment_checked _ _ _ s
    (connected_drop _ initial _ offset
      (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count span active))
    (segmentAt_branch _ offset s h).1

/-- This supplies the named local execution input at any actual cutoff of the
original run. The first-boundary equality is ordinary source boundary data;
the accepted actual-launch constructor supplies it at the eventual consumer. -/
theorem run_collection_initialized_segment_at (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    ∃ a : Initializer p, s.context.initializer = some a ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
        rate.n rate.n_scale a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside s.inputs =
          .success ⟨s.context.preLedger, s.accepted, s.final⟩ := by
  have hc := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count span active
  obtain ⟨a, ha⟩ := segmentAt_from_first_initialized _ initial _ hc hfirst offset s h
  refine ⟨a, ha, ?_⟩
  exact connected_segment_initialized _ _ _ s a (connected_drop _ initial _ offset hc)
    (segmentAt_branch _ offset s h).1 ha

theorem run_collection_input_calendar (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    s.inputs.map (fun input => input.round.val) =
      ((ReferenceActivePhysicalHorizon.calendar start count).drop offset).take s.records.length := by
  have hc := segment_input_calendar _ s (segmentAt_branch _ offset s h).1
  rw [List.map_drop, ReferenceActivePhysicalHorizon.run_time_values] at hc
  exact hc

/-- Exact physical endpoint for every nonempty retained prefix; no carried
array or ledger is reconstructed from scores or arrival histories. -/
theorem completed_endpoint
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial : ReferenceActivePhysicalStep.State p rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hne : records ≠ [])
    (hgood : ∀ record ∈ records, (extractRound record).isSome = true) :
    ∃ payload proposal, (endpointState initial records).coordinator =
      .collection payload (endpointLedger ledger records) proposal := by
  induction records generalizing initial ledger with
  | nil => contradiction
  | cons record rest ih =>
      have hhead := hgood record List.mem_cons_self
      cases he : extractRound record with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hhead
      | some r =>
          cases rest with
          | nil =>
              obtain ⟨_, _, _, payload, proposal, hnext⟩ :=
                actual_collection_round_checked record r he
              exact ⟨payload, proposal, by
                simpa only [endpointState, endpointLedger, completed, List.filterMap_cons,
                  he, List.filterMap_nil, List.foldl_cons, List.foldl_nil] using hnext⟩
          | cons next tail =>
              have ht := ih record.output.next r.final (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
                (fun r hm => hgood r (List.mem_cons_of_mem _ hm))
              simpa only [endpointState, endpointLedger, completed, List.filterMap_cons,
                he, List.foldl_cons] using ht

theorem segment_actual_endpoint
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (s : Segment rate)
    (h : segment records = some s) (hne : s.records ≠ []) :
    ∃ payload proposal, (endpointState s.entry.input.state s.records).coordinator =
      .collection payload s.final proposal :=
  completed_endpoint s.records s.entry.input.state s.context.preLedger hne
    (segment_all_completed records s h)


/-- Expose the actual start/service and filtered-receiver branches that
produced a retained input. The diagnostic parse is absent from this identity. -/
theorem extractWith_inputs (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) (r : CompletedRound rate)
    (h : extractWith x c observation = some r) :
    ∃ recording started decoded bank,
      observation.recording = some recording ∧
      CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1) (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      r.input = inputOf x c.preLedger recording started ∧
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result =
        (if r.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time) = true := by
  cases hc : observation.configuration <;> cases hrec : observation.recording <;>
    simp only [extractWith, hc, hrec, reduceCtorEq] at h
  next payload final proposal recording =>
    cases hs : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) <;>
      simp only [hs, reduceCtorEq] at h
    next started =>
      cases hr : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result <;>
        simp only [hr, reduceCtorEq] at h
      all_goals
        rename_i pair
        rcases pair with ⟨decoded, bank⟩
        cases Option.some.inj h
        exact ⟨recording, started, decoded, bank, rfl, hs, rfl, hr,
          receiveUp_input_check x started (by rw [hr]; intro hbad; contradiction)⟩

theorem collectionFinish_recording (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).recording = some recording := by
  cases hr : cut.result with
  | invalid => simp only [ReferenceActivePhysicalStep.collectionFinish, hr,
      ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      simp only [ReferenceActivePhysicalStep.collectionFinish, hr]
      cases hf : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp only [ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected bad => simp only [ReferenceActivePhysicalStep.coordinatorFailure]
      | success finished =>
          dsimp only
          cases hk : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finished.pending x.row <;>
            simp only [ReferenceActivePhysicalStep.coordinatorFailure]

theorem collectionPostChoice_recording (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (recording : CoordinatorRecordingOperation.Output p)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights).recording =
      some recording) :
    CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) =
        some recording := by
  cases hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) with
  | none => simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
  | some output =>
      cases hs : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output) <;>
        simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs, ReferenceActivePhysicalStep.coordinatorFailure,
          collectionFinish_recording] at h <;>
        cases Option.some.inj h <;> rfl

/-- Every field of the extracted checked input comes from the actual recorder
and actual successful start/service. Its acceptance bit names the filtered
receiver tag, including genuine local rejection and raw-word mismatches. -/
theorem actual_collection_round_inputs
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (r : CompletedRound rate)
    (h : extractRound record = some r) :
    ∃ recording started decoded bank,
      record.output.coordinator.recording = some recording ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare record.input) r.context.payload
          r.context.started r.context.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound r.context.preLedger (record.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled r.context.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      r.input = inputOf record.input r.context.preLedger recording started ∧
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare record.input) started).result =
        (if r.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate record.input.row
          (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare record.input) started) record.input.time) = true := by
  have hc := (actual_collection_round_checked record r h).1
  unfold extractRound at h
  simp only [hc, Option.bind_some] at h
  obtain ⟨recording, started, decoded, bank, hrecord, hstart, hinput, hreceive, hcheck⟩ :=
    extractWith_inputs record.input r.context record.output.coordinator r h
  have htail : record.output.coordinator =
      ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare record.input) r.context.payload
        r.context.preLedger r.context.started r.context.weights := by
    rw [record.output_eq]
    exact choice_tail record.input r.context hc
  exact ⟨recording, started, decoded, bank, hrecord,
    collectionPostChoice_recording record.input r.context recording (htail ▸ hrecord),
    hstart, hinput, hreceive, hcheck⟩

/-- A wrong unique raw word is removed before parsing. Its physical decoder
transition and its diagnostics are still retained by the original record. -/
theorem effectiveParse_of_mismatch (x : ReferenceActivePhysicalStep.RoundInput p rate) (started : ReferenceActivePhysicalStep.Ledger rate)
    (h : (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate x.row (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time)).2 ≠
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)) :
    effectiveParse x started = none := by
  unfold effectiveParse
  rw [ReferenceUpReception.filterRawByExpected_eq_none_of_ne _ _ h]
  rfl

/-- The source raw-input projection distinguishes a recorded arm with zero
amount from absence of a gate. -/
theorem inputOf_raw_gate (x : ReferenceActivePhysicalStep.RoundInput p rate) (pre started : ReferenceActivePhysicalStep.Ledger rate)
    (recording : CoordinatorRecordingOperation.Output p) :
    (inputOf x pre recording started).raw =
      recording.gateArm.map (fun a => (a, recording.rawArrival)) := rfl

/-- The existing checked fold supplies chronological labels. This identity
does not assert that the raw inputs match a global marker history. -/
theorem run_collection_input_chronology (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    CollectionCheckedExecution.chronologicalFrom s.context.preLedger.cursor s.inputs :=
  CollectionCheckedExecution.checkedRounds_success_input_chronology _ _ _ _
    (run_collection_checked_segment initial rows selected rewards start count span active offset s h)

/-- On a source-initialized segment the actual final cursor advances once per
retained calendar input and the final physical ledger is ready. -/
theorem run_collection_final_cursor (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    s.final.cursor = s.context.preLedger.cursor + s.inputs.length ∧ s.final.phase = .ready := by
  have hc := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count span active
  obtain ⟨a, ha⟩ := segmentAt_from_first_initialized _ initial _ hc hfirst offset s h
  have hs := (segmentAt_branch _ offset s h).1
  have hchoice : choice s.entry.input = some s.context := by
    cases hd : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop offset with
    | nil => simp only [hd, segment, reduceCtorEq] at hs
    | cons entry rest =>
        simp only [hd, segment] at hs
        cases he : choice entry.input with
        | none => simp only [he, Option.map_none, reduceCtorEq] at hs
        | some c =>
            simp only [he, Option.map_some] at hs
            split at hs <;> cases Option.some.inj hs <;> exact he
  have hinit := choice_initializer s.entry.input s.context a hchoice ha
  have hready := CollectionCheckedExecution.startCollectionChecked_success_ready p rate.eta.val rate.eta.property
    (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale a.assignment a.sigma a.cutoff
    a.freezeAt a.base a.outside s.context.preLedger hinit
  exact CollectionCheckedExecution.checkedRounds_success_chronology _ _ hready _ _
    (run_collection_checked_segment initial rows selected rewards start count span active offset s h)


/-- Completeness of the local projection: an actual successful collection
endpoint always supplies a checked input, even for the final accepted UP. -/
theorem collection_tail_complete (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (final : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (h : (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights).configuration =
      .collection payload final proposal) :
    ∃ r, extractWith x c
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights) = some r := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  cases hrec : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) with
  | none => simp only [hrec, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
  | some recording =>
      simp only [hrec] at h
      cases hs : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hs, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
      | rejected bad => simp only [hs, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
      | success started =>
          simp only [hs] at h
          cases hr : (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) started).result with
          | invalid => simp only [ReferenceActivePhysicalStep.collectionFinish, hr, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [ReferenceActivePhysicalStep.collectionFinish, hr] at h
              cases hf : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp only [hf, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
              | rejected bad => simp only [hf, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
              | success finished =>
                  simp only [hf] at h
                  cases hk : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => simp only [hk, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at h
                  | ok clockFinished =>
                      simp only [ReferenceActivePhysicalStep.collectionPostChoice, hrec, hs, ReferenceActivePhysicalStep.collectionFinish,
                        hr, hf, hk, extractWith]
                      exact ⟨_, rfl⟩

theorem actual_collection_round_complete
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : Choice rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (final : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hc : choice record.input = some c)
    (h : record.output.next.coordinator = .collection payload final proposal) :
    ∃ r, extractRound record = some r := by
  have htail : record.output.coordinator =
      ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare record.input) c.payload
        c.preLedger c.started c.weights := by
    rw [record.output_eq]
    exact choice_tail record.input c hc
  have he : record.output.coordinator.configuration = .collection payload final proposal := by
    rw [record.output_eq] at h ⊢
    exact h
  rw [htail] at he
  obtain ⟨r, hr⟩ := collection_tail_complete record.input c payload final proposal he
  exact ⟨r, by simp only [extractRound, hc, Option.bind_some, htail, hr]⟩

def Exit.isComplete : Exit rate → Bool
  | .laterChosen _ => true
  | _ => false

theorem segmentAt_partition
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (offset : ℕ)
    (s : Segment rate) (h : segmentAt records offset = some s) :
    s.records ++ s.remaining = records.drop offset :=
  segment_partition _ s (segmentAt_branch records offset s h).1

theorem segmentAt_actual_endpoint
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (offset : ℕ)
    (s : Segment rate) (h : segmentAt records offset = some s) (hne : s.records ≠ []) :
    ∃ payload proposal, (endpointState s.entry.input.state s.records).coordinator =
      .collection payload s.final proposal :=
  segment_actual_endpoint _ s (segmentAt_branch records offset s h).1 hne

/-- The list enumeration adds no assumption: membership is an actual
computed offset extraction. -/
theorem mem_segments (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (s : Segment rate) :
    s ∈ segments records ↔ ∃ offset, offset < records.length ∧ segmentAt records offset = some s := by
  simp only [segments, List.mem_filterMap, List.mem_range]

theorem run_segments_initialized (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (s : Segment rate)
    (h : s ∈ segments (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records) :
    ∃ a : Initializer p, s.context.initializer = some a ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
        rate.n rate.n_scale a.assignment a.sigma a.cutoff a.freezeAt a.base a.outside s.inputs =
          .success ⟨s.context.preLedger, s.accepted, s.final⟩ := by
  obtain ⟨offset, _, hs⟩ := (mem_segments _ s).mp h
  exact run_collection_initialized_segment_at initial rows selected rewards start count span active
    hfirst offset s hs


/-- An absorbing/failed endpoint can never be presented as a successful
collection input. The original record remains available at the segment exit. -/
theorem extractRound_none_of_dagger
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (h : record.output.next.coordinator = .dagger) :
    extractRound record = none := by
  have he : record.output.coordinator.configuration = .dagger := by
    rw [record.output_eq] at h ⊢
    exact h
  unfold extractRound
  cases hc : choice record.input with
  | none => rfl
  | some c => simp only [Option.bind_some, extractWith, he]

theorem segment_failed_first
    (entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (c : Choice rate)
    (hc : choice entry.input = some c) (h : entry.output.next.coordinator = .dagger) :
    segment (entry :: rest) = some ⟨entry, c, [], entry :: rest⟩ := by
  simp only [segment, hc, Option.map_some, extractRound_none_of_dagger entry h,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem segment_input_count
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (s : Segment rate)
    (h : segment records = some s) : s.inputs.length = s.records.length := by
  have hc := congrArg List.length
    (inputs_calendar s.records (segment_all_completed records s h))
  simpa only [List.length_map, Segment.inputs] using hc

/-- Every retained input still contains the original whole public table,
selected index and reward table. All carried physical states remain the
original linked states of this same run. -/
theorem run_collection_original_inputs (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (offset : ℕ) (s : Segment rate)
    (h : segmentAt (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records offset =
      some s) :
    ∀ record ∈ s.records, record.input.rows = rows ∧ record.input.selected = selected ∧
      record.input.rewards = rewards := by
  intro record hm
  have hd : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop offset := by
    rw [← segmentAt_partition _ offset s h]
    exact List.mem_append.mpr (Or.inl hm)
  exact ReferenceActivePhysicalHorizon.run_record_inputs initial rows selected rewards start count span active
    record (List.mem_of_mem_drop hd)

/-- A genuine incoming boundary uses its carried ledger and has no source
initializer. This distinction is derived from the actual dispatch. -/
theorem connected_boundary_incoming
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)) (s : Segment rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hcoord : initial.coordinator = .collection payload ledger proposal)
    (h : segment records = some s) :
    s.context.preLedger = ledger ∧ s.context.initializer = none := by
  cases records with
  | nil => simp only [segment, reduceCtorEq] at h
  | cons entry rest =>
      unfold segment at h
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at h
      | some c =>
          have hi := choice_collection_pre entry.input payload ledger proposal c
            (hchain.1 ▸ hcoord) hc
          simp only [hc, Option.map_some] at h
          split at h <;> cases Option.some.inj h <;> exact hi

end Bandits.Support.ReferenceCollectionSegmentExtraction

end
