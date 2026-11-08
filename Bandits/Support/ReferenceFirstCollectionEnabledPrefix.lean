/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionChosenContext

/-!
# Actual enabled history in the first collection window

The enabled-history cells are read from the checked initializer and the
original connected physical prefix.  The cell at a round after the clipped
freeze boundary remains `some false` until the current cursor; cells outside
the processed collection rounds remain `none`.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.ReferenceFirstCollectionEpochAlignment
open Bandits.Support.ReferenceFirstCollectionChosenContext

namespace Bandits.Support.ReferenceFirstCollectionEnabledPrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

private theorem checked_single_round_history
    (l final : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (accepted : Bool)
    (h : CollectionCheckedExecution.checkedRounds l [input] =
      some ([accepted], final)) :
    final.enabledHistory = Function.update l.enabledHistory input.round
        (some input.enabled) ∧
      final.cursor = l.cursor + 1 ∧ final.phase = .ready := by
  unfold CollectionCheckedExecution.checkedRounds at h
  cases hs : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round)
      input.enabled input.raw with
  | invalid => simp [hs] at h
  | rejected bad => simp [hs] at h
  | success started =>
      cases hd : CoordinatorCollectionLedger.decodeUp started
          input.selectedFollower input.parsed with
      | invalid => simp [hs, hd] at h
      | success decoded | rejected decoded =>
          cases hf : CoordinatorCollectionLedger.finishRound decoded with
          | invalid => simp [hs, hd, hf] at h
          | rejected bad => simp [hs, hd, hf] at h
          | success finished =>
              have hresult : final = finished := by
                have h' := h
                simp [CollectionCheckedExecution.checkedRounds, hs, hd, hf] at h'
                rcases h' with ⟨_, hfinal⟩
                exact hfinal.symm
              subst final
              have hstartHistory :=
                CollectionCheckedExecution.startRound_success_history_update
                  l started input.round input.enabled input.raw hs
              have hdecodeHistory : decoded.enabledHistory = started.enabledHistory := by
                have hbehavior :=
                  CollectionCheckedExecution.decodeUp_cursor_behavior started
                    input.selectedFollower input.parsed
                rw [hd] at hbehavior
                exact hbehavior.2
              have hdecodeCursor : decoded.cursor = started.cursor := by
                have hbehavior :=
                  CollectionCheckedExecution.decodeUp_cursor_behavior started
                    input.selectedFollower input.parsed
                rw [hd] at hbehavior
                exact hbehavior.1
              have hfinish :=
                CollectionCheckedExecution.finishRound_success_chronology
                  decoded finished hf
              have hcursorStart :=
                CollectionCheckedExecution.startRound_success_cursor l started
                  (CoordinatorCollectionLedger.sourceRound input.round)
                  input.enabled input.raw hs
              have htimeStart :=
                CollectionCheckedExecution.startRound_success_time l started
                  (CoordinatorCollectionLedger.sourceRound input.round)
                  input.enabled input.raw hs
              refine ⟨?_, ?_, hfinish.2.1⟩
              · calc
                  finished.enabledHistory = decoded.enabledHistory := hfinish.2.2
                  _ = started.enabledHistory := hdecodeHistory
                  _ = Function.update l.enabledHistory input.round
                      (some input.enabled) := hstartHistory
              · calc
                  finished.cursor = decoded.cursor + 1 := hfinish.1
                  _ = started.cursor + 1 := by rw [hdecodeCursor]
                  _ = l.cursor + 1 := by rw [hcursorStart, htimeStart]

private theorem start_collection_history_empty
    (assignment : CoordinatorCollectionLedger.Assignment p)
    (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CoordinatorCollectionLedger.CutoffRegister)
    (initial : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale assignment sigma cutoff freezeAt baseScore outside =
      .success initial) :
    initial.enabledHistory = (fun _ => none) ∧ initial.phase = .ready ∧
      initial.cursor = cutoff := by
  have hready := CollectionCheckedExecution.startCollectionChecked_success_ready
    p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
    rate.n rate.n_scale assignment sigma cutoff freezeAt baseScore outside initial h
  have hfields := CollectionBufferProvenance.startCollectionChecked_success_context
    assignment sigma cutoff freezeAt baseScore outside initial h
  unfold CoordinatorCollectionLedger.startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; exact ⟨rfl, hready, hfields.2.2.1⟩)

private theorem collection_choice_none_dagger (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    {ledger : ReferenceActivePhysicalStep.Ledger rate}
    {proposal : Option (Fin p.T × Bool)}
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = none) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger := by
  classical
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection input) := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        CoordinatorRoundDispatch.dispatch, hstate, hcutoff, cutoff, clock, input]
      rfl
    cases hdispatch : CoordinatorRoundDispatch.dispatchCollection input <;>
      simp_all [ReferenceCollectionSegmentExtraction.choice,
        ReferenceCollectionSegmentExtraction.choiceOfCut,
        ReferenceCollectionPhaseHistory.laterChosen,
        ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure]
  · have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hcutoff]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      hprepared, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.coordinatorFailure]

private theorem choice_collection_data_pre (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    c.payload = payload ∧ c.preLedger = ledger ∧
      c.preLedger.phase = .ready ∧ c.preLedger.cursor = x.time.val + 1 := by
  have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
    x payload ledger proposal c hstate hchoice
  have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hnone : ReferenceCollectionSegmentExtraction.choice x = none := by
      simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hbad, ReferenceActivePhysicalStep.DispatchCut.selection]
    rw [hnone] at hchoice
    contradiction
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection input) := by
    simp [ReferenceActivePhysicalStep.dispatch, CoordinatorRoundDispatch.dispatch,
      hstate, hvalid, cutoff, clock, input]
    rfl
  cases hround : CoordinatorRoundDispatch.dispatchCollection input with
  | continuing core snapshot boundary scores =>
      have heq :
          ({ payload := payload, preLedger := ledger,
              started := snapshot.clockStarted,
              weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
                input snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
              initializer := none } : ReferenceCollectionSegmentExtraction.Choice rate) = c := by
        simpa [ReferenceCollectionSegmentExtraction.choice,
          ReferenceActivePhysicalStep.prepare, hdispatch, hround,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceCollectionSegmentExtraction.choiceOfCut,
          cutoff, clock, input] using hchoice
      have hphase : c.preLedger.phase = .ready := by
        rw [hpre.1]
        exact core.ledger_ready
      have hcursor : c.preLedger.cursor = x.time.val + 1 := by
        rw [hpre.1]
        simpa [ReferenceActivePhysicalStep.collectionInput, input,
          CoordinatorCollectionUpRoundStep.sourceRound] using core.ledger_cursor_eq
      exact ⟨(congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm,
        hpre.1, hphase, hcursor⟩
  | _ =>
      simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceActivePhysicalStep.prepare, hdispatch, hround,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceCollectionSegmentExtraction.choiceOfCut,
        cutoff, clock, input] at hchoice

private theorem collection_enabled_of_context
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (time : Fin p.T)
    (assignment : CoordinatorCollectionLedger.Assignment p)
    (sigma cutoff freezeAt : ℕ) (base : Fin (p.m - 1) → ℕ)
    (hcontext : CollectionBufferProvenance.collectionContext ledger =
      (assignment, sigma, cutoff, freezeAt, base))
    (hpositive : 0 < sigma) (hcutoff : cutoff ≤ time.val + 1) :
    ReferenceActivePhysicalStep.collectionEnabled ledger time =
      decide (time.val + 1 < freezeAt) := by
  have hsigma : ledger.sigma = sigma := congrArg (fun z => z.2.1) hcontext
  have hcut : ledger.cutoff = cutoff := congrArg (fun z => z.2.2.1) hcontext
  have hfreeze : ledger.freezeAt = freezeAt := congrArg (fun z => z.2.2.2.1) hcontext
  simp [ReferenceActivePhysicalStep.collectionEnabled, hsigma, hcut, hfreeze,
    hpositive, hcutoff]

private theorem collection_enabled_at_value
    {time : Fin p.T} (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (assignment : CoordinatorCollectionLedger.Assignment p)
    (sigma cutoff freezeAt : ℕ) (base : Fin (p.m - 1) → ℕ)
    (hcontext : CollectionBufferProvenance.collectionContext ledger =
      (assignment, sigma, cutoff, freezeAt, base))
    (hpositive : 0 < sigma) (timeValue v : ℕ)
    (htime : time.val = timeValue) (hstep : timeValue + 1 = v)
    (hcutoff : cutoff ≤ v) :
    ReferenceActivePhysicalStep.collectionEnabled ledger time = decide (v < freezeAt) := by
  have hcutoffTime : cutoff ≤ time.val + 1 := by rw [htime, hstep]; exact hcutoff
  have henabled := collection_enabled_of_context ledger time assignment sigma cutoff
    freezeAt base hcontext hpositive hcutoffTime
  rw [henabled, htime, hstep]

private theorem first_history_update
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (u freezeAt : ℕ)
    (hblank : ledger.enabledHistory = fun _ => none)
    (htime : time.val + 1 = u)
    (henabled : ReferenceActivePhysicalStep.collectionEnabled ledger time =
      decide (u < freezeAt)) :
    Function.update ledger.enabledHistory time
        (some (ReferenceActivePhysicalStep.collectionEnabled ledger time)) =
      fun r => if u ≤ r.val + 1 ∧ r.val + 1 < u + 1 then
        some (decide (r.val + 1 < freezeAt)) else none := by
  funext r
  by_cases hr : r = time
  · subst r
    simp [Function.update_self, htime, henabled]
  · have htimeNe : r.val + 1 ≠ u := by
      intro heq
      apply hr
      apply Fin.ext
      omega
    simp [Function.update_of_ne hr, hblank]
    omega

private theorem candidate_history_succ
    {time : Fin p.T} (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (u v freezeAt timeValue : ℕ)
    (henabled : ReferenceActivePhysicalStep.collectionEnabled ledger time =
      decide (v < freezeAt))
    (htime : time.val = timeValue) (hstep : timeValue + 1 = v)
    (hle : u ≤ v)
    (hhistory : ∀ r, ledger.enabledHistory r =
      if u ≤ r.val + 1 ∧ r.val + 1 < v then
        some (decide (r.val + 1 < freezeAt)) else none) :
    ∀ raw r,
      (CoordinatorCollectionLedger.startRoundCandidate ledger time
        (ReferenceActivePhysicalStep.collectionEnabled ledger time) raw).enabledHistory r =
        if u ≤ r.val + 1 ∧ r.val + 1 < v + 1 then
          some (decide (r.val + 1 < freezeAt)) else none := by
  have htimeStep : time.val + 1 = v := by rw [htime, hstep]
  intro raw r
  by_cases hr : r = time
  · subst r
    simp [CoordinatorCollectionLedger.startRoundCandidate,
      Function.update_self, htimeStep, henabled]
    omega
  · have htimeNe : r.val + 1 ≠ v := by
      intro heq
      apply hr
      apply Fin.ext
      omega
    have hbound : r.val + 1 < v + 1 ↔ r.val + 1 < v := by omega
    simp [CoordinatorCollectionLedger.startRoundCandidate,
      Function.update_of_ne hr, hhistory r, hbound]

private theorem selected_enabled_candidate
    {window : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (n : Fin window.length)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (u v freezeAt timeValue : ℕ)
    (assignment : CoordinatorCollectionLedger.Assignment p)
    (sigma cutoff : ℕ) (base : Fin (p.m - 1) → ℕ)
    (hcontext : CollectionBufferProvenance.collectionContext ledger =
      (assignment, sigma, cutoff, freezeAt, base))
    (hpositive : 0 < sigma)
    (htime : window[n].input.time.val = timeValue)
    (hstep : timeValue + 1 = v) (hcutoff : cutoff ≤ v) (hle : u ≤ v)
    (hhistory : ∀ r, ledger.enabledHistory r =
      if u ≤ r.val + 1 ∧ r.val + 1 < v then
        some (decide (r.val + 1 < freezeAt)) else none) :
    ReferenceActivePhysicalStep.collectionEnabled ledger window[n].input.time =
        decide (v < freezeAt)
      ∧ ∀ raw r,
        (CoordinatorCollectionLedger.startRoundCandidate ledger window[n].input.time
          (ReferenceActivePhysicalStep.collectionEnabled ledger window[n].input.time) raw).enabledHistory r =
          if u ≤ r.val + 1 ∧ r.val + 1 < v + 1 then
            some (decide (r.val + 1 < freezeAt)) else none := by
  have henabled := collection_enabled_at_value (time := window[n].input.time) ledger
    assignment sigma cutoff freezeAt base hcontext hpositive timeValue v htime hstep hcutoff
  refine ⟨henabled, ?_⟩
  exact candidate_history_succ (time := window[n].input.time) ledger u v freezeAt
    timeValue henabled htime hstep hle hhistory

private theorem roundRecord_input_time_congr
    {record other : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)} (heq : record = other) :
    record.input.time = other.input.time :=
  congrArg (fun r => r.input.time) heq

private theorem collectionEnabled_congr
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    {left right : Fin p.T} (heq : left = right) :
    ReferenceActivePhysicalStep.collectionEnabled ledger left =
      ReferenceActivePhysicalStep.collectionEnabled ledger right :=
  congrArg (ReferenceActivePhysicalStep.collectionEnabled ledger) heq

private theorem startRoundCandidate_history_congr
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    {left right : Fin p.T} (heq : left = right)
    (raw : Option (Fin p.K × ℕ)) (r : Fin p.T) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger left
      (ReferenceActivePhysicalStep.collectionEnabled ledger left) raw).enabledHistory r =
    (CoordinatorCollectionLedger.startRoundCandidate ledger right
      (ReferenceActivePhysicalStep.collectionEnabled ledger right) raw).enabledHistory r :=
  congrArg (fun time => (CoordinatorCollectionLedger.startRoundCandidate ledger time
    (ReferenceActivePhysicalStep.collectionEnabled ledger time) raw).enabledHistory r) heq

private theorem collectionEnabled_of_roundRecord_eq
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    {record other : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (heq : record = other) {value : Bool}
    (henabled : ReferenceActivePhysicalStep.collectionEnabled ledger other.input.time = value) :
    ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time = value := by
  exact (collectionEnabled_congr ledger
    (roundRecord_input_time_congr heq)).trans henabled

private theorem candidate_history_of_roundRecord_eq
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    {record other : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (heq : record = other) {value : Option Bool}
    (raw : Option (Fin p.K × ℕ)) (r : Fin p.T)
    (h : (CoordinatorCollectionLedger.startRoundCandidate ledger other.input.time
      (ReferenceActivePhysicalStep.collectionEnabled ledger other.input.time) raw).enabledHistory r = value) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger record.input.time
      (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time) raw).enabledHistory r = value := by
  exact (startRoundCandidate_history_congr ledger
    (roundRecord_input_time_congr heq) raw r).trans h

private theorem candidate_history_transfer_window
    {window : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (n : Fin window.length) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    {other : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (heq : window[n] = other) (target : Fin p.T → Option Bool)
    (h : ∀ raw r,
      (CoordinatorCollectionLedger.startRoundCandidate ledger other.input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger other.input.time) raw).enabledHistory r =
        target r) :
    ∀ raw r,
      (CoordinatorCollectionLedger.startRoundCandidate ledger window[n].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger window[n].input.time) raw).enabledHistory r =
        target r := by
  intro raw r
  exact candidate_history_of_roundRecord_eq ledger heq raw r (h raw r)

private theorem actual_selected_step_history
    (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some c)
    (hcontext : CollectionBufferProvenance.collectionContext c.preLedger =
      (initializer.assignment, initializer.sigma, initializer.cutoff,
        initializer.freezeAt, initializer.base))
    {ledger : ReferenceActivePhysicalStep.Ledger rate}
    {proposal : Option (Fin p.T × Bool)}
    (hnext : (ReferenceActivePhysicalStep.step record.input).next.coordinator =
      .collection c.payload ledger proposal) :
    ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.final = ledger ∧
      ledger.enabledHistory = Function.update c.preLedger.enabledHistory
        record.input.time (some (ReferenceActivePhysicalStep.collectionEnabled
          c.preLedger record.input.time)) ∧
      ledger.cursor = c.preLedger.cursor + 1 ∧ ledger.phase = .ready ∧
      CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
  have hactual := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
    rate record.input c initializer hchoice hcontext
  rcases hactual with hdagger | ⟨outLedger, outProposal, completed, hsurvive,
    hframe, hextract, hcompletedContext, htime⟩
  · rw [hnext] at hdagger
    cases hdagger
  · have hcanonical :
        (⟨record.input, ReferenceActivePhysicalStep.step record.input, rfl⟩ :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) = record := by
      cases record with
      | mk input output output_eq =>
          cases output_eq
          rfl
    have hextractRecord : ReferenceCollectionSegmentExtraction.extractRound record =
        some completed := by
      simpa only [hcanonical] using hextract
    have hchecked := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
      record completed hextractRecord
    rcases hchecked with ⟨hchoiceCompleted, hround, hfold, hphysical⟩
    have hcompletedChoice : completed.context = c :=
      Option.some.inj (hchoiceCompleted.symm.trans hchoice)
    have hphysicalStep : ∃ payload physicalProposal,
        (ReferenceActivePhysicalStep.step record.input).next.coordinator =
          .collection payload completed.final physicalProposal := by
      simpa only [record.output_eq] using hphysical
    have houtputLedger : outLedger = ledger := by
      have hcfg := hsurvive.symm.trans hnext
      injection hcfg with hpayload hledger hproposal
    have hout : completed.final = ledger := by
      rcases hphysicalStep with ⟨payload, physicalProposal, hphysicalStep⟩
      have hphysical' := hphysicalStep
      rw [hsurvive] at hphysical'
      have hfinal : outLedger = completed.final := by
        injection hphysical' with hpayload hfinal hproposal
      exact hfinal.symm.trans houtputLedger
    have hinputs := ReferenceCollectionSegmentExtraction.actual_collection_round_inputs
      record completed hextractRecord
    rcases hinputs with ⟨recording, started, decoded, bank, hrecording, hrun,
      hstart, hinput, hreceive, hreceiveCheck⟩
    have henabled : completed.input.enabled =
        ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time := by
      rw [hinput, hcompletedChoice]
      rfl
    have hfold' := hfold
    rw [hcompletedChoice] at hfold'
    have hone := checked_single_round_history c.preLedger completed.final
      completed.input completed.accepted hfold'
    have hroundEq : completed.input.round = record.input.time := hround
    have hupdate : completed.final.enabledHistory =
        Function.update c.preLedger.enabledHistory record.input.time
          (some (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)) := by
      rw [hone.1, hroundEq, henabled]
    have hframeFinal : CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
      rw [← houtputLedger]
      exact hframe
    have hupdateLedger : ledger.enabledHistory =
        Function.update c.preLedger.enabledHistory record.input.time
          (some (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)) := by
      rw [← hout]
      exact hupdate
    have hcursorLedger : ledger.cursor = c.preLedger.cursor + 1 := by
      rw [← hout]
      exact hone.2.1
    have hphaseLedger : ledger.phase = .ready := by
      rw [← hout]
      exact hone.2.2
    exact ⟨completed, hextractRecord, hout, hupdateLedger, hcursorLedger,
      hphaseLedger, hframeFinal⟩

private theorem choice_none_of_dagger (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdagger : x.state.coordinator = .dagger) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  simp [ReferenceCollectionSegmentExtraction.choice,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch_dagger x hdagger,
    ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem connected_append_split {rate : RateInput p}
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil => exact ⟨initial, rfl, hchain⟩
  | cons record rest ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hchain
      obtain ⟨middle, hleft, hright⟩ := ih hchain.2
      exact ⟨middle, ⟨hchain.1, hleft⟩, hright⟩

private theorem roundInput_getElem_eq_tail
    {rate : RateInput p}
    {whole tail : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))}
    {head : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hwhole : whole = head :: tail) (n : Fin whole.length) (hn : n.val ≠ 0) :
    ∃ j : Fin tail.length, j.val + 1 = n.val ∧
      whole[n].input = tail[j.val].input := by
  have hnlt : n.val < tail.length + 1 := by simpa [hwhole] using n.isLt
  let j : Fin tail.length := ⟨n.val - 1, by omega⟩
  have hj : j.val + 1 = n.val := by simp only [j]; omega
  have hlookup : whole[n.val]? = some tail[j.val] := by
    calc
      whole[n.val]? = (head :: tail)[n.val]? :=
        congrArg (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate)) => xs[n.val]?) hwhole
      _ = (head :: tail)[j.val + 1]? := congrArg _ hj.symm
      _ = some tail[j.val] := by simp
  have hget : whole[n.val]? = some whole[n] := by simp [n.isLt]
  have hrecord : whole[n] = tail[j.val] := Option.some.inj (hget.symm.trans hlookup)
  exact ⟨j, hj, congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate) => record.input) hrecord⟩

/-- The original connected prefix transports the checked history cell by cell.
Every processed record is a real selected step: a missing choice or a failed
step would make the later selected target dagger by absorption. -/
private theorem connected_prefix_enabled_history
    (rate : RateInput p)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (u : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) :
    ∀ (initial final : ReferenceActivePhysicalStep.State p rate)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (proposal : Option (Fin p.T × Bool)) (k : ℕ)
      (target : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (after : List (ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)))
      (targetChoice : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceActivePhysicalHorizon.Connected initial
        (records ++ target :: after) final →
      initial.coordinator = .collection payload ledger proposal →
      CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) →
      initializer.cutoff = u → 0 < initializer.sigma →
      ledger.cursor = u + k →
      ledger.phase = .ready →
      (∀ r, ledger.enabledHistory r =
        if u ≤ r.val + 1 ∧ r.val + 1 < u + k then
          some (decide (r.val + 1 < initializer.freezeAt)) else none) →
      (∀ record ∈ records,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false) →
      ReferenceCollectionSegmentExtraction.choice target.input = some targetChoice →
      ∃ targetPayload targetLedger targetProposal,
        target.input.state.coordinator =
          .collection targetPayload targetLedger targetProposal ∧
        targetChoice.preLedger = targetLedger ∧
        targetLedger.cursor = u + (k + records.length) ∧
        targetLedger.phase = .ready ∧
        (∀ r, targetLedger.enabledHistory r =
          if u ≤ r.val + 1 ∧ r.val + 1 < u + (k + records.length) then
            some (decide (r.val + 1 < initializer.freezeAt)) else none) := by
  induction records with
  | nil =>
      intro initial final payload ledger proposal k target after targetChoice
        hchain hstate hcontext hu hpositive hcursor hready hhistory hnoLater htarget
      simp only [List.nil_append, ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨htargetStateEq, _⟩
      have htargetState : target.input.state.coordinator =
          .collection payload ledger proposal := by
        rw [htargetStateEq, hstate]
      have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
        target.input payload ledger proposal targetChoice htargetState htarget
      refine ⟨payload, ledger, proposal, htargetState, hpre.1, ?_, hready, ?_⟩
      · simpa using hcursor
      · intro r
        simpa using hhistory r
  | cons record rest ih =>
      intro initial final payload ledger proposal k target after targetChoice
        hchain hstate hcontext hu hpositive hcursor hready hhistory hnoLater htarget
      have hrecordState : record.input.state.coordinator =
          .collection payload ledger proposal := by
        rw [hchain.1, hstate]
      have hnotLater := hnoLater record (by simp)
      cases hchoice : ReferenceCollectionSegmentExtraction.choice record.input with
      | none =>
          have hdagger := collection_choice_none_dagger rate record.input payload
            (ledger := ledger) (proposal := proposal) hrecordState hnotLater hchoice
          have hdaggerOutput : record.output.next.coordinator = .dagger := by
            calc
              record.output.next.coordinator =
                  (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
                rw [record.output_eq]
              _ = .dagger := hdagger
          have htailDagger :=
            ReferenceActivePhysicalHorizon.Connected.coordinator_dagger
              hchain.2 hdaggerOutput
          have htargetDagger : target.input.state.coordinator = .dagger :=
            htailDagger.2 target (by simp)
          have hnone := choice_none_of_dagger rate target.input htargetDagger
          rw [hnone] at htarget
          contradiction
      | some headChoice =>
          have hhead := choice_collection_data_pre rate record.input payload ledger
            proposal headChoice hrecordState hchoice
          have hheadContext : CollectionBufferProvenance.collectionContext
              headChoice.preLedger =
                (initializer.assignment, initializer.sigma, initializer.cutoff,
                  initializer.freezeAt, initializer.base) := by
            rw [hhead.2.1]
            exact hcontext
          have hheadCursor : record.input.time.val + 1 = u + k := by
            calc
              record.input.time.val + 1 = headChoice.preLedger.cursor := hhead.2.2.2.symm
              _ = ledger.cursor := by rw [hhead.2.1]
              _ = u + k := hcursor
          have hactual := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
            rate record.input headChoice initializer hchoice hheadContext
          rcases hactual with hfailed | ⟨nextLedger, nextProposal, completed,
            hnext, hnextContext, hextract, hcompletedContext, hround⟩
          · have hfailedOutput : record.output.next.coordinator = .dagger := by
              rw [record.output_eq]
              exact hfailed
            have htailDagger :=
              ReferenceActivePhysicalHorizon.Connected.coordinator_dagger
                hchain.2 hfailedOutput
            have htargetDagger : target.input.state.coordinator = .dagger :=
              htailDagger.2 target (by simp)
            have hnone := choice_none_of_dagger rate target.input htargetDagger
            rw [hnone] at htarget
            contradiction
          · have hnext' :
                (ReferenceActivePhysicalStep.step record.input).next.coordinator =
                  .collection headChoice.payload nextLedger nextProposal := hnext
            obtain ⟨completed', hextract', hcompletedFinal, hhistoryUpdate,
              hcursorNext, hphaseNext, hcontextNext⟩ :=
              actual_selected_step_history rate record headChoice initializer
                hchoice hheadContext hnext'
            have henabled :
                ReferenceActivePhysicalStep.collectionEnabled
                    headChoice.preLedger record.input.time =
                  decide (u + k < initializer.freezeAt) := by
              have hcut : initializer.cutoff ≤ record.input.time.val + 1 := by
                rw [hu, hheadCursor]
                omega
              have hcurrent := collection_enabled_of_context headChoice.preLedger record.input.time
                initializer.assignment initializer.sigma initializer.cutoff
                initializer.freezeAt initializer.base hheadContext hpositive hcut
              rw [hcurrent, hheadCursor]
            have hhistoryNext : ∀ r, nextLedger.enabledHistory r =
                if u ≤ r.val + 1 ∧ r.val + 1 < u + (k + 1) then
                  some (decide (r.val + 1 < initializer.freezeAt)) else none := by
              intro r
              rw [hhistoryUpdate]
              by_cases hr : r = record.input.time
              · subst r
                rw [Function.update_self, hheadCursor, henabled]
                simp
              · rw [Function.update_of_ne hr]
                have hrne : r.val + 1 ≠ u + k := by
                  intro heq
                  apply hr
                  apply Fin.ext
                  omega
                rw [hhead.2.1, hhistory r]
                by_cases hlo : u ≤ r.val + 1 <;>
                  by_cases hhi : r.val + 1 < u + k <;>
                  simp [hlo, hhi] <;> omega
            have hnextCursor : nextLedger.cursor = u + (k + 1) := by
              calc
                nextLedger.cursor = headChoice.preLedger.cursor + 1 := hcursorNext
                _ = ledger.cursor + 1 := by rw [hhead.2.1]
                _ = u + (k + 1) := by rw [hcursor]; omega
            have hnextState : record.output.next.coordinator =
                .collection headChoice.payload nextLedger nextProposal := by
              rw [record.output_eq]
              exact hnext
            have hnoLaterRest : ∀ rec ∈ rest,
                ReferenceCollectionPhaseHistory.laterChosen rec.input = false := by
              intro rec hmem
              exact hnoLater rec (List.mem_cons_of_mem _ hmem)
            obtain ⟨targetPayload, targetLedger, targetProposal, htargetState,
              htargetPre, htargetCursor, htargetPhase, htargetHistory⟩ :=
              ih record.output.next final headChoice.payload nextLedger nextProposal
                (k + 1) target after targetChoice hchain.2 hnextState hcontextNext
                hu hpositive hnextCursor hphaseNext hhistoryNext hnoLaterRest htarget
            refine ⟨targetPayload, targetLedger, targetProposal, htargetState,
              htargetPre, ?_, htargetPhase, ?_⟩
            · have hlen : u + (k + 1 + rest.length) =
                  u + (k + (record :: rest).length) := by
                simp [Nat.add_assoc]
                omega
              rw [← hlen]
              exact htargetCursor
            · have hlen : u + (k + 1 + rest.length) =
                  u + (k + (record :: rest).length) := by
                simp [Nat.add_assoc]
                omega
              rw [← hlen]
              exact htargetHistory

/-- The selected current input has exactly the Boolean history produced by
the checked cutoff initializer and the original connected physical prefix.
Every calendar cell is quantified: cells after freeze and before the cursor
are present with value false, while unprocessed cells remain absent.
The final equation is for the literal current start candidate; the selected
round may still fail after choice. No current checked-start success, raw-buffer
cell identity, or complete replay domain is asserted. -/
theorem actual_first_collection_enabled_history_prefix
    (rate : RateInput p)
    (source : SourceInput p)
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
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
      (∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
          (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
          (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
        execution.records = firstWindow ++ cut :: suffix ∧
        cut.input.time.val = start + w ∧
        c0.payload = r.payload ∧
        initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
        ReferenceCollectionSegmentExtraction.segmentAt execution.records w = some seg ∧
        seg.entry = cut ∧ seg.context = c0 ∧
        ReferenceCollectionSegmentExtraction.choice cut.input = some c0 ∧
        c0.initializer = some initializer ∧
        initializer.checkedStart rate = .success c0.preLedger ∧
        initializer.sigma = start + 1 ∧
        initializer.cutoff = start + w + 1 ∧
        initializer.freezeAt = r.gridBoundary ∧
        initializer.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma ∧
        initializer.base = (fun _ => 0) ∧
        initializer.assignment.arm = r.payload.assignment.assigned ∧
        initializer.assignment.arm = c0.payload.assignment.assigned ∧
        0 < w ∧ c.payload = c0.payload ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        W[n].input.time.val = start + w + n.val) ∧
        (∀ r : Fin p.T,
            c.preLedger.enabledHistory r =
              if start + w + 1 ≤ r.val + 1 ∧
                  r.val + 1 < start + w + 1 + n.val then
                some (decide (r.val + 1 < c.preLedger.freezeAt)) else none)
        ∧ c.preLedger.phase = .ready
        ∧ c.preLedger.cursor = start + w + 1 + n.val
        ∧ ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time =
            decide (start + w + 1 + n.val < c.preLedger.freezeAt)
        ∧ ∀ raw : Option (Fin p.K × ℕ), ∀ r : Fin p.T,
            (CoordinatorCollectionLedger.startRoundCandidate c.preLedger
              W[n].input.time
              (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
              raw).enabledHistory r =
              if start + w + 1 ≤ r.val + 1 ∧
                  r.val + 1 < start + w + 1 + n.val + 1 then
                some (decide (r.val + 1 < c.preLedger.freezeAt)) else none := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
      (∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
          (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
          (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
        execution.records = firstWindow ++ cut :: suffix ∧
        cut.input.time.val = start + w ∧
        c0.payload = r.payload ∧
        initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
          (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
        ReferenceCollectionSegmentExtraction.segmentAt execution.records w = some seg ∧
        seg.entry = cut ∧ seg.context = c0 ∧
        ReferenceCollectionSegmentExtraction.choice cut.input = some c0 ∧
        c0.initializer = some initializer ∧
        initializer.checkedStart rate = .success c0.preLedger ∧
        initializer.sigma = start + 1 ∧
        initializer.cutoff = start + w + 1 ∧
        initializer.freezeAt = r.gridBoundary ∧
        initializer.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma ∧
        initializer.base = (fun _ => 0) ∧
        initializer.assignment.arm = r.payload.assignment.assigned ∧
        initializer.assignment.arm = c0.payload.assignment.assigned ∧
        0 < w ∧ c.payload = c0.payload ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        W[n].input.time.val = start + w + n.val) ∧
        (∀ r : Fin p.T,
          c.preLedger.enabledHistory r =
            if start + w + 1 ≤ r.val + 1 ∧
                r.val + 1 < start + w + 1 + n.val then
              some (decide (r.val + 1 < c.preLedger.freezeAt)) else none) ∧
        c.preLedger.phase = .ready ∧
        c.preLedger.cursor = start + w + 1 + n.val ∧
        ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time =
          decide (start + w + 1 + n.val < c.preLedger.freezeAt) ∧
        ∀ raw : Option (Fin p.K × ℕ), ∀ r : Fin p.T,
          (CoordinatorCollectionLedger.startRoundCandidate c.preLedger
            W[n].input.time
            (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
            raw).enabledHistory r =
            if start + w + 1 ≤ r.val + 1 ∧
                r.val + 1 < start + w + 1 + n.val + 1 then
              some (decide (r.val + 1 < c.preLedger.freezeAt)) else none
  intro n c hchoice
  let u := start + w + 1
  let v := start + w + 1 + n.val
  have huDef : u = start + w + 1 := rfl
  have hvDef : v = u + n.val := rfl
  have hC := ReferenceFirstCollectionChosenContext.actual_first_collection_chosen_context
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have hCResult := hC
  rcases hC with ⟨cut, suffix, r, q, base, c0, initializer, seg,
    hsplit, hcutTime, hcutPayload, hinitializer, hsegmentAt, hentry,
    hsegmentContext, hcutChoice, hc0Initializer, hchecked, hsigma,
    hcutoff, hfreeze, hfreezeGrid, hbase, hassignment, hassignmentC0,
    hwpos, hpayload, hcontext, htimeCurrent⟩
  let during := suffix.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hdrop0 : execution.records.drop w = cut :: suffix := by
    calc
      execution.records.drop w = (firstWindow ++ cut :: suffix).drop w :=
        congrArg (fun records => records.drop w) hsplit
      _ = cut :: suffix := by
        rw [List.drop_append_of_le_length (by simp [w])]
        simp [w]
  have hdrop1 : execution.records.drop (w + 1) = suffix := by
    calc
      execution.records.drop (w + 1) =
          (firstWindow ++ cut :: suffix).drop (w + 1) :=
        congrArg (fun records => records.drop (w + 1)) hsplit
      _ = suffix := by
        rw [← List.drop_drop]
        have hdrop0First : (firstWindow ++ cut :: suffix).drop w = cut :: suffix := by
          have htmp := hdrop0
          rw [hsplit] at htmp
          exact htmp
        rw [hdrop0First]
        simp
  have hwindow : W = cut :: during := by
    change ReferenceCollectionPhaseHistory.collectionWindow execution.records w =
      cut :: during
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [hdrop0, hdrop1]
    simp [during]
  have hfreeze : c.preLedger.freezeAt = initializer.freezeAt :=
    congrArg (fun z => z.2.2.2.1) hcontext
  by_cases hn : n.val = 0
  · have hcurrentCut : W[n] = cut := by
      have hlookup : (cut :: during)[n.val]? = some cut := by simp [hn]
      have hget : (cut :: during)[n.val]? = some W[n] := by
        rw [← hwindow]
        simp [n.isLt]
      exact Option.some.inj (hget.symm.trans hlookup)
    have hc0 : c = c0 := by
      apply Option.some.inj
      calc
        some c = ReferenceCollectionSegmentExtraction.choice W[n].input := hchoice.symm
        _ = ReferenceCollectionSegmentExtraction.choice cut.input := by rw [hcurrentCut]
        _ = some c0 := hcutChoice
    have hinitialStart :
        CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val
          rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
          rate.n rate.n_scale initializer.assignment initializer.sigma
          initializer.cutoff initializer.freezeAt initializer.base initializer.outside =
          .success c0.preLedger := by
      simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked
    have hinitial := start_collection_history_empty initializer.assignment
      initializer.sigma initializer.cutoff initializer.freezeAt initializer.base
      initializer.outside c0.preLedger hinitialStart
    have hhistoryI : ∀ index : Fin p.T,
        c0.preLedger.enabledHistory index =
          if u ≤ index.val + 1 ∧ index.val + 1 < u then
            some (decide (index.val + 1 < initializer.freezeAt)) else none := by
      intro index
      rw [hinitial.1]
      by_cases hinside : u ≤ index.val + 1 ∧ index.val + 1 < u
      · omega
      · simp [hinside]
    have hhistory : ∀ index : Fin p.T,
        c.preLedger.enabledHistory index =
          if u ≤ index.val + 1 ∧ index.val + 1 < v then
            some (decide (index.val + 1 < c.preLedger.freezeAt)) else none := by
      intro index
      have hfreeze0 : c0.preLedger.freezeAt = initializer.freezeAt := by
        simpa [hc0] using hfreeze
      have hv0 : v = u := by simpa [hn] using hvDef
      rw [hc0, hfreeze0, hv0]
      exact hhistoryI index
    have hphase : c.preLedger.phase = .ready := by
      rw [hc0]
      exact hinitial.2.1
    have hcursor : c.preLedger.cursor = v := by
      calc
        c.preLedger.cursor = c0.preLedger.cursor := by rw [hc0]
        _ = initializer.cutoff := hinitial.2.2
        _ = u := by rw [huDef]; exact hcutoff
        _ = v := by simpa [hn] using hvDef.symm
    have hsource : W[n].input.time.val + 1 = v := by
      calc
        W[n].input.time.val + 1 = cut.input.time.val + 1 := by rw [hcurrentCut]
        _ = start + w + 1 := by simpa using congrArg Nat.succ hcutTime
        _ = u := by rw [huDef]
        _ = v := by simpa [hn] using hvDef.symm
    have hpositive : 0 < initializer.sigma := by omega
    have hcutLe : initializer.cutoff ≤ W[n].input.time.val + 1 := by
      have hcutEq : initializer.cutoff = v := by
        calc
          initializer.cutoff = start + w + 1 := hcutoff
          _ = u := by rw [huDef]
          _ = v := by simpa [hn] using hvDef.symm
      rw [hsource]
      exact hcutEq.le
    have henabledI := collection_enabled_of_context c.preLedger W[n].input.time
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base hcontext hpositive hcutLe
    have henabled : ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time =
        decide (v < c.preLedger.freezeAt) := by
      rw [henabledI, hsource, hfreeze]
    refine ⟨hCResult, hhistory, hphase, ?_, henabled, ?_⟩
    · simpa [u, v] using hcursor
    · exact candidate_history_succ c.preLedger u v c.preLedger.freezeAt
        W[n].input.time.val henabled rfl hsource (by omega) hhistory
  · let launch := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    have hindexCons : n.val < (cut :: during).length := by
      simpa [hwindow] using n.isLt
    let nCons : Fin (cut :: during).length := ⟨n.val, hindexCons⟩
    have hgetWindow : W[n.val]? = some W[n] := by simp [n.isLt]
    have hgetWindowCons : W[n.val]? = (cut :: during)[n.val]? :=
      congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate)) => records[n.val]?) hwindow
    have hgetCons : (cut :: during)[n.val]? = some ((cut :: during)[nCons]) := by
      simp [nCons]
    have hcurrentRecord : W[n] = (cut :: during)[nCons] :=
      Option.some.inj (hgetWindow.symm.trans (hgetWindowCons.trans hgetCons))
    have htimeWindow : (cut :: during)[nCons].input.time.val = start + w + n.val := by
      exact (congrArg (fun record => record.input.time.val) hcurrentRecord).symm.trans htimeCurrent
    have hfull : ReferenceActivePhysicalHorizon.Connected launch
        execution.records execution.finalState := by
      have hmode :=
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
      change ReferenceActivePhysicalHorizon.Connected launch
        (ReferenceActivePhysicalHorizon.run launch source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan hmode).records
        (ReferenceActivePhysicalHorizon.run launch source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan hmode).finalState
      exact ReferenceActivePhysicalHorizon.run_connected launch source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode
    have hsplitChain : ReferenceActivePhysicalHorizon.Connected launch
        (firstWindow ++ cut :: suffix) execution.finalState := by
      rw [← hsplit]
      exact hfull
    obtain ⟨windowFinal, hwindowChain, hcutChain⟩ :=
      connected_append_split firstWindow (cut :: suffix) hsplitChain
    rcases hcutChain with ⟨hcutInput, hcutOutput⟩
    let remainder := suffix.dropWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hsuffixSplit : suffix = during ++ remainder := by
      dsimp [during, remainder]
      exact List.takeWhile_append_dropWhile.symm
    have hcutOutput' : ReferenceActivePhysicalHorizon.Connected cut.output.next
        (during ++ remainder) execution.finalState := by
      rw [← hsuffixSplit]
      exact hcutOutput
    obtain ⟨afterDuring, hDuringChain, hafterDuring⟩ :=
      connected_append_split during remainder hcutOutput'
    have hnoLater : ∀ record ∈ during,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      intro record hmem
      have hall : (!ReferenceCollectionPhaseHistory.laterChosen record.input) = true :=
        (List.all_eq_true.mp List.all_takeWhile) record hmem
      cases hlater : ReferenceCollectionPhaseHistory.laterChosen record.input <;>
        simp [hlater] at hall ⊢
    obtain ⟨j, hjindex, hinputEq⟩ := roundInput_getElem_eq_tail hwindow n hn
    have hcurrentChoice :
        ReferenceCollectionSegmentExtraction.choice (during[j.val]'j.isLt).input = some c := by
      have hchoiceEq := congrArg
        (fun input => ReferenceCollectionSegmentExtraction.choice input) hinputEq
      exact hchoiceEq.symm.trans hchoice
    let prior := during.take j.val
    let target := during[j.val]'j.isLt
    let afterTarget := during.drop (j.val + 1)
    have hsplitDuring : during = prior ++ target :: afterTarget := by
      calc
        during = during.take j.val ++ during.drop j.val :=
          (List.take_append_drop j.val during).symm
        _ = prior ++ target :: afterTarget := by
          rw [List.cons_getElem_drop_succ (l := during) (n := j.val) (h := j.isLt)]
    have htargetDef : target = during[j.val]'j.isLt := rfl
    clear_value target
    have hpriorTargetChain : ReferenceActivePhysicalHorizon.Connected
        cut.output.next (prior ++ target :: (afterTarget ++ remainder)) execution.finalState := by
      have hseq : prior ++ target :: (afterTarget ++ remainder) = during ++ remainder := by
        calc
          prior ++ target :: (afterTarget ++ remainder) =
              (prior ++ target :: afterTarget) ++ remainder := by simp [List.append_assoc]
          _ = during ++ remainder := by rw [hsplitDuring]
      rw [hseq]
      exact hcutOutput'
    obtain ⟨afterPrior, hpriorChain, htargetChain⟩ :=
      connected_append_split prior (target :: (afterTarget ++ remainder)) hpriorTargetChain
    have htargetState :
        target.input.state = afterPrior := htargetChain.1
    have htargetMem : target ∈ during := by
      rw [hsplitDuring]
      simp
    have htargetChoice :
        ReferenceCollectionSegmentExtraction.choice target.input = some c := by
      rw [htargetDef]
      exact hcurrentChoice
    have hcutContext : CollectionBufferProvenance.collectionContext c0.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
      have hstart := CollectionBufferProvenance.startCollectionChecked_success_context
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside c0.preLedger (by
          simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked)
      rcases hstart with ⟨hassignment, hsigma', hcursor', hcutoff', hfreeze', hbase'⟩
      simp [CollectionBufferProvenance.collectionContext, hassignment,
        hsigma', hcutoff', hfreeze', hbase']
    have hcutLocal := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
      rate cut.input c0 initializer hcutChoice hcutContext
    have hnoLaterPrior : ∀ record ∈ prior,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      intro record hmem
      apply hnoLater record
      rw [hsplitDuring]
      exact List.mem_append_left _ hmem
    have hinitialStart :
        CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val
          rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
          rate.n rate.n_scale initializer.assignment initializer.sigma
          initializer.cutoff initializer.freezeAt initializer.base initializer.outside =
          .success c0.preLedger := by
      simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked
    have hinitial := start_collection_history_empty initializer.assignment
      initializer.sigma initializer.cutoff initializer.freezeAt initializer.base
      initializer.outside c0.preLedger hinitialStart
    have huTime : cut.input.time.val + 1 = u := by
      simpa [u] using congrArg Nat.succ hcutTime
    have hpositive : 0 < initializer.sigma := by omega
    have hcutEnabled := collection_enabled_of_context c0.preLedger cut.input.time
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base hcutContext hpositive (by
        have hcutEq : initializer.cutoff = cut.input.time.val + 1 := by
          calc
            initializer.cutoff = start + w + 1 := hcutoff
            _ = cut.input.time.val + 1 := by simpa using (congrArg Nat.succ hcutTime).symm
        exact hcutEq.le)
    rcases hcutLocal with hcutDagger | ⟨ledger0, proposal0, _,
      hcutNext, hledgerContext, _, _, _⟩
    · have hdaggerOutput : cut.output.next.coordinator = .dagger := by
        rw [cut.output_eq]
        exact hcutDagger
      have hdaggerDuring :=
        ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hDuringChain hdaggerOutput
      have htargetDagger : target.input.state.coordinator = .dagger :=
        hdaggerDuring.2 target htargetMem
      have hnone := choice_none_of_dagger rate target.input htargetDagger
      have hnoneSome :
          (none : Option (ReferenceCollectionSegmentExtraction.Choice rate)) = some c :=
        hnone.symm.trans htargetChoice
      cases hnoneSome
    · have hcutNext' :
          (ReferenceActivePhysicalStep.step cut.input).next.coordinator =
            .collection c0.payload ledger0 proposal0 := hcutNext
      obtain ⟨completed0', hextract0', hcompletedFinal0, hhistoryUpdate0,
        hcursor0, hphase0, hcontext0⟩ :=
        actual_selected_step_history rate cut c0 initializer hcutChoice hcutContext hcutNext'
      have hblank0 : c0.preLedger.enabledHistory = fun _ => none := hinitial.1
      have henabledCut : ReferenceActivePhysicalStep.collectionEnabled
          c0.preLedger cut.input.time = decide (u < initializer.freezeAt) := by
        calc
          ReferenceActivePhysicalStep.collectionEnabled c0.preLedger cut.input.time =
              decide (cut.input.time.val + 1 < initializer.freezeAt) := hcutEnabled
          _ = decide (u < initializer.freezeAt) := by rw [huTime]
      have hhistory0 : ∀ r : Fin p.T, ledger0.enabledHistory r =
          if u ≤ r.val + 1 ∧ r.val + 1 < u + 1 then
            some (decide (r.val + 1 < initializer.freezeAt)) else none := by
        intro r
        rw [hhistoryUpdate0]
        exact congrFun (first_history_update c0.preLedger cut.input.time u
          initializer.freezeAt hblank0 huTime henabledCut) r
      have hcursor0' : ledger0.cursor = u + 1 := by
        calc
          ledger0.cursor = c0.preLedger.cursor + 1 := hcursor0
          _ = initializer.cutoff + 1 := by rw [hinitial.2.2]
          _ = u + 1 := by simpa [u] using congrArg Nat.succ hcutoff
      have hstateCut : cut.output.next.coordinator =
          .collection c0.payload ledger0 proposal0 := by
        rw [cut.output_eq]
        exact hcutNext'
      have hhistoryTarget := connected_prefix_enabled_history rate initializer u prior
          cut.output.next execution.finalState c0.payload ledger0 proposal0 1
          target (afterTarget ++ remainder) c hpriorTargetChain hstateCut hledgerContext
          hcutoff hpositive hcursor0' hphase0 hhistory0 hnoLaterPrior htargetChoice
      rcases hhistoryTarget with ⟨targetPayload, targetLedger, targetProposal,
        htargetState', htargetPre, htargetCursor, htargetReady, htargetHistory⟩
      have htargetLedger : targetLedger = c.preLedger := htargetPre.symm
      have htargetHistoryC : ∀ r : Fin p.T, c.preLedger.enabledHistory r =
          if u ≤ r.val + 1 ∧ r.val + 1 < v then
            some (decide (r.val + 1 < c.preLedger.freezeAt)) else none := by
        intro r
        have hlenPrior : prior.length = j.val := by simp [prior]
        have hnIndex : n.val = prior.length + 1 := by omega
        have hv : u + (1 + prior.length) = v := by
          calc
            u + (1 + prior.length) = u + n.val := by omega
            _ = v := hvDef.symm
        calc
          c.preLedger.enabledHistory r = targetLedger.enabledHistory r := by rw [htargetLedger]
          _ = if u ≤ r.val + 1 ∧ r.val + 1 < u + (1 + prior.length) then
                some (decide (r.val + 1 < initializer.freezeAt)) else none := htargetHistory r
          _ = if u ≤ r.val + 1 ∧ r.val + 1 < v then
                some (decide (r.val + 1 < initializer.freezeAt)) else none := by rw [hv]
          _ = if u ≤ r.val + 1 ∧ r.val + 1 < v then
                some (decide (r.val + 1 < c.preLedger.freezeAt)) else none := by rw [← hfreeze]
      have hphaseCurrent : c.preLedger.phase = .ready := by
        rw [← htargetLedger]
        exact htargetReady
      have hcursorCurrent : c.preLedger.cursor = v := by
        rw [← htargetLedger, htargetCursor]
        have hlenPrior : prior.length = j.val := by simp [prior]
        have hnIndex : n.val = prior.length + 1 := by omega
        calc
          u + (1 + prior.length) = u + n.val := by omega
          _ = v := hvDef.symm
      have hstep : start + w + n.val + 1 = start + w + 1 + n.val := by
        omega
      have hleEndpoint : start + w + 1 ≤ start + w + 1 + n.val := Nat.le_add_right _ _
      have hcutoffV : initializer.cutoff ≤ start + w + 1 + n.val :=
        hcutoff.le.trans hleEndpoint
      have hcontextCurrent : CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            c.preLedger.freezeAt, initializer.base) := by
        have hctx := hcontext
        rw [← hfreeze] at hctx
        exact hctx
      have hEnabledPair := selected_enabled_candidate (window := cut :: during) nCons c.preLedger
        u v c.preLedger.freezeAt (start + w + n.val) initializer.assignment
        initializer.sigma initializer.cutoff initializer.base hcontextCurrent hpositive
        htimeWindow hstep hcutoffV (by simp [u, v]) htargetHistoryC
      rcases hEnabledPair with ⟨henabledCons, hcandidateCons⟩
      have henabledCurrent := collectionEnabled_of_roundRecord_eq c.preLedger
        hcurrentRecord henabledCons
      let candidateHistory : Fin p.T → Option Bool := fun rr =>
        if u ≤ rr.val + 1 ∧ rr.val + 1 < v + 1 then
          some (decide (rr.val + 1 < c.preLedger.freezeAt)) else none
      have hcandidateCurrent := candidate_history_transfer_window (window := W) n
        c.preLedger hcurrentRecord candidateHistory hcandidateCons
      exact ⟨hCResult, htargetHistoryC, hphaseCurrent, hcursorCurrent,
        henabledCurrent, hcandidateCurrent⟩

end Bandits.Support.ReferenceFirstCollectionEnabledPrefix

end
