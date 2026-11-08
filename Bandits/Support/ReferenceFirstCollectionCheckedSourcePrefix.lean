/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCanonicalArrivalSource
public import Bandits.Support.ReferenceFirstCollectionParsedUpBudgets
public import Bandits.Support.ReferenceFirstCutoffKnownNumericalState

import Lean.Elab.Tactic.Omega

/-!
# Checked source cells on the actual first collection prefix

This module joins the actual first-cutoff checked boundary to the finite
collection prefix selected by an actual later source choice.  Earlier
collection choices and completed records are extracted from physical
connectedness; literal numerical cells are computed from the actual cutoff
and later SOME readouts. The result does not assert current START, receive, or FINISH
success, and does not close a manuscript theorem.

Mathematical evidence:
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,391-397`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCheckedSourcePrefix

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters}

private theorem connected_take
    (rate : RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (final : ReferenceActivePhysicalStep.State p rate) (count : ℕ)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceActivePhysicalHorizon.Connected initial (records.take count)
      (ReferenceCollectionSegmentExtraction.endpointState initial (records.take count)) := by
  induction count generalizing initial records final with
  | zero =>
      simp [ReferenceActivePhysicalHorizon.Connected,
        ReferenceCollectionSegmentExtraction.endpointState]
  | succ count ih =>
      cases records with
      | nil =>
          simp [ReferenceActivePhysicalHorizon.Connected,
            ReferenceCollectionSegmentExtraction.endpointState] at hchain ⊢
      | cons record rest =>
          rcases hchain with ⟨hpre, htail⟩
          simpa [ReferenceActivePhysicalHorizon.Connected,
            ReferenceCollectionSegmentExtraction.endpointState,
            List.take_succ_cons] using
            (And.intro hpre (ih record.output.next rest final htail))

private theorem connected_suffix
    (rate : RateInput p)
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (leftPart suffix : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (leftPart ++ suffix) final) :
    ReferenceActivePhysicalHorizon.Connected
      (ReferenceCollectionSegmentExtraction.endpointState initial leftPart) suffix final := by
  induction leftPart generalizing initial with
  | nil => simpa [ReferenceCollectionSegmentExtraction.endpointState] using hchain
  | cons head tail ih =>
      rcases hchain with ⟨_, htail⟩
      simpa [ReferenceCollectionSegmentExtraction.endpointState] using
        ih head.output.next htail

private theorem roundRecord_eq_step
    (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record = ⟨record.input, ReferenceActivePhysicalStep.step record.input, rfl⟩ := by
  cases record with
  | mk input output output_eq =>
      cases output_eq
      rfl

private theorem choice_none_of_dagger_local
    (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdagger : x.state.coordinator = .dagger) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  simp [ReferenceCollectionSegmentExtraction.choice,
    ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch_dagger x hdagger,
    ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem collection_choice_none_dagger_local
    (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
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
  · have hprepared :
        (ReferenceActivePhysicalStep.prepare x).coordinator =
          .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate, hcutoff]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      hprepared, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.coordinatorFailure]

private theorem choice_collection_payload_pre_local
    (rate : RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    c.payload = payload ∧ c.preLedger = ledger ∧ c.initializer = none := by
  have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
    x payload ledger proposal c hstate hchoice
  have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hnone : ReferenceCollectionSegmentExtraction.choice x = none := by
      simp [ReferenceCollectionSegmentExtraction.choice,
        ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate, hbad,
        ReferenceActivePhysicalStep.DispatchCut.selection]
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
  have hpayload : c.payload = payload := by
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
            ReferenceCollectionSegmentExtraction.choiceOfCut, cutoff, clock, input] using hchoice
        exact (congrArg ReferenceCollectionSegmentExtraction.Choice.payload heq).symm
    | _ =>
        simp [ReferenceCollectionSegmentExtraction.choice,
          ReferenceActivePhysicalStep.prepare, hdispatch, hround,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceCollectionSegmentExtraction.choiceOfCut, cutoff, clock, input] at hchoice
  exact ⟨hpayload, hpre.1, hpre.2⟩

private theorem selected_collection_prefix_choices
    (rate : RateInput p)
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hcontext : ∃ ledger proposal,
      initial.coordinator = .collection payload ledger proposal ∧
      CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base))
    (hnoLater : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.laterChosen record.input = false)
    (n : ℕ) (hn : n < records.length)
    (last : ReferenceCollectionSegmentExtraction.Choice rate)
    (hlast : ReferenceCollectionSegmentExtraction.choice records[n].input = some last) :
    ∀ k (hk : k ≤ n),
      ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice (records[k]'(by omega)).input = some c ∧
        c.payload = payload ∧
        c.initializer = none ∧
        CollectionBufferProvenance.collectionContext c.preLedger =
          (initializer.assignment, initializer.sigma, initializer.cutoff,
            initializer.freezeAt, initializer.base) ∧
        (k < n → ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
          ReferenceCollectionSegmentExtraction.extractRound (records[k]'(by omega)) = some completed) := by
  induction n generalizing records initial final last hchain hcontext hnoLater with
  | zero =>
      intro k hk
      cases records with
      | nil => simp at hn
      | cons head tail =>
          have hhead : ReferenceCollectionSegmentExtraction.choice head.input = some last := by
            simpa using hlast
          rcases hchain with ⟨hpre, _⟩
          rcases hcontext with ⟨ledger, proposal, hcoord, hledgerContext⟩
          have hstate : head.input.state.coordinator =
              .collection payload ledger proposal := by
            rw [hpre]
            exact hcoord
          have hp := choice_collection_payload_pre_local rate head.input payload
            ledger proposal last hstate hhead
          have hledger : CollectionBufferProvenance.collectionContext last.preLedger =
              (initializer.assignment, initializer.sigma, initializer.cutoff,
                initializer.freezeAt, initializer.base) := by
            rw [hp.2.1]
            exact hledgerContext
          have hk : k = 0 := by omega
          subst k
          exact ⟨last, hhead, hp.1, hp.2.2, hledger, by intro hlt; omega⟩
  | succ n ih =>
      intro k hk
      cases records with
      | nil => simp at hn
      | cons head tail =>
          rcases hchain with ⟨hpre, htail⟩
          rcases hcontext with ⟨ledger, proposal, hcoord, hledgerContext⟩
          have hheadState : head.input.state.coordinator =
              .collection payload ledger proposal := by
            rw [hpre]
            exact hcoord
          have hnotLater := hnoLater head (by simp)
          have hnTail : n < tail.length := by simp at hn; omega
          have hlastTail : ReferenceCollectionSegmentExtraction.choice tail[n].input = some last := by
            simpa using hlast
          have htailNoLater : ∀ record ∈ tail,
              ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
            intro record hmem
            exact hnoLater record (List.mem_cons_of_mem _ hmem)
          cases hheadChoice : ReferenceCollectionSegmentExtraction.choice head.input with
          | none =>
              have hdagger := collection_choice_none_dagger_local rate head.input
                payload ledger proposal hheadState hnotLater hheadChoice
              have hdaggerNext : head.output.next.coordinator = .dagger := by
                rw [head.output_eq]
                exact hdagger
              have hdaggerTail :=
                ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdaggerNext
              have hcurrentDagger : tail[n].input.state.coordinator = .dagger :=
                hdaggerTail.2 tail[n] (List.getElem_mem hnTail)
              have hcurrentNone := choice_none_of_dagger_local rate tail[n].input hcurrentDagger
              rw [hcurrentNone] at hlastTail
              contradiction
          | some headCall =>
              have hp := choice_collection_payload_pre_local rate head.input
                payload ledger proposal headCall hheadState hheadChoice
              have hheadContext : CollectionBufferProvenance.collectionContext
                  headCall.preLedger =
                    (initializer.assignment, initializer.sigma, initializer.cutoff,
                      initializer.freezeAt, initializer.base) := by
                rw [hp.2.1]
                exact hledgerContext
              have hstep := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
                rate head.input headCall initializer hheadChoice hheadContext
              have hnotDagger : ¬ (ReferenceActivePhysicalStep.step head.input).next.coordinator = .dagger := by
                intro hdagger
                have hdaggerNext : head.output.next.coordinator = .dagger := by
                  rw [head.output_eq]
                  exact hdagger
                have hdaggerTail :=
                  ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdaggerNext
                have hcurrentDagger : tail[n].input.state.coordinator = .dagger :=
                  hdaggerTail.2 tail[n] (List.getElem_mem hnTail)
                have hcurrentNone := choice_none_of_dagger_local rate tail[n].input hcurrentDagger
                rw [hcurrentNone] at hlastTail
                contradiction
              rcases hstep with hdagger | ⟨nextLedger, nextProposal, headCompleted,
                  hnext, hnextContext, hextract, _, _⟩
              · exact (hnotDagger hdagger).elim
              · have hnextCoord : head.output.next.coordinator =
                    .collection payload nextLedger nextProposal := by
                  calc
                    head.output.next.coordinator =
                        (ReferenceActivePhysicalStep.step head.input).next.coordinator := by
                          rw [head.output_eq]
                    _ = .collection headCall.payload nextLedger nextProposal := hnext
                    _ = .collection payload nextLedger nextProposal := by rw [hp.1]
                have htailContext :
                    CollectionBufferProvenance.collectionContext nextLedger =
                      (initializer.assignment, initializer.sigma, initializer.cutoff,
                        initializer.freezeAt, initializer.base) := by
                  exact hnextContext
                have hrec := ih tail head.output.next final htail
                  ⟨nextLedger, nextProposal, hnextCoord, htailContext⟩
                  htailNoLater hnTail last hlastTail
                have hheadLedger : CollectionBufferProvenance.collectionContext
                    headCall.preLedger =
                      (initializer.assignment, initializer.sigma, initializer.cutoff,
                        initializer.freezeAt, initializer.base) := hheadContext
                cases k with
                | zero =>
                    refine ⟨headCall, hheadChoice, hp.1, hp.2.2, hheadLedger, ?_⟩
                    intro _
                    rw [roundRecord_eq_step rate head]
                    exact ⟨headCompleted, hextract⟩
                | succ k =>
                    have hk' : k ≤ n := by omega
                    rcases hrec k hk' with ⟨c, hc, hpayload, hinitializer, hcontext', hcompleted⟩
                    refine ⟨c, ?_, hpayload, hinitializer, hcontext', ?_⟩
                    · simpa using hc
                    · intro hlt
                      have hlt' : k < n := by omega
                      obtain ⟨completed, hcompleted'⟩ := hcompleted hlt'
                      refine ⟨completed, ?_⟩
                      simpa using hcompleted'

/-- Conditional linkage lemma. Its connectedness and completion inputs are
produced from the actual suffix below; no success law is a source premise. -/
private theorem checked_to_current
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hstate : initial.coordinator = .collection payload ledger proposal)
    (n : ℕ) (hn : n < records.length)
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice records[n].input = some call)
    (hcompleted : ∀ k (hk : k < n),
      ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
        ReferenceCollectionSegmentExtraction.extractRound (records[k]'(by omega)) = some completed) :
    CollectionCheckedExecution.checkedRounds ledger
      (ReferenceCollectionSegmentExtraction.inputs (records.take n)) =
        some (ReferenceCollectionSegmentExtraction.acceptances (records.take n), call.preLedger) := by
  induction n generalizing records initial final payload ledger proposal with
  | zero =>
      cases records with
      | nil => simp at hn
      | cons record rest =>
          have hpre : record.input.state.coordinator = .collection payload ledger proposal :=
            hchain.1 ▸ hstate
          have hc : ReferenceCollectionSegmentExtraction.choice record.input = some call := hchoice
          have hl := (ReferenceCollectionSegmentExtraction.choice_collection_pre
            record.input payload ledger proposal call hpre hc).1
          simp only [List.take_zero, ReferenceCollectionSegmentExtraction.inputs,
            ReferenceCollectionSegmentExtraction.acceptances,
            ReferenceCollectionSegmentExtraction.completed, List.filterMap_nil, List.map_nil,
            CollectionCheckedExecution.checkedRounds, hl]
  | succ n ih =>
      cases records with
      | nil => simp at hn
      | cons record rest =>
          obtain ⟨completed, he⟩ := hcompleted 0 (by omega)
          have he' : ReferenceCollectionSegmentExtraction.extractRound record = some completed := he
          obtain ⟨hc, _, hone, nextPayload, nextProposal, hnext⟩ :=
            ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed he'
          have hpre : record.input.state.coordinator = .collection payload ledger proposal :=
            hchain.1 ▸ hstate
          have hl := (ReferenceCollectionSegmentExtraction.choice_collection_pre record.input
            payload ledger proposal completed.context hpre hc).1
          have hn' : n < rest.length := by simpa using hn
          have hlast : ReferenceCollectionSegmentExtraction.choice rest[n].input = some call := hchoice
          have heRest : ∀ k (hk : k < n),
              ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
                ReferenceCollectionSegmentExtraction.extractRound (rest[k]'(by omega)) = some completed := by
            intro k hk
            simpa using hcompleted (k + 1) (by omega)
          have htail := ih rest record.output.next final nextPayload completed.final nextProposal
            hchain.2 hnext hn' hlast heRest
          have hboth := ReferenceCollectionSegmentExtraction.checkedRounds_cons ledger completed.final
            call.preLedger completed.input completed.accepted
            (ReferenceCollectionSegmentExtraction.inputs (rest.take n))
            (ReferenceCollectionSegmentExtraction.acceptances (rest.take n)) (hl ▸ hone) htail
          simpa only [List.take_succ_cons, ReferenceCollectionSegmentExtraction.inputs,
            ReferenceCollectionSegmentExtraction.acceptances,
            ReferenceCollectionSegmentExtraction.completed, List.filterMap_cons, he',
            List.map_cons, Option.toList_some, List.singleton_append] using hboth

/-- Literal numerical cell of an actual collection recorder call. The validity
proof supplies only the recorder's existing domain; rewards are the whole
original table. -/
def sourceCell (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate) (rewards : RewardTable p)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        call.payload call.started call.weights)) : RecordedQueueRun.RoundInput p.K :=
  let input := ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
    call.payload call.started call.weights
  let a := CoordinatorRecorderComplementBridge.recorderInput input
  let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input valid
  let enabled := ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time
  { enabled := enabled
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection enabled
      a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos
      hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
      (record.input.row.2 record.input.time).1
    reward := fun arm => ((rewards record.input.time arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)
    rate := call.payload.rate
    reward_nonneg := fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro arm
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast Nat.le_of_lt_succ (rewards record.input.time arm).isLt
    rate_pos := fun arm => (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (call.payload.beta_le_rate arm) }

private theorem cell_ext {K : ℕ} (a b : RecordedQueueRun.RoundInput K)
    (he : a.enabled = b.enabled) (ha : a.recordedArm = b.recordedArm)
    (hr : a.reward = b.reward) (hx : a.rate = b.rate) : a = b := by
  cases a
  cases b
  cases he
  cases ha
  cases hr
  cases hx
  rfl

/-- Read every actual SOME in order. The proof parameter rules out absence;
there is no default cell and no filter on enable bits, markers, or rewards. -/
def readoutPrefix (rate : RateInput p) (s : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j : Fin records.length) (head : RecordedQueueRun.RoundInput p.K)
    (present : ∀ k : Fin j.val,
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (records[k.val + 1]'(by omega))).isSome = true) :
    List (RecordedQueueRun.RoundInput p.K) :=
  head :: List.ofFn fun k : Fin j.val =>
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
      (records[k.val + 1]'(by omega))).get (present k)

private theorem connected_take_get (rate : RateInput p)
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n < records.length) :
    ReferenceActivePhysicalHorizon.Connected initial (records.take n) records[n].input.state := by
  induction n generalizing initial records with
  | zero =>
      cases records with
      | nil => simp at hn
      | cons head tail =>
          simpa only [List.take_zero, ReferenceActivePhysicalHorizon.Connected, List.getElem_cons_zero]
            using hchain.1
  | succ n ih =>
      cases records with
      | nil => simp at hn
      | cons head tail =>
          exact ⟨hchain.1, ih head.output.next tail hchain.2 (by simpa using hn)⟩

private theorem lookup_cons_tail {α : Type*} (whole tail : List α) (head : α)
    (shape : whole = head :: tail) (n : ℕ)
    (hw : n + 1 < whole.length) (ht : n < tail.length) :
    whole[n + 1] = tail[n] := by
  have h := congrArg (fun xs : List α => xs[n + 1]?) shape
  simpa only [List.getElem?_eq_getElem hw, List.getElem?_cons_succ,
    List.getElem?_eq_getElem ht, Option.some.injEq] using h

/-- The literal readout prefix has one cutoff entry and one entry per queried
later round, including disabled and zero-arrival rows. -/
theorem readoutPrefix_length (rate : RateInput p) (s : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j : Fin records.length) (head : RecordedQueueRun.RoundInput p.K)
    (present : ∀ k : Fin j.val,
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (records[k.val + 1]'(by omega))).isSome = true) :
    (readoutPrefix rate s records j head present).length = j.val + 1 := by
  simp only [readoutPrefix, List.length_cons, List.length_ofFn]

theorem readoutPrefix_readout (rate : RateInput p) (s : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j : Fin records.length) (head : RecordedQueueRun.RoundInput p.K)
    (present : ∀ k : Fin j.val,
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (records[k.val + 1]'(by omega))).isSome = true) (k : Fin j.val) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
      (records[k.val + 1]'(by omega)) =
        some ((readoutPrefix rate s records j head present)[k.val + 1]'(by
          rw [readoutPrefix_length]; omega)) := by
  simpa only [readoutPrefix, List.getElem_cons_succ, List.getElem_ofFn]
    using (Option.some_get (present k)).symm

private theorem sourceCell_congr (rate : RateInput p)
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate) (rewards : RewardTable p)
    (leftValid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput left.output.preparation
        call.payload call.started call.weights))
    (rightValid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput right.output.preparation
        call.payload call.started call.weights)) (heq : left = right) :
    sourceCell rate left call rewards leftValid = sourceCell rate right call rewards rightValid := by
  cases heq
  rfl

private theorem sourceCell_disabled (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate) (rewards : RewardTable p)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        call.payload call.started call.weights))
    (he : (sourceCell rate record call rewards valid).enabled = false) :
    (sourceCell rate record call rewards valid).recordedArm = none := by
  dsimp only [sourceCell] at he ⊢
  rw [he]
  exact SnapshotRecordingKernel.recordingMap_disabled _ _ _ _ _ _ _ _ _ _ _ _

private theorem context_projections (rate : RateInput p)
    (left right : ReferenceActivePhysicalStep.Ledger rate)
    (hcontext : CollectionBufferProvenance.collectionContext left =
      CollectionBufferProvenance.collectionContext right)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceActivePhysicalStep.collectionEnabled left record.input.time =
      ReferenceActivePhysicalStep.collectionEnabled right record.input.time ∧
    ∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord left arm record =
      ReferenceCollectionRawBufferHistory.physicalQueueRecord right arm record := by
  simp only [CollectionBufferProvenance.collectionContext, Prod.mk.injEq] at hcontext
  have he : ReferenceActivePhysicalStep.collectionEnabled left record.input.time =
      ReferenceActivePhysicalStep.collectionEnabled right record.input.time := by
    simp only [ReferenceActivePhysicalStep.collectionEnabled,
      hcontext.2.1, hcontext.2.2.1, hcontext.2.2.2.1]
  refine ⟨he, fun arm => ?_⟩
  simp only [ReferenceCollectionRawBufferHistory.physicalQueueRecord, he, hcontext.2.2.2.1]

private theorem local_record_eq (rate : RateInput p)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K) (arm : Fin p.K)
    (he : ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time = cell.enabled)
    (hp : ReferenceCollectionRawBufferHistory.physicalQueueRecord ledger arm record =
      (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm))
    (hdisabled : cell.enabled = false → cell.recordedArm = none) :
    CoordinatorCollectionLedger.localQueueRecord ledger record.input.time cell.enabled
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm =
        (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) := by
  cases hc : cell.enabled with
  | false =>
      have hz := RecordedQueueRun.quantizedArrival_eq_zero
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm (by
          rw [hdisabled hc]; simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      simp only [CoordinatorCollectionLedger.localQueueRecord, Bool.false_and,
        Bool.false_eq_true, ite_false, hz]
  | true =>
      have hf := congrArg Prod.fst hp
      have hbefore : record.input.time.val + 1 < ledger.freezeAt := by
        simpa only [ReferenceCollectionRawBufferHistory.physicalQueueRecord, he, hc,
          Bool.true_and, decide_eq_true_eq] using hf
      have ha := congrArg Prod.snd hp
      simp only [ReferenceCollectionRawBufferHistory.physicalQueueRecord, hbefore,
        ite_true] at ha
      simp only [CoordinatorCollectionLedger.localQueueRecord, CoordinatorCollectionLedger.sourceRound,
        hbefore, decide_true, Bool.and_self, ite_true, ha]

section ActualSource

variable (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length < count)

include hshort

/-- Backward extraction from a later actual arm choice. The cutoff head is
committed by K's checked operations; only strictly later, strictly earlier
than current ordinary rounds are extracted by dagger absorption. -/
theorem actual_first_collection_checked_prefix
    (j : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length).length))
    (hj : 0 < j.val) (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hc count hspan).records
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan).length)[j].input = some call) :
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let L := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records L.length
    let H := (B.take j.val).drop 1
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (f0 : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      E.records[L.length]? = some cut ∧ E.records = L ++ cut :: suffix ∧
      B = cut :: suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      cut.input.state.coordinator = .live r q base ∧
      head.payload = r.payload ∧
      head.initializer = some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time) ∧
      ReferenceCollectionSegmentExtraction.choice cut.input = some head ∧
      (∃ completed0 : ReferenceCollectionSegmentExtraction.CompletedRound rate,
        ReferenceCollectionSegmentExtraction.extractRound cut = some completed0 ∧
        completed0.context = head ∧ completed0.final = f0 ∧
        CollectionCheckedExecution.checkedRounds head.preLedger [completed0.input] =
          some ([completed0.accepted], f0)) ∧
      cut.output.next.coordinator = .collection r.payload f0 proposal ∧
      call.payload = r.payload ∧ call.initializer = none ∧
      CollectionBufferProvenance.collectionContext f0 =
        CollectionBufferProvenance.collectionContext head.preLedger ∧
      (∀ h : Fin (j.val + 1),
        ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
          ReferenceCollectionSegmentExtraction.choice (B[h.val]'(by exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) j.isLt)).input = some c ∧
          c.payload = r.payload ∧
          CollectionBufferProvenance.collectionContext c.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          (0 < h.val → c.initializer = none) ∧
          (0 < h.val → h.val < j.val →
            ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
              ReferenceCollectionSegmentExtraction.extractRound (B[h.val]'(by exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) j.isLt)) = some completed)) ∧
      ReferenceActivePhysicalHorizon.Connected cut.output.next H B[j].input.state ∧
      CollectionCheckedExecution.checkedRounds f0 (ReferenceCollectionSegmentExtraction.inputs H) =
        some (ReferenceCollectionSegmentExtraction.acceptances H, call.preLedger) := by
  classical
  intro E L B H
  have hjB : j.val < B.length := j.isLt
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  have hK := ReferenceFirstCutoffKnownNumericalState.actual_first_cutoff_known_numerical_state
    rate source rewards C_star C_h hc count hspan hshort
  dsimp only at hK
  rcases hK with ⟨cut, suffix, r, q, base, dispatched, hstart,
    ledger, hinit, hledger, hdomain, hclock, hpending, hnoAssignment,
    selected, out, hcut, hrecords, hphysicalCut, htime, hrows,
    hselected, hrewards, hsigma, hnRate, hbaseZero, hstate, hprep,
    hu, huBound, huGrid, hledgerCutoff, hwpos, hpayloads, hKtail⟩
  rcases hKtail with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstartedExists⟩
  rcases hstartedExists with ⟨ledgerStarted, _hstageOne, _hcandidate,
    _hfastKnown, _hunknown, _hrawBuffer, hreceiver⟩
  rcases hreceiver with ⟨input, diagnostic, _hinput, _hinputLedger,
    _hinputDomain, _hinputCheck, _hrawParsed, _hfiltered, _hparsed, _hreceive,
    _hdiagSome, _hdiagInput, _hdiagRaw, _hdiagParsed, _hdiagExpected,
    _hdiagDecoder, _hdiagAccepted, _hdiagMatches, _hdiagWrong, _hbankOther,
    _hbankEq, _hbatchCompleted, _hbatchPending, hfinished⟩
  rcases hfinished with ⟨f0, _hfinish, _hfinishedCandidate,
    _hfinishedCutoff, _hfinishedKnown, _hfinishedUnknown,
    _hconfiguration, hnext, _hnextBank, _hcoordinatorBank,
    _hfailure, _hrecordingFinal, _hupFinal⟩
  change E.records = L ++ cut :: suffix at hrecords
  let l0 := ReferenceActivePhysicalStep.sharedLedger ledger
  let head : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨r.payload, l0, dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time)⟩
  have hprepared : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input := by
    rw [cut.output_eq]
    rfl
  have hprepCut : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
      .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
        hclock hpending hnoAssignment selected) := hprepared ▸ hprep
  have hhead : ReferenceCollectionSegmentExtraction.choice cut.input = some head := by
    unfold ReferenceCollectionSegmentExtraction.choice
    have hselection : (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection ≠ none := by
      rw [hprepCut]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt]
    rw [ite_eq_right hselection, hprepCut]
    rfl
  let initializer := (ReferenceCollectionSegmentExtraction.cutoffInitializer
    (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
    (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time)
  have hinitHead : initializer.checkedStart rate = .success head.preLedger :=
    ReferenceCollectionSegmentExtraction.choice_initializer cut.input head initializer hhead rfl
  have hstartFields := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside head.preLedger hinitHead
  have hcontextHead : CollectionBufferProvenance.collectionContext head.preLedger =
      (initializer.assignment, initializer.sigma, initializer.cutoff, initializer.freezeAt, initializer.base) := by
    simp only [CollectionBufferProvenance.collectionContext, hstartFields]
  obtain ⟨completed0, he0⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_complete
    cut head r.payload f0 dispatched.startResult.clock.lastProposal hhead hnext
  obtain ⟨hc0, _, hchecked0, payload0, proposal0, hfinal0⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_checked cut completed0 he0
  have hcontext0 : completed0.context = head := Option.some.inj (hc0.symm.trans hhead)
  have hledger0 : completed0.final = f0 := by
    have h := hfinal0.symm.trans hnext
    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj h).2.1
  have hcheckedHead : CollectionCheckedExecution.checkedRounds head.preLedger [completed0.input] =
      some ([completed0.accepted], f0) := by
    simpa only [hcontext0, hledger0] using hchecked0
  have hcontextF0 := CollectionBufferProvenance.checkedRounds_success_preserves_context
    head.preLedger f0 [completed0.input] [completed0.accepted] hcheckedHead
  let W := suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hB : B = cut :: W := by
    change ReferenceCollectionPhaseHistory.collectionWindow E.records L.length = _
    rw [hrecords]
    simp [ReferenceCollectionPhaseHistory.collectionWindow, W]
  have hfull : ReferenceActivePhysicalHorizon.Connected initial E.records E.finalState := by
    exact E.connected
  have hsplit : ReferenceActivePhysicalHorizon.Connected initial ((L ++ [cut]) ++ suffix) E.finalState := by
    simpa only [List.append_assoc, List.singleton_append, ← hrecords] using hfull
  have hsuffix := connected_suffix rate initial E.finalState (L ++ [cut]) suffix hsplit
  have hend : ReferenceCollectionSegmentExtraction.endpointState initial (L ++ [cut]) = cut.output.next := by
    simp only [ReferenceCollectionSegmentExtraction.endpointState, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  have htail : ReferenceActivePhysicalHorizon.Connected cut.output.next suffix E.finalState := hend ▸ hsuffix
  have hWtake : W = suffix.take W.length := List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
  have hWchain : ReferenceActivePhysicalHorizon.Connected cut.output.next W
      (ReferenceCollectionSegmentExtraction.endpointState cut.output.next W) := by
    simpa only [← hWtake] using connected_take rate cut.output.next suffix E.finalState W.length htail
  have hnoLater : ∀ record ∈ W, ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
    intro record hmem
    have ht := (List.all_eq_true.mp List.all_takeWhile) record hmem
    cases hlater : ReferenceCollectionPhaseHistory.laterChosen record.input <;>
      simp only [hlater, Bool.not_false, Bool.not_true, Bool.false_eq_true] at ht ⊢
  let n := j.val - 1
  have hsucc : n + 1 = j.val := by dsimp [n]; omega
  have hn : n < W.length := by
    have hlen := congrArg List.length hB
    have hjlt := j.isLt
    simp only [List.length_cons] at hlen
    omega
  have hBget : B[j.val] = W[n] := by
    have hlookup : B[j.val]? = some W[n] := by
      rw [← hsucc]
      have ht := lookup_cons_tail B W cut hB n (by omega) hn
      simpa only [List.getElem?_eq_getElem (by omega : n + 1 < B.length)] using congrArg some ht
    exact Option.some.inj ((List.getElem?_eq_getElem j.isLt).symm.trans hlookup)
  have hlast : ReferenceCollectionSegmentExtraction.choice W[n].input = some call := hBget ▸ hchoice
  have hp := selected_collection_prefix_choices rate initializer r.payload W cut.output.next
    (ReferenceCollectionSegmentExtraction.endpointState cut.output.next W) hWchain
    ⟨f0, dispatched.startResult.clock.lastProposal, hnext, hcontextF0.trans hcontextHead⟩
    hnoLater n hn call hlast
  obtain ⟨last, hlast', hpayload, hinitializer, _, _⟩ := hp n le_rfl
  have hlastEq : last = call := Option.some.inj (hlast'.symm.trans hlast)
  have hcompleted : ∀ k (hk : k < n),
      ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
        ReferenceCollectionSegmentExtraction.extractRound (W[k]'(by omega)) = some completed := by
    intro k hk
    obtain ⟨_c, _hc, _hpay, _hinit, _hctx, he⟩ := hp k (by omega)
    exact he hk
  have hchecked := checked_to_current rate W cut.output.next
    (ReferenceCollectionSegmentExtraction.endpointState cut.output.next W) r.payload f0
    dispatched.startResult.clock.lastProposal hWchain hnext n hn call hlast hcompleted
  have hH : H = W.take n := by
    change (B.take j.val).drop 1 = _
    rw [hB, ← hsucc, List.take_succ_cons]
    rfl
  have hchain := connected_take_get rate cut.output.next
    (ReferenceCollectionSegmentExtraction.endpointState cut.output.next W) W hWchain n hn
  have hheadLookup : E.records[L.length]? = some cut := by
    rw [hrecords]
    simp only [List.getElem?_append_right (by omega : L.length ≤ L.length), Nat.sub_self,
      List.getElem?_cons_zero]
  refine ⟨cut, suffix, r, q, base, head, f0, dispatched.startResult.clock.lastProposal,
    hheadLookup, hrecords, hB, hstate, rfl, rfl, hhead,
    ⟨completed0, he0, hcontext0, hledger0, hcheckedHead⟩, hnext,
    hlastEq ▸ hpayload, hlastEq ▸ hinitializer, hcontextF0, ?_, ?_, ?_⟩
  · intro h
    by_cases hz : h.val = 0
    · have hrecord : B[h.val]'(by omega) = cut := by
        have ht := congrArg (fun xs => xs[h.val]?) hB
        simpa only [hz, List.getElem?_eq_getElem (by omega : 0 < B.length),
          List.getElem?_cons_zero, Option.some.injEq] using ht
      refine ⟨head, hrecord ▸ hhead, rfl, rfl, ?_, ?_⟩ <;> intro hpos <;> omega
    · have hh : h.val - 1 ≤ n := by omega
      obtain ⟨c, hchoiceC, hpay, hinitC, hctx, he⟩ := hp (h.val - 1) hh
      have hrecord : B[h.val]'(by omega) = W[h.val - 1]'(by omega) := by
        have ht := lookup_cons_tail B W cut hB (h.val - 1) (by omega) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h.val)] using ht
      refine ⟨c, hrecord ▸ hchoiceC, hpay, hctx.trans hcontextHead.symm, fun _ => hinitC, ?_⟩
      intro _ hlt
      exact hrecord ▸ he (by omega)
  · change ReferenceActivePhysicalHorizon.Connected cut.output.next H (B[j.val]).input.state
    rw [hH, hBget]
    exact hchain
  · simpa only [hH] using hchecked

/-- C's existential cell is uniquely its exposed literal recorder formula.
All original-source selectors are explicit; validity is produced here. -/
private theorem actual_cell_source
    (j : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length).length))
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hc count hspan).records
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan).length)[j].input = some call) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let L := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records L.length
    let record := B[j]
    ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        call.payload call.started call.weights),
      let cell := sourceCell rate record call rewards valid
      record.input.rows = source.1.2 ∧
      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      record.input.rewards = rewards ∧ record.input.time.val = s + L.length + j.val ∧
      cell.enabled = decide (record.input.time.val + 1 < call.started.clock.g) ∧
      (∃ out : CoordinatorRecordingOperation.Output p,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            call.payload call.started call.weights) = some out ∧
        record.coordinatorDiagnostics.recording = some out ∧
        out.gateArm = cell.recordedArm ∧
        ReferenceCollectionRawBufferHistory.rawDiagnostic record =
          out.gateArm.map (fun arm => (arm, out.rawArrival)) ∧
        (∀ arm, CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) ∧
        (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord call.preLedger arm record =
          (cell.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)) ∧
        (∀ arm, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm =
          if cell.recordedArm = some arm then
            Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
              (((rewards record.input.time arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)) /
                call.payload.rate arm) else 0) ∧
        (cell.recordedArm = none → out.rawArrival = 0) ∧
        (∀ arm, cell.recordedArm = some arm → cell.reward arm = 0 →
          ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0))) ∧
      (0 < j.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) := by
  classical
  intro s E L B record
  obtain ⟨cut, suffix, payload, headCell, _hcut, _hrecords, _hrows, _hselected,
    _hrewards, _htime, _hlive, _hwindow, _hboundary,
    hrows, hselected, hrewards, htime, _hnone, hcall⟩ :=
    ReferenceFirstCollectionCanonicalArrivalSource.actual_first_collection_canonical_arrival_source
      rate source rewards C_star C_h hc count hspan hshort j
  obtain ⟨_hpayload, _hinitHead, _hinitTail, valid, cell, he, hclock, ha, hr, hx, _hrate,
    hout, hreadout⟩ := hcall call hchoice
  have hcell : cell = sourceCell rate record call rewards valid :=
    cell_ext _ _ he ha hr hx
  refine ⟨valid, hrows, hselected, hrewards, htime, hcell ▸ hclock, hcell ▸ hout, ?_⟩
  intro hj
  rcases hreadout with ⟨hz, _⟩ | ⟨_, hread⟩
  · omega
  · exact hcell ▸ hread

/-- The actual finite checked source prefix. All earlier choices, completed
ordinary rounds, recorder cells and the fold endpoint are produced. The
current call is solely an arm-choice query, with no claimed current START,
receiver or FINISH success. The cutoff is separately committed by K. -/
theorem actual_first_collection_checked_source_prefix
    (j : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length).length))
    (hj : 0 < j.val) (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hc count hspan).records
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan).length)[j].input = some call) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let L := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records L.length
    let H := (B.take j.val).drop 1
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (f0 : ReferenceActivePhysicalStep.Ledger rate) (proposal : Option (Fin p.T × Bool)),
      E.records[L.length]? = some cut ∧ E.records = L ++ cut :: suffix ∧
      B = cut :: suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      cut.input.state.coordinator = .live r q base ∧ head.payload = r.payload ∧
      head.initializer = some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time) ∧
      ReferenceCollectionSegmentExtraction.choice cut.input = some head ∧
      (∃ completed0 : ReferenceCollectionSegmentExtraction.CompletedRound rate,
        ReferenceCollectionSegmentExtraction.extractRound cut = some completed0 ∧
        completed0.context = head ∧ completed0.final = f0 ∧
        CollectionCheckedExecution.checkedRounds head.preLedger [completed0.input] =
          some ([completed0.accepted], f0)) ∧
      cut.output.next.coordinator = .collection r.payload f0 proposal ∧
      ∃ (headValid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
          head.payload head.started head.weights))
        (present : ∀ k : Fin j.val,
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
            (B[k.val + 1]'(by
              have hjB : j.val < B.length := j.isLt
              have hk := k.isLt
              omega))).isSome = true),
      let l0 := head.preLedger
      let c_u := sourceCell rate cut head rewards headValid
      let D := readoutPrefix rate s B j c_u present
      D.length = j.val + 1 ∧ D[0]'(by rw [readoutPrefix_length]; omega) = c_u ∧
      call.payload = r.payload ∧ call.initializer = none ∧
      CollectionBufferProvenance.collectionContext f0 = CollectionBufferProvenance.collectionContext l0 ∧
      ReferenceActivePhysicalHorizon.Connected cut.output.next H B[j].input.state ∧
      CollectionCheckedExecution.checkedRounds f0 (ReferenceCollectionSegmentExtraction.inputs H) =
        some (ReferenceCollectionSegmentExtraction.acceptances H, call.preLedger) ∧
      H.length = j.val - 1 ∧
      (ReferenceCollectionSegmentExtraction.inputs H).length = H.length ∧
      (D.take j.val |>.drop 1).length = H.length ∧
      (∀ k : Fin H.length, H[k] = B[k.val + 1]'(by
          have hk := k.isLt
          have hjB : j.val < B.length := j.isLt
          have hlen : H.length = j.val - 1 := by simp only [H, List.length_drop, List.length_take]; omega
          omega)) ∧
      (∀ h : Fin (j.val + 1),
        let record := B[h.val]'(by exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) j.isLt)
        let cell := D[h.val]'(by rw [readoutPrefix_length]; exact h.isLt)
        ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
          (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              c.payload c.started c.weights)),
          ReferenceCollectionSegmentExtraction.choice record.input = some c ∧
          c.payload = r.payload ∧
          CollectionBufferProvenance.collectionContext c.preLedger = CollectionBufferProvenance.collectionContext l0 ∧
          (0 < h.val → c.initializer = none) ∧
          cell = sourceCell rate record c rewards valid ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + L.length + h.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time ∧
          cell.enabled = decide (record.input.time.val + 1 < c.started.clock.g) ∧
          cell.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
          cell.rate = r.payload.rate ∧
          (∃ out : CoordinatorRecordingOperation.Output p,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                c.payload c.started c.weights) = some out ∧
            record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = cell.recordedArm ∧
            ReferenceCollectionRawBufferHistory.rawDiagnostic record =
              out.gateArm.map (fun arm => (arm, out.rawArrival)) ∧
            (∀ arm, CoordinatorCollectionLedger.localArrival
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) ∧
            (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord c.preLedger arm record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)) ∧
            (cell.recordedArm = none → out.rawArrival = 0) ∧
            (∀ arm, cell.recordedArm = some arm → cell.reward arm = 0 →
              ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0))) ∧
          (0 < h.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) ∧
          (0 < h.val → h.val < j.val →
            ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
              ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
              completed.context = c ∧
              CollectionCheckedExecution.checkedRounds c.preLedger [completed.input] =
                some ([completed.accepted], completed.final) ∧
              completed.input.round = record.input.time ∧
              completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
              completed.input.enabled = cell.enabled ∧
              (∀ arm, CoordinatorCollectionLedger.localQueueRecord f0 completed.input.round
                completed.input.enabled completed.input.raw arm =
                  (cell.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)))) ∧
      (∀ arm : Fin p.K,
        CollectionKnownQueueContinuation.inputQueueRecords f0 arm
          (ReferenceCollectionSegmentExtraction.inputs H) =
          ((D.take j.val).drop 1).map (fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm))) := by
  classical
  intro s E L B H
  have hjB : j.val < B.length := j.isLt
  obtain ⟨cut, suffix, r, q, base, head, f0, proposal, hindex, hrecords, hB,
    hstate, hpayHead, hinitHead, hhead, hcompleted0, hnext, hpayCall, hinitCall,
    hcontextF0, hchoices, hchain, hfold⟩ :=
    actual_first_collection_checked_prefix rate source rewards C_star C_h hc count hspan hshort
      j hj call hchoice
  change E.records = L ++ cut :: suffix at hrecords
  change B = cut :: suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) at hB
  have hzeroBound : 0 < B.length := by omega
  have hzero : B[0]'hzeroBound = cut := by
    have ht := congrArg (fun xs => xs[0]?) hB
    simpa only [List.getElem?_eq_getElem hzeroBound, List.getElem?_cons_zero,
      Option.some.injEq] using ht
  have hzeroChoice : ReferenceCollectionSegmentExtraction.choice B[0].input = some head := hzero ▸ hhead
  have hheadSource := actual_cell_source rate source rewards C_star C_h hc count hspan hshort
    ⟨0, hzeroBound⟩ head hzeroChoice
  dsimp only at hheadSource
  simp only [Fin.getElem_fin] at hheadSource
  change ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
    (ReferenceActivePhysicalStep.collectionRecordingInput B[0].output.preparation
      head.payload head.started head.weights), _ at hheadSource
  obtain ⟨headValidAtZero, _⟩ := hheadSource
  have headValid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
        head.payload head.started head.weights) := hzero ▸ headValidAtZero
  let c_u := sourceCell rate cut head rewards headValid
  have present : ∀ k : Fin j.val,
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (B[k.val + 1]'(by omega))).isSome = true := by
    intro k
    let h : Fin (j.val + 1) := ⟨k.val + 1, by omega⟩
    obtain ⟨c, hcH, _hpay, _hcontext, _hinit, _hcompleted⟩ := hchoices h
    obtain ⟨valid, _hrows, _hselected, _hrewards, _htime, _hclock, _hout, hread⟩ :=
      actual_cell_source rate source rewards C_star C_h hc count hspan hshort
        ⟨h.val, by omega⟩ c hcH
    simpa only [h, Fin.getElem_fin, Option.isSome_some] using
      congrArg Option.isSome (hread (by dsimp [h]; omega))
  let D := readoutPrefix rate s B j c_u present
  have hDlen : D.length = j.val + 1 := readoutPrefix_length rate s B j c_u present
  have hHlen : H.length = j.val - 1 := by
    simp only [H, List.length_drop, List.length_take]
    omega
  have hHAt : ∀ k : Fin H.length, H[k] = B[k.val + 1]'(by omega) := by
    intro k
    simp only [H, Fin.getElem_fin, List.getElem_drop, List.getElem_take, Nat.add_comm]
  have hinputsLength : (ReferenceCollectionSegmentExtraction.inputs H).length = H.length := by
    rw [ReferenceCollectionSegmentExtraction.inputs, List.length_map]
    apply List.filterMap_length_eq_length.mpr
    intro record hmem
    obtain ⟨k, hk, hrecord⟩ := List.mem_iff_getElem.mp hmem
    let idx : Fin H.length := ⟨k, hk⟩
    have hrecordB : record = B[k + 1]'(by omega) := hrecord.symm.trans (hHAt idx)
    let h : Fin (j.val + 1) := ⟨k + 1, by have hi := idx.isLt; omega⟩
    obtain ⟨c, _hc, _hpay, _hctx, _hinit, hcompleted⟩ := hchoices h
    obtain ⟨completed, he⟩ := hcompleted (by dsimp [h]; omega) (by have hi := idx.isLt; dsimp [h]; omega)
    have hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
      simpa only [hrecordB] using he
    rw [hextract]
    rfl
  let l0 := head.preLedger
  have hAll : ∀ h : Fin (j.val + 1),
        let record := B[h.val]'(by exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) j.isLt)
        let cell := D[h.val]'(by rw [readoutPrefix_length]; exact h.isLt)
        ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
          (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              c.payload c.started c.weights)),
          ReferenceCollectionSegmentExtraction.choice record.input = some c ∧
          c.payload = r.payload ∧
          CollectionBufferProvenance.collectionContext c.preLedger = CollectionBufferProvenance.collectionContext l0 ∧
          (0 < h.val → c.initializer = none) ∧
          cell = sourceCell rate record c rewards valid ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + L.length + h.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time ∧
          cell.enabled = decide (record.input.time.val + 1 < c.started.clock.g) ∧
          cell.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
          cell.rate = r.payload.rate ∧
          (∃ out : CoordinatorRecordingOperation.Output p,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                c.payload c.started c.weights) = some out ∧
            record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = cell.recordedArm ∧
            ReferenceCollectionRawBufferHistory.rawDiagnostic record =
              out.gateArm.map (fun arm => (arm, out.rawArrival)) ∧
            (∀ arm, CoordinatorCollectionLedger.localArrival
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
                RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) ∧
            (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord c.preLedger arm record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm)) ∧
            (cell.recordedArm = none → out.rawArrival = 0) ∧
            (∀ arm, cell.recordedArm = some arm → cell.reward arm = 0 →
              ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0))) ∧
          (0 < h.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) ∧
          (0 < h.val → h.val < j.val →
            ∃ completed : ReferenceCollectionSegmentExtraction.CompletedRound rate,
              ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
              completed.context = c ∧
              CollectionCheckedExecution.checkedRounds c.preLedger [completed.input] =
                some ([completed.accepted], completed.final) ∧
              completed.input.round = record.input.time ∧
              completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
              completed.input.enabled = cell.enabled ∧
              (∀ arm, CoordinatorCollectionLedger.localQueueRecord f0 completed.input.round
                completed.input.enabled completed.input.raw arm =
                  (cell.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm))) := by
    intro h
    have hh : h.val ≤ j.val := Nat.le_of_lt_succ h.isLt
    let record := B[h.val]'(by omega)
    obtain ⟨c, hcH, hpay, hcontext, hinitC, hcompleted⟩ := hchoices h
    obtain ⟨valid, hrows, hselected, hrewards, htime, hclock, hout, hread⟩ :=
      actual_cell_source rate source rewards C_star C_h hc count hspan hshort
        ⟨h.val, by omega⟩ c hcH
    let cell := sourceCell rate record c rewards valid
    have hcell : D[h.val]'(by omega) = cell := by
      by_cases hz : h.val = 0
      · have hrecord : record = cut := by simpa only [record, hz] using hzero
        have hquery : ReferenceCollectionSegmentExtraction.choice record.input = some head := hrecord ▸ hhead
        have hcall : c = head := Option.some.inj (hcH.symm.trans hquery)
        have hliteral : cell = c_u := by
          subst c
          exact sourceCell_congr rate record cut head rewards valid headValid hrecord
        simpa only [D, readoutPrefix, hz, List.getElem_cons_zero] using hliteral.symm
      · let k : Fin j.val := ⟨h.val - 1, by omega⟩
        have hsucc : k.val + 1 = h.val := by dsimp [k]; omega
        have hd := readoutPrefix_readout rate s B j c_u present k
        have hd' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record =
            some D[h.val] := by simpa only [hsucc, D, record] using hd
        exact Option.some.inj (hd'.symm.trans (hread (Nat.pos_of_ne_zero hz)))
    obtain ⟨out, hrun, hdiag, hgate, hraw, harrivals, hphysical, _hfloor, hnone, hzeroMarker⟩ := hout
    refine ⟨c, valid, hcH, hpay, hcontext, hinitC, hcell, ?_⟩
    rw [hcell]
    refine ⟨hrows, hselected, hrewards, htime, rfl, hclock, rfl, ?_, ?_, hread, ?_⟩
    · exact congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.rate) hpay
    · exact ⟨out, hrun, hdiag, hgate, hraw, harrivals, hphysical, hnone, hzeroMarker⟩
    · intro hpos hlt
      obtain ⟨completed, he⟩ := hcompleted hpos hlt
      obtain ⟨hcCompleted, hround, hchecked, _hfinal⟩ :=
        ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed he
      have hcontextCompleted : completed.context = c := Option.some.inj (hcCompleted.symm.trans hcH)
      have hrawEnabled := ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled record completed he
      have henabled : completed.input.enabled = cell.enabled := by
        simpa only [hcontextCompleted, cell, sourceCell] using hrawEnabled.2
      refine ⟨completed, he, hcontextCompleted, hcontextCompleted ▸ hchecked,
        hround, hrawEnabled.1, henabled, ?_⟩
      intro arm
      have hctx : CollectionBufferProvenance.collectionContext f0 =
          CollectionBufferProvenance.collectionContext c.preLedger := hcontextF0.trans hcontext.symm
      have hproj := context_projections rate f0 c.preLedger hctx record
      have hphysicalF0 := (hproj.2 arm).trans (hphysical arm)
      have hlocal := local_record_eq rate f0 record cell arm hproj.1 hphysicalF0
        (sourceCell_disabled rate record c rewards valid)
      rw [hround, hrawEnabled.1, henabled]
      exact hlocal
  refine ⟨cut, suffix, r, q, base, head, f0, proposal, hindex, hrecords, hB,
    hstate, hpayHead, hinitHead, hhead, hcompleted0, hnext, headValid, present,
    hDlen, rfl, hpayCall, hinitCall, hcontextF0, hchain, hfold, hHlen,
    hinputsLength, ?_, hHAt, hAll, ?_⟩
  · change ((D.take j.val).drop 1).length = H.length
    rw [List.length_drop, List.length_take, hDlen, hHlen]
    omega
  · intro arm
    have hmapPhysical : CollectionKnownQueueContinuation.inputQueueRecords f0 arm
        (ReferenceCollectionSegmentExtraction.inputs H) =
        H.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord f0 arm) := by
      simp only [CollectionKnownQueueContinuation.inputQueueRecords,
        ReferenceCollectionSegmentExtraction.inputs, ReferenceCollectionSegmentExtraction.completed,
        List.map_filterMap]
      apply List.filterMap_eq_map_iff_forall_eq_some.mpr
      intro record hmem
      obtain ⟨k, hk, hrecord⟩ := List.mem_iff_getElem.mp hmem
      let idx : Fin H.length := ⟨k, hk⟩
      let h : Fin (j.val + 1) := ⟨k + 1, by omega⟩
      obtain ⟨c, valid, _hc, _hpay, hcontext, _hinitC, _hcell, _hrows, _hselected,
        _hrewards, _htime, _henabled, _hclock, _hreward, _hrate, hout, _hread, hcompleted⟩ := hAll h
      obtain ⟨out, _hrun, _hdiag, _hgate, _hraw, _harrival, hphysical, _hnone, _hzero⟩ := hout
      obtain ⟨completed, he, _hctx, _hchecked, _hround, _hrawInput, _henabledInput, hlocal⟩ :=
        hcompleted (by dsimp [h]; omega) (by dsimp [h]; omega)
      have hrecordB : record = B[h.val]'(by omega) := hrecord.symm.trans (hHAt idx)
      have heRecord : ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
        simpa only [hrecordB] using he
      have hproj := context_projections rate f0 c.preLedger
        (hcontextF0.trans hcontext.symm) (B[h.val]'(by omega))
      have hphysicalF0 := (hproj.2 arm).trans (hphysical arm)
      have hlocalPhysical : CoordinatorCollectionLedger.localQueueRecord f0 completed.input.round
          completed.input.enabled completed.input.raw arm =
          ReferenceCollectionRawBufferHistory.physicalQueueRecord f0 arm record := by
        rw [hrecordB]
        exact (hlocal arm).trans hphysicalF0.symm
      simpa only [heRecord, Option.map_some, Function.comp_apply] using congrArg some hlocalPhysical
    rw [hmapPhysical]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_drop, List.length_take]
      change H.length = min j.val D.length - 1
      rw [hHlen, hDlen]
      omega
    · intro k hleft hright
      have hk : k < H.length := by simpa only [List.length_map] using hleft
      let idx : Fin H.length := ⟨k, hk⟩
      let h : Fin (j.val + 1) := ⟨k + 1, by omega⟩
      obtain ⟨c, valid, _hc, _hpay, hcontext, _hinitC, _hcell, _hrows, _hselected,
        _hrewards, _htime, _henabled, _hclock, _hreward, _hrate, hout, _hread, _hcompleted⟩ := hAll h
      obtain ⟨out, _hrun, _hdiag, _hgate, _hraw, _harrival, hphysical, _hnone, _hzero⟩ := hout
      have hproj := context_projections rate f0 c.preLedger
        (hcontextF0.trans hcontext.symm) (B[h.val]'(by omega))
      have hphysicalF0 := (hproj.2 arm).trans (hphysical arm)
      have hDtail : ((D.take j.val).drop 1)[k]'(by
          simp only [List.length_drop, List.length_take, hDlen]; omega) = D[k + 1]'(by omega) := by
        simp only [List.getElem_drop, List.getElem_take, Nat.add_comm]
      have hHAtNat := hHAt idx
      simp only [Fin.getElem_fin] at hHAtNat
      simp only [List.getElem_map]
      rw [hHAtNat, hDtail]
      exact hphysicalF0

end ActualSource

end Bandits.Support.ReferenceFirstCollectionCheckedSourcePrefix

end
