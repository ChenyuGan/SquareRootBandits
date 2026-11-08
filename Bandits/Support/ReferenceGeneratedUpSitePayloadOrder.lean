/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpOrdinaryStaleExclusion

/-!
# Temporal payload order before an actual UP receiver site

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,92-109,139-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-296,327-348,355-361`,
and `sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The actual terminal receiver-site selector is the only additional source
branch input. Connected physical prefixes, absorbing coordinator failure,
whole-payload post-choice frames, and actual installation times prove the
order. Reception or finish at the terminal site can still fail. These are
internal deterministic results through the physical horizon, not a decoder
probability bound or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceAssignmentPayloadChronology
open ReferenceGeneratedUpBatchPrefixEvent
open ReferenceGeneratedUpPrefixPositiveHalf

namespace Bandits.Support.ReferenceGeneratedUpSitePayloadOrder

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem livePostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionFinish_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]

private theorem collectionPostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | success startedLedger =>
          simpa [hrecord, hstart] using
            (collectionFinish_configuration_ne_first (x := x) payload started recording
              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger))

private theorem step_coordinator_ne_first (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.coordinator ≠ .first := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord]
  | first outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | chosen installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | live registers owned base outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) registers owned base outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuingChosen dispatched startRound continuation choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base dispatched.startResult
        | cutoffChosen dispatched startRound ledger initialization ledgerCandidate domain clock pending noAssignment choice =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | collection payload ledger clock cutoff outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuing core prepared boundary currentScores =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) payload ledger prepared.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq)
        | laterChosen core consistent started startRound instruction assignmentStart output consistency clockData installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure]

/-- A stored actual successor contains exactly the whole payload selected
before observation. The live and collection tails may instead fail. -/
theorem actual_step_stored_payload_eq_selected
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate)
    (hnext : storedPayload (step x).next.coordinator = some payload) :
    selectedPayload (actualStepRecord x) = some payload := by
  classical
  have hn : (prepare x).coordinator.selection ≠ none := by
    intro hn
    have he := actualRecord_next_storedPayload_none_of_no_selection (actualStepRecord x) hn
    change storedPayload (step x).next.coordinator = none at he
    rw [hnext] at he
    cases he
  change storedPayload (prepare x).observeCoordinator.configuration = some payload at hnext
  unfold PreparedRound.observeCoordinator at hnext
  rw [dite_eq_right hn] at hnext
  change (prepare x).coordinator.selection.map (fun selected => selected.view.payload) = some payload
  cases hc : (prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          have hf := livePostChoice_payload_frame (prepare x) installed.registers
            installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
          rw [hc] at hnext
          rcases hf with hf | hf
          · rw [hnext] at hf; cases hf
          · have he := Option.some.inj (hf.symm.trans hnext)
            simp only [hc, DispatchCut.selection, selectionAt] at hn
            split at hn
            next ht => simp [DispatchCut.selection, selectionAt, ht, he]
            next ht => exact (hn rfl).elim
      | choiceDomainFailure installed => simp [hc, DispatchCut.selection] at hn
      | recorderBoundaryFailure installed => simp [hc, DispatchCut.selection] at hn
      | choiceRejected installed => simp [hc, DispatchCut.selection] at hn
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hs continuation selected =>
          have hf := livePostChoice_payload_frame (prepare x) (liveRegistersAt registers x.time)
            (liveOwnedAt registers owned x.time) base dispatched.startResult
          rw [hc] at hnext
          rcases hf with hf | hf
          · rw [hnext] at hf; cases hf
          · have he := Option.some.inj (hf.symm.trans hnext)
            simpa [DispatchCut.selection, selectionAt, liveRegistersAt] using congrArg some he
      | cutoffChosen dispatched hs ledger he hl hv hclock hpending hstart selected =>
          have hf := collectionPostChoice_payload_frame (prepare x) registers.payload
            (sharedLedger ledger) dispatched.startResult
            (liveRegistersAt registers x.time).complementWeights
          rw [hc] at hnext
          rcases hf with hf | hf
          · rw [hnext] at hf; cases hf
          · have he := Option.some.inj (hf.symm.trans hnext)
            simpa [DispatchCut.selection, selectionAt] using congrArg some he
      | clockFailure failure he => simp [hc, DispatchCut.selection] at hn
      | initializerFailure dispatched hs checked he => simp [hc, DispatchCut.selection] at hn
      | localFailure dispatched hs reason => simp [hc, DispatchCut.selection] at hn
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hf := collectionPostChoice_payload_frame (prepare x) old ledger
            snapshot.clockStarted (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (collectionInput x old ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          rw [hc] at hnext
          rcases hf with hf | hf
          · rw [hnext] at hf; cases hf
          · have he := Option.some.inj (hf.symm.trans hnext)
            simpa only [DispatchCut.selection, Option.map_some] using congrArg some he
      | laterChosen core consistent started hs instruction hi output he clockData installed selected =>
          have hf := livePostChoice_payload_frame (prepare x) installed.registers
            installed.ownedRegisters installed.retainedBaseScore started
          rw [hc] at hnext
          rcases hf with hf | hf
          · rw [hnext] at hf; cases hf
          · have he := Option.some.inj (hf.symm.trans hnext)
            simp only [hc, DispatchCut.selection, selectionAt] at hn
            split at hn
            next ht => simp [DispatchCut.selection, selectionAt, ht, he]
            next ht => exact (hn rfl).elim
      | clockFailure failure he => simp [hc, DispatchCut.selection] at hn
      | localFailure started hs invalid reason => simp [hc, DispatchCut.selection] at hn
      | coreFailure core started hs reason => simp [hc, DispatchCut.selection] at hn
      | laterReconstructionFailure core consistent started hs instruction hi reason he =>
          simp [hc, DispatchCut.selection] at hn
      | laterPrefixFailure core consistent started hs instruction hi arm reason he =>
          simp [hc, DispatchCut.selection] at hn
      | laterOrientationFailure core consistent started hs instruction hi set he =>
          simp [hc, DispatchCut.selection] at hn
      | laterChoiceFailure core consistent started hs instruction hi output he clockData installed reason =>
          simp [hc, DispatchCut.selection] at hn
  | invalidCollectionCutoff => simp [hc, DispatchCut.selection] at hn
  | dagger => simp [hc, DispatchCut.selection] at hn

private theorem tail_ledger_sigma
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger L : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? (prepare x)
      payload ledger started weights = some L) :
    L.sigma = ledger.sigma := by
  unfold ReferenceCoordinatorUpPhysicalCall.tailLedger? at htail
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) payload started weights) with
  | none => simp only [hrecording] at htail; cases htail
  | some recording =>
      simp only [hrecording] at htail
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hstart] at htail; cases htail
      | rejected out => simp only [hstart] at htail; cases htail
      | success out =>
          simp only [hstart] at htail
          have he : out = L := Option.some.inj htail
          subst out
          rw [collection_started_candidate ledger L x.time _ hstart]
          rfl

/-- The same actual receiver site selects its retained whole payload, with
ledger start equal to that payload's one-based start. This does not require
an ordinary receiver or FinishRound output. -/
theorem actual_site_selected_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some L) :
    ∃ payload, storedPayload x.state.coordinator = some payload ∧
      ∃ selected : Selection x,
        (prepare x).coordinator.selection = some selected ∧
        selected.view.payload = payload ∧ L.sigma = payload.sigma.val + 1 := by
  classical
  have hn : (prepare x).coordinator.selection ≠ none := by
    intro hn
    simp only [ReferenceCoordinatorUpPhysicalCall.siteLedger?, dite_eq_left hn] at hsite
    cases hsite
  obtain ⟨terminalSel, hselected⟩ : ∃ selected, (prepare x).coordinator.selection = some selected := by
    cases he : (prepare x).coordinator.selection with
    | none => exact (hn he).elim
    | some selected => exact ⟨selected, rfl⟩
  have htail := hsite
  simp only [ReferenceCoordinatorUpPhysicalCall.siteLedger?, dite_eq_right hn] at htail
  cases hstate : x.state.coordinator with
  | first =>
      have hcut := dispatch_first x hstate
      change (prepare x).coordinator = _ at hcut
      simp only [hcut] at htail
      cases CoordinatorRoundDispatch.dispatchFirst (firstInput x) <;> cases htail
  | dagger =>
      have hcut := dispatch_dagger x hstate
      change (prepare x).coordinator = .dagger at hcut
      rw [hcut] at htail
      cases htail
  | live registers owned base =>
      cases hd : CoordinatorRoundDispatch.dispatch (.live (liveInput x registers owned base)) with
      | live outcome =>
          have hcut : (prepare x).coordinator = .live registers owned base outcome := by
            simp only [ReferenceActivePhysicalStep.prepare, dispatch, hstate, hd]
            rfl
          rw [hcut] at htail
          cases outcome with
          | cutoffChosen dispatched hs ledger he hl hv hclock hpending hstart selected =>
              refine ⟨registers.payload, by simp only [storedPayload_live],
                terminalSel, hselected, ?_, ?_⟩
              · have he : some registers.payload = some terminalSel.view.payload := by
                  simpa [hcut, DispatchCut.selection, selectionAt] using
                    congrArg (fun v => v.map (fun a => a.view.payload)) hselected
                exact (Option.some.inj he).symm
              have hframe := tail_ledger_sigma x registers.payload (sharedLedger ledger) L
                dispatched.startResult (liveRegistersAt registers x.time).complementWeights htail
              rw [hframe]
              change ledger.sigma = registers.payload.sigma.val + 1
              rw [hl]
              exact (CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
                (liveRegistersAt registers x.time) (liveOwnedAt registers owned x.time)
                base x.time).2.1
          | clockFailure failure he => cases htail
          | initializerFailure dispatched hs checked he => cases htail
          | localFailure dispatched hs reason => cases htail
          | continuingChosen dispatched hs continuation selected => cases htail
  | collection payload ledger saved =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger saved cutoff
        cases hd : CoordinatorRoundDispatch.dispatch
            (.collection (collectionInput x payload ledger clock cutoff)) with
        | collection outcome =>
            have hcut : (prepare x).coordinator =
                .collection payload ledger clock cutoff outcome := by
              simp [ReferenceActivePhysicalStep.prepare, dispatch, hstate, hvalid, cutoff, clock, hd]
              rfl
            rw [hcut] at htail
            cases outcome with
            | continuing core snapshot boundary scores =>
                refine ⟨payload, by simp only [storedPayload_collection],
                  terminalSel, hselected, ?_, ?_⟩
                · have he : some payload = some terminalSel.view.payload := by
                    simpa only [hcut, DispatchCut.selection, Option.map_some] using
                      congrArg (fun v => v.map (fun a => a.view.payload)) hselected
                  exact (Option.some.inj he).symm
                have hframe := tail_ledger_sigma x payload ledger L snapshot.clockStarted
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (collectionInput x payload ledger clock cutoff)
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) htail
                exact hframe.trans snapshot.inputsValid.ledger_sigma_eq
            | clockFailure failure he => cases htail
            | localFailure started hs invalid reason => cases htail
            | coreFailure core started hs reason => cases htail
            | laterReconstructionFailure core consistent started hs instruction hi reason he => cases htail
            | laterPrefixFailure core consistent started hs instruction hi arm reason he => cases htail
            | laterOrientationFailure core consistent started hs instruction hi set he => cases htail
            | laterChosen core consistent started hs instruction hi output he clockData installed selected => cases htail
            | laterChoiceFailure core consistent started hs instruction hi output he clockData installed reason => cases htail
      · have hcut := (dispatch_collection_invalid_cutoff x payload ledger saved hstate hvalid).1
        change (prepare x).coordinator = .invalidCollectionCutoff at hcut
        rw [hcut] at htail
        cases htail

/-- An ordinary coordinator endpoint excludes every earlier coordinator
dagger in the same connected actual prefix. No follower condition is used. -/
theorem actual_prefix_coordinator_ne_dagger
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hmode : allActiveAtStart initial s)
    (hend : (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode).finalState.coordinator ≠ .dagger)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s prefixLength (by omega) hmode).finalState.coordinator ≠ .dagger := by
  induction count generalizing prefixLength with
  | zero =>
      have he : prefixLength = 0 := by omega
      subst prefixLength
      exact hend
  | succ n ih =>
      let record := actualRunRecordAt initial rows J rewards s n hspan hmode
      have hfinal := run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards s n hspan hmode
      have hnext : record.output.next.coordinator ≠ .dagger := by
        simpa only [hfinal] using hend
      have hprior : (ReferenceActivePhysicalHorizon.run initial rows J rewards s n
          (by omega) hmode).finalState.coordinator ≠ .dagger := by
        intro hd
        exact hnext (step_coordinator_dagger record.input hd).1
      by_cases he : prefixLength = n + 1
      · subst prefixLength
        exact hend
      · exact ih (by omega) hprior prefixLength (by omega)

/-- Before a retained terminal payload, every earlier selection has an
at-most-as-large start. A dropped payload cannot be followed by an older
payload: a drop to dagger is absorbing, first cannot recur, and replacement
has the actual current installation time. All records are the real run. -/
theorem actual_prefix_selected_start_le
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hmode : allActiveAtStart initial s) (hfirst : initial.coordinator = .first)
    (payload : Payload rate)
    (hstored : storedPayload (ReferenceActivePhysicalHorizon.run initial rows J rewards
      s count hspan hmode).finalState.coordinator = some payload)
    (k : ℕ) (hkc : k < count) (hk : s + (k + 1) ≤ p.T)
    (selected : Selection (actualRunRecordAt initial rows J rewards s k hk hmode).input)
    (hselected : (prepare (actualRunRecordAt initial rows J rewards s k hk hmode).input).coordinator.selection = some selected) :
    selected.view.payload.sigma.val + 1 ≤ payload.sigma.val + 1 := by
  induction count generalizing payload k with
  | zero => omega
  | succ n ih =>
      let record := actualRunRecordAt initial rows J rewards s n hspan hmode
      let prior := ReferenceActivePhysicalHorizon.run initial rows J rewards s n (by omega) hmode
      have hfinal := run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards s n hspan hmode
      have hnext : storedPayload (step record.input).next.coordinator = some payload := by
        simpa only [hfinal, record, actualRunRecordAt] using hstored
      by_cases he : k = n
      · subst k
        have hselectedPayload := actual_step_stored_payload_eq_selected record.input payload hnext
        change (prepare record.input).coordinator.selection.map
          (fun a => a.view.payload) = some payload at hselectedPayload
        rw [hselected, Option.map_some] at hselectedPayload
        have heq : selected.view.payload = payload := Option.some.inj hselectedPayload
        rw [heq]
      · have hkn : k < n := by omega
        have hpriorNotFirst : prior.finalState.coordinator ≠ .first := by
          intro hf
          cases n with
          | zero => omega
          | succ n =>
              rw [run_successor_finalState_eq_actualRunRecordAt] at hf
              exact step_coordinator_ne_first _ hf
        have hpriorNotDagger : prior.finalState.coordinator ≠ .dagger := by
          intro hd
          have hn := (step_coordinator_dagger record.input hd).1
          rw [hn, storedPayload_dagger] at hnext
          cases hnext
        obtain ⟨old, hold⟩ : ∃ old, storedPayload prior.finalState.coordinator = some old := by
          cases hc : prior.finalState.coordinator with
          | first => exact (hpriorNotFirst hc).elim
          | dagger => exact (hpriorNotDagger hc).elim
          | live registers owned base => exact ⟨registers.payload, rfl⟩
          | collection old ledger saved => exact ⟨old, rfl⟩
        have hmono : old.sigma.val ≤ payload.sigma.val := by
          rcases actualStep_payload_classification record.input with
            hnone | ⟨retained, hbefore, hafter⟩ | ⟨fresh, hborn, hafter⟩
          · rw [hnext] at hnone
            cases hnone
          · have he1 : retained = old := Option.some.inj (hbefore.symm.trans hold)
            have he2 : retained = payload := Option.some.inj (hafter.symm.trans hnext)
            rw [← he1, ← he2]
          · have heq : fresh = payload := Option.some.inj (hafter.symm.trans hnext)
            subst fresh
            have hbornTime := installationBirth_time_eq (actualStepRecord record.input) payload hborn
            change payload.sigma.val = record.input.time.val at hbornTime
            obtain ⟨_, _, _, _, _, htime⟩ := run_prefix_storedPayload_has_birth
              initial rows J rewards s n (by omega) hmode hfirst n (by omega) old hold
            have hrtime : record.input.time.val = s + n := rfl
            omega
        have hearlier := ih (by omega) old hold k hkn hk selected hselected
        omega

private theorem original_source_seed_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    input.val.1.coordinator = .first ∧ storedPayload input.val.1.coordinator = none ∧
      input.val.2.1 = z.val.1.2 ∧
      input.val.2.2.1 = ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      input.val.2.2.2 = rewards := by
  dsimp only
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 launch
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s launch.1 fields.1 control0 control).mp fields.2
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  have hbridge := ReferenceGeneratedUpResetPrefixBridge.original_source_run_eq_generated
    rate rewards C_star C_h q t s hs control0 i z 0 (by omega)
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z.1 rewards C_star C_h = some active := by
    rw [← hbridge.1]
    exact hspec.1
  obtain ⟨seed, hchar, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate z.1 rewards C_star C_h z.property.2.1
  have he : seed = active := Option.some.inj (hchar.1.symm.trans hlaunch)
  have hfirst : active.coordinator = .first := he ▸ hchar.2.1
  have hinput : (originalSourceRunInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z).val.1 = active :=
    congrArg Prod.fst hbridge.2.1
  have hinitial : (originalSourceRunInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z).val.1.coordinator = .first := by
    rw [hinput]
    exact hfirst
  exact ⟨hinitial, by rw [hinitial, storedPayload_first], rfl, rfl, rfl⟩

private theorem original_current_eq_actual_record
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z =
      actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
        s (t.val - s) (by omega) input.property := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hentry : (⟨t.val, hs, t.isLt⟩ : CalendarEntry p s) =
      ⟨s + (t.val - s), by omega, by omega⟩ := Subtype.ext (Nat.add_sub_of_le hs).symm
  exact congrArg (fun entry : CalendarEntry p s =>
    actualStepRecord (roundInputAt input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
      s input.property (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s (t.val - s) (by omega) input.property) entry)) hentry

/-- The terminal receiver site selects precisely its retained payload, rather
than an arbitrary equal-start witness. Only the actual site selector is added
to the original-source launch telescope. -/
theorem original_source_site_selected_payload
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input) = some L) :
    let current := originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z
    ∃ payload, storedPayload current.input.state.coordinator = some payload ∧
      ∃ selected : Selection current.input,
        (prepare current.input).coordinator.selection = some selected ∧
        selected.view.payload = payload ∧ L.sigma = payload.sigma.val + 1 := by
  exact actual_site_selected_payload _ L hsite

/-- The actual terminal site rules out coordinator dagger at every earlier
prefix endpoint. Failure remains absorbing throughout the connected physical
run; this conclusion says nothing about the terminal site's later tail. -/
theorem original_source_site_coordinator_prefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input) = some L)
    (k : ℕ) (hkc : k ≤ t.val - s) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s k (by omega) input.property).finalState.coordinator ≠ .dagger := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  obtain ⟨payload, hstored, _⟩ :=
    original_source_site_selected_payload rewards C_star C_h q t s hs control0 i z L hsite
  have hend : (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s (t.val - s) (by omega) input.property).finalState.coordinator ≠ .dagger := by
    intro hd
    change storedPayload (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s (t.val - s) (by omega) input.property).finalState.coordinator = some payload at hstored
    rw [hd, storedPayload_dagger] at hstored
    cases hstored
  exact actual_prefix_coordinator_ne_dagger input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 s (t.val - s) (by omega) input.property hend k hkc

/-- Every selected payload start in the real original-source prefix is at
most the actual terminal UP receiver-site start, including the terminal round.
No ordinary terminal follower, ordinary reception output, or no-newer-DOWN
premise is required. This supplies the coordinator ancestry input for the
later unoccupied-follower suffix argument of AppA:92-109. -/
theorem original_source_site_selected_start_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input) = some L)
    (k : ℕ) (hkc : k ≤ t.val - s) (hk : s + (k + 1) ≤ p.T)
    (selected : Selection (actualRunRecordAt
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
      s k hk
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input)
    (hselected : (prepare (actualRunRecordAt
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
      s k hk
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input).coordinator.selection = some selected) :
    selected.view.payload.sigma.val + 1 ≤ L.sigma := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  obtain ⟨payload, hstored, terminal, hterminal, hwhole, hsigma⟩ :=
    original_source_site_selected_payload rewards C_star C_h q t s hs control0 i z L hsite
  rw [hsigma]
  by_cases he : k = t.val - s
  · subst k
    have hrecord := original_current_eq_actual_record rewards C_star C_h q t s hs control0 i z
    have hprojection : selectedPayload current = some payload := by
      change (prepare current.input).coordinator.selection.map (fun a => a.view.payload) = _
      rw [hterminal, Option.map_some, hwhole]
    dsimp only [current] at hprojection
    rw [hrecord] at hprojection
    change (prepare (actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s (t.val - s) hk input.property).input).coordinator.selection.map
        (fun a => a.view.payload) = some payload at hprojection
    rw [hselected, Option.map_some] at hprojection
    rw [Option.some.inj hprojection]
  · have hfirst := (original_source_seed_fields rewards C_star C_h q t s hs control0 i z).1
    exact actual_prefix_selected_start_le input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s (t.val - s) (by omega) input.property hfirst payload hstored
      k (by omega) hk selected hselected

end Bandits.Support.ReferenceGeneratedUpSitePayloadOrder
