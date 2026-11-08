/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionSourceSections
public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota

import Mathlib.Tactic

/-!
# Original collection reply-formation chronology

The source interval below follows an actual LIVE cutoff through the maximal
no-later-installation suffix.  It preserves the current reply boundary, the
whole inherited UP decoder bank, and the exact formation chronology.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceOriginalCollectionReplyFormationChronology

variable {p : Parameters}

/-- Every prefix of an actual LIVE cutoff's no-later-installation suffix is
the corresponding prefix of the original physical run.  In particular, the
UP decoder bank at the cutoff is inherited from the launch replay rather than
reinitialized at the cutoff. -/
theorem actual_cutoff_original_up_bank_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen ..) =>
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let start := ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h
        ∃ (initial : ReferenceActivePhysicalStep.State p rate)
          (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start),
          ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate source rewards C_star C_h = some initial ∧
          initial.coordinator = .first ∧
          initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
          ReferenceUpDecoderBankInvariant.upBankInvariant initial ∧
          (∀ i, AffineBatchDecoder.collected (initial.upDecoderBank i) = []) ∧
          (∀ j : ℕ, j ≤ K.length →
            ∃ span : start + (e + j) ≤ p.T,
              (ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start (e + j) span active).records.drop e = K.take j ∧
              (ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start (e + j) span active).finalState = Z j) ∧
          ∀ j : ℕ, j ≤ K.length →
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z j)
      | _ => True := by
  classical
  dsimp only
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => simp only [hcoord]
    | collection _ _ _ _ _ => simp only [hcoord]
    | dagger => simp only [hcoord]
    | invalidCollectionCutoff => simp only [hcoord]
    | live registers owned base outcome =>
      cases outcome <;> simp only [hcoord]
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      let W := (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let K := cut :: W
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hKprefix : K <+: R.drop e := by
        obtain ⟨hei, hecut⟩ := List.getElem?_eq_some_iff.mp hcut
        rw [List.drop_eq_getElem_cons hei, hecut]
        refine ⟨(R.drop (e + 1)).dropWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
        simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
      obtain ⟨initial, active, hlaunch, hfirst, hbank, hinvariant, hseed,
        _hfull, hRuns⟩ :=
        ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
          rate source rewards C_star C_h e cut hcut K hKprefix
      refine ⟨initial, active, hlaunch, hfirst, hbank, hinvariant, hseed, ?_, ?_⟩
      · intro j hj
        obtain ⟨span, hdrop, hend⟩ := hRuns j hj
        exact ⟨span, hdrop, hend⟩
      · intro j hj
        obtain ⟨span, _, hend⟩ := hRuns j hj
        change ReferenceUpDecoderBankInvariant.upBankInvariant (Z j)
        change (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (e + j) span active).finalState = Z j at hend
        rw [← hend]
        exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (e + j) span active hinvariant

private theorem current_down_start
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i) = P.sigma := by
  apply Fin.ext
  have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate (P.downRecord i)
  rw [P.downRecord_fields i] at h
  exact Nat.add_right_cancel h

/-- At an arbitrary actual LIVE cutoff, the old payload has an actual earlier
installation. A current reply at this round's START is already unoccupied and
has a unique retained acceptance in the strict original physical prefix.
Neither the installation nor the follower's state or acceptance is an input. -/
theorem actual_cutoff_started_current_reply_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let P := registers.payload
        cut.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + e ∧
        FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
              cut.input.time.val + 1 ∧
        (∃ birth : Fin R.length, birth.val < e ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth R[birth.val] P) ∧
        ∀ i : Fin (p.m - 1),
          ∃ (before choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            cut.input.state.followers i = .ordinary before memory ∧
            ActiveFollowerLifecycle.localStateDomainValid before ∧
            ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
              .ok (choice, memory) ∧
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary choice memory ∧
            ActiveFollowerLifecycle.localStateDomainValid choice ∧
            (choice.lastDown = some (P.downRecord i) →
              choice.status = .unoccupied ∧
              ∃! q : Fin (R.take e).length,
                ReferenceAcceptedUpFollowerHistory.RetainedDown
                  ((R.take e).get q) i (P.downRecord i))
      | _ => True := by
  classical
  dsimp only
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => simp only [hcoord]
    | collection _ _ _ _ _ => simp only [hcoord]
    | dagger => simp only [hcoord]
    | invalidCollectionCutoff => simp only [hcoord]
    | live registers owned base outcome =>
      cases outcome <;> simp only [hcoord]
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      obtain ⟨he, hget⟩ := List.getElem?_eq_some_iff.mp hcut
      let index : Fin R.length := ⟨e, he⟩
      have hprepared : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
          .live registers owned base (.cutoffChosen dispatched hstart ledger
            hinitialization hledger hdomains hclock hpending hassignment selection) := by
        rw [← hcoord, cut.output_eq]
        rfl
      let c : ReferenceCollectionSegmentExtraction.Choice rate :=
        ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
          dispatched.startResult,
          (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights,
          some (ReferenceCollectionSegmentExtraction.cutoffInitializer
            (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time)
            base cut.input.time)⟩
      have hchoice : ReferenceCollectionSegmentExtraction.choice cut.input = some c := by
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [hprepared]
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte, reduceCtorEq,
          ↓reduceIte, ReferenceCollectionSegmentExtraction.choiceOfCut]
        rfl
      have hchoiceR : ReferenceCollectionSegmentExtraction.choice R[index.val].input =
          some c := by
        change ReferenceCollectionSegmentExtraction.choice R[e].input = some c
        rw [hget]
        exact hchoice
      obtain ⟨birth, hbirthBefore, hbirth, _, _, hcutoff, _⟩ :=
        ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
          rate rewards C_star C_h source index c hchoiceR
      have hledgerCutoff : c.preLedger.cutoff = cut.input.time.val + 1 := by
        change (ReferenceActivePhysicalStep.sharedLedger ledger).cutoff = _
        rw [(ReferenceActivePhysicalStep.sharedLedger_fields ledger).2.2.1, hledger]
        exact (CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
          (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time)
          base cut.input.time).2.2.1
      have hcalendar := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source index
      change R[e].input.time.val = _ at hcalendar
      rw [hget] at hcalendar
      have hminimum : FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
          cut.input.time.val + 1 := hcutoff.symm.trans hledgerCutoff
      refine ⟨hcalendar, hminimum, ⟨birth, hbirthBefore, hbirth⟩, ?_⟩
      intro i
      obtain ⟨before, memory, choice, hinput, hdomain, hstarted, hactual,
        hchoiceDomain, _⟩ :=
        ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
          (rate := rate) rewards C_star C_h source index i
      change R[e].input.state.followers i = _ at hinput
      change ActiveFollowerLifecycle.startRound rate.eta R[e].input.time before memory = _
        at hstarted
      change (ReferenceFollowerFixedReply.actualChoice R[e] i).configuration = _ at hactual
      rw [hget] at hinput hstarted hactual
      refine ⟨before, choice, memory, hinput, hdomain, hstarted, hactual, hchoiceDomain, ?_⟩
      intro hcurrent
      have hframe := ActiveFollowerLifecycle.startRound_frame
        rate.eta cut.input.time before choice memory memory hstarted
      have hbeforeCurrent : before.lastDown = some (registers.payload.downRecord i) :=
        hframe.1.symm.trans hcurrent
      have hinputR : R[index.val].input.state.followers i = .ordinary before memory := by
        change R[e].input.state.followers i = _
        rw [hget]
        exact hinput
      have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
        rate rewards C_star C_h source index i before memory hinputR
        (registers.payload.downRecord i) hbeforeCurrent
      have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
        rate rewards C_star C_h source index i before memory hinputR
      change (before.status = .unoccupied ↔
        FollowerCutoffScan.firstCutoff p rate.eta.val _ _ ≤ R[e].input.time.val) at hphase
      change (before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
        stamp.val + 1 = R[e].input.time.val ∧ memory.lastProposalRead = some
          ⟨stamp, FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[e].input.row stamp⟩)
        at htoken
      rw [hget] at hphase htoken
      have hchoicePhase := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
        cut.input.time cut.input.row before choice memory memory
        (registers.payload.downRecord i) hbeforeCurrent hphase htoken hstarted
      have hrow := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h source index
      obtain ⟨_, _, hdata⟩ := hrow
      have hsourceRow : cut.input.row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        have hd := congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
          r.input.row) hdata
        change R[e].input.row = _ at hd
        rw [hget] at hd
        exact hd
      have hunoccupied : choice.status = .unoccupied := by
        apply hchoicePhase.mpr
        rw [current_down_start, hsourceRow, hminimum]
      obtain ⟨_, accepted, _, _, _, hacceptedBefore, _, _, hretained, _, _, _⟩ :=
        ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
          (rate := rate) rewards C_star C_h source index i choice memory
          (by change (ReferenceFollowerFixedReply.actualChoice R[e] i).configuration = _
              rw [hget]; exact hactual)
          (registers.payload.downRecord i) hcurrent
      obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h source index
      have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hchain e he
      rw [hget] at hprefix
      have hacceptedLength : accepted.val < (R.take e).length := by
        simp only [List.length_take]
        exact lt_min hacceptedBefore accepted.isLt
      have hevent : ∃ q : Fin (R.take e).length,
          ReferenceAcceptedUpFollowerHistory.RetainedDown
            ((R.take e).get q) i (registers.payload.downRecord i) := by
        refine ⟨⟨accepted.val, hacceptedLength⟩, ?_⟩
        simpa only [List.get_eq_getElem, List.getElem_take] using hretained
      exact ⟨hunoccupied,
        ReferenceFirstReplacementCollectionUpOfferCut.unique_actual_retained_down_event
          hprefix i before memory hinput (registers.payload.downRecord i) hevent⟩

open ReferenceActivePhysicalStep in
private theorem collection_step_same_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection payload movingLedger movingSaved := by
  by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
    | collection outcome =>
      have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .collection payload ledger clock cutoff outcome := by
        change ReferenceActivePhysicalStep.dispatch x =
          .collection payload ledger clock cutoff outcome
        unfold ReferenceActivePhysicalStep.dispatch
        rw [hcoord]
        simp only [dite_eq_left hvalid]
        dsimp [cutoff, clock, input]
        rw [hdispatch]
        rfl
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcut
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hselection :
              (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hpost : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) := by
            simpa [hselection] using hobs
          have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights input
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights input
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          rcases hphase with hdagger | ⟨nextPayload, nextLedger, nextSaved, hnext⟩
          · left
            rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
            rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost]
            exact hdagger
          · have hpayload : nextPayload = payload := by
              rw [hnext] at hpayloadFrame
              simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hpayloadFrame
              exact hpayloadFrame
            right
            refine ⟨nextLedger, nextSaved, ?_⟩
            rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
            rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost,
              hnext, hpayload]
      | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
          have hfalse := hn
          unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
          rw [hcut] at hfalse
          simp at hfalse
      | _ =>
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
            rw [hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hselectionOut := hselection
          rw [hcut] at hselectionOut
          left
          rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
          have hfailure : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                .dispatchRejected none none := by
            simpa [hselectionOut] using hobs
          rw [hfailure]
          rfl
  · have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hvalid, hcoord]
    left
    rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
      ReferenceActivePhysicalStep.coordinatorFailure]

/-- The actual no-new-installation interval keeps the old payload in every
post-round collection state, including the horizon endpoint. The original
calendar records supply all adjacency and source identities. -/
theorem actual_cutoff_collection_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        (∀ q : Fin K.length,
          R[e + q.val]? = some (K.get q) ∧
          (K.get q).input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
              (e + q.val) ∧
          (K.get q).input.row =
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
          (K.get q).input.state = Z q.val ∧
          (K.get q).output.next = Z (q.val + 1)) ∧
        (∀ q : Fin K.length, ReferenceCollectionPhaseHistory.laterChosen (K.get q).input = false) ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ K.length →
          ∃ ledger saved, (Z j).coordinator = .collection registers.payload ledger saved
      | _ => True := by
  classical
  dsimp only
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => simp only [hcoord]
    | collection _ _ _ _ _ => simp only [hcoord]
    | dagger => simp only [hcoord]
    | invalidCollectionCutoff => simp only [hcoord]
    | live registers owned base outcome =>
      cases outcome <;> simp only [hcoord]
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      let W := (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let K := cut :: W
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      obtain ⟨he, hget⟩ := List.getElem?_eq_some_iff.mp hcut
      have hKprefix : K <+: R.drop e := by
        rw [List.drop_eq_getElem_cons he, hget]
        refine ⟨(R.drop (e + 1)).dropWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
        simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
      have hbound : ∀ q : Fin K.length, e + q.val < R.length := by
        intro q
        have h := hKprefix.length_le
        simp only [List.length_drop] at h
        omega
      have hgetK : ∀ q : Fin K.length, R[e + q.val]'(hbound q) = K.get q := by
        intro q
        have h := hKprefix.getElem q.isLt
        simpa only [List.getElem_drop, List.get_eq_getElem] using h.symm
      have houtput : ∀ q : Fin K.length, (K.get q).output.next = Z (q.val + 1) := by
        intro q
        dsimp only [Z]
        rw [List.take_succ_eq_append_getElem q.isLt]
        simp only [ReferenceCollectionSegmentExtraction.endpointState, List.foldl_append,
          List.foldl_cons, List.foldl_nil, List.get_eq_getElem]
      have hinput : ∀ q : Fin K.length, (K.get q).input.state = Z q.val := by
        intro ⟨q, hq⟩
        cases q with
        | zero => rfl
        | succ q =>
          have hprevious : q < K.length := by omega
          have hadj := ReferenceFirstReplacementCollectionFollowerPrefix.completeSuffix_adjacent
            (rate := rate) source rewards C_star C_h (e + q) (by
              have h := hbound ⟨q + 1, hq⟩
              omega)
          dsimp only at hadj
          simp only [List.get_eq_getElem] at hadj
          have hnextBound : e + q + 1 < R.length := by
            have h := hbound ⟨q + 1, hq⟩
            omega
          have hnext : R[e + q + 1]'hnextBound = K.get ⟨q + 1, hq⟩ := by
            simpa only [Nat.add_assoc] using hgetK ⟨q + 1, hq⟩
          rw [hnext, hgetK ⟨q, hprevious⟩] at hadj
          exact hadj.1.trans (houtput ⟨q, hprevious⟩)
      have hnoLater : ∀ q : Fin K.length,
          ReferenceCollectionPhaseHistory.laterChosen (K.get q).input = false := by
        intro ⟨q, hq⟩
        cases q with
        | zero =>
          change ReferenceCollectionPhaseHistory.laterChosen cut.input = false
          unfold ReferenceCollectionPhaseHistory.laterChosen
          have hprepared : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
              cut.output.preparation.coordinator := by rw [cut.output_eq]; rfl
          rw [hprepared, hcoord]
        | succ q =>
          have hqW : q < W.length := by
            have h : q + 1 < W.length + 1 := hq
            omega
          have hm : W[q] ∈ W := List.getElem_mem hqW
          have hp := List.mem_takeWhile_imp hm
          change ReferenceCollectionPhaseHistory.laterChosen W[q].input = false
          simpa only [Bool.not_eq_true', Bool.coe_iff_coe] using hp
      have hexhaust := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h source).1
      have hnotDagger : ∀ q : Fin K.length, (K.get q).output.next.coordinator ≠ .dagger := by
        intro q
        have h := (hexhaust ⟨e + q.val, hbound q⟩).2.2.2.2
        change (R[e + q.val]'(hbound q)).output.next.coordinator ≠ .dagger at h
        rw [hgetK q] at h
        exact h
      have hfirst : ∃ firstLedger firstSaved,
          (Z 1).coordinator = .collection registers.payload firstLedger firstSaved := by
        have hprepared : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
            .live registers owned base (.cutoffChosen dispatched hstart ledger
              hinitialization hledger hdomains hclock hpending hassignment selection) := by
          rw [← hcoord, cut.output_eq]
          rfl
        have hpost : cut.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
            (ReferenceActivePhysicalStep.prepare cut.input) registers.payload
            (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
            (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights := by
          rw [cut.output_eq]
          change (ReferenceActivePhysicalStep.prepare cut.input).observeCoordinator = _
          simp only [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hprepared,
            ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte, reduceCtorEq]
        have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
          (ReferenceActivePhysicalStep.prepare cut.input) registers.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights
        have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
          (ReferenceActivePhysicalStep.prepare cut.input) registers.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights
        have hnext : cut.output.next.coordinator = cut.output.coordinator.configuration := by
          rw [cut.output_eq]
          rfl
        rw [← hpost, ← hnext] at hphase hframe
        rcases hphase with hd | ⟨P, l, saved, hc⟩
        · exact (hnotDagger ⟨0, by simp only [K, List.length_cons]; omega⟩ hd).elim
        · rw [hc] at hframe
          have hP : P = registers.payload := by
            simpa only [ReferenceAssignmentPayloadPersistence.storedPayload, reduceCtorEq,
              false_or, Option.some.injEq] using hframe
          refine ⟨l, saved, ?_⟩
          rw [← houtput ⟨0, by simp only [K, List.length_cons]; omega⟩]
          change cut.output.next.coordinator = _
          rw [hc, hP]
      refine ⟨?_, hnoLater, ?_⟩
      · intro q
        have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨e + q.val, hbound q⟩
        change (R[e + q.val]'(hbound q)).input.time.val = _ at htime
        rw [hgetK q] at htime
        obtain ⟨_, _, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
          rate rewards C_star C_h source ⟨e + q.val, hbound q⟩
        have hrow := congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
          r.input.row) hrecord
        change (R[e + q.val]'(hbound q)).input.row = _ at hrow
        rw [hgetK q] at hrow
        exact ⟨(List.getElem?_eq_getElem (hbound q)).trans (congrArg some (hgetK q)),
          htime, hrow, hinput q, houtput q⟩
      · change ∀ j : ℕ, 1 ≤ j → j ≤ K.length →
          ∃ ledger saved, (Z j).coordinator = .collection registers.payload ledger saved
        intro j
        induction j with
        | zero => intro hj; omega
        | succ j ih =>
          intro hj hlen
          change j + 1 ≤ K.length at hlen
          by_cases hjzero : j = 0
          · subst j
            exact hfirst
          · obtain ⟨movingLedger, movingSaved, hcollection⟩ := ih (by omega) (by omega)
            have hjK : j < K.length := by omega
            let record := K.get ⟨j, hjK⟩
            have hrecordCoord : record.input.state.coordinator =
                .collection registers.payload movingLedger movingSaved := by
              rw [hinput ⟨j, hjK⟩]
              exact hcollection
            have hstep := collection_step_same_payload record.input registers.payload
              movingLedger movingSaved hrecordCoord (hnoLater ⟨j, hjK⟩)
            rw [← record.output_eq] at hstep
            rcases hstep with hd | ⟨l, saved, hc⟩
            · exact (hnotDagger ⟨j, hjK⟩ hd).elim
            · refine ⟨l, saved, ?_⟩
              rw [← houtput ⟨j, hjK⟩]
              exact hc

open ReferenceFirstReplacementCollectionStoppedPureUpQuota in
private theorem linked_prefix_connected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ q : Fin K.length,
      (K.get q).input.state = Z q.val ∧ (K.get q).output.next = Z (q.val + 1))
    (n : ℕ) (hn : n ≤ K.length) :
    ReferenceActivePhysicalHorizon.Connected (Z 0) (K.take n) (Z n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < K.length := by omega
    have hl := hlinks ⟨n, hlt⟩
    rw [← hl.2, List.take_succ_eq_append_getElem hlt]
    exact ReferenceActivePhysicalHorizon.Connected.append_one _ _ (ih (by omega)) hl.1

open ReferenceFirstReplacementCollectionStoppedPureUpQuota in
/-- A literal stage identity preserves the complete entries, including stamps. -/
private theorem formed_entries_eq_drop
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstage : ∀ a : Fin K.length, replyFormedAt (K.get a) i M ↔ b ≤ a.val)
    (n : ℕ) :
    formedPositiveEntries (K.take n) i M =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries ((K.take n).drop b) i := by
  induction K generalizing b n with
  | nil => simp [formedPositiveEntries, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
  | cons head tail ih =>
    cases n with
    | zero => simp [formedPositiveEntries, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
    | succ n =>
      cases b with
      | zero =>
        have hh : replyFormedAt head i M := (hstage ⟨0, by simp⟩).mpr (Nat.zero_le _)
        have ht : ∀ a : Fin tail.length, replyFormedAt (tail.get a) i M ↔ 0 ≤ a.val := by
          intro a
          simpa using hstage ⟨a.val + 1, by simp⟩
        simpa only [List.take_succ_cons, formedPositiveEntries, List.flatMap_cons,
          ite_eq_left hh, List.drop_zero,
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries] using
          congrArg (fun entries => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries head i ++ entries)
            (ih 0 ht n)
      | succ b =>
        have hh : ¬ replyFormedAt head i M := by
          have h : replyFormedAt head i M ↔ b + 1 ≤ 0 := hstage ⟨0, by simp⟩
          exact fun hh => Nat.not_succ_le_zero b (h.mp hh)
        have ht : ∀ a : Fin tail.length, replyFormedAt (tail.get a) i M ↔ b ≤ a.val := by
          intro a
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, Nat.add_le_add_iff_right]
            using hstage ⟨a.val + 1, by simp⟩
        simpa only [List.take_succ_cons, formedPositiveEntries, List.flatMap_cons,
          ite_eq_right hh, List.nil_append, List.drop_succ_cons] using ih b ht n

private theorem retained_down_eq_selected_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown r i M) :
    M = selected.view.payload.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hlogged, hdown, haccepted⟩ := hretained
  obtain ⟨_, _, actualLogged, _, _, _, hactualLogged, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  have hloggedEq : actualLogged = logged := Option.some.inj (hactualLogged.symm.trans hlogged)
  rw [hloggedEq] at hcut
  have hactual := haccepted
  rw [hcut] at hactual
  have halignment := r.output.preparation.follower_alignment i
  rw [halignment.1, halignment.2.1, halignment.2.2.1] at hactual
  have hview : r.output.preparation.coordinator.downView = some selected.view := by
    change Option.map ReferenceActivePhysicalStep.Selection.view
      r.output.preparation.coordinator.selection = some selected.view
    rw [hselected]
    rfl
  rw [hview] at hactual
  exact (ReferenceActiveDataOwnership.referenceDown_accepted_fields selected.view i
    r.input.row r.input.time _ logged logged after raw M scan registers lastService hactual).1

private theorem current_choice_output_frame
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hm : choice.lastDown = some (selected.view.payload.downRecord i))
    (hn : r.output.next.followers i = .ordinary next nextMemory) :
    next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply choice := by
  obtain ⟨actual, actualMemory, ha, _, hkeep, hchange⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology r i next nextMemory hn
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans ha)
  apply hkeep hu
  by_contra hne
  obtain ⟨logged, cut, after, raw, M, scan, registers, lastService,
    hlogged, hdown, haccepted, hsigma⟩ := hchange hne
  have hM := retained_down_eq_selected_payload r selected hselected i M
    ⟨logged, cut, after, raw, scan, registers, lastService, hlogged, hdown, haccepted⟩
  have hstart : ReferencePrelaunchFollower.acceptedStart choice =
      (selected.view.payload.downRecord i).val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hm]
  apply hne
  exact hstart.trans ((congrArg (fun word => word.val.sigma) hM).symm.trans hsigma)

private theorem executed_collection_tail_fields
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved)
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (ht : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    tail.payload = payload ∧ tail.ledger = ledger := by
  classical
  have hdispatch : (ReferenceActivePhysicalStep.prepare x).coordinator =
      ReferenceActivePhysicalStep.dispatch x := rfl
  unfold ReferenceActivePhysicalStep.dispatch at hdispatch
  rw [hstate] at hdispatch
  dsimp only at hdispatch
  split at hdispatch
  · rename_i hcut
    cases hd : CoordinatorRoundDispatch.dispatch (.collection
        (ReferenceActivePhysicalStep.collectionInput x payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved
            ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩)) with
    | collection outcome =>
      rw [hd] at hdispatch
      unfold ReferenceCollectionPhaseHistory.executedTail at ht
      dsimp only at ht
      split at ht <;> try contradiction
      rw [hdispatch] at ht
      cases outcome <;> try contradiction
      cases Option.some.inj ht
      exact ⟨rfl, rfl⟩
  · simp only [ReferenceCollectionPhaseHistory.executedTail, hdispatch] at ht
    split at ht <;> contradiction

/-- Any actual current-DOWN acceptance in this actual collection forms its
reply at the successor boundary. All later choices retain the same four reply
fields and the original bank, even when the acceptance is the last record.
The fixed-offer equation covers every retained positive of the suffix. -/
theorem actual_cutoff_retained_current_reply_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let W := (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let K := cut :: W
        let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
          cut.input.state (K.take j)
        let M := registers.payload.downRecord i
        ∀ q : Fin K.length,
          ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i M →
          ∃ (anchor : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p)
            (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)),
            (Z (q.val + 1)).followers i = .ordinary anchor memory ∧
            anchor.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid anchor ∧
            anchor.lastDown = some M ∧
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant (Z (q.val + 1)) ∧
            ((Z (q.val + 1)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
            (∀ a : Fin K.length,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M ↔
                q.val + 1 ≤ a.val) ∧
            (∀ j : ℕ,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
                (K.take j) i M =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                ((K.take j).drop (q.val + 1)) i) ∧
            (∀ a : Fin K.length, q.val + 1 ≤ a.val →
              ∃ state mem,
                (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                  .ordinary state mem ∧ state.status = .unoccupied ∧
                state.lastDown = some M ∧
                ReferenceFollowerReplyChronology.reply state =
                  ReferenceFollowerReplyChronology.reply anchor ∧
                (ReferenceActivePhysicalStep.upSenderIndex (K.get a).input = i →
                  PublicDiscreteDraws.slotDraw ((K.get a).input.row.2
                    (K.get a).input.time).1 = PublicDiscreteDraws.upSlot →
                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get a).input.row
                    ((K.get a).input.state.activations i) (K.get a).input.time state = .offer U ∧
                  ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare (K.get a).input) =
                      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))) ∧
            (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (K.drop (q.val + 1)) i,
              AffineChannelLaw.affineHash entry.sample
                (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) ∧
            (∀ a : Fin K.length, q.val + 1 ≤ a.val →
              ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                (K.get a).output.coordinator.up = some d ∧
                (d.input.selectedFollower = i → CoordinatorUpReception.receptionGate d.input →
                  ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate (K.get a) i U ∧
                  ReferenceCompleteAwaitedBatchSourceCoverage.originalUpAwaitedCallAt
                    rate (K.get a) i U ∧
                  ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt
                    rate rewards C_star C_h source i U (K.get a).input.time ∧
                  (d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) →
                    ReferenceCollectionPhaseHistory.AcceptedUp (K.get a).input i U ∧
                    ∃ ledger saved,
                      (Z (a.val + 1)).coordinator = .collection registers.payload ledger saved ∧
                      i ∉ ledger.pending)))
      | _ => True := by
  classical
  have hframes := actual_cutoff_collection_prefix rate source rewards C_star C_h e
  have hstarted := actual_cutoff_started_current_reply_origin rate source rewards C_star C_h e
  have hreplay := actual_cutoff_original_up_bank_replay rate source rewards C_star C_h e
  dsimp only at hframes hstarted hreplay ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h with hR
  simp only [← hR] at hframes hstarted hreplay
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hframes hstarted hreplay ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hframes hstarted hreplay ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hframes hstarted hreplay ⊢
      let W := (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let K := cut :: W
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let M := registers.payload.downRecord i
      obtain ⟨hrecords, hnoLater, hcollections⟩ := hframes
      obtain ⟨hcutTime, hcutoff, _, _⟩ := hstarted
      obtain ⟨_, _, _, _, _, _, _, _, hbanks⟩ := hreplay
      change (∀ a : Fin K.length,
        R[e + a.val]? = some (K.get a) ∧
        (K.get a).input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + (e + a.val) ∧
        (K.get a).input.row = source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
        (K.get a).input.state = Z a.val ∧
        (K.get a).output.next = Z (a.val + 1)) at hrecords
      change (∀ a : Fin K.length,
        ReferenceCollectionPhaseHistory.laterChosen (K.get a).input = false) at hnoLater
      change (∀ j : ℕ, 1 ≤ j → j ≤ K.length →
        ∃ ledger saved, (Z j).coordinator = .collection registers.payload ledger saved)
        at hcollections
      change (∀ j : ℕ, j ≤ K.length →
        ReferenceUpDecoderBankInvariant.upBankInvariant (Z j)) at hbanks
      have hsourceIndex : ∀ a : Fin K.length, e + a.val < R.length := by
        intro a
        exact (List.getElem?_eq_some_iff.mp (hrecords a).1).1
      have hsourceGet : ∀ a : Fin K.length,
          R[e + a.val]'(hsourceIndex a) = K.get a := by
        intro a
        exact (List.getElem?_eq_some_iff.mp (hrecords a).1).2
      have houtput : ∀ a : Fin K.length,
          ∃ state memory, (K.get a).output.next.followers i = .ordinary state memory ∧
            ActiveFollowerLifecycle.localStateDomainValid state := by
        intro a
        obtain ⟨_, _, _, state, memory, _, _, _, hd, _, _, hout⟩ :=
          ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
            (rate := rate) rewards C_star C_h source ⟨e + a.val, hsourceIndex a⟩ i
        change (R[e + a.val]'(hsourceIndex a)).output.next.followers i = _ at hout
        rw [hsourceGet a] at hout
        exact ⟨state, memory, hout, hd⟩
      intro q hretained
      have hqK : q.val < K.length := q.isLt
      obtain ⟨logged, downCut, after, raw, scan, registersAfter, lastService,
        hlogged, hdown, haccepted⟩ := hretained
      have hloggedR : ((R[e + q.val]'(hsourceIndex q)).output.followers i).downInput =
          some logged := by rw [hsourceGet q]; exact hlogged
      have hdownR : ((R[e + q.val]'(hsourceIndex q)).output.followers i).down =
          some downCut := by rw [hsourceGet q]; exact hdown
      obtain ⟨hlast, _, _, _, memory, hnextR⟩ :=
        ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
          (rate := rate) rewards C_star C_h source ⟨e + q.val, hsourceIndex q⟩ i
          logged after downCut raw M scan registersAfter lastService hloggedR hdownR haccepted
      change (R[e + q.val]'(hsourceIndex q)).output.next.followers i = _ at hnextR
      rw [hsourceGet q] at hnextR
      have hanchor : (Z (q.val + 1)).followers i = .ordinary after memory := by
        rw [← (hrecords q).2.2.2.2]
        exact hnextR
      obtain ⟨next, nextMemory, hnext, hnextDomain⟩ := houtput q
      obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hnextR.symm.trans hnext)
      have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
        (K.get q) i logged downCut after raw M scan registersAfter lastService
        hlogged hdown haccepted
      have halignment := (K.get q).output.preparation.follower_alignment i
      rw [halignment.1, halignment.2.1, halignment.2.2.1] at htransition
      have hscan := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint
        i (K.get q).input.row (K.get q).input.time _ logged after raw M scan
        registersAfter lastService htransition
      obtain ⟨_, _, _, _, _, _, hafter⟩ :=
        ActiveFollowerDownAcceptance.downTransition_accepted_checked p i
          (K.get q).input.row (K.get q).input.time _ rate logged after raw M scan
          registersAfter lastService htransition
      have hscanEndpoint : scan.endpoint = cut.input.time.val + 1 := by
        rw [hscan, current_down_start, (hrecords q).2.2.1, hcutoff]
        apply Nat.min_eq_left
        have ht := (hrecords q).2.1
        omega
      have hunoccupied : after.status = .unoccupied := by
        have ht := (hrecords q).2.1
        have hne : scan.endpoint ≠ (K.get q).input.time.val + 2 := by
          rw [hscanEndpoint]
          omega
        rw [hafter]
        exact ite_eq_right hne
      have hspan : ∀ n : ℕ, q.val + 1 ≤ n → n ≤ K.length →
          ∃ state mem, (Z n).followers i = .ordinary state mem ∧
            state.status = .unoccupied ∧
            ReferenceFollowerReplyChronology.reply state =
              ReferenceFollowerReplyChronology.reply after := by
        intro n
        induction n with
        | zero => intro h; omega
        | succ n ih =>
          intro hn hlen
          by_cases heq : n = q.val
          · subst n
            exact ⟨after, memory, hanchor, hunoccupied, rfl⟩
          · have hnK : n < K.length := by omega
            obtain ⟨state, mem, hstate, hu, hr⟩ := ih (by omega) (by omega)
            obtain ⟨movingLedger, saved, hcollection⟩ := hcollections n (by omega) (by omega)
            have hseedStart : ReferencePrelaunchFollower.acceptedStart after =
                registers.payload.sigma.val + 1 := by
              rw [ReferencePrelaunchFollower.acceptedStart, hlast]
              rfl
            have hstep := ReferenceCollectionUnoccupiedHistory.step_collection_unoccupied
              registers.payload i after hseedStart (K.get ⟨n, hnK⟩).input
              (hnoLater ⟨n, hnK⟩)
              (Or.inr ⟨movingLedger, saved, by
                rw [(hrecords ⟨n, hnK⟩).2.2.2.1]; exact hcollection⟩)
              (Or.inr ⟨state, mem, by
                rw [(hrecords ⟨n, hnK⟩).2.2.2.1]; exact hstate, hu, hr⟩)
            rw [← (K.get ⟨n, hnK⟩).output_eq] at hstep
            obtain ⟨actual, actualMemory, hactual, _⟩ := houtput ⟨n, hnK⟩
            rcases hstep.2.1 with hd | ⟨out, outMemory, ho, hou, hor⟩
            · rw [hactual] at hd
              contradiction
            · exact ⟨out, outMemory, by
                rw [← (hrecords ⟨n, hnK⟩).2.2.2.2]; exact ho, hou, hor⟩
      have hchoices : ∀ a : Fin K.length, q.val + 1 ≤ a.val →
          ∃ state mem,
            (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
              .ordinary state mem ∧ state.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid state ∧ state.lastDown = some M ∧
            ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply after := by
        intro a ha
        obtain ⟨before, mem, state, hinput, _, _, hc, hd, _⟩ :=
          ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
            (rate := rate) rewards C_star C_h source ⟨e + a.val, hsourceIndex a⟩ i
        change (ReferenceFollowerFixedReply.actualChoice (R[e + a.val]'(hsourceIndex a)) i).configuration = _
          at hc
        rw [hsourceGet a] at hc
        obtain ⟨before', mem', hi, hr, hstatus⟩ :=
          ReferenceFollowerReplyChronology.record_input_to_choice (K.get a) i state mem hc
        obtain ⟨retained, retainedMemory, hin, hu, hreply⟩ := hspan a.val ha (Nat.le_of_lt a.isLt)
        rw [(hrecords a).2.2.2.1] at hi
        obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          (hi.symm.trans hin)
        have hrall := hr.trans hreply
        have hlastChoice : state.lastDown = some M := (congrArg Prod.fst hrall).trans hlast
        exact ⟨state, mem, hc, hstatus hu, hd, hlastChoice, hrall⟩
      obtain ⟨U, hfields, hsigma, hpositive, hoffers, hequations⟩ :=
        ReferenceFirstReplacementCollectionUpOfferCut.fixed_offer_on_actual_reply_suffix
          K i (q.val + 1) after M hnextDomain hlast hchoices
      have hchain : ReferenceActivePhysicalHorizon.Connected (Z 0) K (Z K.length) := by
        have h := linked_prefix_connected K Z
          (fun a => ⟨(hrecords a).2.2.2.1, (hrecords a).2.2.2.2⟩) K.length le_rfl
        simpa only [List.take_length] using h
      have hretainedEvent : ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i M :=
        ⟨logged, downCut, after, raw, scan, registersAfter, lastService,
          hlogged, hdown, haccepted⟩
      obtain ⟨choiceQ, memoryQ, hchoiceQ, hstrictQ, _⟩ :=
        ReferenceFollowerReplyChronology.record_appliedDown_strict (K.get q) i M.val.sigma
          (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretainedEvent)
          after memory hnextR
      have hstage : ∀ a : Fin K.length,
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M ↔
            q.val + 1 ≤ a.val := by
        intro a
        constructor
        · rintro ⟨state, mem, hc, _, hm⟩
          by_contra hnot
          have haq : a.val ≤ q.val := by omega
          have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology
            hchain i a.val q.val a.isLt q.isLt haq state choiceQ mem memoryQ hc hchoiceQ).1
          have hs : ReferencePrelaunchFollower.acceptedStart state = M.val.sigma := by
            simp only [ReferencePrelaunchFollower.acceptedStart, hm]
          omega
        · intro ha
          obtain ⟨state, mem, hc, hu, _, hm, _⟩ := hchoices a ha
          exact ⟨state, mem, hc, hu, hm⟩
      have hentries : ∀ j : ℕ,
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take j) i M =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            ((K.take j).drop (q.val + 1)) i :=
        formed_entries_eq_drop K (q.val + 1) i M hstage
      have hbank := hbanks (q.val + 1) (Nat.succ_le_of_lt q.isLt)
      have hbankLength : ((Z (q.val + 1)).upDecoderBank i).pending.length <
          AffineBatchDecoder.quota p := hbank.1 i |>.1
      refine ⟨after, memory, U, hanchor, hunoccupied, hnextDomain, hlast,
        hfields, hsigma, hpositive, hbank, hbankLength, hstage, hentries, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨state, mem, hc, hu, hm, hr, ho, _⟩ := hoffers a ha
        exact ⟨state, mem, hc, hu, hm, hr, ho⟩
      · intro entry he
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hhash⟩ := hequations entry he
        exact hhash
      · intro a ha
        obtain ⟨movingLedger, saved, hcollection⟩ := hcollections a.val (by omega) (Nat.le_of_lt a.isLt)
        have hstate : (K.get a).input.state.coordinator =
            .collection registers.payload movingLedger saved := by
          rw [(hrecords a).2.2.2.1]
          exact hcollection
        obtain ⟨outLedger, outSaved, hout⟩ := hcollections (a.val + 1) (by omega) (Nat.succ_le_of_lt a.isLt)
        have hnext : (K.get a).output.next.coordinator =
            .collection registers.payload outLedger outSaved := by
          rw [(hrecords a).2.2.2.2]
          exact hout
        obtain ⟨tail, htail, _, _⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
          (K.get a).input registers.payload outLedger outSaved (by
            rw [← (K.get a).output_eq]; exact hnext)
        obtain ⟨recording, L, d, _hrecording, hstartL, _hsite, hcheck, hdiag, hdi,
          _hreception, _hnotInvalid, _hfinishData, _hdecoder, _hraw, _hparsed, _hlocal,
          hexpected, _hmatch, _hbank, _htime, _hsample, _hobs, _hwrong, hmatching⟩ :=
          ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
            (K.get a) registers.payload movingLedger saved tail hstate htail
            (by rw [hnext]; exact fun h => nomatch h)
        refine ⟨d, hdiag, ?_⟩
        intro hi hgate
        have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
          (K.get a) d hdiag
        obtain ⟨_, _, _hL, _, _, _, hsender, _, hslot, _, _, _, _, _⟩ := hfields
        have hledger : d.input.ledger = L := by rw [hdi]; rfl
        have hcheckD : CoordinatorUpReception.receptionInputCheck d.input = true := by
          rw [hdi]; exact hcheck
        have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex (K.get a).input = i :=
          hsender.symm.trans hi
        have hslotUp : PublicDiscreteDraws.slotDraw
            ((K.get a).input.row.2 (K.get a).input.time).1 = PublicDiscreteDraws.upSlot :=
          hslot.symm.trans hgate.2.1
        obtain ⟨_, _, _, _, _, _, ho, _⟩ := hoffers a ha
        have hword := (ho hsenderIndex hslotUp).2
        have hbirth := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
          rate rewards C_star C_h source ⟨e + a.val, hsourceIndex a⟩
        dsimp only at hbirth
        simp only [← hR] at hbirth
        rw [hsourceGet a, hstate] at hbirth
        have hsigmaL : L.sigma = registers.payload.sigma.val + 1 := by
          rw [ReferenceActivePhysicalStep.collection_started_candidate tail.ledger L
            (K.get a).input.time
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstartL]
          change tail.ledger.sigma = _
          rw [(executed_collection_tail_fields (K.get a).input registers.payload
            movingLedger saved tail hstate htail).2]
          exact hbirth.2.2.1
        have hwordSigma : U.val.sigma = d.input.ledger.sigma := by
          rw [hledger, hsigmaL, hsigma]
          rfl
        have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheckD
        have hpending : i ∈ d.input.ledger.pending := hi ▸ hgate.2.2
        have haccept : CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true := by
          simp only [CoordinatorCollectionLedger.acceptUpCheck, hdomain.2.2.2.2.1,
            hpending, hwordSigma, decide_true, Bool.true_and]
        have haw : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate (K.get a) i U :=
          ⟨d, hdiag, hi, hcheckD, hgate, hexpected.trans hword, haccept⟩
        have hordinary := ReferenceCompleteAwaitedBatchSourceCoverage.originalUpAwaitedCallAt_of_physical
          rate (K.get a) i U
          (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt_of_awaitedUpAt (K.get a) i U haw)
        have htime := (hrecords a).2.1
        have hlaunchLE : ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h ≤ (K.get a).input.time.val := by omega
        have hcalendarIndex : (K.get a).input.time.val -
            ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
              e + a.val := by omega
        have hactualRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h (K.get a).input.time source = some (K.get a) := by
          unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
          rw [ite_eq_left hlaunchLE, hcalendarIndex, ← hR]
          exact (hrecords a).1
        refine ⟨haw, hordinary, ?_, ?_⟩
        · rw [ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt, hactualRecord]
          exact hordinary
        · intro hrawWord
          have hacceptL : CoordinatorCollectionLedger.acceptUpCheck L
              (ReferenceActivePhysicalStep.upSenderIndex (K.get a).input) U = true := by
            rw [hsenderIndex, ← hledger]
            exact haccept
          obtain ⟨_, _, _, _, _, decoded, bank, _, haccepted⟩ :=
            hmatching U hrawWord (hexpected.trans hword) hacceptL
          rw [hsenderIndex] at haccepted
          have hlabel : ReferenceCollectionPhaseHistory.acceptedLabel (K.get a).input = some i := by
            obtain ⟨acceptedTail, rec, started, decoded, acceptedBank,
              ht, hr, hs, hreceive, _, hiAccepted⟩ := haccepted
            simp only [ReferenceCollectionPhaseHistory.acceptedLabel,
              ReferenceCollectionPhaseHistory.Tail.reception, ht, Option.bind_some,
              hr, hs, hreceive, ← hiAccepted]
          obtain ⟨_, _, hpendingOut, _⟩ := ReferenceCollectionPhaseHistory.step_collection_frame
            (K.get a).input registers.payload outLedger outSaved (by
              rw [← (K.get a).output_eq]; exact hnext)
          refine ⟨haccepted, outLedger, outSaved, hout, ?_⟩
          rw [hpendingOut, hlabel]
          exact Finset.notMem_erase i _

/-- If this actual cutoff START already retains the current DOWN, formation
is boundary zero. Its old physical acceptance and fixed offer are derived from
the same source, while the entire original decoder bank remains at `Z 0`. -/
theorem actual_cutoff_inherited_current_reply_suffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        match (ReferenceFollowerFixedReply.actualChoice cut i).configuration with
        | .dagger => True
        | .ordinary anchor _memory =>
          anchor.lastDown = some (registers.payload.downRecord i) →
          anchor.status = .unoccupied ∧
          ActiveFollowerLifecycle.localStateDomainValid anchor ∧
          ∃ U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta),
            U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
            U.val.sigma = (registers.payload.downRecord i).val.sigma ∧ 0 < U.val.sigma ∧
            ReferenceUpDecoderBankInvariant.upBankInvariant cut.input.state ∧
            (cut.input.state.upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
            (∀ a : Fin K.length, ∃ state mem,
              (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                .ordinary state mem ∧ state.status = .unoccupied ∧
              state.lastDown = some (registers.payload.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
              (ReferenceActivePhysicalStep.upSenderIndex (K.get a).input = i →
                PublicDiscreteDraws.slotDraw ((K.get a).input.row.2
                  (K.get a).input.time).1 = PublicDiscreteDraws.upSlot →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get a).input.row
                  ((K.get a).input.state.activations i) (K.get a).input.time state = .offer U ∧
                ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare (K.get a).input) =
                  some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))) ∧
            (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries K i,
              AffineChannelLaw.affineHash entry.sample
                (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) ∧
            ∀ j : ℕ,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
                (K.take j) i (registers.payload.downRecord i) =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.take j) i
      | _ => True := by
  classical
  have hframes := actual_cutoff_collection_prefix rate source rewards C_star C_h e
  have hstarted := actual_cutoff_started_current_reply_origin rate source rewards C_star C_h e
  have hreplay := actual_cutoff_original_up_bank_replay rate source rewards C_star C_h e
  dsimp only at hframes hstarted hreplay ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h with hR
  simp only [← hR] at hframes hstarted hreplay
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hframes hstarted hreplay ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hframes hstarted hreplay ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hframes hstarted hreplay ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let M := registers.payload.downRecord i
      obtain ⟨hrecords, hnoLater, hcollections⟩ := hframes
      change (∀ a : Fin K.length,
        R[e + a.val]? = some (K.get a) ∧
        (K.get a).input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + (e + a.val) ∧
        (K.get a).input.row = source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
        (K.get a).input.state = Z a.val ∧
        (K.get a).output.next = Z (a.val + 1)) at hrecords
      change (∀ a : Fin K.length,
        ReferenceCollectionPhaseHistory.laterChosen (K.get a).input = false) at hnoLater
      change (∀ j : ℕ, 1 ≤ j → j ≤ K.length →
        ∃ ledger saved, (Z j).coordinator = .collection registers.payload ledger saved)
        at hcollections
      obtain ⟨_, _, _, hstarts⟩ := hstarted
      obtain ⟨before, choice, mem, _, _, _, hc, hd, hcurrentChoice⟩ := hstarts i
      cases hanchorChoice : (ReferenceFollowerFixedReply.actualChoice cut i).configuration with
      | dagger => trivial
      | ordinary anchor memory =>
        obtain ⟨heq, hmem⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          (hc.symm.trans hanchorChoice)
        subst choice
        subst mem
        intro hcurrent
        have hu := (hcurrentChoice hcurrent).1
        have hsourceIndex : ∀ a : Fin K.length, e + a.val < R.length := by
          intro a
          exact (List.getElem?_eq_some_iff.mp (hrecords a).1).1
        have hsourceGet : ∀ a : Fin K.length,
            R[e + a.val]'(hsourceIndex a) = K.get a := by
          intro a
          exact (List.getElem?_eq_some_iff.mp (hrecords a).1).2
        have houtput : ∀ a : Fin K.length,
            ∃ state memory, (K.get a).output.next.followers i = .ordinary state memory ∧
              ActiveFollowerLifecycle.localStateDomainValid state := by
          intro a
          obtain ⟨_, _, _, state, mem, _, _, _, hd, _, _, hout⟩ :=
            ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
              (rate := rate) rewards C_star C_h source ⟨e + a.val, hsourceIndex a⟩ i
          change (R[e + a.val]'(hsourceIndex a)).output.next.followers i = _ at hout
          rw [hsourceGet a] at hout
          exact ⟨state, mem, hout, hd⟩
        have hzero : 0 < K.length := by simp only [K, List.length_cons]; omega
        obtain ⟨next, nextMemory, hnext, _⟩ := houtput ⟨0, hzero⟩
        have he : e < R.length := by
          simpa only [Nat.add_zero] using hsourceIndex ⟨0, hzero⟩
        have hexhaust := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
          rate rewards C_star C_h source).1 ⟨e, he⟩
        have hselected : cut.output.preparation.coordinator.selection ≠ none := by
          have h := hexhaust.2.1
          have hget := hsourceGet ⟨0, hzero⟩
          change R[e]'he = cut at hget
          change (R[e]'he).output.preparation.coordinator.selection ≠ none at h
          rw [hget] at h
          exact h
        obtain ⟨selected, hs⟩ := Option.ne_none_iff_exists'.mp hselected
        have hp : selected.view.payload = registers.payload := by
          have hm : cut.output.preparation.coordinator.selection.map
              (fun s => s.view.payload) = some registers.payload := by
            rw [hcoord]
            simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte, Option.map_some]
          rw [hs] at hm
          exact Option.some.inj hm
        have hnextFrame := current_choice_output_frame cut selected hs i anchor next
          memory nextMemory hanchorChoice hu (by rw [hp]; exact hcurrent) hnext
        have hfirst : (Z 1).followers i = .ordinary next nextMemory := hnext
        have hspan : ∀ n : ℕ, 1 ≤ n → n ≤ K.length →
            ∃ state mem, (Z n).followers i = .ordinary state mem ∧
              state.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor := by
          intro n
          induction n with
          | zero => intro h; omega
          | succ n ih =>
            intro hn hlen
            by_cases hnzero : n = 0
            · subst n
              exact ⟨next, nextMemory, hfirst, hnextFrame⟩
            · have hnK : n < K.length := by omega
              obtain ⟨state, mem, hstate, hsu, hr⟩ := ih (by omega) (by omega)
              obtain ⟨movingLedger, saved, hcollection⟩ := hcollections n (by omega) (by omega)
              have hseedStart : ReferencePrelaunchFollower.acceptedStart anchor =
                  registers.payload.sigma.val + 1 := by
                rw [ReferencePrelaunchFollower.acceptedStart, hcurrent]
                rfl
              have hstep := ReferenceCollectionUnoccupiedHistory.step_collection_unoccupied
                registers.payload i anchor hseedStart (K.get ⟨n, hnK⟩).input
                (hnoLater ⟨n, hnK⟩)
                (Or.inr ⟨movingLedger, saved, by
                  rw [(hrecords ⟨n, hnK⟩).2.2.2.1]; exact hcollection⟩)
                (Or.inr ⟨state, mem, by
                  rw [(hrecords ⟨n, hnK⟩).2.2.2.1]; exact hstate, hsu, hr⟩)
              rw [← (K.get ⟨n, hnK⟩).output_eq] at hstep
              obtain ⟨actual, actualMemory, hactual, _⟩ := houtput ⟨n, hnK⟩
              rcases hstep.2.1 with hdagger | ⟨out, outMemory, ho, hou, hor⟩
              · rw [hactual] at hdagger
                contradiction
              · exact ⟨out, outMemory, by
                  rw [← (hrecords ⟨n, hnK⟩).2.2.2.2]; exact ho, hou, hor⟩
        have hchoices : ∀ a : Fin K.length, 0 ≤ a.val →
            ∃ state mem,
              (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                .ordinary state mem ∧ state.status = .unoccupied ∧
              ActiveFollowerLifecycle.localStateDomainValid state ∧ state.lastDown = some M ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor := by
          intro a _
          by_cases hazero : a.val = 0
          · have ha : K.get a = cut := by simp only [List.get_eq_getElem, hazero, K, List.getElem_cons_zero]
            exact ⟨anchor, memory, ha ▸ hanchorChoice, hu, hd, hcurrent, rfl⟩
          · obtain ⟨_, mem, state, _, _, _, hc, hdomain, _⟩ :=
              ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
                (rate := rate) rewards C_star C_h source ⟨e + a.val, hsourceIndex a⟩ i
            change (ReferenceFollowerFixedReply.actualChoice (R[e + a.val]'(hsourceIndex a)) i).configuration = _ at hc
            rw [hsourceGet a] at hc
            obtain ⟨old, oldMemory, hi, hr, hstatus⟩ :=
              ReferenceFollowerReplyChronology.record_input_to_choice (K.get a) i state mem hc
            obtain ⟨retained, retainedMemory, hin, hsu, hreply⟩ := hspan a.val (by omega) (Nat.le_of_lt a.isLt)
            rw [(hrecords a).2.2.2.1] at hi
            obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hi.symm.trans hin)
            have hrall := hr.trans hreply
            exact ⟨state, mem, hc, hstatus hsu, hdomain,
              (congrArg Prod.fst hrall).trans hcurrent, hrall⟩
        obtain ⟨U, hfields, hsigma, hpositive, hoffers, hequations⟩ :=
          ReferenceFirstReplacementCollectionUpOfferCut.fixed_offer_on_actual_reply_suffix
            K i 0 anchor M hd hcurrent hchoices
        obtain ⟨_, _, _, _, _, _, _, _, hbanks⟩ := hreplay
        have hbank : ReferenceUpDecoderBankInvariant.upBankInvariant cut.input.state := hbanks 0 (Nat.zero_le _)
        refine ⟨hu, hd, U, hfields, hsigma, hpositive, hbank, (hbank.1 i).1, ?_, ?_, ?_⟩
        · intro a
          obtain ⟨state, mem, hc, hsu, hm, hr, ho, _⟩ := hoffers a (Nat.zero_le _)
          exact ⟨state, mem, hc, hsu, hm, hr, ho⟩
        · intro entry he
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hhash⟩ := hequations entry (by simpa only [List.drop_zero] using he)
          exact hhash
        · intro j
          have hstage : ∀ a : Fin K.length,
              ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M ↔ 0 ≤ a.val := by
            intro a
            constructor
            · intro _; exact Nat.zero_le _
            · intro _
              obtain ⟨state, mem, hc, hsu, _, hm, _⟩ := hchoices a (Nat.zero_le _)
              exact ⟨state, mem, hc, hsu, hm⟩
          simpa only [List.drop_zero] using formed_entries_eq_drop K 0 i M hstage j

/-- These are exhaustive actual formation alternatives. If START has not
formed the current reply and there is no retained current acceptance anywhere
in this interval, every existing formed-positive prefix is literally empty. -/
theorem actual_cutoff_reply_formation_exhaustion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let M := registers.payload.downRecord i
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt cut i M ∨
          (∃ q : Fin K.length,
            ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i M ∧
            ∀ a : Fin K.length, a.val < q.val →
              ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M) ∨
          (∀ a : Fin K.length,
            ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M) ∧
          (∀ j : ℕ,
            ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
              (K.take j) i M = [])
      | _ => True := by
  classical
  have hframes := actual_cutoff_collection_prefix rate source rewards C_star C_h e
  have hstarted := actual_cutoff_started_current_reply_origin rate source rewards C_star C_h e
  dsimp only at hframes hstarted ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h with hR
  simp only [← hR] at hframes hstarted
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hframes hstarted ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hframes hstarted ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hframes hstarted ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let M := registers.payload.downRecord i
      obtain ⟨hrecords, _, _⟩ := hframes
      change (∀ a : Fin K.length,
        R[e + a.val]? = some (K.get a) ∧
        (K.get a).input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + (e + a.val) ∧
        (K.get a).input.row = source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
        (K.get a).input.state = Z a.val ∧
        (K.get a).output.next = Z (a.val + 1)) at hrecords
      by_cases hformed : ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt cut i M
      · exact Or.inl hformed
      · right
        by_cases hevent : ∃ q : Fin K.length,
            ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i M
        · obtain ⟨q, hq, hfirst⟩ :=
            ReferenceFirstReplacementCollectionUpOfferCut.least_actual_retained_down_event K i M hevent
          exact Or.inl ⟨q, hq, hfirst⟩
        · right
          obtain ⟨_, _, _, hstarts⟩ := hstarted
          obtain ⟨before, choice, memory, hinput, _, hstartChoice, hchoice, _, hcurrent⟩ := hstarts i
          have hbeforeNot : before.lastDown ≠ some M := by
            intro hm
            have hframe := ActiveFollowerLifecycle.startRound_frame
              rate.eta cut.input.time before choice memory memory hstartChoice
            have hchoiceCurrent := hframe.1.trans hm
            exact hformed ⟨choice, memory, hchoice, (hcurrent hchoiceCurrent).1, hchoiceCurrent⟩
          have hnone : ∀ a : Fin K.length,
              ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M := by
            intro a hformedA
            obtain ⟨state, mem, hc, _, hm⟩ := hformedA
            obtain ⟨old, oldMemory, hi, hr, _⟩ :=
              ReferenceFollowerReplyChronology.record_input_to_choice (K.get a) i state mem hc
            have hlastOld : old.lastDown = some M := (congrArg Prod.fst hr).symm.trans hm
            have hchain := linked_prefix_connected K Z
              (fun a => ⟨(hrecords a).2.2.2.1, (hrecords a).2.2.2.2⟩)
              a.val (Nat.le_of_lt a.isLt)
            change ReferenceActivePhysicalHorizon.Connected cut.input.state (K.take a.val) (Z a.val) at hchain
            rw [← (hrecords a).2.2.2.1] at hchain
            rcases ReferenceFirstReplacementCollectionUpOfferCut.connected_endpoint_current_down_has_actual_origin
                hchain i before memory old oldMemory hinput hi M hlastOld with
              hinherited | ⟨r, hr, hretained⟩
            · exact hbeforeNot hinherited
            · have hrK : r ∈ K := List.mem_of_mem_take hr
              obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hrK
              apply hevent
              refine ⟨⟨q, hq⟩, ?_⟩
              simpa only [List.get_eq_getElem, hget] using hretained
          refine ⟨hnone, ?_⟩
          intro j
          unfold ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
          apply List.flatMap_eq_nil_iff.mpr
          intro r hr
          have hrK : r ∈ K := List.mem_of_mem_take hr
          obtain ⟨a, ha, hget⟩ := List.mem_iff_getElem.mp hrK
          have hnot : ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i M := by
            simpa only [List.get_eq_getElem, hget] using hnone ⟨a, ha⟩
          exact ite_eq_right hnot

end Bandits.Support.ReferenceOriginalCollectionReplyFormationChronology

end
