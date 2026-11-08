/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage
public import Bandits.Support.ReferenceGeneratedUpFalseDiagnosticCut
public import Bandits.Support.ReferenceAcceptedUpFollowerHistory
public import Bandits.Support.ReferenceCollectionUpReceiverLocal

/-!
# Ordinary terminal UP stale-candidate exclusion

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-284,327-348,355-361`,
and `sources/zip4/manuscript/08_main_theorem.tex:29-42`.

These internal results concern the actual original-source execution. The
terminal follower's ordinary branch is explicit. They do not assert full
stale-batch exclusion, an exceptional-event inclusion, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceAssignmentPayloadChronology
open ReferenceFollowerFixedReply
open ReferenceFollowerReplyChronology
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound
open ReferenceGeneratedUpBatchPrefixEvent
open ReferenceGeneratedUpPrefixPositiveHalf
open ReferenceGeneratedUpSourceCalendar

namespace Bandits.Support.ReferenceGeneratedUpOrdinaryStaleExclusion

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem down_accepted_word
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
      .accepted before after raw M scan registers lastService) :
    ReferenceDownReception.expectedDownFlatWord view i row t = raw ∧
      ReferenceDownReception.ordinaryParse p rate raw = some M ∧ M.val.sigma ≤ t.val + 1 := by
  classical
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            next hmatches =>
              dsimp only at h
              split at h
              · cases h
              next message hparsed =>
                split at h
                next haccepted =>
                  split at h
                  · cases h
                  · cases h
                    exact ⟨hmatches.symm, hparsed, haccepted.2⟩
                · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

private theorem next_payload_eq_selected
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

private theorem record_start_cases
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ before memory, record.input.state.followers i = .ordinary before memory ∧
      (acceptedStart next = acceptedStart before ∨
        (acceptedStart next ≤ record.input.time.val + 1 ∧
          ∃ selected : Selection record.input,
            record.output.preparation.coordinator.selection = some selected ∧
            acceptedStart next = selected.view.payload.sigma.val + 1)) := by
  classical
  rcases record with ⟨input, output, ho⟩
  cases ho
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration = _ at hout
  obtain ⟨choice, choiceMemory, post, hc, hr, hf, _, _⟩ :=
    finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  obtain ⟨before, memory, hb, hreply, _⟩ :=
    record_input_to_choice (actualStepRecord input) i choice choiceMemory hc
  have hs := acceptedStart_eq_of_reply_eq hreply
  have hfinish := acceptedStart_eq_of_reply_eq
    (releaseAndFinish_frame _ _ _ _ choice post next choiceMemory nextMemory hf).1
  have halign := (prepare input).follower_alignment i
  simp only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] at hr
  refine ⟨before, memory, hb, ?_⟩
  rcases recordFollower_ordinary_inversion _ _ _ _ _ _ _ _ choice post hr with
    ⟨hlast, _⟩ | ⟨logged, cut, raw, M, scan, registers, lastService,
      _, _, hcut, haccepted, _, hlast⟩
  · left
    rw [hfinish, acceptedStart, hlast]
    exact hs
  · subst cut
    obtain ⟨hword, hparse, htime⟩ := down_accepted_word _ _ _ _ _ _ _ _ _ _ _ _ haccepted
    have hstart : acceptedStart next = M.val.sigma := by
      rw [hfinish, acceptedStart, hlast]
    right
    refine ⟨hstart ▸ htime, ?_⟩
    cases hselected : (prepare input).coordinator.selection with
    | none =>
        have hraw : raw = none := by
          simpa only [DispatchCut.downView, hselected, Option.map_none,
            ReferenceDownReception.expectedDownFlatWord] using hword.symm
        simp only [hraw, ReferenceDownReception.ordinaryParse,
          OrdinaryMessageCodec.parseDown] at hparse
        cases hparse
    | some selected =>
        have hword' : ReferenceDownReception.expectedDownFlatWord
            (some selected.view) i input.row input.time = raw := by
          simpa only [DispatchCut.downView, hselected, Option.map_some] using hword
        have hsourceWord := hword'
        simp only [ReferenceDownReception.expectedDownFlatWord] at hword'
        split at hword'
        next hbranch =>
          have hactual := actualSelection_expectedDownFlatWord
            (actualStepRecord input) selected hselected i hbranch.2
          have hraw : raw = some (CoordinatorLocalArmChoice.storedDownFlatWord
              selected.view.payload i) := hsourceWord.symm.trans hactual.1
          have hencoded : M = selected.view.payload.downRecord i := by
            rw [hraw] at hparse
            change OrdinaryMessageCodec.parseDown (codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta)).symm
                ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta))
                  (OrdinaryMessageCodec.encodeDown (codecParams p rate.eta)
                    (selected.view.payload.downRecord i))))) = some M at hparse
            rw [Equiv.symm_apply_apply, OrdinaryMessageCodec.parseDown_encode] at hparse
            exact (Option.some.inj hparse).symm
          refine ⟨selected, hselected, ?_⟩
          rw [hstart, hencoded]
          exact congrArg OrdinaryMessageCodec.DownFields.sigma
            (selected.view.payload.downRecord_fields i)
        next hbranch =>
          rw [← hword'] at hparse
          simp only [ReferenceDownReception.ordinaryParse,
            OrdinaryMessageCodec.parseDown] at hparse
          cases hparse

private theorem run_start_bounds
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hmode : allActiveAtStart initial s)
    (hfirst : initial.coordinator = .first)
    (hzero : ∀ i state memory, initial.followers i = .ordinary state memory →
      acceptedStart state = 0) :
    let final := (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode).finalState
    (∀ i state memory, final.followers i = .ordinary state memory →
      acceptedStart state ≤ s + count) ∧
    (∀ payload, storedPayload final.coordinator = some payload →
      ∀ i state memory, final.followers i = .ordinary state memory →
        acceptedStart state ≤ payload.sigma.val + 1) := by
  induction count with
  | zero =>
      dsimp only
      constructor
      · intro i state memory hout
        have hz := hzero i state memory hout
        omega
      · intro payload hpayload
        change storedPayload initial.coordinator = some payload at hpayload
        simp only [hfirst, storedPayload_first] at hpayload
        cases hpayload
  | succ n ih =>
      dsimp only
      let record := actualRunRecordAt initial rows J rewards s n hspan hmode
      have hfinal := run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards s n hspan hmode
      rw [hfinal]
      have htime : record.input.time.val = s + n := rfl
      have hb := ih (by omega)
      have hclassification := actualStep_payload_classification record.input
      constructor
      · intro i state memory hout
        obtain ⟨before, beforeMemory, hbefore, hcase⟩ := record_start_cases record i state memory hout
        rcases hcase with heq | ⟨hbound, _⟩
        · rw [heq]
          have hbound := hb.1 i before beforeMemory hbefore
          omega
        · rw [htime] at hbound
          omega
      · intro payload hpayload i state memory hout
        obtain ⟨before, beforeMemory, hbefore, hcase⟩ := record_start_cases record i state memory hout
        rcases hcase with heq | ⟨_, selected, hselected, hstart⟩
        · rw [heq]
          rcases hclassification with hnone | ⟨old, hold, hretained⟩ | ⟨fresh, hborn, hfresh⟩
          · change storedPayload record.output.next.coordinator = none at hnone
            rw [hpayload] at hnone
            cases hnone
          · have he : old = payload := Option.some.inj (hretained.symm.trans hpayload)
            subst old
            exact hb.2 payload hold i before beforeMemory hbefore
          · have he : fresh = payload := Option.some.inj (hfresh.symm.trans hpayload)
            subst fresh
            have hbornTime := installationBirth_time_eq (actualStepRecord record.input) payload hborn
            have hbound := hb.1 i before beforeMemory hbefore
            change payload.sigma.val = record.input.time.val at hbornTime
            omega
        · have hnext : storedPayload (step record.input).next.coordinator = some payload := hpayload
          have hselectedPayload := next_payload_eq_selected record.input payload hnext
          change (prepare record.input).coordinator.selection.map
            (fun selected => selected.view.payload) = some payload at hselectedPayload
          change (prepare record.input).coordinator.selection = some selected at hselected
          rw [hselected, Option.map_some] at hselectedPayload
          have he := Option.some.inj hselectedPayload
          rw [hstart, he]

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

private theorem site_payload_sigma
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some L) :
    ∃ payload, storedPayload x.state.coordinator = some payload ∧
      L.sigma = payload.sigma.val + 1 := by
  classical
  have hn : (prepare x).coordinator.selection ≠ none := by
    intro hn
    simp only [ReferenceCoordinatorUpPhysicalCall.siteLedger?, dite_eq_left hn] at hsite
    cases hsite
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
              refine ⟨registers.payload, by simp only [storedPayload_live], ?_⟩
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
                refine ⟨payload, by simp only [storedPayload_collection], ?_⟩
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

private theorem original_seed_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    input.val.1.coordinator = .first ∧
      ∀ j state memory, input.val.1.followers j = .ordinary state memory →
        state.lastDown = none ∧ acceptedStart state = 0 := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hlaunch := originalSourceRunInput_launch rewards C_star C_h q t s hs control0 i z
  obtain ⟨active, hchar, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate z.1 rewards C_star C_h z.property.2.1
  have he : active = input.val.1 := Option.some.inj (hchar.1.symm.trans hlaunch)
  refine ⟨he ▸ hchar.2.1, ?_⟩
  obtain ⟨seed, hseed, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate z.1 rewards C_star C_h z.property.2.1
  have hseedEq : seed = input.val.1 := Option.some.inj (hseed.symm.trans hlaunch)
  intro j state memory hstate
  have hfj := hfields j
  rw [hseedEq, hstate] at hfj
  have heq := LocalConfiguration.ordinary.inj hfj.1
  exact heq.1 ▸ ⟨hfj.2.1, hfj.2.2.1⟩

private theorem original_choice_start_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input) = some L)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((prepare (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input).followers.followers i).configuration =
        .ordinary choice memory) :
    acceptedStart choice ≤ L.sigma := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  obtain ⟨hfirst, hzero⟩ := original_seed_fields rewards C_star C_h q t s hs control0 i z
  have hbound := run_start_bounds input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s (t.val - s) (by omega) input.property hfirst
    (fun j state memory h => (hzero j state memory h).2)
  obtain ⟨payload, hstored, hsigma⟩ := site_payload_sigma current.input L hsite
  have hchoice : (actualChoice current i).configuration = .ordinary choice memory := hc
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    record_input_to_choice current i choice memory hchoice
  have hstart := acceptedStart_eq_of_reply_eq hreply
  rw [hstart, hsigma]
  exact hbound.2 payload hstored i before beforeMemory hbefore

private theorem record_time_index
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records) :
    s ≤ record.input.time.val ∧
      (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records[
        record.input.time.val - s]? = some record := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hn
  have hlen := run_record_count input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s count hspan input.property
  have hnCount : n < count := by
    change n < (ReferenceActivePhysicalHorizon.run _ _ _ _ _ _ _ _).records.length at hlt
    omega
  have htimes := run_time_values input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s count hspan input.property
  have he := congrArg (fun xs : List ℕ => xs[n]?) htimes
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hn
  rw [List.getElem?_map, hn] at he
  have htime : record.input.time.val = s + n := by
    simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hnCount, ite_true, Nat.one_mul,
      Option.map_some, Option.some.injEq] using he
  constructor
  · omega
  · simpa only [ReferenceActiveHorizonMeasurability.runOfInput, htime, Nat.add_sub_cancel_left] using hn

private theorem original_current_get
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records[
      t.val - s]? = some (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z) := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let n := t.val - s + 1
  obtain ⟨suffix, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n (p.T - s - n)
      (by omega) input.property
  have hcount : n + (p.T - s - n) = p.T - s := by omega
  simp only [hcount] at hsplit
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
  rw [hsplit, List.getElem?_append_left (by
    rw [run_record_count]; dsimp only [n]; omega)]
  rw [run_successor_actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 s (t.val - s) (by omega) input.property,
    List.getElem?_append_right (by rw [run_record_count])]
  simp only [run_record_count, Nat.sub_self, List.getElem?_cons_zero]
  have hentry : (⟨s + (t.val - s), by omega, by omega⟩ : CalendarEntry p s) =
      ⟨t.val, hs, t.isLt⟩ := Subtype.ext (Nat.add_sub_of_le hs)
  have he := congrArg (fun entry : CalendarEntry p s =>
    actualStepRecord (roundInputAt input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s input.property
      (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
        input.val.2.2.2 s (t.val - s) (by omega) input.property) entry)) hentry
  exact congrArg some he

private theorem channel_up_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p (x.row.2 x.time).1 = some (1, i)) :
    PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
      upSenderIndex x = i := by
  by_cases hd : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot
  · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hd] at h
    have hn : (0 : Fin 2) ≠ 1 := by decide
    exact (hn (congrArg Prod.fst (Option.some.inj h))).elim
  · by_cases hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot
    · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hu] at h
      exact ⟨hu, (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x).trans
        (congrArg Prod.snd (Option.some.inj h))⟩
    · simp only [ReferenceSelectedAffinePairLaw.selectedChannel,
        ReferenceSelectedAffinePairLaw.channelFromDraws, hd, hu, ite_false] at h
      cases h

private theorem original_current_channel
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let current := originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z
    ReferenceSelectedAffinePairLaw.selectedChannel p (current.input.row.2 current.input.time).1 =
      some (1, i) := by
  have hf := originalSourceCurrentInput_original_fields rewards C_star C_h q t s hs control0 i z
  have hc := (ReferenceSelectedAffinePairLaw.selector_eq_iff p q t (1, i) z.1).mp z.property.1
  change ReferenceSelectedAffinePairLaw.selectedChannel p
    (((originalSourceCurrentInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z).rows
      (originalSourceCurrentInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z).selected).2
      (originalSourceCurrentInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z).time).1 = _
  rw [hf.1, hf.2.1, hf.2.2.1]
  exact hc.2

private theorem ordinary_selected_offer
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (actualChoice record i).configuration = .ordinary state memory)
    (hu : state.status = .unoccupied)
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (record.input.row.2 record.input.time).1 = some (1, i)) :
    ∃ offered, ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state = .offer offered := by
  classical
  have hprep : actualChoice record i = DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i) := record.output.preparation.followers.followers_eq i
  have hspec := ReferenceUpPhysicalHashRule.prepare_arm_spec i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)
  simp only [← hprep, hc] at hspec
  obtain ⟨hslot, hsender⟩ := channel_up_fields record.input i hchannel
  have hselected : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time ∧ state.status = .unoccupied :=
    ⟨⟨record.input.active i, hslot,
      (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw record.input).symm.trans hsender⟩, hu⟩
  cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state with
  | failure => simp only [hoff] at hspec
  | noOffer =>
      by_cases hdomain : ActiveFollowerQueueOperation.stateInputDomain state
      · by_cases hadm : OrdinaryMessageCodec.upAdmissible (codecParams p rate.eta)
            (ActiveFollowerQueueOperation.upOfferFields state)
        · simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_left hdomain,
            dite_eq_left hselected, dite_eq_left hadm] at hoff
          cases hoff
        · simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_left hdomain,
            dite_eq_left hselected, dite_eq_right hadm] at hoff
          cases hoff
      · simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_right hdomain] at hoff
        cases hoff
  | offer offered => exact ⟨offered, rfl⟩

private theorem repeated_word_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (L : Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger?
      (x := (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input) = some L)
    (M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta))
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hparse : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some v) = some M)
    (hsigma : M.val.sigma = L.sigma)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).records)
    (hle : record.input.time.val ≤ t.val)
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (record.input.row.2 record.input.time).1 = some (1, i))
    (hsent : ReferenceActiveAffinePositiveTest.upSent record.input = some v)
    (ho : ((prepare (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input).followers.followers i).configuration ≠ .dagger) :
    ReferenceActiveAffinePositiveTest.upSent (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input = some v := by
  classical
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hcurrent := original_current_get rewards C_star C_h q t s hs control0 i z
  obtain ⟨hstart, hrecord⟩ := record_time_index s (p.T - s) (by omega) input record hmem
  obtain ⟨ha, hgetA⟩ := List.getElem?_eq_some_iff.mp hrecord
  obtain ⟨hb, hgetB⟩ := List.getElem?_eq_some_iff.mp hcurrent
  let a : Fin full.records.length := ⟨record.input.time.val - s, ha⟩
  let b : Fin full.records.length := ⟨t.val - s, hb⟩
  have hab : a.val ≤ b.val := Nat.sub_le_sub_right hle s
  have hsender := (channel_up_fields record.input i hchannel).2
  have hcurrentChannel := original_current_channel rewards C_star C_h q t s hs control0 i z
  have hcurrentSender := (channel_up_fields current.input i hcurrentChannel).2
  rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration, hsender] at hsent
  cases hleft : ((prepare record.input).followers.followers i).configuration with
  | dagger => simp only [hleft] at hsent; cases hsent
  | ordinary left leftMemory =>
      rw [hleft] at hsent
      dsimp only at hsent
      cases hlo : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
          (record.input.state.activations i) record.input.time left with
      | failure => simp only [hlo] at hsent; cases hsent
      | noOffer => simp only [hlo] at hsent; cases hsent
      | offer old =>
          rw [hlo] at hsent
          have hword : ActiveFollowerArmChoice.offeredUpWord rate.eta old = v := Option.some.inj hsent
          have hparseOld : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
              (some (ActiveFollowerArmChoice.offeredUpWord rate.eta old)) = some old := by
            change OrdinaryMessageCodec.parseUp (codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta)).symm
                ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta))
                  (OrdinaryMessageCodec.encodeUp (codecParams p rate.eta) old)))) = some old
            rw [Equiv.symm_apply_apply, OrdinaryMessageCodec.parseUp_encode]
          rw [hword] at hparseOld
          have hM : old = M := Option.some.inj (hparseOld.symm.trans hparse)
          have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields
            rate.eta i record.input.row (record.input.state.activations i) record.input.time left old hlo
          have hleftStart : acceptedStart left = L.sigma := by
            have he := congrArg OrdinaryMessageCodec.UpFields.sigma hfields
            change old.val.sigma = acceptedStart left at he
            exact he.symm.trans ((congrArg (fun M => M.val.sigma) hM).trans hsigma)
          have hleftChoice : (actualChoice record i).configuration = .ordinary left leftMemory := by
            rw [actualChoice, record.output_eq]
            exact hleft
          have hunoccupied := (ReferenceUpPhysicalHashRule.checked_offer_facts
            i record.input.row (record.input.state.activations i) record.input.time left old hlo).2.1
          cases hright : ((prepare current.input).followers.followers i).configuration with
          | dagger => exact (ho hright).elim
          | ordinary right rightMemory =>
              have hrightChoice : (actualChoice current i).configuration = .ordinary right rightMemory := hright
              have hlA : (actualChoice full.records[a.val] i).configuration = .ordinary left leftMemory := by
                rw [hgetA]; exact hleftChoice
              have hrB : (actualChoice full.records[b.val] i).configuration = .ordinary right rightMemory := by
                rw [hgetB]; exact hrightChoice
              have hmono := (run_acceptedStart_mono input.val.1 input.val.2.1 input.val.2.2.1
                input.val.2.2.2 s (p.T - s) (by omega) input.property i a b hab left right
                leftMemory rightMemory hlA hrB).1
              have hupper := original_choice_start_le rewards C_star C_h q t s hs control0 i z
                L hsite right rightMemory hright
              have heq : acceptedStart left = acceptedStart right := by omega
              have hfixed := run_unoccupied_reply_const input.val.1 input.val.2.1 input.val.2.2.1
                input.val.2.2.2 s (p.T - s) (by omega) input.property i a b hab left right
                leftMemory rightMemory hlA hrB hunoccupied heq
              obtain ⟨offered, hro⟩ := ordinary_selected_offer current i right rightMemory
                hrightChoice hfixed.1 hcurrentChannel
              have hrightFields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta
                i current.input.row (current.input.state.activations i) current.input.time right offered hro
              have hsame : offered = old := by
                apply Subtype.ext
                rw [hrightFields, hfields]
                apply OrdinaryMessageCodec.UpFields.ext
                · exact heq.symm
                · exact hfixed.2.2.1
                · exact hfixed.2.2.2.1
                · exact hfixed.2.2.2.2
              change ReferenceActiveAffinePositiveTest.upSent current.input = some v
              rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration, hcurrentSender, hright]
              dsimp only
              rw [hro, hsame]
              exact congrArg some hword

/-- One actual locally accepted wrong UP word survives its one actual
completed batch on the ordinary terminal-follower branch. The single birth
precedes every test quantifier, and the projection is the literal decoder
entry projection. This is the ordinary branch of AppA:92-109, not full
stale-candidate exclusion. -/
theorem actual_wrong_local_up_survival_of_ordinary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : d.raw = some v) (hl : d.locallyAccepted = true) (hw : some v ≠ d.expected)
    (ho : ((ReferenceActivePhysicalStep.prepare (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input).followers.followers i).configuration ≠ .dagger) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let kept := (originalSourceTests (rate := rate)
        rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
      kept.length = AffineBatchDecoder.quota p ∧
      kept.map (fun test => (test.time, test.sample)) =
        batch.map (fun entry => (entry.time.val, entry.sample)) ∧
      (∀ test ∈ kept, test.sent ≠ some v) ∧
      z.val ∈ ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) := by
  classical
  dsimp only
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
  obtain ⟨L, M, hsite, _, _, _, hrawParsed, haccept, hp, hQ, _⟩ :=
    ReferenceGeneratedUpFalseDiagnosticCut.actual_wrong_local_up_rejected
      rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
  obtain ⟨_, _, _, _, _, hraw, _, _, _, hexpected, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields current d hd
  have hparse : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some v) = some M := by
    simpa only [ReferenceUpReception.rawParsedOutput, ← hraw, hv] using hrawParsed
  have hsigma : M.val.sigma = L.sigma := by
    have hchecks := haccept
    simp only [CoordinatorCollectionLedger.acceptUpCheck, Bool.and_eq_true,
      decide_eq_true_eq] at hchecks
    exact hchecks.2.2
  obtain ⟨alpha, ha, hat, hbirth, hlength, _, hprojection, hrecords,
      _, _, hbatchRaw, hcandidate⟩ :=
    ReferenceGeneratedUpAwaitedBatchCoverage.actual_completed_up_candidates
      rewards C_star C_h q t s hs control0 i z d hd hi hp hQ
  have hnever : ∀ test ∈ (originalSourceTests (rate := rate)
      rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p),
      test.sent ≠ some v := by
    intro test htest hsent
    obtain ⟨record, hmem, _, _, _, hword, _, hchannel, htime⟩ := hrecords test htest
    have hsentRecord : ReferenceActiveAffinePositiveTest.upSent record.input = some v :=
      hword.symm.trans hsent
    have hcurrentSent := repeated_word_current rewards C_star C_h q t s hs control0 i z
      L hsite M v hparse hsigma record hmem htime hchannel hsentRecord ho
    apply hw
    exact hcurrentSent.symm.trans hexpected.symm
  have hsolution : AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v := by
    apply (AffineBatchDecoder.satisfies_samples_iff batch v).mpr
    exact ((AffineBatchDecoder.batchOutput_eq_some_iff batch v).mp
      (hbatchRaw.symm.trans hv)).1
  exact ⟨alpha, ha, hat, hbirth, hlength, hprojection, hnever,
    (hcandidate v hsolution).mpr hnever⟩

/-- On the same unrestricted actual diagnostic telescope, a repetition in
the one actual completed UP batch forces the terminal prepared follower to
be dagger. This retains the remaining exceptional branch; it does not prove
that that branch is unreachable. -/
theorem actual_wrong_local_up_repeat_forces_dagger
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : d.raw = some v) (hl : d.locallyAccepted = true) (hw : some v ≠ d.expected) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let kept := (originalSourceTests (rate := rate)
        rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
      kept.length = AffineBatchDecoder.quota p ∧
      kept.map (fun test => (test.time, test.sample)) =
        batch.map (fun entry => (entry.time.val, entry.sample)) ∧
      ∀ test ∈ kept, test.sent = some v →
        ((ReferenceActivePhysicalStep.prepare current.input).followers.followers i).configuration = .dagger := by
  classical
  dsimp only
  by_cases hdagger : ((ReferenceActivePhysicalStep.prepare (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).input).followers.followers i).configuration = .dagger
  · obtain ⟨_, _, _, _, _, _, _, _, hp, hQ, _⟩ :=
      ReferenceGeneratedUpFalseDiagnosticCut.actual_wrong_local_up_rejected
        rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
    obtain ⟨alpha, ha, hat, hbirth, hlength, _, hprojection, _⟩ :=
      ReferenceGeneratedUpAwaitedBatchCoverage.actual_completed_up_candidates
        rewards C_star C_h q t s hs control0 i z d hd hi hp hQ
    exact ⟨alpha, ha, hat, hbirth, hlength, hprojection, fun _ _ _ => hdagger⟩
  · obtain ⟨alpha, ha, hat, hbirth, hlength, hprojection, hnever, _⟩ :=
      actual_wrong_local_up_survival_of_ordinary rewards C_star C_h q t s hs control0 i z
        d hd hi v hv hl hw hdagger
    exact ⟨alpha, ha, hat, hbirth, hlength, hprojection,
      fun test htest hsent => (hnever test htest hsent).elim⟩

end Bandits.Support.ReferenceGeneratedUpOrdinaryStaleExclusion
