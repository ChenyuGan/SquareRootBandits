/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOfferedSenderReplay

/-!
# Actual first-collection late DOWN recovery and fixed reply seed

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-88`,
`sources/zip4/manuscript/06_interruptions.tex:192-209,246-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64,151-157`.

The conclusion keeps the original source, complete reward grid, and computed
first-collection run. A retained DOWN query is made only after the common
cutoff payload has been identified. Its diagnostic and fixed reply are then
recovered from the actual zero-seeded launch follower.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstCollectionLateDownReplySeed

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem laterChosen_false_of_mem_takeWhile
    (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ suffix.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)) :
    ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
  induction suffix generalizing record with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hp : !ReferenceCollectionPhaseHistory.laterChosen head.input
      · simp [List.takeWhile, hp] at hmem
        rcases hmem with heq | htail
        · subst record
          simpa using hp
        · exact ih record htail
      · simp [List.takeWhile, hp] at hmem

private theorem retained_output_reply_and_status
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (logged after next : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : ∃ raw scan registers lastService,
      cut.outcome = .accepted logged after raw message scan registers lastService)
    (hafter : after.status = .unoccupied)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next =
        ReferenceFollowerReplyChronology.reply after := by
  obtain ⟨raw, scan, registers, lastService, haccepted⟩ := haccepted
  obtain ⟨choice, choiceMemory, logged', hchoice, hunoccupied, hlogging,
      hinput', hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hlogged : logged' = logged := Option.some.inj (hinput'.symm.trans hinput)
  subst logged'
  obtain ⟨choice', memory, post, hprepared, hrecord, hfinish, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory
      (by
        have he := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record
        change (ReferenceActivePhysicalStep.finishFollower _
          (record.output.preparation.followers.followers i) _).configuration = _
        rw [← he]
        have hn : record.output.next.followers i = (record.output.followers i).configuration := by
          rw [record.output_eq]
          rfl
        exact hn ▸ hout)
  rcases DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hprepared.symm.trans hchoice) with
    ⟨rfl, rfl⟩
  have hpost : post = after := by
    have hu := hunoccupied
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
    rw [← hcut, haccepted] at hrecord
    exact (Except.ok.inj hrecord).symm
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    (actualChoice record i).follower (actualChoice record i).row
    (actualChoice record i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    choice' post next memory nextMemory hfinish
  exact ⟨(hframe.2 hunoccupied).trans
      (congrArg (fun state => state.status) hpost) |>.trans hafter,
    by simpa only [hpost] using hframe.1⟩

private theorem collection_choice_of_selection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    ∃ choice, ReferenceCollectionSegmentExtraction.choice x = some choice ∧
      choice.payload = payload := by
  classical
  have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hinvalid := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
      x payload ledger proposal hstate hbad
    have hselected : (ReferenceActivePhysicalStep.dispatch x).selection ≠ none := by
      simpa only [ReferenceActivePhysicalStep.PreparedRound.coordinator_eq] using hselection
    rw [hinvalid.1] at hselected
    simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselected
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
  | collection outcome =>
      have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .collection payload ledger clock cutoff outcome := by
        calc
          (ReferenceActivePhysicalStep.prepare x).coordinator =
              ReferenceActivePhysicalStep.dispatch x :=
            (ReferenceActivePhysicalStep.prepare x).coordinator_eq
          _ = .collection payload ledger clock cutoff outcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            rw [hstate]
            simp only [dite_eq_left hvalid]
            dsimp [cutoff, clock, input]
            rw [hdispatch]
            rfl
      have hselectionOutcome :
          (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection ≠ none := by
        simpa only [hprepared] using hselection
      cases houtcome : outcome with
      | continuing core prepared boundary scores =>
          let choice : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨payload, ledger, prepared.clockStarted,
              CoordinatorCollectionInteractive.PreObservationInputs.weights input
                prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq, none⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some choice := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [if_neg hselection]
            rw [hprepared]
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut, houtcome,
              choice, input]
          exact ⟨choice, hchoice, rfl⟩
      | laterChosen core consistent started startRound instruction assignmentStart output
          consistency clockData installed selected =>
          have hlater : ReferenceCollectionPhaseHistory.laterChosen x = true := by
            simp [ReferenceCollectionPhaseHistory.laterChosen, hprepared, houtcome]
          exact False.elim (Bool.noConfusion (hnotLater.symm.trans hlater))
      | clockFailure failure startRoundEq =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | localFailure started startRoundEq coreInvalid reason =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | coreFailure core started startRoundEq reason =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | laterReconstructionFailure core consistent started startRoundEq instruction
          assignmentStartEq reason laterEq =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | laterPrefixFailure core consistent started startRoundEq instruction
          assignmentStartEq arm reason laterEq =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | laterOrientationFailure core consistent started startRoundEq instruction
          assignmentStartEq set laterEq =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localConsistencyEq clockData installed selected =>
          rw [houtcome] at hselectionOutcome
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectionOutcome

private theorem collection_step_keeps_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ nextLedger nextSaved,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection payload nextLedger nextSaved := by
  by_cases hselection :
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
  · left
    have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger := by
      cases hcut : (ReferenceActivePhysicalStep.prepare x).coordinator with
      | first outcome =>
          have hs : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none := by
            simpa only [hcut] using hselection
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | live registers owned base outcome =>
          have hs : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none := by
            simpa only [hcut] using hselection
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | collection cp cl clock cutoff outcome =>
          have hs : (ReferenceActivePhysicalStep.DispatchCut.collection cp cl clock cutoff outcome).selection = none := by
            simpa only [hcut] using hselection
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | invalidCollectionCutoff =>
          have hs : (ReferenceActivePhysicalStep.DispatchCut.invalidCollectionCutoff (x := x)).selection = none := by
            simpa only [hcut] using hselection
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | dagger =>
          have hs : (ReferenceActivePhysicalStep.DispatchCut.dagger (x := x)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs]
    rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
    exact hobs
  · obtain ⟨choice, hchoice, hchoicePayload⟩ :=
      collection_choice_of_selection x payload ledger proposal hstate hselection hnotLater
    have htail := ReferenceCollectionSegmentExtraction.choice_tail x choice hchoice
    have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
      (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
      choice.started choice.weights
    have hstep : (ReferenceActivePhysicalStep.step x).next.coordinator =
        (ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
          choice.started choice.weights).configuration := by
      rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
      exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration htail
    rcases hphase with hdagger | ⟨postPayload, postLedger, postSaved, hpost⟩
    · exact Or.inl (hstep.trans hdagger)
    · have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
        (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
        choice.started choice.weights
      rw [hpost] at hpayloadFrame
      rcases hpayloadFrame with hnone | hsome
      · simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hnone
      · have hpayload : postPayload = payload := by
          simpa [ReferenceAssignmentPayloadPersistence.storedPayload] using
            (Option.some.inj hsome).trans hchoicePayload
        exact Or.inr ⟨postLedger, postSaved, by
          rw [hstep, hpost, hpayload]⟩

private theorem selected_choice_keeps_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some choice) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ ledger saved,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection choice.payload ledger saved := by
  have htail := ReferenceCollectionSegmentExtraction.choice_tail x choice hchoice
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
    choice.started choice.weights
  have hstep : (ReferenceActivePhysicalStep.step x).next.coordinator =
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
        choice.started choice.weights).configuration := by
    rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
    exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration htail
  rcases hphase with hdagger | ⟨postPayload, postLedger, postSaved, hpost⟩
  · exact Or.inl (hstep.trans hdagger)
  · have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
      (ReferenceActivePhysicalStep.prepare x) choice.payload choice.preLedger
      choice.started choice.weights
    rw [hpost] at hpayloadFrame
    rcases hpayloadFrame with hnone | hsome
    · simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hnone
    · have hpayload : postPayload = choice.payload := by
        simpa [ReferenceAssignmentPayloadPersistence.storedPayload] using
          Option.some.inj hsome
      exact Or.inr ⟨postLedger, postSaved, by
        rw [hstep, hpost, hpayload]⟩

private theorem live_cutoff_choice
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live registers owned base)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ choice, ReferenceCollectionSegmentExtraction.choice x = some choice ∧
      choice.payload = registers.payload := by
  let outcome := CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput x registers owned base)
  have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base outcome := by
    rw [ReferenceActivePhysicalStep.PreparedRound.coordinator_eq]
    unfold ReferenceActivePhysicalStep.dispatch
    rw [hstate]
    simp only [CoordinatorRoundDispatch.dispatch]
    rfl
  have htag := hcutoff
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at htag
  rw [hprepared] at htag
  cases houtcome : outcome with
  | cutoffChosen dispatched startRoundEq ledger initializationEq ledgerEq
      domains clockFrame pendingFrame noAssignment selection =>
      let liveRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers x.time
      let liveOwned := ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time
      let choice : ReferenceCollectionSegmentExtraction.Choice rate :=
        ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
          dispatched.startResult, liveRegisters.complementWeights,
          some (ReferenceCollectionSegmentExtraction.cutoffInitializer
            liveRegisters liveOwned base x.time)⟩
      have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
        rw [hprepared, houtcome]
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      refine ⟨choice, ?_, rfl⟩
      unfold ReferenceCollectionSegmentExtraction.choice
      rw [if_neg hselection]
      unfold ReferenceCollectionSegmentExtraction.choiceOfCut
      rw [hprepared, houtcome]
  | clockFailure failure dispatchEq =>
      simp [houtcome] at htag
  | initializerFailure dispatched startRoundEq checked checkedEq =>
      simp [houtcome] at htag
  | localFailure dispatched startRoundEq reason =>
      simp [houtcome] at htag
  | continuingChosen dispatched startRoundEq continuation selection =>
      simp [houtcome] at htag

private theorem connected_append_split
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (before suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (before ++ suffix) final) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial before middle ∧
      ReferenceActivePhysicalHorizon.Connected middle suffix final := by
  induction before generalizing initial with
  | nil => exact ⟨initial, by rfl, hchain⟩
  | cons record rest ih =>
      change record.input.state = initial ∧
        ReferenceActivePhysicalHorizon.Connected record.output.next (rest ++ suffix) final at hchain
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hchain.2
      exact ⟨middle, ⟨hchain.1, hprefix⟩, hsuffix⟩

private theorem collection_phase_along_records
    (payload : ReferenceActivePhysicalStep.Payload rate)
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hnotLater : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.laterChosen record.input = false)
    (hphase : initial.coordinator = .dagger ∨
      ∃ ledger saved, initial.coordinator = .collection payload ledger saved) :
    final.coordinator = .dagger ∨
      ∃ ledger saved, final.coordinator = .collection payload ledger saved := by
  induction records generalizing initial with
  | nil =>
      change final = initial at hchain
      subst final
      exact hphase
  | cons record rest ih =>
      change record.input.state = initial ∧
        ReferenceActivePhysicalHorizon.Connected record.output.next rest final at hchain
      rcases hphase with hdagger | ⟨ledger, saved, hcollection⟩
      · have hrecord : record.input.state.coordinator = .dagger := by
          rw [hchain.1]
          exact hdagger
        have hnext : record.output.next.coordinator = .dagger := by
          rw [record.output_eq]
          exact (ReferenceActivePhysicalStep.step_coordinator_dagger
            record.input hrecord).1
        exact ih hchain.2
          (fun current hmem => hnotLater current (List.mem_cons_of_mem _ hmem))
          (Or.inl hnext)
      · have hrecord : record.input.state.coordinator =
            .collection payload ledger saved := by
          rw [hchain.1]
          exact hcollection
        have hnext := collection_step_keeps_payload record.input payload ledger saved
          hrecord (hnotLater record (List.mem_cons_self))
        rw [← record.output_eq] at hnext
        exact ih hchain.2
          (fun current hmem => hnotLater current (List.mem_cons_of_mem _ hmem)) hnext

/-- One actual late retained DOWN in the first collection window is the first
payload's zero-seeded DOWN. Its scan terminates at the fixed cutoff, and an
ordinary returned follower carries that exact unoccupied reply into the next
collection boundary. The DOWN query is universally quantified inside the
conclusion and is never an input assumption. -/
theorem actual_first_collection_late_down_reply_seed
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
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let hactive := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < E.records.length,
        cutoffRecord = E.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∀ k : Fin B.length,
        E.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
          (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
          (after : ReferencePrelaunchFollower.State p rate.eta)
          (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
          (scan : FollowerCutoffScan.ScanResult p.T)
          (registers : ℕ × ℕ) (lastService : ℕ),
          (r.output.followers i).downInput = some logged ∧
          (r.output.followers i).down = some cutD ∧
          cutD.outcome = .accepted logged after raw M scan registers lastService ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 ∧
          ActiveFollowerDownAcceptance.downStart p rate M = P0.sigma ∧
          scan.endpoint = u ∧ after.status = .unoccupied ∧
          after.lastDown = some M ∧
          (∃ hindex : j < count, ∃ n0,
            n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
            ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
              .ok ⟨registers, lastService⟩ ∧
            (let physicalInput :=
              ((ReferenceFollowerSparseEmissionRecovery.physicalRecords I
                source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s j
                (by
                  dsimp only [s, b0, x0] at hspan ⊢
                  omega) hactive).take n0).map
                (fun record => (true,
                  ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record))
             ∀ prefixLength, ∃ middle,
              ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (physicalInput.take prefixLength) =
                  .ok middle ∧
              ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p)
                middle ∧
              middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                (physicalInput.take prefixLength))) ∧
          (let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
           registers = V w ∧ lastService = (V w).1 - (V (w - 1)).1 ∧
           after.S = (V w).1 ∧ after.backlog = (V w).2 ∧
           after.delta = (V w).1 - (V (w - 1)).1) ∧
          (r.output.next.followers i = .dagger ∨
            ∃ out memory,
              r.output.next.followers i = .ordinary out memory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply after ∧
              (let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
               out.S = (V w).1 ∧ out.backlog = (V w).2 ∧
               out.delta = (V w).1 - (V (w - 1)).1 ∧
               ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1)) ∧
          (r.output.next.coordinator = .dagger ∨
            ∃ actualLedger actualSaved,
              r.output.next.coordinator = .collection P0 actualLedger actualSaved) := by
  classical
  intro x0 b0 s I hactive E W w B u
  let hO := ReferenceFirstCollectionOfferedSenderReplay.run_first_collection_offered_sender_replay
    rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutO, suffixO, regsO, ownedO, baseO, P0O, birthO,
      hsplitO, hindexO, htimeO, hstateO, htagO, hpayloadO, hsigmaO,
      hqueuesO, hcutoffO, hbirthMemO, hbirthInstallO, hbirthTimeO,
      _hbirthChosenO, hwindowO, _hqueriesO⟩ := hO
  have hsplitO' : E.records = W ++ cutO :: suffixO := by
    simpa only [E, W, I, s,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hsplitO
  have hOrigin :=
    ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
      rate source rewards C_star C_h count hcross hspan hshort
  rcases hOrigin with ⟨_, hOrigin⟩
  rcases hOrigin with ⟨cutR, P0R, birthR, regsR, ownedR, baseR,
      hindexR, huniqueR, hstateR, htagR, hpayloadR, hsigmaR, hqueuesR,
      hcutoffR, hbirthMemR, hbirthInstallR, hbirthTimeR, _hbirthChosenR,
      hwindowR, hselectedR, hretainedR, _hpriorR⟩
  have hcutEq : cutO = cutR := huniqueR cutO suffixO hsplitO
  have hregsEq : regsO = regsR := by
    have hstate := congrArg (fun record => record.input.state.coordinator) hcutEq
    rw [hstateO, hstateR] at hstate
    injection hstate with hregsEq
  have hP0Eq : P0O = P0R := by
    rw [hpayloadO, hpayloadR, hregsEq]
  have hseedSource := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  obtain ⟨_, _, _, _, _, _, _, hseeds⟩ := hseedSource
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hcross
  have hI : I = initial := by
    dsimp only [I, initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
  have hactivePair := ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross
  have hfirst : I.coordinator = .first := hactivePair.2
  refine ⟨cutO, suffixO, regsO, ownedO, baseO, P0O, birthO,
    hsplitO, hindexO, htimeO, hstateO, htagO, hpayloadO, hsigmaO,
    hqueuesO, hcutoffO, hbirthMemO, hbirthInstallO, hbirthTimeO, hwindowO, ?_⟩
  intro k i M j r hretained
  have hwindow := hwindowO k
  have hjlt : j < E.records.length := (List.getElem?_eq_some_iff.mp hwindow.1).1
  have hrecord : r = E.records[j]'hjlt := by
    have hget := hwindow.1
    rw [List.getElem?_eq_getElem hjlt] at hget
    exact (Option.some.inj hget).symm
  have hlookupR : E.records[j]? = some r := by
    rw [List.getElem?_eq_getElem hjlt, ← hrecord]
  have hrB : r = B[k.val] :=
    Option.some.inj (hlookupR.symm.trans hwindow.1)
  have hretainedE : ReferenceAcceptedUpFollowerHistory.RetainedDown
      E.records[j] i M := by
    change ReferenceAcceptedUpFollowerHistory.RetainedDown r i M at hretained
    rw [hrecord] at hretained
    exact hretained
  have hretOrigin := hretainedR k r hwindow.1 i M hretained
  rcases hretOrigin with ⟨hMpayload, hMsigma, hMq⟩
  have hMpayloadO : M = P0O.downRecord i := by
    rw [← hP0Eq] at hMpayload
    exact hMpayload
  have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = P0O.sigma := by
    have hstart := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    rw [hMsigma] at hstart
    apply Fin.ext
    rw [hsigmaO]
    omega
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  have hseedFacts := hseeds i
  let seed := ReferenceInitializationRun.ordinary x0 b0
    (ActualReferenceInitializationBlock.refFollower i)
  let memory := ActiveFollowerLifecycle.initialMemory p
  rcases hseedFacts with ⟨hseed0, hnone, _hseedStart, _hseedS, _hseedDelta,
      _hseedBacklog, hunoccupied, _hdomain, hvalid, hpair, htime⟩
  have hseed : I.followers i = .ordinary seed memory := by
    rw [hI]
    simpa only [seed] using hseed0
  have hrecover := ReferenceFirstDownZeroRecovery.actual_first_down_zero_seeded_recovery
    I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan hactive hfirst i seed memory hseed hnone hunoccupied
    hvalid hpair htime ⟨j, hjlt⟩ M hretainedE hMsigma
  obtain ⟨logged, cutD, after, raw, scan, recovered, lastService,
      hinput, hdown, haccepted, _view, selected, _hview, hselected, _hviewEq,
      _hmessageView, _birth, _installed, _firstChoice, _hbirth, _hborn,
      _hbirthTime, _hbirthFirst, _hhead, _hdispatch, _hpayload, _hfirstPayload,
      _hmessageInstalled, _hqzero, _hseedNone, _hseedStatus, n0, hn0, hend,
      _hn0pos, _hn0le, _hnoprior, _hrecovery, hchecked, hregisters,
      hlastService, hprefix, hafter⟩ := hrecover
  have hinputR : (r.output.followers i).downInput = some logged := by
    have h := hinput
    change ((E.records[j]'hjlt).output.followers i).downInput = some logged at h
    rw [← hrecord] at h
    exact h
  have hdownR : (r.output.followers i).down = some cutD := by
    have h := hdown
    change ((E.records[j]'hjlt).output.followers i).down = some cutD at h
    rw [← hrecord] at h
    exact h
  have htimeRecord : r.input.time.val = s + j := by
    have ht : B[k.val].input.time.val + 1 = s + w + 1 + k.val := by
      simpa only [u] using hwindow.2
    rw [congrArg (fun record => record.input.time.val) hrB]
    dsimp only [j]
    omega
  have hfirstCutoffDown : FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M) bits = u := by
    rw [hdownStart]
    exact hcutoffO
  have hscan : scan.endpoint = u := by
    change scan.endpoint = min
      (FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M) bits)
      (s + j + 2) at hend
    rw [hfirstCutoffDown] at hend
    have hjle : w ≤ j := by dsimp only [j]; omega
    have hlt : u < s + j + 2 := by dsimp only [u]; omega
    rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at hend
    exact hend
  have hn0eq : n0 = w := by
    calc
      n0 = scan.endpoint - M.val.sigma := hn0
      _ = u - (s + 1) := by rw [hscan, hMsigma]
      _ = w := by change s + w + 1 - (s + 1) = w; omega
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
  change recovered = V n0 at hregisters
  change lastService = (V n0).1 - (V (n0 - 1)).1 at hlastService
  have hafterPair : (after.S, after.backlog) = V n0 := by
    rw [hafter]
    exact hregisters
  have hafterDelta : after.delta = (V n0).1 - (V (n0 - 1)).1 := by
    rw [hafter]
    exact hlastService
  have hafterUnoccupied : after.status = .unoccupied := by
    have htimeFollower :
        (r.output.preparation.followers.followers i).time.val = s + j := by
      rw [(r.output.preparation.follower_alignment i).2.2.1]
      exact htimeRecord
    have htimeFollowerE :
        ((E.records[j]'hjlt).output.preparation.followers.followers i).time.val = s + j := by
      rw [← hrecord]
      exact htimeFollower
    have hneq : scan.endpoint ≠
        ((E.records[j]'hjlt).output.preparation.followers.followers i).time.val + 2 := by
      rw [hscan, htimeFollowerE]
      change s + w + 1 ≠ s + j + 2
      have hjle : w ≤ j := by dsimp only [j]; omega
      omega
    let recoveredRun := ReferenceActivePhysicalHorizon.run I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hactive
    have hRecovered : recoveredRun = E := by
      dsimp only [recoveredRun, E,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    have hRecoveredLength : recoveredRun.records.length = E.records.length :=
      congrArg (fun execution => execution.records.length) hRecovered
    have hjltRecovered : j < recoveredRun.records.length := by
      calc
        j < E.records.length := hjlt
        _ = recoveredRun.records.length := hRecoveredLength.symm
    have hrecordsOpt := congrArg
      (fun execution : ReferenceActivePhysicalHorizon.Run I => execution.records[j]?) hRecovered
    rw [List.getElem?_eq_getElem hjltRecovered,
      List.getElem?_eq_getElem hjlt] at hrecordsOpt
    have hrecordActual : recoveredRun.records[j]'hjltRecovered = E.records[j]'hjlt :=
      Option.some.inj hrecordsOpt
    have htimeActual :
        ((recoveredRun.records[j]'hjltRecovered).output.preparation.followers.followers i).time.val = s + j := by
      rw [hrecordActual]
      exact htimeFollowerE
    have hneqActual : scan.endpoint ≠
        ((recoveredRun.records[j]'hjltRecovered).output.preparation.followers.followers i).time.val + 2 := by
      rw [hscan, htimeActual]
      change s + w + 1 ≠ s + j + 2
      have hjle : w ≤ j := by dsimp only [j]; omega
      omega
    rw [hafter]
    simp only [recoveredRun, if_neg hneqActual]
  have hafterLastDown : after.lastDown = some M := by
    simpa only [hafter]
  have hafterS : after.S = (V w).1 := by
    have h := congrArg Prod.fst hafterPair
    simpa only [hn0eq] using h
  have hafterBacklog : after.backlog = (V w).2 := by
    have h := congrArg Prod.snd hafterPair
    simpa only [hn0eq] using h
  have hafterService : after.delta = (V w).1 - (V (w - 1)).1 := by
    simpa only [hn0eq] using hafterDelta
  have hregistersW : recovered = V w := by
    simpa only [hn0eq] using hregisters
  have hlastServiceW : lastService = (V w).1 - (V (w - 1)).1 := by
    simpa only [hn0eq] using hlastService
  have hcount := ReferenceActivePhysicalHorizon.run_record_count I
    source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hactive
  have hlen : E.records.length = count := by
    simpa only [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun, I] using hcount
  have hjcount : j < count := by
    calc
      j < E.records.length := hjlt
      _ = count := hlen
  have hprefixOutput :
      (let physicalInput :=
        ((ReferenceFollowerSparseEmissionRecovery.physicalRecords I
          source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s j
          (by
            dsimp only [s, b0, x0] at hspan ⊢
            omega) hactive).take n0).map
          (fun record => (true,
            ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record))
       ∀ prefixLength, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
          (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (physicalInput.take prefixLength) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          (physicalInput.take prefixLength)) := by
    exact hprefix
  have hnextFollower : r.output.next.followers i = .dagger ∨
      ∃ out memory, r.output.next.followers i = .ordinary out memory ∧
        out.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply out =
          ReferenceFollowerReplyChronology.reply after ∧
        out.S = (V w).1 ∧ out.backlog = (V w).2 ∧
        out.delta = (V w).1 - (V (w - 1)).1 ∧
        ReferencePrelaunchFollower.acceptedStart out = P0O.sigma.val + 1 := by
    cases hout : r.output.next.followers i with
    | dagger => exact Or.inl rfl
    | ordinary out memory =>
        have hreply := retained_output_reply_and_status r i M logged after out cutD memory
          hinputR hdownR ⟨raw, scan, recovered, lastService, haccepted⟩ hafterUnoccupied hout
        rcases hreply with ⟨houtStatus, hreply⟩
        have hS : out.S = after.S := congrArg (fun reply => reply.2.1) hreply
        have hdelta : out.delta = after.delta := congrArg (fun reply => reply.2.2.1) hreply
        have hbacklog : out.backlog = after.backlog := congrArg (fun reply => reply.2.2.2) hreply
        have hlastOut : out.lastDown = some M := by
          have h := congrArg Prod.fst hreply
          simpa only [ReferenceFollowerReplyChronology.reply, hafterLastDown] using h
        have hstart : ReferencePrelaunchFollower.acceptedStart out = P0O.sigma.val + 1 := by
          simp [ReferencePrelaunchFollower.acceptedStart, hlastOut, hMsigma, hsigmaO]
        refine Or.inr ⟨out, memory, rfl, houtStatus, hreply, ?_, ?_, ?_, hstart⟩
        · rw [hS, hafterS]
        · rw [hbacklog, hafterBacklog]
        · rw [hdelta, hafterService]
  have hnextCoordinator : r.output.next.coordinator = .dagger ∨
      ∃ actualLedger actualSaved,
        r.output.next.coordinator = .collection P0O actualLedger actualSaved := by
    let tailWindow := suffixO.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hBshape : B = cutO :: tailWindow := by
      dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow, tailWindow]
      rw [hsplitO']
      rw [List.drop_append_length, List.drop_add_one_eq_tail_drop,
        List.drop_append_length]
      simp only [List.tail_cons, List.take_succ_cons, List.take_zero,
        List.singleton_append]
    obtain ⟨cutChoice, hcutChoice, hcutChoicePayload⟩ :=
      live_cutoff_choice cutO.input regsO ownedO baseO hstateO htagO
    have hcutPhase := selected_choice_keeps_payload cutO.input cutChoice hcutChoice
    have hcutNext : cutO.output.next.coordinator = .dagger ∨
        ∃ ledger saved, cutO.output.next.coordinator = .collection P0O ledger saved := by
      have hpayload : cutChoice.payload = P0O := hcutChoicePayload.trans hpayloadO.symm
      rw [cutO.output_eq]
      rcases hcutPhase with hdagger | ⟨ledger, saved, hcollection⟩
      · exact Or.inl hdagger
      · exact Or.inr ⟨ledger, saved, by rw [hcollection, hpayload]⟩
    by_cases hk0 : k.val = 0
    · have hrecordCut : r = cutO := by
        have hlookupR0 : E.records[w]? = some r := by
          have hj0 : j = w := by dsimp only [j]; omega
          simpa only [hj0] using hlookupR
        have hlookupCut : E.records[w]? = some cutO := by
          rw [hsplitO']
          simp [w]
        exact Option.some.inj (hlookupR0.symm.trans hlookupCut)
      rw [hrecordCut]
      exact hcutNext
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
      let n := k.val - 1
      have hnlt : n < tailWindow.length := by
        have hbound : k.val < tailWindow.length + 1 := by
          calc
            k.val < B.length := k.isLt
            _ = tailWindow.length + 1 := by rw [hBshape]; simp
        dsimp only [n]
        omega
      let target : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
        tailWindow[n]'hnlt
      have hBtarget : B[k.val] = target := by
        have hkEq : k.val = n + 1 := by dsimp only [n]; omega
        have hkBoundCons : k.val < (cutO :: tailWindow).length := by
          calc
            k.val < B.length := k.isLt
            _ = (cutO :: tailWindow).length := by rw [hBshape]
        have hgetB := List.getElem?_eq_getElem k.isLt
        have hgetCons : (cutO :: tailWindow)[k.val]? = some target := by
          rw [hkEq]
          simp only [List.getElem?_cons_succ]
          rw [List.getElem?_eq_getElem hnlt]
        have hgetEq := congrArg (fun records : List
            (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) => records[k.val]?)
          hBshape
        rw [hgetB, hgetCons] at hgetEq
        exact Option.some.inj hgetEq
      have hrTarget : r = target := hrB.trans hBtarget
      have hconnectedE : ReferenceActivePhysicalHorizon.Connected I
          (W ++ cutO :: suffixO) E.finalState := by
        rw [← hsplitO']
        exact E.connected
      obtain ⟨middle, _, hcutChain⟩ := connected_append_split W (cutO :: suffixO) hconnectedE
      change cutO.input.state = middle ∧
        ReferenceActivePhysicalHorizon.Connected cutO.output.next suffixO E.finalState at hcutChain
      have hchainAfterCut := hcutChain.2
      have htailPrefix : tailWindow.IsPrefix suffixO := by
        dsimp only [tailWindow]
        exact List.takeWhile_prefix _
      obtain ⟨remainder, htailSplit⟩ := htailPrefix
      have hnle : n ≤ tailWindow.length := Nat.le_of_lt hnlt
      have hsplitTail : tailWindow = tailWindow.take n ++
          target :: tailWindow.drop (n + 1) := by
        calc
          tailWindow = tailWindow.take n ++ tailWindow.drop n :=
            (List.take_append_drop n tailWindow).symm
          _ = tailWindow.take n ++ tailWindow[n] :: tailWindow.drop (n + 1) := by
            rw [List.cons_getElem_drop_succ (l := tailWindow) (n := n) (h := hnlt)]
          _ = tailWindow.take n ++ target :: tailWindow.drop (n + 1) := rfl
      have hsplitSuffix : suffixO = tailWindow.take n ++
          target :: (tailWindow.drop (n + 1) ++ remainder) := by
        calc
          suffixO = tailWindow ++ remainder := htailSplit.symm
          _ = (tailWindow.take n ++ target :: tailWindow.drop (n + 1)) ++ remainder :=
            congrArg (fun preList => preList ++ remainder) hsplitTail
          _ = tailWindow.take n ++ target :: (tailWindow.drop (n + 1) ++ remainder) := by
            simp [List.append_assoc]
      rw [hsplitSuffix] at hchainAfterCut
      obtain ⟨middle', hprefixChain, htargetChain⟩ :=
        connected_append_split (tailWindow.take n)
          (target :: (tailWindow.drop (n + 1) ++ remainder)) hchainAfterCut
      change target.input.state = middle' ∧ _ at htargetChain
      have hrecordState : r.input.state = middle' :=
        (congrArg (fun record => record.input.state) hrTarget).trans htargetChain.1
      have hnotPrefix : ∀ record ∈ tailWindow.take n,
          ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
        intro record hmem
        have hmemTail := List.mem_of_mem_take hmem
        have hpred := laterChosen_false_of_mem_takeWhile suffixO record
          (by simpa only [tailWindow] using hmemTail)
        exact hpred
      have hphaseBefore := collection_phase_along_records P0O (tailWindow.take n) hprefixChain
        hnotPrefix hcutNext
      have hselectedR : r.output.preparation.coordinator.selection ≠ none := by
        intro hnone
        rw [hrecord] at hnone
        exact (Option.some_ne_none selected) (hselected.symm.trans hnone)
      have hnotCurrent :
          ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
        have htargetNot := laterChosen_false_of_mem_takeWhile suffixO target
          (by simpa only [tailWindow] using List.getElem_mem hnlt)
        rw [hrTarget]
        exact htargetNot
      rcases hphaseBefore with hdagger | ⟨ledger, saved, hcollection⟩
      · have hstate : r.input.state.coordinator = .dagger := by
          have h := hdagger
          rw [← hrecordState] at h
          exact h
        have hselectedPrepared :
            (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection ≠ none := by
          simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselectedR
        have hdispatch := ReferenceActivePhysicalStep.dispatch_dagger r.input hstate
        rw [ReferenceActivePhysicalStep.PreparedRound.coordinator_eq, hdispatch]
          at hselectedPrepared
        simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselectedPrepared
      · have hstate : r.input.state.coordinator = .collection P0O ledger saved := by
          have h := hcollection
          rw [← hrecordState] at h
          exact h
        have hnext := collection_step_keeps_payload r.input P0O ledger saved
          hstate hnotCurrent
        rw [← r.output_eq] at hnext
        exact hnext
  refine ⟨logged, cutD, after, raw, scan, recovered, lastService,
    hinputR, hdownR, haccepted, hMpayloadO, hMsigma, hMq, hdownStart,
    hscan, hafterUnoccupied, hafterLastDown,
    ⟨hjcount, n0, hn0, hn0eq, hchecked, hprefixOutput⟩,
    ⟨hregistersW, hlastServiceW, hafterS, hafterBacklog, hafterService⟩,
    hnextFollower, hnextCoordinator⟩

end Bandits.Support.ReferenceFirstCollectionLateDownReplySeed

end
