/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedReplyStateInterval

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection formed-UP offer and receiver

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-296,327-348,459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-108`.

This module composes the admitted state interval with the existing ordinary
UP codec and physical receiver. It adds no bank-history, second-batch,
service-law, numerical-identity, or regret conclusion.

The next consumer is the actual formation-UP bank/second-pure-UP batch
composer. Possible placeholder or older preformation contamination remains.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower

namespace Bandits.Support.ReferenceFirstCollectionFormedUpOfferReceiver

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The canonical coordinator word for one follower-codec UP record. -/
public def encodedUpOfferWord
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    AffineChannelLaw.Word (AffineBatchDecoder.width p) :=
  OrdinaryMessageCodec.wordEquivFlat
    (CoordinatorCollectionLedger.codecParams p rate.eta.val)
    (OrdinaryMessageCodec.encodeUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      (cast (congrArg (fun codec => OrdinaryMessageCodec.UpRecord codec)
        (ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate).symm) U))

private theorem encodedUpOfferWord_eq_flat
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    encodedUpOfferWord (p := p) (rate := rate) U =
      OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) U) := by
  unfold encodedUpOfferWord
  have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
  cases hcodec
  rfl

private theorem upOfferFields_eq_of_reply_eq
    {left right : ReferencePrelaunchFollower.State p rate.eta}
    (h : ReferenceFollowerReplyChronology.reply left =
      ReferenceFollowerReplyChronology.reply right) :
    ActiveFollowerQueueOperation.upOfferFields left =
      ActiveFollowerQueueOperation.upOfferFields right := by
  have hparts : left.lastDown = right.lastDown ∧ left.S = right.S ∧
      left.delta = right.delta ∧ left.backlog = right.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using h
  ext
  · exact ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq h
  · exact hparts.2.1
  · exact hparts.2.2.1
  · exact hparts.2.2.2

/-- The expected-word filter can only retain the encoded message itself.
The proof follows the literal filter and parser and uses `parseUp_encode`; it
does not assume uniqueness for the unfiltered decoder output. -/
private theorem filteredParsed_expected_unique
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) =
        some (encodedUpOfferWord U))
    (hparsed : ReferenceCollectionPhaseHistory.filteredParsed record.input ledger = some M) :
    M = U := by
  let receiverInput := ReferenceUpReception.receptionInputAtRow rate record.input.row
    (ReferenceActivePhysicalStep.upInputs
      (ReferenceActivePhysicalStep.prepare record.input) ledger) record.input.time
  let raw := (CoordinatorUpReception.decoderTransition receiverInput).2
  let expected := ReferenceActivePhysicalStep.upExpected
    (ReferenceActivePhysicalStep.prepare record.input)
  have hrawEq : raw = expected := by
    by_contra hne
    have hnone := ReferenceUpReception.filterRawByExpected_eq_none_of_ne raw expected hne
    have hbad : ReferenceCollectionPhaseHistory.filteredParsed record.input ledger = none := by
      simp [ReferenceCollectionPhaseHistory.filteredParsed, receiverInput, raw,
        expected, hnone, CoordinatorUpReception.parseDecoderOutput,
        OrdinaryMessageCodec.parseUp, Option.map]
    rw [hbad] at hparsed
    cases hparsed
  have hparse : CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected raw expected) = some M := by
    simpa [ReferenceCollectionPhaseHistory.filteredParsed, receiverInput, raw, expected] using hparsed
  rw [ReferenceUpReception.filterRawByExpected_eq_raw_of_eq raw expected hrawEq] at hparse
  rw [hrawEq] at hparse
  dsimp only [expected] at hparse
  rw [hexpected] at hparse
  let Uc := cast (congrArg (fun codec => OrdinaryMessageCodec.UpRecord codec)
    (ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate).symm) U
  have hdecoded :
      CoordinatorUpReception.parseDecoderOutput
        (some (encodedUpOfferWord U)) = some Uc := by
    rw [CoordinatorUpReception.parseDecoderOutput]
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) Uc)))) = some Uc
    rw [Equiv.symm_apply_apply]
    exact OrdinaryMessageCodec.parseUp_encode
      (CoordinatorCollectionLedger.codecParams p rate.eta.val) Uc
  have hsome : some Uc = some M := hdecoded.symm.trans hparse
  have hcast : Uc = U := by
    dsimp [Uc]
    have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
    cases hcodec
    rfl
  exact (Option.some.inj hsome).symm.trans hcast

/-- Acceptance contains the actual filtered parse, so the same expected-word
argument applies without a successful-batch or raw-uniqueness hypothesis. -/
private theorem acceptedUp_expected_unique
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) = some (encodedUpOfferWord U))
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M) :
    M = U := by
  obtain ⟨_tail, _recording, started, _decoded, _bank,
    _htail, _hrecording, _hstart, _hreceived, hparsed, _hsender⟩ := haccepted
  exact filteredParsed_expected_unique record started U M hexpected hparsed

private theorem upOfferFields_admissible
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state) :
    OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
  have hstartBound : ReferencePrelaunchFollower.acceptedStart state ≤ p.T := by
    cases hlast : state.lastDown with
    | none => simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hpositive
    | some down =>
        have hbound : down.val.sigma ≤ p.T := by
          simpa only [ReferencePrelaunchFollower.codecParams] using down.property.2.1
        simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using hbound
  unfold OrdinaryMessageCodec.upAdmissible ActiveFollowerQueueOperation.upOfferFields
  exact Or.inr ⟨hpositive, hstartBound, hdomain.1.1,
    hdomain.1.2.1, hdomain.1.2.2⟩

private theorem checkedUpOffer_of_fields
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hstatus : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state)
    (hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation time)
    (hfields : U.val = ActiveFollowerQueueOperation.upOfferFields state) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
      .offer U := by
  have hstateDomain := ActualReferenceInitializationBlock.up_domain_of_local_domain state hdomain
  have hadmissible := upOfferFields_admissible state hdomain hpositive
  have hU : (⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩ :
      OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) = U :=
    Subtype.ext hfields.symm
  have hselectedState : ActiveFollowerQueueOperation.selectedUpRound i row activation time ∧
      state.status = .unoccupied := ⟨hselected, hstatus⟩
  unfold ActiveFollowerQueueOperation.checkedUpOffer
  simp only [dite_eq_left hstateDomain, dite_eq_left hselectedState,
    dite_eq_left hadmissible]
  exact congrArg ActiveFollowerQueueOperation.UpOfferResult.offer hU

private theorem actual_choice_domains_of_preparation
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice choiceMemory) :
    ∃ before : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
        record.input.state.followers i = .ordinary before memory ∧
        ActiveFollowerLifecycle.localStateDomainValid before ∧
        ActiveFollowerLifecycle.localStateDomainValid choice ∧
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (choice, choiceMemory) := by
  have hprepared : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i
  have hdeclared :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).configuration = .ordinary choice choiceMemory := by
    change (record.output.preparation.followers.followers i).configuration = _ at hconfiguration
    rw [hprepared] at hconfiguration
    exact hconfiguration
  obtain ⟨before, memory, hinput, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i) choice choiceMemory hdeclared
  have hdomainBefore : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hbad
    have hdecision : ActiveFollowerLifecycle.interruptionDecision rate.eta
        record.input.time before memory = .error .invalidLocalStateDomain := by
      simp [ActiveFollowerLifecycle.interruptionDecision, hbad]
    have hstart' := hstart
    unfold ActiveFollowerLifecycle.startRound at hstart'
    rw [hdecision] at hstart'
    cases hstart'
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
    before choice memory choiceMemory hstart
  rcases hframe with ⟨_hdown, hS, hdelta, hbacklog, hbatch, hbuffer,
    _hfailure, _hmemory⟩
  have hdomainChoice : ActiveFollowerLifecycle.localStateDomainValid choice := by
    rcases hdomainBefore with ⟨hservice, hbufferDomain, hbatchDomain⟩
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨by simpa only [hS] using hservice.1,
        by simpa only [hdelta] using hservice.2.1,
        by simpa only [hbacklog] using hservice.2.2⟩
    · simpa [ActiveFollowerLifecycle.localBufferValid, hbuffer] using hbufferDomain
    · simpa [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hbatchDomain
  exact ⟨before, memory, hinput, hdomainBefore, hdomainChoice, hstart⟩

private theorem actual_positive_choice_eq_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hstatus : state.status = .unoccupied)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice choiceMemory) :
    choice = state ∧ choiceMemory = memory := by
  have hprepared : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i
  have hdeclared :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (.ordinary state memory)).configuration = .ordinary choice choiceMemory := by
    change (record.output.preparation.followers.followers i).configuration = _ at hconfiguration
    rw [hprepared, hinput] at hconfiguration
    exact hconfiguration
  obtain ⟨inputState, inputMemory, hinputState, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
      choice choiceMemory hdeclared
  have hinputEq : inputState = state ∧ inputMemory = memory := by
    rcases DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hinputState with
      ⟨hstate, hmemory⟩
    exact ⟨hstate.symm, hmemory.symm⟩
  have hstartState : ActiveFollowerLifecycle.startRound rate.eta record.input.time state memory =
      .ok (choice, choiceMemory) := by
    simpa [hinputEq.1, hinputEq.2] using hstart
  have hunoccupied := ActiveFollowerLifecycle.startRound_unoccupied rate.eta
    record.input.time state memory hdomain hstatus
  have hsame : (choice, choiceMemory) = (state, memory) :=
    Except.ok.inj (hstartState.symm.trans hunoccupied)
  exact Prod.mk.inj hsame

private theorem actual_cutoff_follower_properties
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
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcutIndex : (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records[
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length]? = some cutRecord) :
    ∀ i : Fin (p.m - 1),
      ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        cutRecord.input.state.followers i = .ordinary before memory ∧
        (ReferenceFollowerFixedReply.actualChoice cutRecord i).configuration =
          .ordinary { before with status := .unoccupied } memory ∧
        ActiveFollowerLifecycle.localStateDomainValid
          { before with status := .unoccupied } ∧
        ActiveFollowerLifecycle.startRound rate.eta cutRecord.input.time before memory =
          .ok ({ before with status := .unoccupied }, memory) := by
  classical
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let seed (a : Fin (p.m - 1)) :=
    ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower a)
  let seedMemory (_a : Fin (p.m - 1)) := ActiveFollowerLifecycle.initialMemory p
  have hRun : E = ReferenceActivePhysicalHorizon.run initial rows selected rewards s count
      hspan active := by
    rfl
  have hshortRun :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards s count
          hspan active).records).length < count := by
    simpa [E, initial, active,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hshort
  have hseedAll := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hseedAll with ⟨_, hactive, _, hfirst, _, _, _, hseedFields⟩
  have hseedProperties (a : Fin (p.m - 1)) :
      initial.followers a = .ordinary (seed a) (seedMemory a) ∧
      (seed a).lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart (seed a) = 0 ∧
      (seed a).S = 0 ∧ (seed a).delta = 0 ∧ (seed a).backlog = 0 ∧
      (seed a).status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid (seed a) ∧
      ActiveFollowerLifecycle.localBufferValid (seed a) ∧
      (seed a).buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
      ∀ saved, saved ∈ (seed a).buffer → saved.calendarRound ≤ s := by
    simpa [initial, seed, seedMemory,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hseedFields a
  have hseedOrd : ∀ a, initial.followers a = .ordinary (seed a) (seedMemory a) :=
    fun a => (hseedProperties a).1
  have hseedNone : ∀ a, (seed a).lastDown = none := fun a => (hseedProperties a).2.1
  have hseedS : ∀ a, (seed a).S = 0 := fun a => (hseedProperties a).2.2.2.1
  have hseedDelta : ∀ a, (seed a).delta = 0 := fun a => (hseedProperties a).2.2.2.2.1
  have hseedBacklog : ∀ a, (seed a).backlog = 0 := fun a => (hseedProperties a).2.2.2.2.2.1
  have hseedUnoccupied : ∀ a, (seed a).status = .unoccupied :=
    fun a => (hseedProperties a).2.2.2.2.2.2.1
  have hseedDomain : ∀ a, ActiveFollowerLifecycle.localStateDomainValid (seed a) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.1
  have hseedBuffer : ∀ a, ActiveFollowerLifecycle.localBufferValid (seed a) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.1
  have hseedPair : ∀ a, (seed a).buffer.Pairwise
      (fun x y => x.calendarRound < y.calendarRound) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.2.1
  have hseedTime : ∀ a saved, saved ∈ (seed a).buffer → saved.calendarRound ≤ s :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.2.2
  have hseedBatch : ∀ a, ActiveFollowerLifecycle.downDecoderStateValid (seed a) := by
    intro a
    exact (hseedDomain a).2.2
  have hcutPrep :=
    ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
      initial rows selected rewards s count hspan hactive hfirst seed seedMemory
      hseedOrd hseedS hseedDelta hseedBacklog hseedNone hseedUnoccupied hseedBuffer
      hseedPair hseedTime hseedBatch hshortRun
  rcases hcutPrep with ⟨cut, suffix, hsplit, hcutInRun, hcutTime, hcutStateRun,
    _hcutRows, _hcutSelected, _hcutRewards, hcutFollowers, _hcutFeedback,
    _hcutEntries⟩
  have hw : w < E.records.length := (List.getElem?_eq_some_iff.mp hcutIndex).1
  have hcutAt : cut = E.records[w]'hw := by
    have hActiveProof : active = hactive := Subsingleton.elim _ _
    cases hActiveProof
    simpa [hRun, w] using hcutInRun
  have hcutLookup : E.records[w]? = some cut := by
    rw [List.getElem?_eq_getElem hw]
    exact congrArg some hcutAt.symm
  have hcutEq : cut = cutRecord := Option.some.inj (hcutLookup.symm.trans hcutIndex)
  intro i
  obtain ⟨before, memory, hbefore, _hstatusFacts, _hoccupiedFacts, hstartRound, hprepareCut,
    hlocalDomain, _hmass, _hSBound, _hDeltaBound, _hBacklogBound, _hBufferPair,
    _hBufferTime, _hfields, _hOffer, _hNotOffer, _hPilot, _hNoSelected⟩ := hcutFollowers i
  have hbeforeCut : cutRecord.input.state.followers i = .ordinary before memory := by
    calc
      cutRecord.input.state.followers i = cut.input.state.followers i := by
        rw [hcutEq]
      _ = _ := by
        rw [hcutStateRun]
        exact hbefore
  let cutChoice : ReferencePrelaunchFollower.State p rate.eta :=
    { before with status := .unoccupied }
  have hconfigCut : (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
      .ordinary cutChoice memory := by
    simpa [cutChoice, ReferenceFollowerFixedReply.actualChoice] using hprepareCut
  have hprepare : (ReferenceFollowerFixedReply.actualChoice cutRecord i).configuration =
      .ordinary cutChoice memory := by
    rw [← hcutEq]
    exact hconfigCut
  have hlocalDomain' : ActiveFollowerLifecycle.localStateDomainValid cutChoice := by
    simpa [cutChoice] using hlocalDomain
  have hstartRound' : ActiveFollowerLifecycle.startRound rate.eta cutRecord.input.time before memory =
      .ok (cutChoice, memory) := by
    simpa [cutChoice, hcutEq] using hstartRound
  exact ⟨before, memory, hbeforeCut, hprepare, hlocalDomain', hstartRound'⟩

/-- The actual checked cutoff initializer resets pending before service;
successful START preserves that reset. No FINISH ledger is used as PRECHOICE. -/
private theorem cutoff_execution_pending
    {cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    {payload : ReferenceActivePhysicalStep.Payload rate}
    {finished : ReferenceActivePhysicalStep.Ledger rate}
    (execution : ReferenceFirstCollectionReadyStream.CutoffExecution cut payload finished) :
    execution.initial.pending = Finset.univ ∧
      execution.started.pending = Finset.univ := by
  have hinitial : execution.initial.pending = Finset.univ := by
    have h := execution.checkedInitialization
    unfold ReferenceCollectionSegmentExtraction.Initializer.checkedStart
      CoordinatorCollectionLedger.startCollectionChecked at h
    split at h
    · dsimp only at h
      split at h
      · exact (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.pending)
          (CoordinatorCollectionLedger.Checked.success.inj h)).symm
      · cases h
    · cases h
  have hcandidate := CollectionCheckedExecution.startRound_success_candidate
    execution.initial execution.started (cut.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled execution.initial cut.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder execution.recording)
    execution.startSuccess
  refine ⟨hinitial, ?_⟩
  rw [hcandidate]
  exact hinitial

private theorem actual_choice_fixed_offer
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (terminal : ReferencePrelaunchFollower.State p rate.eta)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice choiceMemory)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hstatus : choice.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart choice)
    (hterminalFields : U.val = ActiveFollowerQueueOperation.upOfferFields terminal)
    (hreply : ReferenceFollowerReplyChronology.reply choice =
      ReferenceFollowerReplyChronology.reply terminal)
    (hslot : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time choice = .offer U ∧
    ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
      (ReferenceFollowerFixedReply.actualChoice record i)
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
        some (encodedUpOfferWord U) ∧
    ReferenceFollowerFixedReply.actualUpExpected record = some (encodedUpOfferWord U) := by
  have hfieldsChoice : U.val = ActiveFollowerQueueOperation.upOfferFields choice := by
    exact hterminalFields.trans (upOfferFields_eq_of_reply_eq hreply).symm
  have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time :=
    ⟨record.input.active i, hslot, hselected⟩
  have hoff := checkedUpOffer_of_fields i record.input.row
    (record.input.state.activations i) record.input.time choice U hdomain hstatus
    hpositive hselectedUp hfieldsChoice
  have hsender : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    exact hselected
  have halignment := ReferenceFollowerFixedReply.actualChoice_alignment record i
  have hactivation : (ReferenceFollowerFixedReply.actualChoice record i).activation =
      record.input.state.activations i := by
    simpa [ReferenceFollowerFixedReply.actualChoice] using
      (record.output.preparation.follower_alignment i).2.2.2
  have hoffPrepared : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time choice = .offer U := by
    simpa only [halignment.1, halignment.2.1, hactivation, halignment.2.2] using hoff
  have hfixed := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer record i
    hsender choice choiceMemory hconfiguration U hoffPrepared
  have hword := ReferenceUpReception.currentOfferWord_eq_encoded_offer rate
    record.input.row i record.input.time (ReferenceFollowerFixedReply.actualChoice record i)
    (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
    (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
    (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2
    choice choiceMemory hconfiguration U hoffPrepared
  have hflat := encodedUpOfferWord_eq_flat (p := p) (rate := rate) U
  have hword' : ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
      (ReferenceFollowerFixedReply.actualChoice record i)
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
      (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
        some (encodedUpOfferWord U) := by
    rw [hflat]
    exact hword
  have hfixed' : ReferenceFollowerFixedReply.actualUpExpected record =
      some (encodedUpOfferWord U) := by
    rw [hflat]
    exact hfixed
  exact ⟨hoff, hword', hfixed'⟩

private theorem executed_tail_of_choice
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x = some
      ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hselection : prepared.coordinator.selection ≠ none := by
    intro hnone
    simp [ReferenceCollectionSegmentExtraction.choice, prepared, hnone] at hchoice
  have hcut : ReferenceCollectionSegmentExtraction.choiceOfCut prepared.coordinator =
      some c := by
    simpa [ReferenceCollectionSegmentExtraction.choice, prepared, hselection] using hchoice
  cases hcoord : prepared.coordinator with
  | first outcome => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
        simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
        have hc := Option.some.inj hcut
        cases hc
        unfold ReferenceCollectionPhaseHistory.executedTail
        dsimp only [prepared]
        rw [ite_eq_right hselection, hcoord]
      | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
        simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
        have hc := Option.some.inj hcut
        cases hc
        unfold ReferenceCollectionPhaseHistory.executedTail
        dsimp only [prepared]
        rw [ite_eq_right hselection, hcoord]
      | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
  | invalidCollectionCutoff => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
  | dagger => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut

private theorem actual_continuing_receiver_from_cell
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (j count start : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
      source rewards records j count start r payload ledger saved)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hi : i ∈ ledger.pending)
    (hUsigma : U.val.sigma = ledger.sigma)
    (hExpected : (hslot : PublicDiscreteDraws.slotDraw
        (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot) →
      (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i) →
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
        some (encodedUpOfferWord U)) :
    ∃ (tail : ReferenceCollectionPhaseHistory.Tail r.input)
      (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      tail.payload = payload ∧ tail.ledger = ledger ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
        some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L ∧
      L = cell.started ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      r.output.coordinator.up = some diagnostic ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
      diagnostic.input.time = r.input.time ∧
      diagnostic.input.affineSample =
        ((r.input.rows r.input.selected).2 r.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time)) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      i ∈ L.pending ∧
      CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
      ((hslot : PublicDiscreteDraws.slotDraw
          (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot) →
        (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 = i) →
        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
          ReferenceCollectionPhaseHistory.filteredParsed r.input L = some M → M = U) ∧
        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
          ReferenceCollectionPhaseHistory.AcceptedUp r.input i M → M = U)) := by
  have hchoiceTail := executed_tail_of_choice r.input cell.choice cell.actualChoice
  let tail : ReferenceCollectionPhaseHistory.Tail r.input :=
    ⟨cell.choice.payload, cell.choice.preLedger, cell.choice.started, cell.choice.weights⟩
  have htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail := by
    simpa [tail] using hchoiceTail
  have hstate : r.input.state.coordinator = .collection payload ledger saved :=
    cell.readyInput.1
  have hordinary : r.output.next.coordinator ≠ .dagger := by
    intro hdagger
    rw [cell.serviceNextCoordinator] at hdagger
    cases hdagger
  obtain ⟨recording, L, diagnostic, hrecording, hstart, hsite, hcheck,
    hdiagnostic, hinput, htailReception, hnoninvalid, hrest⟩ :=
    ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver
      r payload ledger saved tail hstate htail hordinary
  have htime : diagnostic.input.time = r.input.time := by
    rw [hinput]
    simp [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceUpReception.receptionInputAtRow_inputTime,
      ReferenceActivePhysicalStep.upInputs]
  have hsample : diagnostic.input.affineSample =
      ((r.input.rows r.input.selected).2 r.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((r.input.rows r.input.selected).2 r.input.time)) := by
    rw [hinput]
    simp [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceUpReception.receptionInputAtRow_affineSample,
      ReferenceActivePhysicalStep.RoundInput.row]
    rfl
  have hobservation : diagnostic.input.ownObservation =
      (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
        (ActiveRoundActions.coordinator p.two_le_m) := by
    rw [hinput]
    rfl
  have hsameStart : L = cell.started := by
    have hrecordingCell : recording = cell.recording := by
      have h := hrecording.symm.trans cell.actualRecording
      exact Option.some.inj (by simpa [tail] using h)
    have hstartCell : CoordinatorCollectionLedger.startRound ledger
        (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success cell.started := by
      simpa [tail, cell.choiceLedger, hrecordingCell] using cell.actualStart
    have hstart' : CoordinatorCollectionLedger.startRound ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success L := by simpa [tail, cell.choiceLedger] using hstart
    exact CoordinatorCollectionLedger.Checked.success.inj (hstart'.symm.trans hstartCell)
  have hcandidate := CollectionCheckedExecution.startRound_success_candidate ledger
    cell.started (r.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder cell.recording)
    cell.actualStart
  have hpendingStarted : i ∈ cell.started.pending := by
    rw [hcandidate]
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using hi
  have hpendingL : i ∈ L.pending := by rw [hsameStart]; exact hpendingStarted
  have hsigmaStarted : cell.started.sigma = ledger.sigma := by
    rw [hcandidate]
    simp [CoordinatorCollectionLedger.startRoundCandidate]
  have hsigmaL : U.val.sigma = L.sigma := by
    rw [hsameStart]
    exact hUsigma.trans hsigmaStarted.symm
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff
    (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L)).mp hcheck
  rcases CoordinatorUpReception.receptionInputDomain_parts
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) hdomain with
    ⟨_, _, _, _, hcutoffCursor, _, _, _⟩
  have haccept : CoordinatorCollectionLedger.acceptUpCheck L i U = true := by
    apply (CoordinatorCollectionLedger.acceptUpCheck_iff L i U).2
    refine ⟨hcutoffCursor, ?_, hsigmaL⟩
    simpa [CoordinatorCollectionLedger.pendingNaturalLabels_mem_iff] using hpendingL
  refine ⟨tail, recording, L, diagnostic, htail, ?_, ?_, hrecording, hstart,
    hsameStart, hsite, hcheck, hdiagnostic, hinput, htailReception, hnoninvalid,
    htime, hsample, hobservation, hpendingL, haccept, ?_⟩
  · exact cell.choicePayload
  · exact cell.choiceLedger
  · intro hslot hselected
    have hexpected := hExpected hslot hselected
    exact ⟨fun M hparsed => filteredParsed_expected_unique r L U M hexpected hparsed,
      fun M haccepted => acceptedUp_expected_unique r i U M hexpected haccepted⟩

/-- Compose the admitted state interval with one actual formed-UP record and
the ordinary UP receiver at every positive continuing coordinate. The cutoff
coordinate retains its own execution and rejected receive, while the fixed
offer and sender word are shared across the whole post-formation interval. -/
public theorem actual_initialized_first_collection_formed_up_offer_receiver
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
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        E.records[w]? = some cutRecord ∧
        cutRecord.input.state.coordinator = .live registers owned base ∧
        registers.payload = out.payload ∧
        out.cutoff.ledger.pending = Finset.univ ∧
        ∃ hBpos : 0 < B.length,
          B[0]'hBpos = cutRecord ∧
        out.cutoff.cut = cutRecord ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : ReferenceActivePhysicalStep.Ledger rate)
                (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  source rewards E.records (w + n.val) count s
                  r out.payload incoming out.saved)
                (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 = s + w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                cell.serviceLedger = out.ledgers n ∧
                r.input.state.followers i = .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
                state.S + state.backlog ≤ w * D p ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  state.lastDown = some (out.payload.downRecord i)) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  ∃ (U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta)),
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    U.val.sigma = s + 1 ∧
                    1 ≤ U.val.sigma ∧
                    (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
                      PublicDiscreteDraws.slotDraw
                          (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                            .ordinary state memory ∧
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                          (r.input.state.activations i) r.input.time state = .offer U ∧
                        ReferenceFollowerFixedReply.actualUpExpected r =
                          some ((OrdinaryMessageCodec.wordEquivFlat
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                            (OrdinaryMessageCodec.encodeUp
                              (CoordinatorCollectionLedger.codecParams p rate.eta.val) U))) ∧
                    (out.payload.downRecord i).val.sigma = s + 1 ∧
                    ReferencePrelaunchFollower.acceptedStart state = s + 1 ∧
                    ∃ (j : ℕ) (hjIndex : j < E.records.length)
                      (acceptedRecord : ReferenceActivePhysicalHorizon.RoundRecord
                        (p := p) (rate := rate)),
                      j < w + n.val ∧ E.records[j]? = some acceptedRecord ∧
                      ReferenceAcceptedUpFollowerHistory.RetainedDown
                        (E.records[j]'(hjIndex)) i
                        (out.payload.downRecord i) ∧
                      (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                        (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                        (after : ReferencePrelaunchFollower.State p rate.eta)
                        (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
                        (scan : FollowerCutoffScan.ScanResult p.T)
                        (registers' : ℕ × ℕ) (lastService : ℕ),
                        (acceptedRecord.output.followers i).downInput = some logged ∧
                        (acceptedRecord.output.followers i).down = some cut ∧
                        cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                          logged after raw (out.payload.downRecord i) scan registers' lastService) ∧
                      acceptedRecord.input.time.val + 1 = s + j + 1 ∧
                      acceptedRecord.input.rows = source.1.2 ∧
                      acceptedRecord.input.selected =
                        ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                      acceptedRecord.input.rewards = rewards ∧
                      (∀ (j' : ℕ) (hjPrimeIndex : j' < E.records.length)
                        (other : ReferenceActivePhysicalHorizon.RoundRecord
                          (p := p) (rate := rate)),
                        j' < w + n.val → E.records[j']? = some other →
                          ReferenceAcceptedUpFollowerHistory.RetainedDown
                            (E.records[j']'(hjPrimeIndex)) i
                            (out.payload.downRecord i) → j' = j) ∧
                      let f := if j < w then 0 else j - w + 1
                      ∃ hf : f < B.length,
                        f ≤ n.val ∧
                        B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) ∧
                        (j < w → f = 0) ∧
                        (j = w → f = 1) ∧
                        (∀ (k : Fin B.length) (_hkpos : 0 < k.val)
                          (hkn : k.val ≤ n.val),
                          (out.ledgers ⟨n.val - 1, by omega⟩).pending ⊆
                            (out.ledgers ⟨k.val - 1, by omega⟩).pending) ∧
                        ∀ (k : Fin B.length) (hfk : f ≤ k.val)
                          (hkn : k.val ≤ n.val),
                          ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                            (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).configuration = .ordinary choice choiceMemory ∧
                            ActiveFollowerLifecycle.localStateDomainValid choice ∧
                            choice.status = .unoccupied ∧
                            ReferenceFollowerReplyChronology.reply choice =
                              ReferenceFollowerReplyChronology.reply state ∧
                            choice.lastDown = some (out.payload.downRecord i) ∧
                            choice.S = state.S ∧ choice.delta = state.delta ∧
                            choice.backlog = state.backlog ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).row =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.row ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).follower = i ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).activation =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.state.activations i ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).time =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.time ∧
                            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
                              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.state.followers i =
                                  .ordinary before beforeMemory ∧
                              ActiveFollowerLifecycle.localStateDomainValid before ∧
                              ActiveFollowerLifecycle.startRound rate.eta
                                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                  B k).input.time before beforeMemory =
                                  .ok (choice, choiceMemory) ∧
                              ReferenceFollowerReplyChronology.reply choice =
                                ReferenceFollowerReplyChronology.reply before ∧
                              ((k.val = 0 →
                                i ∈ out.cutoff.ledger.pending ∧
                                out.cutoff.ledger.pending = Finset.univ ∧
                                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                  B k).input.state.coordinator = .live registers owned base ∧
                                E.records[w]? = some cutRecord) ∧
                               (0 < k.val →
                                i ∈ (out.ledgers ⟨k.val - 1, by omega⟩).pending ∧
                                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                                i ∈ incoming.pending)) ∧
                              ((hslot : PublicDiscreteDraws.slotDraw
                                  (((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k).input.row).2
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input.time).1 = PublicDiscreteDraws.upSlot) →
                                (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                                  p.m_lt_K
                                  (((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k).input.row).2
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input.time).1 = i) →
                                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.row
                                    ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.state.activations i)
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.time choice = .offer U ∧
                                  ReferenceUpReception.currentOfferWord rate
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.row i
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.time
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                                      B i k)
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).1
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).2.1
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).2.2 = some (encodedUpOfferWord U) ∧
                                  ReferenceFollowerFixedReply.actualUpExpected
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k) = some (encodedUpOfferWord U) ∧
                                  ReferenceActivePhysicalStep.upExpected
                                    (ReferenceActivePhysicalStep.prepare
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input) = some (encodedUpOfferWord U)) ∧
                              (k.val = 0 →
                                ∃ (cutBefore : ReferencePrelaunchFollower.State p rate.eta)
                                  (cutMemory : ActiveFollowerLifecycle.LocalMemory p),
                                  cutRecord.input.state.followers i =
                                    .ordinary cutBefore cutMemory ∧
                                  (ReferenceFollowerFixedReply.actualChoice cutRecord i).configuration =
                                    .ordinary { cutBefore with status := .unoccupied } cutMemory ∧
                                  ActiveFollowerLifecycle.localStateDomainValid
                                    { cutBefore with status := .unoccupied } ∧
                                  ActiveFollowerLifecycle.startRound rate.eta cutRecord.input.time
                                    cutBefore cutMemory =
                                      .ok ({ cutBefore with status := .unoccupied }, cutMemory) ∧
                                  Nonempty (ReferenceFirstCollectionReadyStream.CutoffExecution
                                    out.cutoff.cut out.cutoff.payload out.cutoff.ledger) ∧
                                  ∃ execution : ReferenceFirstCollectionReadyStream.CutoffExecution
                                      cutRecord out.cutoff.payload out.cutoff.ledger,
                                    execution.initial.pending = Finset.univ ∧
                                    execution.started.pending = Finset.univ) ∧
                              (0 < k.val →
                                ∃ (jK : ℕ)
                                  (recordK : ReferenceActivePhysicalHorizon.RoundRecord
                                    (p := p) (rate := rate))
                                  (incomingK : ReferenceActivePhysicalStep.Ledger rate)
                                  (cellK : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                                    source rewards E.records jK count s recordK
                                    out.payload incomingK out.saved),
                                  jK = w + k.val ∧
                                  out.window[k.val]? = some recordK ∧
                                  cellK.serviceLedger = out.ledgers ⟨k.val, by omega⟩ ∧
                                  incomingK = out.ledgers ⟨k.val - 1, by omega⟩ ∧
                                  (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k) = recordK ∧
                                  recordK.input.state.coordinator =
                                    .collection out.payload incomingK out.saved ∧
                                  recordK.input.time.val + 1 = s + w + 1 + k.val ∧
                                  recordK.input.rows = source.1.2 ∧
                                  recordK.input.selected =
                                    ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                                  recordK.input.rewards = rewards ∧
                                  choice = before ∧ choiceMemory = beforeMemory ∧
                                  ∃ (tail : ReferenceCollectionPhaseHistory.Tail recordK.input)
                                    (recording : CoordinatorRecordingOperation.Output p)
                                    (L : ReferenceActivePhysicalStep.Ledger rate)
                                    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                                    ReferenceCollectionPhaseHistory.executedTail recordK.input =
                                      some tail ∧
                                    tail.payload = out.payload ∧ tail.ledger = incomingK ∧
                                    CoordinatorRecorderComplementBridge.run
                                      (ReferenceActivePhysicalStep.collectionRecordingInput
                                        (ReferenceActivePhysicalStep.prepare recordK.input)
                                        tail.payload tail.started tail.weights) = some recording ∧
                                    CoordinatorCollectionLedger.startRound tail.ledger
                                      (recordK.input.time.val + 1)
                                      (ReferenceActivePhysicalStep.collectionEnabled tail.ledger
                                        recordK.input.time)
                                      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder
                                        recording) = .success L ∧
                                    L = cellK.started ∧
                                    ReferenceCoordinatorUpPhysicalCall.siteLedger?
                                      (x := recordK.input) = some L ∧
                                    CoordinatorUpReception.receptionInputCheck
                                      (ReferenceCoordinatorUpPhysicalCall.actualUpInput
                                        recordK.input L) = true ∧
                                    recordK.output.coordinator.up = some diagnostic ∧
                                    diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput
                                      recordK.input L ∧
                                    tail.reception = some (L,
                                      ReferenceActivePhysicalStep.receiveUp
                                        (ReferenceActivePhysicalStep.prepare recordK.input) L) ∧
                                    (ReferenceActivePhysicalStep.receiveUp
                                      (ReferenceActivePhysicalStep.prepare recordK.input) L).result ≠
                                        .invalid ∧
                                    diagnostic.input.time = recordK.input.time ∧
                                    diagnostic.input.affineSample =
                                      ((recordK.input.rows recordK.input.selected).2
                                        recordK.input.time).2
                                        (1, CoordinatorUpMeasurability.selectedChannelFollower
                                          ((recordK.input.rows recordK.input.selected).2
                                            recordK.input.time)) ∧
                                    diagnostic.input.ownObservation =
                                      (ReferenceActivePhysicalStep.prepare recordK.input).feedback.feedback
                                        (ActiveRoundActions.coordinator p.two_le_m) ∧
                                    i ∈ L.pending ∧
                                    CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                                    ((hslot : PublicDiscreteDraws.slotDraw
                                        (recordK.input.row.2 recordK.input.time).1 =
                                          PublicDiscreteDraws.upSlot) →
                                      (hselected : PublicDiscreteDraws.selectedFollowerDraw
                                        p.two_le_m p.m_lt_K
                                        (recordK.input.row.2 recordK.input.time).1 = i) →
                                        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
                                          ReferenceCollectionPhaseHistory.filteredParsed
                                            recordK.input L = some M → M = U) ∧
                                        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
                                          ReferenceCollectionPhaseHistory.AcceptedUp
                                            recordK.input i M → M = U))))) := by
  classical
  obtain ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hboundaries⟩ :=
    ReferenceFirstCollectionFormedReplyStateInterval.actual_initialized_first_collection_formed_reply_state_interval
      rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hWindow : out.window = B := by
    simpa [out, E, w, B, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  have hBpos : 0 < B.length := by simpa [hWindow] using out.windowNonempty
  have houtPos : 0 < out.window.length := by simpa using out.windowNonempty
  have hentryZero : out.window[0]? = some (B[0]'hBpos) := by
    rw [hWindow]
    exact List.getElem?_eq_some_iff.mpr ⟨hBpos, rfl⟩
  have helemZero : out.window[0]'houtPos = B[0]'hBpos :=
    (List.getElem?_eq_some_iff.mp hentryZero).2
  have halignZero := out.alignment ⟨0, out.windowNonempty⟩
  have hrootB0 : E.records[w]? = some (B[0]'hBpos) := by
    have hroot : E.records[w]? = some (out.window[0]'houtPos) := by
      simpa [out, E, w, Nat.add_zero,
        ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using halignZero.1
    simpa [helemZero] using hroot
  have hcutB0 : B[0] = cutRecord := Option.some.inj (hrootB0.symm.trans hcutIndex)
  have hcutoffRecord : out.cutoff.cut = cutRecord := by
    calc
      out.cutoff.cut = out.window[0]'houtPos := out.cutoffIsHead.symm
      _ = B[0] := helemZero
      _ = cutRecord := hcutB0
  refine ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hBpos, hcutB0, hcutoffRecord, ?_⟩
  intro n hn i hi
  rcases hboundaries n hn i hi with
    ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
      hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
      hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast,
      hboundaryOffer, horigin⟩
  refine ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
    hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
    hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast, ?_⟩
  intro hformed
  obtain ⟨U, hUfields, hUpositive, hcurrentOffer⟩ := hboundaryOffer hformed
  obtain ⟨hmessageSigma, hstart, j, acceptedRecord, hj, hlookup, hretained,
    hdiagnostics, hacceptedTime, hacceptedRows, hacceptedSelected,
    hacceptedRewards, hunique, hf, hfn, hdate, hjw0, hjw1, hinterval⟩ :=
    horigin hformed
  have hjIndex : j < E.records.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have hunique' : ∀ (j' : ℕ) (hj'Index : j' < E.records.length)
      (other : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      j' < w + n.val → E.records[j']? = some other →
        ReferenceAcceptedUpFollowerHistory.RetainedDown (E.records[j']'(hj'Index)) i
          (out.payload.downRecord i) → j' = j := by
    intro j' hj'Index other hj' hlookup' hretained'
    have helemOther : E.records[j']'(hj'Index) = other := by
      exact (List.getElem?_eq_some_iff.mp hlookup').2
    have hretainedOther :
        ReferenceAcceptedUpFollowerHistory.RetainedDown other i (out.payload.downRecord i) := by
      rw [← helemOther]
      exact hretained'
    exact hunique j' other hj' hlookup' hretainedOther
  have hUsigma : U.val.sigma = s + 1 := by
    calc
      U.val.sigma = ReferencePrelaunchFollower.acceptedStart state := by
        rw [hUfields]
        rfl
      _ = s + 1 := hstart
  have hcurrentOffer' :
      (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
        PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.upSlot →
          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
              .ordinary state memory ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
            (r.input.state.activations i) r.input.time state = .offer U ∧
          ReferenceFollowerFixedReply.actualUpExpected r = some (encodedUpOfferWord U)) := by
    intro hsender hslot
    rcases hcurrentOffer hsender hslot with ⟨hconfig, hoff, hflat⟩
    have hencoded : ReferenceFollowerFixedReply.actualUpExpected r =
        some (encodedUpOfferWord U) := by
      rw [encodedUpOfferWord_eq_flat]
      exact hflat
    exact ⟨hconfig, hoff, hencoded⟩
  have hlastSome : state.lastDown = some (out.payload.downRecord i) := hformed
  let f := if j < w then 0 else j - w + 1
  have hretainedIndex :
      ReferenceAcceptedUpFollowerHistory.RetainedDown (E.records[j]'(hjIndex)) i
        (out.payload.downRecord i) := by
    have hrecordElem : E.records[j]'(hjIndex) = acceptedRecord :=
      (List.getElem?_eq_some_iff.mp hlookup).2
    rw [hrecordElem]
    exact hretained
  rcases hinterval with ⟨hpendingInterval, hAt⟩
  refine ⟨U, hUfields, hUsigma, hUpositive, hcurrentOffer', hmessageSigma, hstart,
    j, hjIndex, acceptedRecord, hj, hlookup, hretainedIndex, hdiagnostics,
    hacceptedTime, hacceptedRows, hacceptedSelected, hacceptedRewards,
    hunique', ?_⟩
  refine ⟨by simpa only [f] using hf,
    by simpa only [f] using hfn,
    by simpa only [f] using hdate,
    by simpa only [f] using hjw0,
    by simpa only [f] using hjw1,
    hpendingInterval, ?_⟩
  intro k hfk hkn
  have hfk' : (if j < w then 0 else j - w + 1) ≤ k.val := by
    simpa only [f] using hfk
  rcases hAt k hfk' hkn with
      ⟨choice, choiceMemory, hconfiguration, hstatusChoice, hreply, hchoiceDown,
        hchoiceS, hchoiceDelta, hchoiceBacklog, hrowChoice, hfollowerChoice,
        hactivationChoice, htimeChoice, before, beforeMemory, hbefore,
        hreplyBefore, hpendingCases⟩
  let record := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k
  change (ReferenceFollowerFixedReply.actualChoice record i).configuration =
    .ordinary choice choiceMemory at hconfiguration
  obtain ⟨beforePrepared, memoryPrepared, hinputPrepared, hdomainBeforePrepared,
    hdomainChoice, hstartPrepared⟩ :=
    actual_choice_domains_of_preparation record i choice choiceMemory hconfiguration
  have hinputEq : beforePrepared = before ∧ memoryPrepared = beforeMemory := by
    have hcfg : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
        beforePrepared memoryPrepared = .ordinary before beforeMemory :=
      hinputPrepared.symm.trans hbefore
    exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hcfg
  have hdomainBefore : ActiveFollowerLifecycle.localStateDomainValid before := by
    rw [← hinputEq.1]
    exact hdomainBeforePrepared
  have hstartBefore : ActiveFollowerLifecycle.startRound rate.eta record.input.time
      before beforeMemory = .ok (choice, choiceMemory) := by
    rw [← hinputEq.1, ← hinputEq.2]
    exact hstartPrepared
  have hpositiveChoice : 1 ≤ ReferencePrelaunchFollower.acceptedStart choice := by
    have hstartChoice : ReferencePrelaunchFollower.acceptedStart choice = s + 1 := by
      calc
        ReferencePrelaunchFollower.acceptedStart choice =
            ReferencePrelaunchFollower.acceptedStart state := by
          simp [ReferencePrelaunchFollower.acceptedStart, hchoiceDown, hformed]
        _ = s + 1 := hstart
    rw [hstartChoice]
    omega
  have hOffers
      (hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.upSlot)
      (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i) :=
    actual_choice_fixed_offer record i choice choiceMemory state U
      (by simpa [record] using hconfiguration) hdomainChoice hstatusChoice
      hpositiveChoice hUfields hreply hslot hselected
  refine ⟨choice, choiceMemory, hconfiguration, hdomainChoice, hstatusChoice, hreply,
    hchoiceDown, hchoiceS, hchoiceDelta, hchoiceBacklog, hrowChoice,
    hfollowerChoice, hactivationChoice, htimeChoice, before, beforeMemory,
    hbefore, hdomainBefore, hstartBefore, hreplyBefore, hpendingCases,
    ?_, ?_, ?_⟩
  · intro hslot hselected
    have hslot' : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.upSlot := by simpa [record] using hslot
    have hselected' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i := by simpa [record] using hselected
    rcases hOffers hslot' hselected' with ⟨hoff, hword, hfixed⟩
    have hpreparedExpected :
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare record.input) =
            some (encodedUpOfferWord U) := by
      simpa [ReferenceFollowerFixedReply.actualUpExpected,
        ReferenceActivePhysicalStep.step, record.output_eq] using hfixed
    have hwordAligned : ReferenceUpReception.currentOfferWord rate record.input.row i
        record.input.time
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i k)
        (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
        (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
        (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
          some (encodedUpOfferWord U) := by
      simpa [ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice,
        record] using hword
    exact ⟨hoff, by simpa [record] using hwordAligned,
      by simpa [record] using hfixed, hpreparedExpected⟩
  · intro hkzero
    have hkEq : k = ⟨0, by omega⟩ := Fin.ext hkzero
    subst k
    obtain ⟨cutBefore, cutMemory, hcutBefore, hcutChoice, hcutDomain, hcutStart⟩ :=
      actual_cutoff_follower_properties source rewards C_star C_h count
        hcross hspan hshort cutRecord hcutIndex i
    obtain ⟨execution⟩ := out.cutoffExecution
    have hexecution : ReferenceFirstCollectionReadyStream.CutoffExecution
        cutRecord out.cutoff.payload out.cutoff.ledger := by
      rw [← hcutoffRecord]
      exact execution
    exact ⟨cutBefore, cutMemory, hcutBefore, hcutChoice, hcutDomain,
      hcutStart, out.cutoffExecution, hexecution, cutoff_execution_pending hexecution⟩
  · intro hkpos
    let kOut : Fin out.ell := ⟨k.val, lt_of_le_of_lt hkn n.isLt⟩
    obtain ⟨jK, recordK, incomingK, cellK, hjK, hrecordK, hserviceK,
      hincomingK⟩ := out.cell_at kOut hkpos
    have hrecordEntry : out.window[k.val]? = some
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k) := by
      rw [hWindow]
      exact List.getElem?_eq_some_iff.mpr ⟨k.isLt, rfl⟩
    have hrecordEq :
        ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k =
          recordK := Option.some.inj (hrecordEntry.symm.trans hrecordK)
    have hiK : i ∈ incomingK.pending := by
      rw [hincomingK]
      exact (hpendingCases.2 hkpos).1
    obtain ⟨boundaryRecord, boundaryIncoming, boundaryCell, boundaryState, boundaryMemory,
      hboundaryRecord, htimeK, hrowsK, hselectedK, hrewardsK, _hincomingBoundary,
      _hiBoundary, _hreadyBoundary, _hserviceBoundary, hboundaryState, hboundaryStatus,
      _hdomainBoundary, _hSBoundary, _hdeltaBoundary, _hbacklogBoundary, _hmassBoundary,
      _hbankBoundary, _hcompletedBoundary, _hlastBoundary, _hofferBoundary,
      _horiginBoundary⟩ := hboundaries kOut hkpos i (hpendingCases.2 hkpos).1
    have hboundaryEq : boundaryRecord = recordK :=
      Option.some.inj (hboundaryRecord.symm.trans hrecordK)
    have hbeforeK : recordK.input.state.followers i = .ordinary before beforeMemory := by
      rw [← hrecordEq]
      exact hbefore
    have hboundaryStateEq : boundaryState = before ∧ boundaryMemory = beforeMemory := by
      rw [hboundaryEq] at hboundaryState
      exact DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hboundaryState.symm.trans hbeforeK)
    have hbeforeStatus : before.status = .unoccupied := by
      rw [← hboundaryStateEq.1]
      exact hboundaryStatus
    have hchoiceInput := actual_positive_choice_eq_input record i before beforeMemory
      choice choiceMemory hbefore hdomainBefore hbeforeStatus hconfiguration
    rcases cellK.readyInput with
      ⟨_, _, _, _, _, hSigmaCell, _⟩
    have hPayloadSigma : out.payload.sigma.val = s := by
      calc
        out.payload.sigma.val = out.cutoff.payload.sigma.val :=
          congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.sigma.val)
            out.payloadMatchesCutoff
        _ = s := by simpa [s, ReferenceFirstCollectionReadyStream.startTime]
          using out.cutoffContext.2.1
    have hUsigmaCell : U.val.sigma = incomingK.sigma := by
      calc
        U.val.sigma = s + 1 := hUsigma
        _ = out.payload.sigma.val + 1 := by omega
        _ = incomingK.sigma := hSigmaCell.symm
    have hExpectedRecord :
        (hslot : PublicDiscreteDraws.slotDraw
          (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot) →
        (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i) →
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare record.input) =
            some (encodedUpOfferWord U) := by
      intro hslot hselected
      have hslot' : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.upSlot := by simpa [record] using hslot
      have hselected' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i := by simpa [record] using hselected
      have hfixed := (hOffers hslot' hselected').2.2
      simpa [ReferenceFollowerFixedReply.actualUpExpected,
        ReferenceActivePhysicalStep.step, record.output_eq] using hfixed
    have hExpectedCell :
        (hslot : PublicDiscreteDraws.slotDraw
          (recordK.input.row.2 recordK.input.time).1 = PublicDiscreteDraws.upSlot) →
        (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (recordK.input.row.2 recordK.input.time).1 = i) →
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare recordK.input) =
            some (encodedUpOfferWord U) := by
      intro hslot hselected
      have hslotRecord : PublicDiscreteDraws.slotDraw
          (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot := by
        simpa only [← hrecordEq, record] using hslot
      have hselectedRecord : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i := by
        simpa only [← hrecordEq, record] using hselected
      have hExpectedAtRecord := hExpectedRecord hslotRecord hselectedRecord
      have hExpectedActual :
          ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare
              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input) =
            some (encodedUpOfferWord U) := by
        simpa only [record] using hExpectedAtRecord
      rw [hrecordEq] at hExpectedActual
      exact hExpectedActual
    obtain ⟨tail, recording, L, diagnostic, htail, htailPayload, htailLedger,
      hrecording, hstart, hsameStart, hsite, hcheck, hdiagnostic, hinput,
      htailReception, hnoninvalid, htimeInput, hsampleInput, hobservation,
      hpendingL, haccept, hfiltered⟩ :=
      actual_continuing_receiver_from_cell source rewards E.records jK count s
        recordK out.payload incomingK out.saved cellK i U hiK hUsigmaCell hExpectedCell
    refine ⟨jK, recordK, incomingK, cellK, hjK, hrecordK, ?_, ?_, hrecordEq,
      cellK.readyInput.1, ?_, ?_, ?_, ?_, hchoiceInput.1, hchoiceInput.2,
      tail, recording, L, diagnostic, htail, htailPayload, htailLedger,
      hrecording, hstart, hsameStart, hsite, hcheck, hdiagnostic, hinput,
      htailReception, hnoninvalid, htimeInput, hsampleInput, hobservation,
      hpendingL, haccept, hfiltered⟩
    · simpa [kOut] using hserviceK
    · simpa [kOut] using hincomingK
    · simpa only [hboundaryEq, kOut] using htimeK
    · simpa only [hboundaryEq] using hrowsK
    · simpa only [hboundaryEq] using hselectedK
    · simpa only [hboundaryEq] using hrewardsK

end Bandits.Support.ReferenceFirstCollectionFormedUpOfferReceiver

end
