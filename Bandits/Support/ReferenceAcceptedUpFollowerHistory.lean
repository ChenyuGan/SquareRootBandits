/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerReplyChronology
public import Bandits.Support.ReferenceCollectionPhaseHistory

/-!
# Accepted UP sender and prior DOWN history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:108-110`,
`sources/zip4/manuscript/06_interruptions.tex:270-284,303-324,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:104-108`.

These results connect an actually filtered and accepted UP reception to its
actual local sender and retained earlier DOWN diagnostic. They do not identify
the offered fields with global service, score, or queue quantities.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceAcceptedUpFollowerHistory

variable {p : Parameters}

section LocalRate

variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Label (p : Parameters) := Fin (p.m - 1)
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

/-- A retained, locally accepted DOWN diagnostic for this exact record. -/
def RetainedDown
    (record : Record (p := p) (rate := rate)) (i : Label p)
    (message : DownRecord (p := p) (rate := rate)) : Prop :=
  ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ),
    (record.output.followers i).downInput = some logged ∧
    (record.output.followers i).down = some cut ∧
    cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
      logged after raw message scan registers lastService

private theorem acceptedUp_receiver_domain
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {i : Label p} {message : ReferenceCollectionPhaseHistory.UpRecord p rate}
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp x i message) :
    ∃ (started decoded : ReferenceActivePhysicalStep.Ledger rate)
      (input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale),
      ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time = input ∧
      CoordinatorUpReception.receptionInputDomain input ∧
      CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
        (ReferenceCollectionPhaseHistory.filteredParsed x started) = .success decoded ∧
      message.val.sigma = started.sigma ∧ 1 ≤ started.sigma := by
  rcases haccepted with
    ⟨tail, recording, started, decoded, bank, htail, hrecording, hstarted,
      hreceived, hparsed, hindex⟩
  let prepared := ReferenceActivePhysicalStep.prepare x
  let input := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared started) x.time
  have hreceive : ReferenceUpReception.receiveUpFilteredAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared started) x.time
      (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
      (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 rfl = .success (decoded, bank) := by
    simpa only [ReferenceActivePhysicalStep.receiveUp] using hreceived
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    by_cases hcheck : CoordinatorUpReception.receptionInputCheck input = true
    · exact hcheck
    · simp [ReferenceUpReception.receiveUpFilteredAtRow, input, hcheck] at hreceive
  have hdomain : CoordinatorUpReception.receptionInputDomain input :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hcheck
  have hdecode : CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
      (CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition input).2
          (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
            (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
            (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1))) = .success decoded := by
    rw [ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared started) x.time
      (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
      (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 rfl hcheck] at hreceive
    change CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
          (CoordinatorUpReception.parseDecoderOutput
            (ReferenceUpReception.filterRawByExpected
              (CoordinatorUpReception.decoderTransition input).2
              (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
                (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
                (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
                (prepared.follower_alignment _).2.2.1))))
        (CoordinatorUpReception.decoderBankAfter input) = .success (decoded, bank) at hreceive
    cases hresult : CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
        (CoordinatorUpReception.parseDecoderOutput
          (ReferenceUpReception.filterRawByExpected
            (CoordinatorUpReception.decoderTransition input).2
            (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
              (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
              (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
              (prepared.follower_alignment _).2.2.1))) with
    | success out =>
        simp only [CoordinatorUpReception.packDecodeResult, hresult,
          CoordinatorCollectionLedger.Checked.success.injEq] at hreceive
        have hout : out = decoded := (Prod.mk.inj hreceive).1
        exact congrArg
          (fun ledger => CoordinatorCollectionLedger.Checked.success ledger) hout
    | rejected out => simp [CoordinatorUpReception.packDecodeResult, hresult] at hreceive
    | invalid => simp [CoordinatorUpReception.packDecodeResult, hresult] at hreceive
  obtain ⟨parsed, hparsedEq, hacceptUp⟩ :=
    CoordinatorUpReception.decodeUp_success_implies_literal_acceptUp input hdomain
      (CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition input).2
          (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
            (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
            (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1))) decoded hdecode
  have hparsedMessage : parsed = message := by
    have hparsedAtInput : CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition input).2
          (ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower input.time
            (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
            (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1)) = some message := by
      simpa [input, ReferenceCollectionPhaseHistory.filteredParsed,
        ReferenceActivePhysicalStep.upInputs, ReferenceActivePhysicalStep.upExpected,
        ReferenceActivePhysicalStep.upSenderIndex] using hparsed
    exact Option.some.inj (hparsedEq.symm.trans hparsedAtInput)
  subst parsed
  rcases CoordinatorUpReception.receptionInputDomain_parts input hdomain with
    ⟨_, hsigma, _, _, _, _, _, _⟩
  rcases hacceptUp with ⟨_, _, hmessageSigma⟩
  refine ⟨started, decoded, input, rfl, hdomain, hdecode, ?_, ?_⟩
  · have hinputLedger : input.ledger = started := by rfl
    rw [hinputLedger] at hmessageSigma
    exact hmessageSigma
  · have hinputLedger : input.ledger = started := by rfl
    rw [hinputLedger] at hsigma
    exact hsigma

/-- An actually accepted filtered UP is the sender's checked local offer.
The returned equations concern only the prepared local state and its memory;
no global queue or truthful-score identity is included. -/
theorem acceptedUp_current_choice
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {i : Label p} {message : ReferenceCollectionPhaseHistory.UpRecord p rate}
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp x i message) :
    ∃ (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      sender = (ReferenceActivePhysicalStep.prepare x).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex x) ∧
      i = ReferenceActivePhysicalStep.upSenderIndex x ∧
      sender.configuration = .ordinary state memory ∧
      state.status = .unoccupied ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
        sender.activation sender.time state = .offer message ∧
      message.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
      (∃ started : ReferenceActivePhysicalStep.Ledger rate,
        message.val.sigma = started.sigma ∧
        ReferencePrelaunchFollower.acceptedStart state = started.sigma) ∧
      message.val.S = state.S ∧ message.val.delta = state.delta ∧
      message.val.q = state.backlog ∧
      (∃ prior : DownRecord, state.lastDown = some prior ∧
        prior.val.sigma = message.val.sigma) ∧
      0 < message.val.sigma ∧
      PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot := by
  have hacceptedOriginal := haccepted
  rcases haccepted with
    ⟨tail, recording, started, decoded, bank, htail, hrecording, hstarted,
      hreceived, hparsed, hindex⟩
  let prepared := ReferenceActivePhysicalStep.prepare x
  let sender := prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x)
  let input := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared started) x.time
  let raw := (CoordinatorUpReception.decoderTransition input).2
  let expected := ReferenceActivePhysicalStep.upExpected prepared
  let filtered := ReferenceUpReception.filterRawByExpected raw expected
  have hfilteredParsed : CoordinatorUpReception.parseDecoderOutput filtered = some message := by
    simpa [filtered, raw, expected, input,
      ReferenceCollectionPhaseHistory.filteredParsed,
      ReferenceActivePhysicalStep.upInputs] using hparsed
  have hexpected : expected = some
      ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) message)) := by
    cases hfiltered : filtered with
    | none =>
        have hfalse : False := by
          have hnone : CoordinatorUpReception.parseDecoderOutput
              (p := p) (eta := rate.eta.val) none = none := by
            change OrdinaryMessageCodec.parseUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)
              ((none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))).map
                (OrdinaryMessageCodec.wordEquivFlat
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) = none
            rfl
          have h := hfilteredParsed
          rw [hfiltered, hnone] at h
          cases h
        exact hfalse.elim
    | some word =>
        have hparse : OrdinaryMessageCodec.parseUp
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)
            (some ((OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm word)) =
              some message := by
          have h := hfilteredParsed
          rw [hfiltered] at h
          change OrdinaryMessageCodec.parseUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)
              ((some word : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))).map
                (OrdinaryMessageCodec.wordEquivFlat
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) =
            some message at h
          dsimp only [Option.map] at h
          exact h
        have hencoded := OrdinaryMessageCodec.parseUp_some_sound
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) hparse
        have hword : word = (OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) message) := by
          have hflat := congrArg (OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)) hencoded
          have hleft : word = (OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val))
              ((OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm word) :=
            Eq.symm ((OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)).apply_symm_apply word)
          exact hleft.trans hflat
        have hrawExpected : raw = expected := by
          change ReferenceUpReception.filterRawByExpected raw expected = some word at hfiltered
          unfold ReferenceUpReception.filterRawByExpected at hfiltered
          split at hfiltered
          · assumption
          · cases hfiltered
        have hfilterEq := ReferenceUpReception.filterRawByExpected_eq_raw_of_eq
          raw expected hrawExpected
        have hraw : raw = some word := hfilterEq.symm.trans hfiltered
        have hwordSome : (some word : Option (AffineChannelLaw.Word
            (AffineBatchDecoder.width p))) =
            some ((OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val))
              (OrdinaryMessageCodec.encodeUp
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) message)) :=
          congrArg some hword
        have hrawEncoded : raw = some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) message)) :=
          hraw.trans hwordSome
        exact hrawExpected.symm.trans hrawEncoded
  have hcurrent : ReferenceUpReception.currentOfferWord rate x.row
      (ReferenceActivePhysicalStep.upSenderIndex x) x.time sender
      (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 = some
      ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) message)) := by
    simpa only [expected, ReferenceActivePhysicalStep.upExpected, sender, prepared] using
      hexpected
  cases hconfig : sender.configuration with
  | dagger => simp [ReferenceUpReception.currentOfferWord, hconfig] at hcurrent
  | ordinary state memory =>
      cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower
          sender.row sender.activation sender.time state with
      | failure => simp [ReferenceUpReception.currentOfferWord, hconfig, hoff] at hcurrent
      | noOffer => simp [ReferenceUpReception.currentOfferWord, hconfig, hoff] at hcurrent
      | offer offered =>
          have hencodedOffer := ReferenceUpReception.currentOfferWord_eq_encoded_offer
            rate x.row (ReferenceActivePhysicalStep.upSenderIndex x) x.time sender
            (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1 state memory hconfig offered hoff
          have hflat :
              (OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                (OrdinaryMessageCodec.encodeUp
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered) =
              (OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                (OrdinaryMessageCodec.encodeUp
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) message) :=
            Option.some.inj (hencodedOffer.symm.trans hcurrent)
          have hencode : OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered =
              OrdinaryMessageCodec.encodeUp
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) message :=
            (OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val)).injective hflat
          have hoffered : offered = message := by
            have hparseEq := congrArg
              (OrdinaryMessageCodec.parseUp
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
              (congrArg some hencode)
            rw [OrdinaryMessageCodec.parseUp_encode
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered,
              OrdinaryMessageCodec.parseUp_encode
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) message] at hparseEq
            exact Option.some.inj hparseEq
          subst offered
          have hselected : ActiveFollowerQueueOperation.selectedUpRound sender.follower
              sender.row sender.activation sender.time ∧ state.status = .unoccupied := by
            unfold ActiveFollowerQueueOperation.checkedUpOffer at hoff
            split at hoff
            · split at hoff
              · assumption
              · cases hoff
            · cases hoff
          have hfields := ReferenceUpReception.checkedPreparedOffer_field_equations
            rate sender.row sender.follower sender.time sender rfl rfl rfl state memory
            hconfig message hoff
          obtain ⟨started, _, input, _, _, hdecode,
            hmessageSigma, hstartedPositive⟩ :=
            acceptedUp_receiver_domain hacceptedOriginal
          have hpositive : 0 < message.val.sigma := by omega
          have hstartedEq : ReferencePrelaunchFollower.acceptedStart state = started.sigma :=
            hfields.1.symm.trans hmessageSigma
          have hprior : ∃ prior : DownRecord,
              state.lastDown = some prior ∧ prior.val.sigma = message.val.sigma := by
            cases hlast : state.lastDown with
            | none =>
                simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hfields
                omega
            | some prior =>
                have hacceptedStart :
                    ReferencePrelaunchFollower.acceptedStart state = prior.val.sigma := by
                  simp [ReferencePrelaunchFollower.acceptedStart, hlast]
                exact ⟨prior, rfl, (hfields.1.trans hacceptedStart).symm⟩
          have hslot : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
              PublicDiscreteDraws.upSlot := by
            have halignment := prepared.follower_alignment
              (ReferenceActivePhysicalStep.upSenderIndex x)
            simpa only [sender, prepared, halignment.1, halignment.2.2.1] using
              hselected.1.2.1
          exact ⟨sender, state, memory, rfl, hindex, hconfig, hselected.2,
            hoff, hfields.1, ⟨started, hmessageSigma, hstartedEq⟩,
            hfields.2.1, hfields.2.2.1, hfields.2.2.2,
            hprior, hpositive, hslot⟩

private theorem record_lastDown_origin
    (record : Record) (i : Label p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (target : DownRecord)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hlast : next.lastDown = some target) :
    (∃ (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      record.input.state.followers i = .ordinary before beforeMemory ∧
      before.lastDown = some target) ∨ RetainedDown record i target := by
  rcases record with ⟨input, output, output_eq⟩
  cases output_eq
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let view := prepared.coordinator.downView
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have houtFinish :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).configuration =
        .ordinary next nextMemory := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hout
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hfinish,
      hfinishDownInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view sender observation next nextMemory houtFinish
  obtain ⟨before, beforeMemory, hinput, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ i choice choiceMemory hchoice
  have hfinishFrame := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    sender.follower sender.row sender.time observation choice post next choiceMemory nextMemory hfinish
  have hnextPost : next.lastDown = post.lastDown := by
    have h := congrArg Prod.fst hfinishFrame.1
    change next.lastDown = post.lastDown at h
    exact h
  have hrecordResult := ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
    view sender.follower sender.row sender.activation sender.time sender.active sender.arm
      observation choice post hrecord
  rcases hrecordResult with ⟨hpostChoice, _⟩ |
    ⟨logged, cut, raw, message, scan, registers, lastService,
      hrecordInput, hrecordDown, hcut, houtcome, _, hpostMessage⟩
  · left
    refine ⟨before, beforeMemory, hinput, ?_⟩
    have hchoiceBefore : choice.lastDown = before.lastDown := by
      have h := congrArg Prod.fst hreply
      change choice.lastDown = before.lastDown at h
      exact h
    calc
      before.lastDown = choice.lastDown := hchoiceBefore.symm
      _ = post.lastDown := hpostChoice.symm
      _ = next.lastDown := hnextPost.symm
      _ = some target := hlast
  · right
    have hmessage : message = target := by
      have hnext : next.lastDown = some message := hnextPost.trans hpostMessage
      exact Option.some.inj (hnext.symm.trans hlast)
    subst message
    refine ⟨logged, cut, post, raw, scan, registers, lastService, ?_, ?_, houtcome⟩
    · change ((ReferenceActivePhysicalStep.step input).followers i).downInput = some logged
      have halignment := prepared.follower_alignment i
      simpa only [ReferenceActivePhysicalStep.step,
        ReferenceActivePhysicalStep.PreparedRound.observeFollower,
        sender, prepared, halignment.1, halignment.2.1] using
        hfinishDownInput.trans hrecordInput
    · change ((ReferenceActivePhysicalStep.step input).followers i).down = some cut
      have halignment := prepared.follower_alignment i
      simpa only [ReferenceActivePhysicalStep.step,
        ReferenceActivePhysicalStep.PreparedRound.observeFollower,
        sender, prepared, halignment.1, halignment.2.1] using
        hfinishDown.trans hrecordDown

private theorem connected_lastDown_origin
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List Record}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Label p)
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.followers i = .ordinary first firstMemory)
    (hlast : final.followers i = .ordinary last lastMemory)
    (target : DownRecord)
    (hdown : last.lastDown = some target) :
    first.lastDown = some target ∨
      ∃ record ∈ records, RetainedDown record i target := by
  induction records generalizing initial first firstMemory final last lastMemory with
  | nil =>
      change final = initial at chain
      subst final
      have hstates := LocalConfiguration.ordinary.inj (hfirst.symm.trans hlast)
      rcases hstates with ⟨rfl, rfl⟩
      exact Or.inl hdown
  | cons record rest ih =>
      rcases chain with ⟨hpre, hrest⟩
      obtain ⟨middle, middleMemory, hmiddle, _, _, _⟩ :=
        ReferenceFollowerReplyChronology.connected_ordinary_chronology
          hrest i last lastMemory hlast
      have hrecordInput : record.input.state.followers i = .ordinary first firstMemory := by
        rw [hpre]
        exact hfirst
      rcases ih hrest middle middleMemory last lastMemory hmiddle hlast hdown with
        hmiddleDown | ⟨laterRecord, hlaterRecord, hlaterDown⟩
      · rcases record_lastDown_origin record i middle middleMemory target hmiddle hmiddleDown with
          ⟨before, beforeMemory, hbefore, hbeforeDown⟩ | hcurrentDown
        · have hstates := LocalConfiguration.ordinary.inj (hbefore.symm.trans hrecordInput)
          rcases hstates with ⟨rfl, rfl⟩
          exact Or.inl hbeforeDown
        · exact Or.inr ⟨record, List.mem_cons_self, hcurrentDown⟩
      · exact Or.inr ⟨laterRecord, List.mem_cons_of_mem _ hlaterRecord, hlaterDown⟩

private theorem record_no_appliedDown_of_up
    (record : Record) (i : Label p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (sigma : ℕ) :
    ¬ ReferenceFollowerReplyChronology.appliedDown record i sigma := by
  intro happ
  rcases record with ⟨input, output, output_eq⟩
  cases output_eq
  have hchoice' :
      ((ReferenceActivePhysicalStep.prepare input).followers.followers i).configuration =
        .ordinary state memory := by
    have hactual : ReferenceFollowerFixedReply.actualChoice
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ i =
          (ReferenceActivePhysicalStep.prepare input).followers.followers i := by
      unfold ReferenceFollowerFixedReply.actualChoice
      rfl
    rw [hactual] at hchoice
    exact hchoice
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let view := prepared.coordinator.downView
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have houtFinish :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).configuration =
        .ordinary next nextMemory := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hout
  obtain ⟨choice, choiceMemory, post, hconfig, hrecord, hfinish,
      hfinishDownInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view sender observation next nextMemory houtFinish
  have hsame := LocalConfiguration.ordinary.inj (hchoice'.symm.trans hconfig)
  rcases hsame with ⟨rfl, rfl⟩
  rcases happ with ⟨logged, cut, after, raw, message, scan, registers, lastService,
    hdownInput, hdown, houtcome, _⟩
  have hfinishCut :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).down = some cut := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hdown
  have hrecordCut : (ReferenceActivePhysicalStep.recordFollower view i input.row
      sender.activation sender.time sender.active sender.arm observation state).down = some cut :=
    by
      have halignment := prepared.follower_alignment i
      simpa only [sender, prepared, halignment.1, halignment.2.1] using
        hfinishDown.symm.trans hfinishCut
  cases hlogging : ActiveFollowerLogging.checkedLogging i input.row sender.activation
      sender.time (sender.arm, observation) state with
  | error failure =>
      simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging] at hrecordCut
  | ok logged' =>
      have hactualCut : ReferenceDownReception.referenceDownCut p view i input.row
          sender.time observation rate logged' = cut := by
        have hsome := hrecordCut
        simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging] using hsome
      have hacceptedCut : (ReferenceDownReception.referenceDownCut p view i input.row
          sender.time observation rate logged').outcome =
            .accepted logged after raw message scan registers lastService := by
        rw [hactualCut]
        exact houtcome
      have hdownSelected : ActiveFollowerDownAcceptance.downSelected p i input.row sender.time := by
        unfold ReferenceDownReception.referenceDownCut at hacceptedCut
        split at hacceptedCut
        · assumption
        · cases hacceptedCut
      have hslotDown : PublicDiscreteDraws.slotDraw (input.row.2 sender.time).1 =
          PublicDiscreteDraws.downSlot := hdownSelected.1
      have hslotUp : PublicDiscreteDraws.slotDraw (input.row.2 sender.time).1 =
          PublicDiscreteDraws.upSlot := by
        have halignment := prepared.follower_alignment i
        simpa only [sender, prepared, halignment.2.2.1] using hslot
      have hneq : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot := by decide
      exact hneq (hslotUp.symm.trans hslotDown)

/-- The actual output of an accepted UP round, when ordinary, keeps this
follower unoccupied and preserves the complete local reply projection. -/
theorem record_acceptedUp_output_frame
    {record : Record} {i : Label p}
    {message : ReferenceCollectionPhaseHistory.UpRecord p rate}
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i message)
    {next : ReferencePrelaunchFollower.State p rate.eta}
    {nextMemory : ActiveFollowerLifecycle.LocalMemory p}
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice record i).configuration =
        .ordinary state memory ∧
      state.status = .unoccupied ∧ next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next =
        ReferenceFollowerReplyChronology.reply state := by
  obtain ⟨sender, state, memory, hsender, hindex, hconfiguration, hunoccupied,
      _, _, _, _, _, _, _, _, hslot⟩ := acceptedUp_current_choice haccepted
  have hactual : ReferenceFollowerFixedReply.actualChoice record i = sender := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    calc
      (ReferenceActivePhysicalStep.prepare record.input).followers.followers i =
          (ReferenceActivePhysicalStep.prepare record.input).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex record.input) := by rw [hindex]
      _ = sender := hsender.symm
  have hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory := by rw [hactual]; exact hconfiguration
  obtain ⟨choice, choiceMemory, hchoiceRound, _, hfreeze, hchanged⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology record i next nextMemory hout
  have hsame := LocalConfiguration.ordinary.inj (hchoice.symm.trans hchoiceRound)
  rcases hsame with ⟨rfl, rfl⟩
  have hequalStart : ReferencePrelaunchFollower.acceptedStart state =
      ReferencePrelaunchFollower.acceptedStart next := by
    by_contra hne
    exact record_no_appliedDown_of_up record i state memory hchoice hunoccupied hslot
      next nextMemory hout (ReferencePrelaunchFollower.acceptedStart next)
      (hchanged hne)
  obtain ⟨hnextStatus, hreply⟩ := hfreeze hunoccupied hequalStart
  exact ⟨state, memory, hchoice, hunoccupied, hnextStatus, hreply⟩

/-- The exact retained accepted diagnostic is also the project's actual
`appliedDown` predicate, with the sigma read from that same DOWN record. -/
theorem retainedDown_appliedDown
    {record : Record (p := p) (rate := rate)} {i : Label p}
    {message : DownRecord (p := p) (rate := rate)}
    (h : RetainedDown record i message) :
    ReferenceFollowerReplyChronology.appliedDown (p := p) (rate := rate)
      record i message.val.sigma := by
  rcases h with ⟨logged, cut, after, raw, scan, registers, lastService,
    hinput, hdown, houtcome⟩
  exact ⟨logged, cut, after, raw, message, scan, registers, lastService,
    hinput, hdown, houtcome, rfl⟩

/-- An accepted UP in an indexed record has an exact earlier DOWN origin in
the actual connected prefix, provided only this follower's initial state is
ordinary with no retained DOWN. The UP choice fields and the started receiver
ledger remain visible in the result. -/
abbrev AcceptedUpPriorDown
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Label p)
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.length)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate) : Prop :=
    ∃ j : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records.length,
      j.val < k.val ∧ ∃ prior : DownRecord,
        RetainedDown
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count hspan hmode).records[j.val] i prior ∧
        ReferenceFollowerReplyChronology.appliedDown (p := p) (rate := rate)
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count hspan hmode).records[j.val] i prior.val.sigma ∧
        prior.val.sigma = message.val.sigma ∧
        ∃ (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
          (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          sender = ReferenceFollowerFixedReply.actualChoice
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start count hspan hmode).records[k.val] i ∧
          sender.configuration = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
            sender.activation sender.time state = .offer message ∧
          message.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
          (∃ started : ReferenceActivePhysicalStep.Ledger rate,
            message.val.sigma = started.sigma ∧
            ReferencePrelaunchFollower.acceptedStart state = started.sigma) ∧
          message.val.S = state.S ∧ message.val.delta = state.delta ∧
          message.val.q = state.backlog ∧ state.lastDown = some prior ∧
          prior.val.sigma = message.val.sigma ∧ 0 < message.val.sigma
theorem run_acceptedUp_prior_down
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Label p)
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.followers i = .ordinary first firstMemory)
    (hfirstNoDown : first.lastDown = none)
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.length)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records[k.val].input) i message) :
    AcceptedUpPriorDown initial rows selected rewards start count hspan hmode i k message := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  let records := execution.records
  let record : Record := records[k.val]
  obtain ⟨sender, state, memory, hsender, hindex, hconfiguration, hunoccupied,
      hoff, hstart, hstarted, hS, hdelta, hbacklog, hprior, hpositive, _⟩ :=
    acceptedUp_current_choice haccepted
  have hsenderActual : sender = ReferenceFollowerFixedReply.actualChoice record i := by
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [record.output_eq]
    simpa [record, hindex, ReferenceActivePhysicalStep.step] using hsender
  have hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory := by
    rw [← hsenderActual]
    exact hconfiguration
  obtain ⟨before, beforeMemory, hinput, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice record i state memory hchoice
  rcases hprior with ⟨target, htarget, htargetSigma⟩
  have hstateLast : state.lastDown = before.lastDown := by
    have h := congrArg Prod.fst hreply
    change state.lastDown = before.lastDown at h
    exact h
  have hbeforeLast : before.lastDown = some target := hstateLast.symm.trans htarget
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
    execution.connected k.val k.isLt
  rcases connected_lastDown_origin hprefix i first firstMemory before beforeMemory
      hfirst hinput target hbeforeLast with hinitial | ⟨oldRecord, holdRecord, hretained⟩
  · rw [hfirstNoDown] at hinitial
    cases hinitial
  · obtain ⟨j, hj, hgetTake⟩ := List.mem_iff_getElem.mp holdRecord
    have hjk : j < k.val := by
      simp only [List.length_take] at hj
      omega
    have hget := List.getElem_take (xs := records) (j := k.val) (i := j) (h := hj)
    have hgetRecord : records[j] = oldRecord := by
      rw [hget] at hgetTake
      exact hgetTake
    have hretainedAt : RetainedDown records[j] i target := by
      rw [hgetRecord]
      exact hretained
    have hchoiceRecord :
        sender = ReferenceFollowerFixedReply.actualChoice records[k.val] i := by
      simpa [record] using hsenderActual
    refine ⟨⟨j, by omega⟩, hjk, target, hretainedAt,
      retainedDown_appliedDown hretainedAt, htargetSigma, sender, state, memory,
      ?_, ?_, hunoccupied, hoff, hstart, hstarted, hS, hdelta, hbacklog,
      htarget, htargetSigma, hpositive⟩
    · exact hchoiceRecord
    · simpa [record] using hconfiguration

/-- Each follower's actual later-start witness contains an earlier accepted
UP CHOICE and an exact, strictly earlier accepted DOWN diagnostic with the
old coordinator sigma. The first component preserves every decomposition
fact returned by `run_laterStart_all_up_accepted`. -/
abbrev LaterStartPriorDown
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : Prop :=
    ∃ (before : List (ReferenceCollectionPhaseHistory.Record p rate))
      (cutoff : ReferenceCollectionPhaseHistory.Record p rate)
      (during : List (ReferenceCollectionPhaseHistory.Record p rate))
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (old : ReferenceActivePhysicalStep.Ledger rate)
      (proposal : Option (Fin p.T × Bool)),
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count (by omega) hmode).records = before ++ cutoff :: during ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoff.input = true ∧
      (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards
        start count hspan hmode).state.coordinator = .collection payload old proposal ∧
      old.pending = ∅ ∧
      ReferenceCollectionPhaseHistory.collectionWindow
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count (by omega) hmode).records ++
          [⟨ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards
              start count hspan hmode,
            ReferenceActivePhysicalStep.step
              (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards
                start count hspan hmode), rfl⟩]) before.length = cutoff :: during ∧
      (∀ i : Label p, ∃ (k : ℕ) (record : ReferenceCollectionPhaseHistory.Record p rate)
        (message : ReferenceCollectionPhaseHistory.UpRecord p rate),
        before.length ≤ k ∧ k < count ∧
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count (by omega) hmode).records[k]? = some record ∧
        ReferenceCollectionPhaseHistory.AcceptedUp record.input i message ∧
        message.val.sigma = old.sigma ∧
        ∃ (j : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count (by omega) hmode).records.length)
          (prior : DownRecord)
          (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
          (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          j.val < k ∧
          RetainedDown
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start count (by omega) hmode).records[j.val] i prior ∧
          ReferenceFollowerReplyChronology.appliedDown
            (ReferenceActivePhysicalHorizon.run initial rows selected rewards
              start count (by omega) hmode).records[j.val] i prior.val.sigma ∧
          prior.val.sigma = old.sigma ∧
          sender = ReferenceFollowerFixedReply.actualChoice record i ∧
          sender.configuration = .ordinary state memory ∧ state.status = .unoccupied ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
            sender.activation sender.time state = .offer message ∧
          message.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
          (∃ started : ReferenceActivePhysicalStep.Ledger rate,
            message.val.sigma = started.sigma ∧
            ReferencePrelaunchFollower.acceptedStart state = started.sigma) ∧
          message.val.S = state.S ∧ message.val.delta = state.delta ∧
          message.val.q = state.backlog ∧ state.lastDown = some prior ∧
          prior.val.sigma = message.val.sigma ∧ 0 < message.val.sigma)

theorem run_laterStart_prior_down
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirstCoordinator : initial.coordinator = .first)
    (hseed : ∀ i : Label p,
      ∃ first firstMemory,
        initial.followers i = .ordinary first firstMemory ∧ first.lastDown = none)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards
        start count hspan hmode) = true) :
    LaterStartPriorDown initial rows selected rewards start count hspan hmode := by
  obtain ⟨before, cutoff, during, payload, old, proposal,
    hrecords, hcutoff, hcoordinator, hempty, hwindow, heach⟩ :=
    ReferenceCollectionPhaseHistory.run_laterStart_all_up_accepted initial rows selected
      rewards start count hspan hmode hfirstCoordinator hlater
  refine ⟨before, cutoff, during, payload, old, proposal, hrecords, hcutoff,
    hcoordinator, hempty, hwindow, ?_⟩
  intro i
  obtain ⟨k, record, message, hbefore, hkcount, hget?, haccepted, hmessageSigma⟩ := heach i
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count (by omega) hmode
  have hk : k < (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count (by omega) hmode).records.length := by
    rw [hlength]
    exact hkcount
  have hrecord :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        (by omega) hmode).records[k] = record := by
    have hsome := List.getElem?_eq_getElem hk
    rw [hget?] at hsome
    exact Option.some.inj hsome.symm
  have hacceptedAt : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count (by omega) hmode).records[k].input) i message := by
    rw [hrecord]
    exact haccepted
  obtain ⟨first, firstMemory, hfirst, hfirstNoDown⟩ := hseed i
  let index : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count (by omega) hmode).records.length := ⟨k, hk⟩
  obtain ⟨j, hjk, prior, hretained, happlied, hpriorSigma,
      sender, state, memory, hsender, hconfiguration, hunoccupied, hoff,
      hstart, hstarted, hS, hdelta, hbacklog, hlast, hlastSigma, hpositive⟩ :=
    run_acceptedUp_prior_down initial rows selected rewards start count (by omega)
      hmode i first firstMemory hfirst hfirstNoDown index message hacceptedAt
  have hpriorOld : prior.val.sigma = old.sigma := hpriorSigma.trans hmessageSigma
  have hjkCount : j.val < k := by exact hjk
  have hsenderRecord : sender = ReferenceFollowerFixedReply.actualChoice record i := by
    rw [← hrecord]
    exact hsender
  exact ⟨k, record, message, hbefore, hkcount, hget?, haccepted, hmessageSigma,
    j, prior, sender, state, memory, hjkCount, hretained, happlied, hpriorOld,
    hsenderRecord, hconfiguration, hunoccupied, hoff, hstart, hstarted, hS, hdelta,
    hbacklog, hlast, hlastSigma, hpositive⟩

end LocalRate

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

include source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
  learnerSeed hlaunched

/-- Actual launched-boundary specialization of the indexed UP-to-DOWN
history. It keeps the converted ordinary replay state and its carried memory
as the same objects returned by the launch-state producer, along with the
full original source, selected row, and reward table. The clipped interval
allows `count = 0` at `start = T`; its accepted-record premise is then empty. -/
theorem ofActualLaunchedBoundary_run_acceptedUp_prior_down
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + count ≤ p.T)
    (i : Label p)
    (k : Fin (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
      count hspan
      (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched i)).records.length)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceActivePhysicalHorizon.run
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
        count hspan
        (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
          hlaunched i)).records[k.val].input) i message) :
    ∃ first firstMemory,
      ReferenceActivePhysicalStep.State.followers
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) i =
          .ordinary first firstMemory ∧
      first = ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        (ActualReferenceInitializationBlock.refFollower i) ∧
      ReferencePrelaunchFollower.acceptedStart first = 0 ∧
      first.S = 0 ∧ first.delta = 0 ∧ first.backlog = 0 ∧
      first.lastDown = none ∧ first.status = .unoccupied ∧
      AcceptedUpPriorDown
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
        count hspan
        (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
          hlaunched i)
        i k message := by
  rcases ReferenceFollowerFixedReply.ofActualLaunchedBoundary_replaySeed
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i with
    ⟨first, firstMemory, hconfiguration, hstate, hlast, hstart, hS, hdelta,
      hbacklog, hstatus, _⟩
  have hcore := run_acceptedUp_prior_down
    (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    count hspan
    (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i)
    i first firstMemory hconfiguration hlast k message haccepted
  exact ⟨first, firstMemory, hconfiguration, hstate, hstart, hS, hdelta,
    hbacklog, hlast, hstatus, hcore⟩

/-- The actual launched later-start specialization of the combined producer.
All initialization, replay, private-row, reward-table, rate, and activation
inputs stay explicit. Its clipped bound requires the actual later-start round
to lie inside the calendar. -/
theorem ofActualLaunchedBoundary_laterStart_prior_down
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + (count + 1) ≤ p.T)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCollectionPhaseHistory.nextInput
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
        count hspan
        (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
          hlaunched i)) = true) :
    (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).coordinator =
        .first ∧
    (∀ i : Label p, ∃ state memory,
      ReferenceActivePhysicalStep.State.followers
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) i =
          .ordinary state memory ∧
      state = ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        (ActualReferenceInitializationBlock.refFollower i) ∧
      state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧ state.status = .unoccupied) ∧
    LaterStartPriorDown
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
      count (by omega)
      (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched i) := by
  have hseeds : ∀ i : Label p, ∃ state memory,
      ReferenceActivePhysicalStep.State.followers
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
          C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) i =
          .ordinary state memory ∧
      state = ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        (ActualReferenceInitializationBlock.refFollower i) ∧
      state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧ state.status = .unoccupied := by
    intro i
    rcases ReferenceFollowerFixedReply.ofActualLaunchedBoundary_replaySeed
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
        learnerSeed hlaunched i with
      ⟨state, memory, hconfiguration, hstate, hlast, hstart, hS, hdelta,
        hbacklog, hstatus, _⟩
    exact ⟨state, memory, hconfiguration, hstate, hlast, hstart, hS, hdelta,
      hbacklog, hstatus⟩
  have hhistory := run_laterStart_prior_down
    (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    count (by omega)
    (fun i => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i)
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched)
    (fun i => by
      rcases ReferenceFollowerFixedReply.ofActualLaunchedBoundary_replaySeed
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
          learnerSeed hlaunched i with
        ⟨state, memory, hconfiguration, _, hlast, _, _, _, _, _, _⟩
      exact ⟨state, memory, hconfiguration, hlast⟩)
    hlater
  exact ⟨ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched, ⟨hseeds, hhistory⟩⟩

end LaunchInputs
