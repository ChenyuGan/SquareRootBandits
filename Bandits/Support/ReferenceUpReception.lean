/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.ActiveFollowerQueueOperation
public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.ActiveFollowerLifecycle
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.CoordinatorUpMeasurability
public import Bandits.Support.CoordinatorUpReception
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.ReferencePrelaunchFollower

/-!
# Reference-only checked UP reception

This file constructs the local checked UP receiver cut before ledger
acceptance or recovery. It follows
`sources/zip4/manuscript/06_interruptions.tex:3-5,123-177,235-297`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

The expected word is derived only from the aligned choice-time follower
snapshot and its checked ordinary UP offer. This is a local operation on the
existing carriers; it does not assert endpoint provenance, physical
reachability, or a manuscript theorem.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceUpReception

open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorUpMeasurability
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferencePrelaunchFollower

variable {p : ConstructorDimensions.Parameters}

/-- Re-express the follower's cap witness as the coordinator ledger's accepted
cap predicate. -/
theorem sourceCap_forLedger (rate : ActiveFollowerDownAcceptance.RateInput p) :
    CoordinatorCollectionLedger.sourceLearningCap p rate.eta.val := by
  change rate.eta.val ≤
    1 / (1024 * (p.m : ℝ) * p.K *
      (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ))
  exact rate.sourceCap

/-- The row-local coordinator inputs at the same rate witness carried by a
choice-time follower snapshot. -/
abbrev ReceptionLocalInputs (rate : ActiveFollowerDownAcceptance.RateInput p) :=
  CoordinatorUpMeasurability.ReceptionLocalInputs p rate.eta.val
    rate.eta.property (sourceCap_forLedger rate) rate.n rate.n_scale

/-- The checked receiver input constructed from the actual supplied row. -/
def receptionInputAtRow (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T) :=
  CoordinatorUpMeasurability.receptionInputAtRow row inputs t

@[simp] theorem receptionInputAtRow_inputTime
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T) :
    (receptionInputAtRow rate row inputs t).time = inputs.2.2.1 := rfl

/-- A prepared snapshot is at the row index only when its stored time agrees
with the time carried by the supplied local registers. -/
theorem preparedTime_eq_rowIndex_of_alignment
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hprepared : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (hinputTime : inputs.2.2.1 = t) :
    prepared.time = t := by
  rw [hprepared, receptionInputAtRow_inputTime]
  exact hinputTime

@[simp] theorem receptionInputAtRow_selectedFollower
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T) :
    (receptionInputAtRow rate row inputs t).selectedFollower =
      CoordinatorUpMeasurability.selectedFollowerIndex (row.2 t) := rfl

@[simp] theorem receptionInputAtRow_affineSample
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T) :
    (receptionInputAtRow rate row inputs t).affineSample =
      (row.2 t).2 (1, CoordinatorUpMeasurability.selectedChannelFollower (row.2 t)) := rfl

/-- Keep a decoded flat word exactly when it equals the derived current UP
offer; a mismatch becomes the ordinary no-decoded-word input to the ledger. -/
def filterRawByExpected {α : Type*} (raw expected : Option α) : Option α := by
  classical
  exact if raw = expected then raw else none

theorem filterRawByExpected_eq_raw_of_eq {α : Type*} (raw expected : Option α)
    (h : raw = expected) : filterRawByExpected raw expected = raw := by
  classical
  simp [filterRawByExpected, h]

theorem filterRawByExpected_eq_none_of_ne {α : Type*} (raw expected : Option α)
    (h : raw ≠ expected) : filterRawByExpected raw expected = none := by
  classical
  simp [filterRawByExpected, h]

/-- The current expected encoded word from this follower's choice-time
configuration. The proof arguments expose the required same-row, same-follower,
and same-round alignment. A dagger configuration, a failed checked offer, or a
non-offer produces no word. -/
def currentOfferWord (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (_sameRow : prepared.row = row)
    (_sameFollower : prepared.follower = follower)
    (_sameTime : prepared.time = time) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) := by
  classical
  match prepared.configuration with
  | .dagger => exact none
  | .ordinary state _ =>
      match ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          prepared.follower prepared.row prepared.activation prepared.time state with
      | .failure => exact none
      | .noOffer => exact none
      | .offer record =>
          exact some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
              (OrdinaryMessageCodec.encodeUp
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) record))

/-- The accepted ledger and follower codecs are definitionally the same
five-block codec at the shared rate witness. -/
theorem ledgerCodecParams_eq_followerCodecParams
    (rate : ActiveFollowerDownAcceptance.RateInput p) :
    CoordinatorCollectionLedger.codecParams p rate.eta.val =
      ReferencePrelaunchFollower.codecParams p rate.eta := rfl

/-- Exact field equation for a checked current UP offer. -/
theorem checkedPreparedOffer_fields
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (_hrow : prepared.row = row) (_hfollower : prepared.follower = follower)
    (_htime : prepared.time = time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (_hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      prepared.follower prepared.row prepared.activation prepared.time state =
        .offer offered) :
    offered.val = ActiveFollowerQueueOperation.upOfferFields state := by
  exact ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta
    prepared.follower prepared.row prepared.activation prepared.time state offered hoff

/-- The checked sender fields are exactly `(accepted start, served sum, last
service, queue)` from the ordinary choice-time state. -/
theorem checkedPreparedOffer_field_equations
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row) (hfollower : prepared.follower = follower)
    (htime : prepared.time = time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      prepared.follower prepared.row prepared.activation prepared.time state =
        .offer offered) :
    offered.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
      offered.val.S = state.S ∧ offered.val.delta = state.delta ∧
      offered.val.q = state.backlog := by
  have hfields := checkedPreparedOffer_fields rate row follower time prepared
    hrow hfollower htime state memory hconfiguration offered hoff
  constructor
  · simpa [ActiveFollowerQueueOperation.upOfferFields] using
      congrArg OrdinaryMessageCodec.UpFields.sigma hfields
  constructor
  · simpa [ActiveFollowerQueueOperation.upOfferFields] using
      congrArg OrdinaryMessageCodec.UpFields.S hfields
  constructor
  · simpa [ActiveFollowerQueueOperation.upOfferFields] using
      congrArg OrdinaryMessageCodec.UpFields.delta hfields
  · simpa [ActiveFollowerQueueOperation.upOfferFields] using
      congrArg OrdinaryMessageCodec.UpFields.q hfields

/-- Exact word equation for a checked sender offer: flatten the ordinary
five-block UP encoding with the existing codec equivalence. -/
theorem currentOfferWord_eq_encoded_offer
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row) (hfollower : prepared.follower = follower)
    (htime : prepared.time = time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      prepared.follower prepared.row prepared.activation prepared.time state =
        .offer offered) :
    currentOfferWord rate row follower time prepared hrow hfollower htime =
      some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
          (OrdinaryMessageCodec.encodeUp
            (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) := by
  simp [currentOfferWord, hconfiguration, hoff]
  rfl

/-- Dagger has no ordinary word to send. -/
theorem currentOfferWord_eq_none_of_dagger
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row) (hfollower : prepared.follower = follower)
    (htime : prepared.time = time)
    (hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.dagger) :
    currentOfferWord rate row follower time prepared hrow hfollower htime = none := by
  simp [currentOfferWord, hconfiguration]

/-- A checked failure or non-offer never creates an encoded current word. -/
theorem currentOfferWord_eq_none_of_checked_nonoffer
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row) (hfollower : prepared.follower = follower)
    (htime : prepared.time = time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (hnonoffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      prepared.follower prepared.row prepared.activation prepared.time state =
        .failure ∨
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        prepared.follower prepared.row prepared.activation prepared.time state =
          .noOffer) :
    currentOfferWord rate row follower time prepared hrow hfollower htime = none := by
  rcases hnonoffer with hfailure | hnoOffer
  · simp [currentOfferWord, hconfiguration, hfailure]
  · simp [currentOfferWord, hconfiguration, hnoOffer]

/-- Parse the unfiltered actual raw decoder output through the accepted UP
parser. This records ordinary local acceptance before the reference-only cut. -/
def rawParsedOutput
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val
      rate.eta.property (sourceCap_forLedger rate) rate.n rate.n_scale) :=
  CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
    (CoordinatorUpReception.decoderTransition input).2

/-- Whether the unfiltered raw output parses and passes the existing local UP
acceptance predicate. A raw `none` is not accepted. -/
def rawParsedLocalAcceptance
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val
      rate.eta.property (sourceCap_forLedger rate) rate.n rate.n_scale) : Bool :=
  match rawParsedOutput rate input with
  | none => false
  | some record =>
      CoordinatorCollectionLedger.acceptUpCheck input.ledger
        input.selectedFollower record

/-- Exact local acceptance characterization for the unfiltered raw parser. -/
theorem rawParsedLocalAcceptance_eq_true_iff
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val
      rate.eta.property (sourceCap_forLedger rate) rate.n rate.n_scale) :
    rawParsedLocalAcceptance rate input = true ↔
      ∃ record, rawParsedOutput rate input = some record ∧
        CoordinatorCollectionLedger.acceptUpCheck input.ledger
          input.selectedFollower record = true := by
  cases hparsed : rawParsedOutput rate input <;>
    simp [rawParsedLocalAcceptance, hparsed]

/-- Reference-only receiver cut specialized to the actual row adapter. The
alignment proofs prevent mixing the coordinator row, follower, or time with a
different choice-time snapshot. -/
def receiveUpFilteredAtRow
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t) :
    CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
        (sourceCap_forLedger rate) rate.n rate.n_scale ×
        CoordinatorUpReception.UpDecoderBank p) := by
  classical
  let input := receptionInputAtRow rate row inputs t
  exact if CoordinatorUpReception.receptionInputCheck input = true then
    let expected := currentOfferWord rate row input.selectedFollower input.time
      prepared hrow hfollower htime
    let transition := CoordinatorUpReception.decoderTransition input
    let filteredRaw := filterRawByExpected transition.2 expected
    let parsed := CoordinatorUpReception.parseDecoderOutput filteredRaw
    CoordinatorUpReception.packDecodeResult
      (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed)
      (Function.update input.upDecoderBank input.selectedFollower transition.1)
  else
    .invalid

/-- The wrong-unique-and-local-acceptance flag for the unfiltered raw output.
It requires a unique raw word, a parsed record that passes the ordinary local
UP acceptance test, and inequality with the current choice-time word. -/
def wrongUniqueAndLocalAcceptanceAtRow
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t) : Bool := by
  classical
  let input := receptionInputAtRow rate row inputs t
  let expected := currentOfferWord rate row input.selectedFollower input.time
    prepared hrow hfollower htime
  let raw := (CoordinatorUpReception.decoderTransition input).2
  exact match raw with
  | none => false
  | some word =>
      decide (some word ≠ expected) &&
        match CoordinatorUpReception.parseDecoderOutput (p := p)
            (eta := rate.eta.val) (some word) with
        | none => false
        | some record =>
            CoordinatorCollectionLedger.acceptUpCheck input.ledger
              input.selectedFollower record

/-- Exact logical content of the wrong-unique-and-local-acceptance flag. -/
theorem wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t) :
    wrongUniqueAndLocalAcceptanceAtRow rate row inputs t prepared hrow hfollower htime _hinputTime = true ↔
      ∃ word record,
        (CoordinatorUpReception.decoderTransition
          (receptionInputAtRow rate row inputs t)).2 = some word ∧
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (some word) = some record ∧
        CoordinatorCollectionLedger.acceptUpCheck
          (receptionInputAtRow rate row inputs t).ledger
          (receptionInputAtRow rate row inputs t).selectedFollower record = true ∧
        some word ≠ currentOfferWord rate row
          (receptionInputAtRow rate row inputs t).selectedFollower
          (receptionInputAtRow rate row inputs t).time prepared
          hrow hfollower htime := by
  classical
  let input := receptionInputAtRow rate row inputs t
  cases hraw : (CoordinatorUpReception.decoderTransition
      (receptionInputAtRow rate row inputs t)).2 with
  | none => simp [wrongUniqueAndLocalAcceptanceAtRow, hraw]
  | some word =>
      cases hparse : CoordinatorUpReception.parseDecoderOutput (p := p)
          (eta := rate.eta.val) (some word) with
      | none => simp [wrongUniqueAndLocalAcceptanceAtRow, hraw, hparse]
      | some record =>
          unfold wrongUniqueAndLocalAcceptanceAtRow
          simp only [hraw, hparse]
          change
            (decide (some word ≠ currentOfferWord rate row input.selectedFollower
                input.time prepared hrow hfollower htime) &&
              CoordinatorCollectionLedger.acceptUpCheck input.ledger
                input.selectedFollower record) = true ↔
              ∃ word' record',
                some word = some word' ∧
                CoordinatorUpReception.parseDecoderOutput (p := p)
                  (eta := rate.eta.val) (some word') = some record' ∧
                CoordinatorCollectionLedger.acceptUpCheck input.ledger
                  input.selectedFollower record' = true ∧
                some word' ≠ currentOfferWord rate row input.selectedFollower
                  input.time prepared hrow hfollower htime
          constructor
          · intro h
            rcases Bool.and_eq_true_iff.mp h with ⟨hneq, haccept⟩
            refine ⟨word, record, ?_, hparse, haccept, ?_⟩
            · rfl
            · exact of_decide_eq_true hneq
          · rintro ⟨word', record', hraw', hparse', haccept, hneq⟩
            have hword : word' = word := Option.some.inj hraw'.symm
            subst word'
            have hrecord : record' = record :=
              Option.some.inj (hparse'.symm.trans hparse)
            subst record'
            apply Bool.and_eq_true_iff.mpr
            constructor
            · exact decide_eq_true hneq
            · exact haccept

/-- A missing raw unique word never sets the wrong-unique-and-acceptance flag,
even when `none` differs from the current expected `some` word. -/
theorem wrongUniqueAndLocalAcceptanceAtRow_false_of_raw_none
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hraw : (CoordinatorUpReception.decoderTransition
      (receptionInputAtRow rate row inputs t)).2 = none) :
    wrongUniqueAndLocalAcceptanceAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      false := by
  simp [wrongUniqueAndLocalAcceptanceAtRow, hraw]

/-- Input-domain failure agrees exactly with the accepted ordinary receiver's
invalid branch and performs no decoder or ledger transition. -/
theorem receiveUpFilteredAtRow_input_invalid
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hinvalid : CoordinatorUpReception.receptionInputCheck
      (receptionInputAtRow rate row inputs t) = false) :
    receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime = .invalid ∧
      CoordinatorUpReception.receiveUp (receptionInputAtRow rate row inputs t) = .invalid := by
  constructor
  · simp [receiveUpFilteredAtRow, hinvalid]
  · exact CoordinatorUpReception.receiveUp_invalid_of_domain_check
      (receptionInputAtRow rate row inputs t) hinvalid

/-- If the decoded raw option equals the prepared current offer, the filtered
receiver is exactly the existing ordinary `receiveUp`, including all ordinary
rejected and successful cases. -/
theorem receiveUpFilteredAtRow_eq_receiveUp_of_no_mismatch
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hraw : (CoordinatorUpReception.decoderTransition
      (receptionInputAtRow rate row inputs t)).2 =
        currentOfferWord rate row
          (receptionInputAtRow rate row inputs t).selectedFollower
          (receptionInputAtRow rate row inputs t).time prepared
          hrow hfollower htime) :
    receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      CoordinatorUpReception.receiveUp (receptionInputAtRow rate row inputs t) := by
  classical
  let input := receptionInputAtRow rate row inputs t
  cases hcheck : CoordinatorUpReception.receptionInputCheck input with
  | false =>
      simp [receiveUpFilteredAtRow, input, hcheck,
        CoordinatorUpReception.receiveUp]
  | true =>
      have hordinary := CoordinatorUpReception.receiveUp_eq_existing_decodeUp input hcheck
      rw [hordinary]
      simp [receiveUpFilteredAtRow, input, hcheck,
        filterRawByExpected, hraw, CoordinatorUpReception.parseDecoderOutput]

/-- The valid branch is exactly the existing decode-result packer applied to
the filtered parse and the selected channel's advanced decoder state. -/
theorem receiveUpFilteredAtRow_eq_filtered_decode
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (receptionInputAtRow rate row inputs t) = true) :
    receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp
          (receptionInputAtRow rate row inputs t).ledger
          (receptionInputAtRow rate row inputs t).selectedFollower
          (CoordinatorUpReception.parseDecoderOutput
            (filterRawByExpected
              (CoordinatorUpReception.decoderTransition
                (receptionInputAtRow rate row inputs t)).2
              (currentOfferWord rate row
                (receptionInputAtRow rate row inputs t).selectedFollower
                (receptionInputAtRow rate row inputs t).time prepared
                hrow hfollower htime))))
        (CoordinatorUpReception.decoderBankAfter
          (receptionInputAtRow rate row inputs t)) := by
  simp [receiveUpFilteredAtRow,
    CoordinatorUpReception.decoderBankAfter, hinput]

/-- On an explicit raw/current-word mismatch, ordinary ledger processing sees
`none`: rejection advances only the prescribed decode phase and preserves the
actual advanced decoder bank. The record update states all semantic ledger
fields remain unchanged. -/
theorem receiveUpFilteredAtRow_mismatch_rejected
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (receptionInputAtRow rate row inputs t) = true)
    (hmismatch : (CoordinatorUpReception.decoderTransition
      (receptionInputAtRow rate row inputs t)).2 ≠
        currentOfferWord rate row
          (receptionInputAtRow rate row inputs t).selectedFollower
          (receptionInputAtRow rate row inputs t).time prepared
          hrow hfollower htime) :
    receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      .rejected
        ({(receptionInputAtRow rate row inputs t).ledger with
          phase := CoordinatorCollectionLedger.Phase.decoded},
          CoordinatorUpReception.decoderBankAfter
            (receptionInputAtRow rate row inputs t)) := by
  classical
  let input := receptionInputAtRow rate row inputs t
  have hdomain : CoordinatorUpReception.receptionInputDomain input :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hinput
  have hdecode := CoordinatorUpReception.decodeUp_none_rejected input hdomain
  unfold receiveUpFilteredAtRow
  simp only [hinput]
  have hfiltered : filterRawByExpected
      (CoordinatorUpReception.decoderTransition input).2
      (currentOfferWord rate row input.selectedFollower input.time prepared
        hrow hfollower htime) = none :=
    filterRawByExpected_eq_none_of_ne _ _ hmismatch
  rw [hfiltered]
  have hparsed : CoordinatorUpReception.parseDecoderOutput
      (p := p) (eta := rate.eta.val) none = none := by
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      ((none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))).map
        (OrdinaryMessageCodec.wordEquivFlat
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) = none
    rfl
  rw [hparsed, hdecode]
  simp [input, CoordinatorUpReception.packDecodeResult,
    CoordinatorUpReception.decoderBankAfter]

/-- Every non-invalid filtered result carries the decoder bank advanced by the
actual selected-channel transition; all unselected follower channels are
preserved. -/
theorem receiveUpFilteredAtRow_preserves_unselected_bank
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (receptionInputAtRow rate row inputs t) = true)
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (sourceCap_forLedger rate) rate.n rate.n_scale ×
      CoordinatorUpReception.UpDecoderBank p)
    (hresult : receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      .success out ∨
      receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
        .rejected out)
    (i : Fin (p.m - 1))
    (hi : i ≠ (receptionInputAtRow rate row inputs t).selectedFollower) :
    out.2 i = (receptionInputAtRow rate row inputs t).upDecoderBank i := by
  let input := receptionInputAtRow rate row inputs t
  have hpacked := receiveUpFilteredAtRow_eq_filtered_decode rate row inputs t
    prepared hrow hfollower htime _hinputTime hinput
  rw [hpacked] at hresult
  have hbank := CoordinatorUpReception.packDecodeResult_output_bank _ _ _ hresult
  rw [hbank]
  exact CoordinatorUpReception.decoderBankAfter_unselected input i hi

/-- The decoder bank returned by any non-invalid filtered result is
well-formed whenever the literal UP input domain check passed. -/
theorem receiveUpFilteredAtRow_bank_wellFormed
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (receptionInputAtRow rate row inputs t).time)
    (_hinputTime : inputs.2.2.1 = t)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (receptionInputAtRow rate row inputs t) = true)
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (sourceCap_forLedger rate) rate.n rate.n_scale ×
      CoordinatorUpReception.UpDecoderBank p)
    (hresult : receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
      .success out ∨
      receiveUpFilteredAtRow rate row inputs t prepared hrow hfollower htime _hinputTime =
        .rejected out) :
    CoordinatorUpReception.decoderBankWellFormed p out.2 := by
  let input := receptionInputAtRow rate row inputs t
  have hdomain : CoordinatorUpReception.receptionInputDomain input :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hinput
  have hpacked := receiveUpFilteredAtRow_eq_filtered_decode rate row inputs t
    prepared hrow hfollower htime _hinputTime hinput
  rw [hpacked] at hresult
  have hbank := CoordinatorUpReception.packDecodeResult_output_bank _ _ _ hresult
  rw [hbank]
  exact CoordinatorUpReception.decoderBankAfter_wellFormed input hdomain

/-- The choice-time current word is absent when the checked offer returns
`noOffer`; this includes an occupied follower or a nonselected channel under
the accepted local offer gate. -/
theorem currentOfferWord_none_of_local_noOffer
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row) (hfollower : prepared.follower = follower)
    (htime : prepared.time = time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary state memory)
    (hdomain : ActiveFollowerQueueOperation.stateInputDomain state)
    (hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound prepared.follower
      prepared.row prepared.activation prepared.time ∧
      state.status = .unoccupied)) :
    currentOfferWord rate row follower time prepared hrow hfollower htime = none := by
  apply currentOfferWord_eq_none_of_checked_nonoffer rate row follower time prepared
    hrow hfollower htime state memory hconfiguration
  right
  exact ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta
    prepared.follower prepared.row prepared.activation prepared.time state hdomain
    hnot

end Bandits.Support.ReferenceUpReception

end
