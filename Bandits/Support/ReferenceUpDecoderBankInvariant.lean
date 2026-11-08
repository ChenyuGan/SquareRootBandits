/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Persistent UP decoder bank on the actual computed run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-42`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,277-284,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108`.

This module follows the actual `ReferenceActivePhysicalStep.step` inside the
canonical `ReferenceActivePhysicalHorizon.run`.  The UP bank is initialized at
launch and carried across the first, live, and later-assignment phases.  During
collection, each channel outside the actual ledger's pending set has an empty
pending batch.  A completed decoder batch remains in its audit history when
its pending list is cleared.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.ReferenceUpReception

namespace Bandits.Support.ReferenceUpDecoderBankInvariant

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The literal phase-indexed UP-bank clause in the source induction
invariant. -/
def coordinatorBankInvariant (configuration :
    ReferenceActivePhysicalStep.CoordinatorConfiguration p rate)
    (bank : CoordinatorUpReception.UpDecoderBank p) : Prop :=
  CoordinatorUpReception.decoderBankWellFormed p bank ∧
    match configuration with
    | .first => ∀ i, (bank i).pending = []
    | .live _ _ _ => ∀ i, (bank i).pending = []
    | .collection _ ledger _ =>
        ∀ i, i ∉ ledger.pending → (bank i).pending = []
    | .dagger => True

/-- The source induction invariant for the persistent coordinator UP bank.
Assignment phases have empty channel batches.  During collection, every
channel already removed from that collection's pending set has an empty batch.
Dagger states impose only the bank's decoder-state bounds. -/
def upBankInvariant (state : ReferenceActivePhysicalStep.State p rate) : Prop :=
  coordinatorBankInvariant state.coordinator state.upDecoderBank

/-- Decode-state well-formedness gives the empty-batch lemmas consumed by the
physical cutoff windows. -/
theorem decoderStateWellFormed_pending_empty
    (channel : Bandits.Support.AffineBatchDecoder.State p.T
      (Bandits.Support.AffineBatchDecoder.width p))
    (hempty : channel.pending = []) :
    channel.pending.length = 0 ∧
      ∀ entry, entry ∈ channel.pending → False := by
  simp [hempty]

/-- The source base constructor has the first coordinator phase and the exact
initial UP bank. Follower configurations and activations are arbitrary. -/
theorem firstState_upBankInvariant
    (activations : Fin (p.m - 1) → ReferencePrelaunchFollower.Activation p)
    (followers : Fin (p.m - 1) → DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    upBankInvariant
      ({ coordinator := .first
         upDecoderBank := CoordinatorUpReception.initialUpDecoderBank p
         activations := activations
         followers := followers } : ReferenceActivePhysicalStep.State p rate) := by
  simp [upBankInvariant, coordinatorBankInvariant]
  exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩

/-- The actual launched-boundary constructor initializes exactly the first
phase and source empty UP bank.  All original boundary data and hypotheses
remain explicit. -/
theorem ofActualLaunchedBoundary_upBankInvariant
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ActualInitializationLaunchState.RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
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
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    upBankInvariant
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched) := by
  unfold upBankInvariant
  rw [ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator,
    ActualInitializationLaunchState.ofActualLaunchedBoundary_upDecoderBank]
  exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, by
    intro i
    rfl⟩

/-- An accepted decoder record is the only UP transition that erases a
collection member. -/
private theorem decodeUp_success_pending_erase
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hdom : CoordinatorUpReception.receptionInputDomain input)
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hresult : CoordinatorCollectionLedger.decodeUp input.ledger
      input.selectedFollower parsed = .success out) :
    out.pending = input.ledger.pending.erase input.selectedFollower := by
  classical
  obtain ⟨hvalid, _, hphase, hcut, hcutCursor, hcursorT, _, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts input hdom
  have hinput : CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
      input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ input.ledger.cutoff ∧ input.ledger.cutoff ≤ input.ledger.cursor ∧
      input.ledger.cursor ≤ p.T :=
    ⟨hvalid, hphase, hcut, hcutCursor, hcursorT⟩
  obtain ⟨M, hparsed, haccept⟩ :=
    CoordinatorUpReception.decodeUp_success_implies_literal_acceptUp
      input hdom parsed out hresult
  have hacceptCheck : CoordinatorCollectionLedger.acceptUpCheck
      input.ledger input.selectedFollower M = true :=
    (CoordinatorCollectionLedger.acceptUpCheck_iff
      input.ledger input.selectedFollower M).2 haccept
  have hresult' : CoordinatorCollectionLedger.decodeUp input.ledger
      input.selectedFollower (some M) = .success out := by
    simpa [hparsed] using hresult
  unfold CoordinatorCollectionLedger.decodeUp at hresult'
  simp only [dite_eq_left hinput, hparsed, ite_eq_left hacceptCheck] at hresult'
  repeat' (first | split at hresult' |
    simp_all [CoordinatorCollectionLedger.acceptUpCandidate])
  all_goals
    exact congrArg (fun ledger => ledger.pending) hresult'.symm

/-- A locally rejected decoder record changes only the decode phase, so its
collection pending set is unchanged. -/
private theorem decodeUp_rejected_pending_frame
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hdom : CoordinatorUpReception.receptionInputDomain input)
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hresult : CoordinatorCollectionLedger.decodeUp input.ledger
      input.selectedFollower parsed = .rejected out) :
    out.pending = input.ledger.pending := by
  classical
  obtain ⟨hvalid, _, hphase, hcut, hcutCursor, hcursorT, _, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts input hdom
  have hinput : CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
      input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ input.ledger.cutoff ∧ input.ledger.cutoff ≤ input.ledger.cursor ∧
      input.ledger.cursor ≤ p.T :=
    ⟨hvalid, hphase, hcut, hcutCursor, hcursorT⟩
  cases hparsed : parsed with
  | none =>
      have hnone := CoordinatorUpReception.decodeUp_none_rejected input hdom
      rw [hparsed, hnone] at hresult
      have hEq := Checked.rejected.inj hresult
      rw [← hEq]
  | some M =>
      by_cases hacceptCheck : CoordinatorCollectionLedger.acceptUpCheck
          input.ledger input.selectedFollower M = true
      · unfold CoordinatorCollectionLedger.decodeUp at hresult
        simp only [dite_eq_left hinput, hparsed, ite_eq_left hacceptCheck] at hresult
        repeat' (first | split at hresult | simp_all)
      · have hnot : ¬ CoordinatorCollectionLedger.acceptUpCheck
            input.ledger input.selectedFollower M := by
          intro h
          exact hacceptCheck h
        have hunaccepted := CoordinatorUpReception.decodeUp_unaccepted_rejected
          input hdom M hnot
        rw [hparsed, hunaccepted] at hresult
        have hEq := Checked.rejected.inj hresult
        rw [← hEq]

/-- The actual filtered UP reception preserves the bank bounds and couples a
removed collection member to a completed, cleared raw decoder batch. -/
private theorem filteredReceive_upBankInvariant
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hpending : ∀ i, i ∉ ledger.pending →
      (x.state.upDecoderBank i).pending = [])
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hresult : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result =
        .success out ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .rejected out) :
    CoordinatorUpReception.decoderBankWellFormed p out.2 ∧
      (∀ i, i ∉ out.1.pending → (out.2 i).pending = []) ∧
      out.2 = CoordinatorUpReception.decoderBankAfter
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) := by
  classical
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  let selectedFollower := ReferenceActivePhysicalStep.upSenderIndex x
  let sender := prepared.followers.followers selectedFollower
  have hrow := (prepared.follower_alignment selectedFollower).1
  have hfollower := (prepared.follower_alignment selectedFollower).2.1
  have htime := (prepared.follower_alignment selectedFollower).2.2.1
  have hfiltered : ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time
      sender
      hrow hfollower htime rfl = .success out ∨
      ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time sender
        hrow hfollower htime rfl = .rejected out := by
    have h := hresult
    unfold ReferenceActivePhysicalStep.receiveUp at h
    change ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time
      (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
      hrow hfollower htime rfl = .success out ∨
      ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time sender
        hrow hfollower htime rfl = .rejected out at h
    exact h
  have hinput : CoordinatorUpReception.receptionInputCheck input = true := by
    cases hcheck : CoordinatorUpReception.receptionInputCheck input with
    | true => rfl
    | false =>
        rcases hfiltered with hs | hr
        · unfold ReferenceUpReception.receiveUpFilteredAtRow at hs
          simp [input, inputs, hcheck] at hs
        · unfold ReferenceUpReception.receiveUpFilteredAtRow at hr
          simp [input, inputs, hcheck] at hr
  have hdom : CoordinatorUpReception.receptionInputDomain input :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hinput
  let raw := (CoordinatorUpReception.decoderTransition input).2
  let expected := ReferenceUpReception.currentOfferWord rate x.row input.selectedFollower
    input.time sender hrow hfollower htime
  let parsed := CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
    (ReferenceUpReception.filterRawByExpected raw expected)
  have hpacked := ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode
    rate x.row inputs x.time sender hrow hfollower htime rfl hinput
  have hpacked' :
      ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time sender
        hrow hfollower htime rfl =
        CoordinatorUpReception.packDecodeResult
          (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed)
          (CoordinatorUpReception.decoderBankAfter input) := by
    simpa only [raw, expected, parsed, inputs, input,
      CoordinatorUpReception.decoderBankAfter] using hpacked
  have hresult' := hfiltered
  rw [hpacked'] at hresult'
  have hdecoded : CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed =
      .success out.1 ∨
      CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed =
        .rejected out.1 := by
    cases hresult' with
    | inl hs =>
        cases hd : CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed with
        | success decoded =>
            have hpair := Checked.success.inj (by
              simpa [CoordinatorUpReception.packDecodeResult, hd] using hs)
            exact Or.inl (congrArg Checked.success (congrArg Prod.fst hpair))
        | rejected decoded => simp [CoordinatorUpReception.packDecodeResult, hd] at hs
        | invalid => simp [CoordinatorUpReception.packDecodeResult, hd] at hs
    | inr hr =>
        cases hd : CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower parsed with
        | success decoded => simp [CoordinatorUpReception.packDecodeResult, hd] at hr
        | rejected decoded =>
            have hpair := Checked.rejected.inj (by
              simpa [CoordinatorUpReception.packDecodeResult, hd] using hr)
            exact Or.inr (congrArg Checked.rejected (congrArg Prod.fst hpair))
        | invalid => simp [CoordinatorUpReception.packDecodeResult, hd] at hr
  have houtBank : out.2 = CoordinatorUpReception.decoderBankAfter input :=
    CoordinatorUpReception.packDecodeResult_output_bank _ _ out hresult'
  have hwell := ReferenceUpReception.receiveUpFilteredAtRow_bank_wellFormed
    rate x.row inputs x.time sender hrow hfollower htime rfl hinput out hfiltered
  refine ⟨hwell, ?_, ?_⟩
  intro i hi
  by_cases hisel : i = input.selectedFollower
  · subst i
    by_cases hwasPending : input.selectedFollower ∈ input.ledger.pending
    · rcases hdecoded with hsuccess | hrejected
      ·
        obtain ⟨M, hparsed, _⟩ :=
          CoordinatorUpReception.decodeUp_success_implies_literal_acceptUp
            input hdom parsed out.1 hsuccess
        have hfilteredSome : ∃ word,
            ReferenceUpReception.filterRawByExpected raw expected = some word := by
          cases hfilteredRaw : ReferenceUpReception.filterRawByExpected raw expected with
          | none =>
              have hparsedNone : parsed = none := by
                dsimp [parsed, CoordinatorUpReception.parseDecoderOutput]
                rw [hfilteredRaw]
                rfl
              rw [hparsedNone] at hparsed
              cases hparsed
          | some word => exact ⟨word, rfl⟩
        obtain ⟨word, hfilteredRaw⟩ := hfilteredSome
        have hraw : raw = some word := by
          unfold ReferenceUpReception.filterRawByExpected at hfilteredRaw
          split at hfilteredRaw
          · exact hfilteredRaw
          · contradiction
        have hclear := CoordinatorUpReception.decoderTransition_decision_clears
          input hdom word (by simpa [raw] using hraw)
        rw [houtBank, CoordinatorUpReception.decoderBankAfter, Function.update_self,
          hclear.1]
      · have hnew := decodeUp_rejected_pending_frame input hdom _ out.1 hrejected
        rw [hnew] at hi
        exact False.elim (hi hwasPending)
    · have hnotGate : ¬ CoordinatorUpReception.receptionGate input := by
        rintro ⟨_, _, hmem⟩
        exact hwasPending hmem
      have hnotEligible : ¬ AffineBatchDecoder.eligible
          (CoordinatorUpReception.traceAt input input.time) := by
        intro heligible
        have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate input).mp heligible.1
        exact hnotGate hgate
      have htransition := CoordinatorUpReception.decoderTransition_ineligible input hdom hnotEligible
      rw [houtBank, CoordinatorUpReception.decoderBankAfter, Function.update_self,
        htransition]
      have hnotOld : input.selectedFollower ∉ ledger.pending := by
        change input.selectedFollower ∉ input.ledger.pending
        exact hwasPending
      exact hpending input.selectedFollower hnotOld
  ·
    have hnotOld : i ∉ input.ledger.pending := by
      cases hdecoded with
      | inl hsuccess =>
          rw [decodeUp_success_pending_erase input hdom _ out.1 hsuccess] at hi
          intro hmem
          exact hi (Finset.mem_erase.mpr ⟨hisel, hmem⟩)
      | inr hrejected =>
          rw [decodeUp_rejected_pending_frame input hdom _ out.1 hrejected] at hi
          exact hi
    have hframe := ReferenceUpReception.receiveUpFilteredAtRow_preserves_unselected_bank
      rate x.row inputs x.time sender hrow hfollower htime rfl hinput out hfiltered i hisel
    rw [hframe]
    have hnotOld' : i ∉ ledger.pending := by
      change i ∉ input.ledger.pending
      exact hnotOld
    exact hpending i hnotOld'
  simpa [inputs, input] using houtBank

/-- Stage one changes queue, cursor, recorder history, and possibly a sparse
learning cell, but it never changes the collection pending set. -/
private theorem startRound_pending_frame
    (ledger ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      enabled raw = .success ledgerStarted) :
    ledgerStarted.pending = ledger.pending := by
  unfold CoordinatorCollectionLedger.startRound at hstart
  repeat' (first | split at hstart | simp_all)
  simpa [CoordinatorCollectionLedger.startRoundCandidate] using
    (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.pending) hstart.symm)

/-- FinishRound advances phase/cursor fields but retains the actual pending
follower set. -/
private theorem finishRound_pending_frame
    (ledger ledgerFinished : ReferenceActivePhysicalStep.Ledger rate)
    (hfinish : CoordinatorCollectionLedger.finishRound ledger = .success ledgerFinished) :
    ledgerFinished.pending = ledger.pending := by
  unfold CoordinatorCollectionLedger.finishRound at hfinish
  repeat' (first | split at hfinish | simp_all)
  simpa [CoordinatorCollectionLedger.finishRoundCandidate] using
    (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.pending) hfinish.symm)

/-- The live post-choice tail either keeps the exact bank in a dagger failure
or installs it unchanged in the next live phase. -/
private theorem livePostChoice_upBankInvariant
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hbank : CoordinatorUpReception.decoderBankWellFormed p x.state.upDecoderBank)
    (hempty : ∀ i, (x.state.upDecoderBank i).pending = []) :
    coordinatorBankInvariant
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).upDecoderBank := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  repeat' (first | split |
    simp [ReferenceActivePhysicalStep.coordinatorFailure,
      coordinatorBankInvariant, hbank, hempty])

/-- No UP receiver is committed by the live post-choice tail: recorder,
service, confirmation, and clock outcomes all retain the exact old bank. -/
theorem livePostChoice_upDecoderBank_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).upDecoderBank =
      x.state.upDecoderBank := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  repeat' (first | split |
    simp [ReferenceActivePhysicalStep.coordinatorFailure])

/-- A later assignment can be installed only after the actual pending set is
empty. The conclusion uses the carried StartRound output, not a history
assumption. -/
private theorem laterChosen_pending_empty
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending =
      .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hinstruction : started.assignmentStart = some instruction) :
    ledger.pending = ∅ := by
  by_contra hne
  have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time clock := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_start_time_valid
  have hSigma : clock.sigma = some payload.sigma := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_sigma_eq
  have hU : clock.u = some cutoff := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_cutoff_eq
  unfold CoordinatorPhaseClock.startRoundTimeValid at htime
  rw [hSigma, hU] at htime
  have hut : cutoff.val ≤ x.time.val := htime.2
  have hcollection := CoordinatorPhaseClock.startRound_collection_pending p rate.eta.val
    x.time payload.sigma cutoff clock ledger.pending core.clock_parameter_valid
    core.clock_registers_valid core.clock_sigma_eq core.clock_cutoff_eq hut hne
  have hstarted := Except.ok.inj (hstart.symm.trans hcollection)
  have hfield := congrArg (fun result => result.assignmentStart) hstarted
  rw [hinstruction] at hfield
  cases hfield

/-- The actual collection tail transports the phase-indexed clause through
stage one, filtered reception, ledger finish, and clock finish. Failure at any
later stage is the literal dagger branch with the bank reached at that point.
-/
private theorem collectionPostChoice_upBankInvariant
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hbank : CoordinatorUpReception.decoderBankWellFormed p x.state.upDecoderBank)
    (hpending : ∀ i, i ∉ ledger.pending → (x.state.upDecoderBank i).pending = []) :
    coordinatorBankInvariant
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).upDecoderBank := by
  classical
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord,
        ReferenceActivePhysicalStep.coordinatorFailure,
        coordinatorBankInvariant, hbank]
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          enabled raw with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            enabled, raw, ReferenceActivePhysicalStep.coordinatorFailure,
            coordinatorBankInvariant, hbank]
      | rejected _ =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            enabled, raw, ReferenceActivePhysicalStep.coordinatorFailure,
            coordinatorBankInvariant, hbank]
      | success ledgerStarted =>
          have hservice : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success ledgerStarted := by
            simpa [enabled, raw] using hstart
          rw [ReferenceActivePhysicalStep.collectionPostChoice_after_start
            prepared payload ledger started weights recording ledgerStarted hrecord hservice]
          have hstartedPending : ledgerStarted.pending = ledger.pending :=
            startRound_pending_frame ledger ledgerStarted x.time enabled raw hstart
          have hpendingStarted : ∀ i, i ∉ ledgerStarted.pending →
              (x.state.upDecoderBank i).pending = [] := by
            intro i hi
            apply hpending i
            simpa [hstartedPending] using hi
          cases hcut : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result with
          | invalid =>
              simp [hcut, ReferenceActivePhysicalStep.collectionFinish,
                ReferenceActivePhysicalStep.coordinatorFailure, coordinatorBankInvariant, hbank]
          | success out =>
              have hout := filteredReceive_upBankInvariant prepared ledgerStarted
                hpendingStarted out (Or.inl hcut)
              cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
              | invalid =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure,
                    coordinatorBankInvariant, hout.1]
              | rejected _ =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure,
                    coordinatorBankInvariant, hout.1]
              | success ledgerFinished =>
                  have hfinishedPending := finishRound_pending_frame out.1 ledgerFinished hfinish
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock out.1.pending x.row with
                  | error _ =>
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                        hclock, ReferenceActivePhysicalStep.coordinatorFailure,
                        coordinatorBankInvariant, hout.1, hfinishedPending]
                  | ok clockFinished =>
                      have hclock' : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock ledgerFinished.pending x.row = .ok clockFinished := by
                        simpa [hfinishedPending] using hclock
                      have hcollection := ReferenceActivePhysicalStep.collectionFinish_success
                        payload started recording (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)
                        out.1 ledgerFinished out.2 clockFinished (Or.inl (by simpa using hcut))
                        hfinish hclock'
                      rw [hcollection]
                      simpa [coordinatorBankInvariant, hfinishedPending] using
                        ⟨hout.1, hout.2.1⟩
          | rejected out =>
              have hout := filteredReceive_upBankInvariant prepared ledgerStarted
                hpendingStarted out (Or.inr hcut)
              cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
              | invalid =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure,
                    coordinatorBankInvariant, hout.1]
              | rejected _ =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure,
                    coordinatorBankInvariant, hout.1]
              | success ledgerFinished =>
                  have hfinishedPending := finishRound_pending_frame out.1 ledgerFinished hfinish
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock out.1.pending x.row with
                  | error _ =>
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                        hclock, ReferenceActivePhysicalStep.coordinatorFailure,
                        coordinatorBankInvariant, hout.1, hfinishedPending]
                  | ok clockFinished =>
                      have hclock' : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock ledgerFinished.pending x.row = .ok clockFinished := by
                        simpa [hfinishedPending] using hclock
                      have hcollection := ReferenceActivePhysicalStep.collectionFinish_success
                        payload started recording (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)
                        out.1 ledgerFinished out.2 clockFinished (Or.inr (by simpa using hcut))
                        hfinish hclock'
                      rw [hcollection]
                      simpa [coordinatorBankInvariant, hfinishedPending] using
                        ⟨hout.1, hout.2.1⟩

/-- The computed coordinator observation preserves the literal phase-indexed
bank invariant in one actual physical round. -/
private theorem observeCoordinator_upBankInvariant
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (hInv : upBankInvariant x.state) :
    coordinatorBankInvariant prepared.observeCoordinator.configuration
      prepared.observeCoordinator.upDecoderBank := by
  classical
  cases hphase : x.state.coordinator with
  | first =>
      simp [upBankInvariant, coordinatorBankInvariant, hphase] at hInv
      rcases hInv with ⟨hbank, hempty⟩
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput x)) with
      | first outcome =>
        cases outcome with
        | chosen installed selected =>
          have hcut : prepared.coordinator = .first (.chosen installed selected) := by
            have h := prepared.coordinator_eq
            simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
            rw [hdispatch] at h
            exact h
          have hfirst : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selected := by
            have h := hdispatch
            simp only [CoordinatorRoundDispatch.dispatch] at h
            exact CoordinatorRoundDispatch.Outcome.first.inj h
          have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
            x installed selected hfirst
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared (.chosen installed selected) hcut]
          have hpost := livePostChoice_upBankInvariant prepared installed.registers
            installed.ownedRegisters installed.followerBaseScore
            installed.startRoundResult hbank hempty
          simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt, htime] using hpost
        | choiceDomainFailure installed =>
          have hcut : prepared.coordinator = .first (.choiceDomainFailure installed) := by
            have h := prepared.coordinator_eq
            simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
            rw [hdispatch] at h
            exact h
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared (.choiceDomainFailure installed) hcut]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure,
            coordinatorBankInvariant, hbank]
        | recorderBoundaryFailure installed =>
          have hcut : prepared.coordinator = .first (.recorderBoundaryFailure installed) := by
            have h := prepared.coordinator_eq
            simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
            rw [hdispatch] at h
            exact h
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared (.recorderBoundaryFailure installed) hcut]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure,
            coordinatorBankInvariant, hbank]
        | choiceRejected installed =>
          have hcut : prepared.coordinator = .first (.choiceRejected installed) := by
            have h := prepared.coordinator_eq
            simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
            rw [hdispatch] at h
            exact h
          rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
            prepared (.choiceRejected installed) hcut]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.coordinatorFailure,
            coordinatorBankInvariant, hbank]
  | live registers owned baseScores =>
      simp [upBankInvariant, coordinatorBankInvariant, hphase] at hInv
      rcases hInv with ⟨hbank, hempty⟩
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned baseScores)) with
      | live outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation selected =>
            have hcut : prepared.coordinator = .live registers owned baseScores
                (.continuingChosen dispatched hstart continuation selected) := by
              have h := prepared.coordinator_eq
              simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
              rw [hdispatch] at h
              exact h
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned baseScores
              (.continuingChosen dispatched hstart continuation selected) hcut]
            have hpost := livePostChoice_upBankInvariant prepared
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) baseScores
              dispatched.startResult hbank hempty
            simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt] using hpost
        | cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
            hclock hpending noAssignment selected =>
            have hcut : prepared.coordinator = .live registers owned baseScores
                (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                  hclock hpending noAssignment selected) := by
              have h := prepared.coordinator_eq
              simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
              rw [hdispatch] at h
              exact h
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned baseScores
              (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                hclock hpending noAssignment selected) hcut]
            have hsharedPending :
                (ReferenceActivePhysicalStep.sharedLedger ledger).pending = Finset.univ := by
              simp [ReferenceActivePhysicalStep.sharedLedger, ledgerEq,
                CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
            have hpendingShared : ∀ i,
                i ∉ (ReferenceActivePhysicalStep.sharedLedger ledger).pending →
                  (x.state.upDecoderBank i).pending = [] := by
              intro i hi
              simp [hsharedPending] at hi
            have hpost := collectionPostChoice_upBankInvariant prepared registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
              hbank hpendingShared
            simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt] using hpost
        | clockFailure failure hfail =>
            have hcut : prepared.coordinator = .live registers owned baseScores
                (.clockFailure failure hfail) := by
              have h := prepared.coordinator_eq
              simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
              rw [hdispatch] at h
              exact h
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned baseScores (.clockFailure failure hfail) hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.coordinatorFailure,
              coordinatorBankInvariant, hbank]
        | initializerFailure dispatched hstart checked hchecked =>
            have hcut : prepared.coordinator = .live registers owned baseScores
                (.initializerFailure dispatched hstart checked hchecked) := by
              have h := prepared.coordinator_eq
              simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
              rw [hdispatch] at h
              exact h
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned baseScores
              (.initializerFailure dispatched hstart checked hchecked) hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.coordinatorFailure,
              coordinatorBankInvariant, hbank]
        | localFailure dispatched hstart reason =>
            have hcut : prepared.coordinator = .live registers owned baseScores
                (.localFailure dispatched hstart reason) := by
              have h := prepared.coordinator_eq
              simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
              rw [hdispatch] at h
              exact h
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned baseScores (.localFailure dispatched hstart reason) hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.coordinatorFailure,
              coordinatorBankInvariant, hbank]
  | collection payload ledger proposal =>
      simp [upBankInvariant, coordinatorBankInvariant, hphase] at hInv
      rcases hInv with ⟨hbank, hpending⟩
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput
              x payload ledger clock cutoff)) with
        | collection outcome =>
          cases outcome with
          | continuing core snapshot boundary scores =>
              have hcut : prepared.coordinator =
                  .collection payload ledger clock cutoff
                    (.continuing core snapshot boundary scores) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.continuing core snapshot boundary scores) hcut]
              have hpost := collectionPostChoice_upBankInvariant prepared payload
                ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                hbank hpending
              simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt] using hpost
          | laterChosen core consistent started hstart instruction hinstruction output
              localEq clockData installed selected =>
              have hcut : prepared.coordinator =
                  .collection payload ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction
                      output localEq clockData installed selected) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.laterChosen core consistent started hstart instruction hinstruction
                  output localEq clockData installed selected) hcut]
              have hledgerEmpty := laterChosen_pending_empty payload ledger clock cutoff
                core started hstart instruction hinstruction
              have hempty : ∀ i, (x.state.upDecoderBank i).pending = [] := by
                intro i
                apply hpending i
                simp [hledgerEmpty]
              have hpost := livePostChoice_upBankInvariant prepared installed.registers
                installed.ownedRegisters installed.retainedBaseScore started hbank hempty
              have htime := ReferenceActivePhysicalStep.later_instruction_time x payload
                ledger clock cutoff core started instruction hstart hinstruction
              simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt, htime] using hpost
          | clockFailure failure hstart =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.clockFailure failure hstart) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff (.clockFailure failure hstart) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | localFailure started hstart hinvalid reason =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.localFailure started hstart hinvalid reason) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff (.localFailure started hstart hinvalid reason) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | coreFailure core started hstart reason =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.coreFailure core started hstart reason) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff (.coreFailure core started hstart reason) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
          | laterChoiceFailure core consistent started hstart instruction hinstruction output
              localEq clockData installed reason =>
              have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                  (.laterChoiceFailure core consistent started hstart instruction hinstruction
                    output localEq clockData installed reason) := by
                have h := prepared.coordinator_eq
                simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                prepared payload ledger clock cutoff
                (.laterChoiceFailure core consistent started hstart instruction hinstruction
                  output localEq clockData installed reason) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure,
                coordinatorBankInvariant, hbank]
      · have hcut : prepared.coordinator = .invalidCollectionCutoff := by
          simpa [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] using
            prepared.coordinator_eq
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.coordinatorFailure,
          coordinatorBankInvariant, hbank]
  | dagger =>
      simp [upBankInvariant, coordinatorBankInvariant, hphase] at hInv
      have hbank := hInv
      have hcut : prepared.coordinator = .dagger := by
        simpa [ReferenceActivePhysicalStep.dispatch, hphase] using prepared.coordinator_eq
      rw [ReferenceActivePhysicalStep.observeCoordinator_dagger prepared hcut]
      simp [coordinatorBankInvariant, hbank]

/-- Literal one-step preservation for the sole physical `step` and its actual
coordinator/follower output. -/
theorem step_upBankInvariant
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (hInv : upBankInvariant x.state) :
    upBankInvariant (ReferenceActivePhysicalStep.step x).next := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hobs := observeCoordinator_upBankInvariant prepared hInv
  simpa [upBankInvariant, ReferenceActivePhysicalStep.step, prepared] using hobs

/-- The one-step bank result is exactly the bank carried by the sole prepared
coordinator observation. -/
theorem step_upDecoderBank_eq_actualObservation
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.upDecoderBank =
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.upDecoderBank :=
  (ReferenceActivePhysicalStep.step_next_fields x).2.1

/-- Every computed prefix of the canonical physical run preserves the
phase-indexed persistent UP-bank invariant. -/
theorem run_prefix_upBankInvariant
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial) :
    ∀ k, (hk : k ≤ count) → upBankInvariant
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
        (by omega) hmode).finalState := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [ReferenceActivePhysicalHorizon.run_zero_final]
      exact hinitial
  | succ k ih =>
      intro hk
      have hstepSpan : start + (k + 1) ≤ p.T := by omega
      let acc := ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
        (by omega) hmode
      let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
        ⟨start + k, by omega, by omega⟩
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
        start hmode acc entry
      have hacc : upBankInvariant acc.finalState := ih (by omega)
      have hfold := ReferenceActivePhysicalHorizon.foldRound_equations initial rows selected
        rewards start hmode acc entry
      change (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
        hmode acc entry).finalState = (ReferenceActivePhysicalStep.step input).next ∧ _ at hfold
      have hrun := ReferenceActivePhysicalHorizon.run_successor_step initial rows selected
        rewards start k hstepSpan hmode
      rw [hrun]
      change upBankInvariant
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
          hmode acc entry).finalState
      rw [hfold.1]
      exact step_upBankInvariant hacc

/-- The endpoint of the actual canonical run is the corresponding computed
prefix and therefore has a well-formed persistent UP bank. -/
theorem run_upBankInvariant
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial) :
    upBankInvariant
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).finalState := by
  exact run_prefix_upBankInvariant initial rows selected rewards start count hspan hmode
    hinitial count le_rfl

/-- Appending a suffix to the computed prefix preserves the same invariant;
the equality is the accepted canonical `run_append` decomposition. -/
theorem run_append_upBankInvariant
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial) :
    upBankInvariant
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
        (start + left) right (by omega) (by omega) hmode
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
          (by omega) hmode)).finalState := by
  rw [← ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start left right
    hspan hmode]
  exact run_upBankInvariant initial rows selected rewards start (left + right) hspan hmode hinitial

/-- The accepted launch-boundary conversion supplies the initialized state for
the actual run invariant. The active suffix may begin at any source index at
or after the conversion's computed block stop. -/
theorem ofActualLaunchedBoundary_run_upBankInvariant
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ActualInitializationLaunchState.RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
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
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (start count : ℕ) (hstart : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) ≤ start)
    (hspan : start + count ≤ p.T) :
    upBankInvariant
      (ReferenceActivePhysicalHorizon.run
        (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
          b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
        source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        (by
          intro i
          have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
            source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
            hlaunched i
          omega)).finalState := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro i
    have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
    have hactivation' : (initial.activations i).val ≤
        BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 := by
      simpa [initial] using hactivation
    omega
  have hinitial := ofActualLaunchedBoundary_upBankInvariant source rewards rate C_star C_h b h
    actual past hr hdown hclean hforce launch learnerSeed hlaunched
  exact run_upBankInvariant initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    hinitial

/-- The actual records in `H.run` all start from the invariant state reached
by the preceding literal `S.step`. -/
theorem run_record_input_upBankInvariant
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial) :
    ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records, upBankInvariant record.input.state := by
  have hwalk : ∀ (state : ReferenceActivePhysicalStep.State p rate)
      (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (final : ReferenceActivePhysicalStep.State p rate),
      ReferenceActivePhysicalHorizon.Connected state records final →
      upBankInvariant state →
      ∀ record, record ∈ records → upBankInvariant record.input.state := by
    intro state records
    induction records generalizing state with
    | nil =>
        intro final hconnected hstate record hmem
        simp at hmem
    | cons head tail ih =>
        intro final hconnected hstate record hmem
        rcases hconnected with ⟨hhead, htail⟩
        rcases List.mem_cons.mp hmem with heq | htailmem
        · subst record
          rw [hhead]
          exact hstate
        · have hheadInv : upBankInvariant head.input.state := by
            rw [hhead]
            exact hstate
          have hnextInv : upBankInvariant head.output.next := by
            rw [head.output_eq]
            exact step_upBankInvariant hheadInv
          exact ih head.output.next final htail hnextInv record htailmem
  exact hwalk initial _ _
    (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count
      hspan hmode) hinitial

/-- Every retained input time is one of the actual calendar coordinates in
the canonical computed run. -/
theorem run_record_time_mem_calendar
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan hmode).records) :
    record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar start count := by
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan hmode
  have hmem : record.input.time.val ∈
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.map (fun record => record.input.time.val)) :=
    List.mem_map.mpr ⟨record, hrecord, rfl⟩
  rw [htimes] at hmem
  exact hmem

/-- The retained pre-reception dispatch cut is the actual live `cutoffChosen`
outcome, together with its actual live input configuration. -/
def isActualCutoffChosen {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) : Prop :=
  ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base)),
    x.state.coordinator = .live registers owned base ∧
    cut = .live registers owned base outcome ∧
      match outcome with
      | .cutoffChosen .. => True
      | _ => False

/-- At the pre-reception choice cut of every actual `cutoffChosen` record,
each persistent UP channel is empty. The record is drawn from the canonical
computed run and its output remains the literal result of `S.step`. -/
theorem run_cutoff_up_pending_empty
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan hmode).records)
    (hcut : isActualCutoffChosen record.output.preparation.coordinator) :
    ∀ i, (record.input.state.upDecoderBank i).pending = [] := by
  have hInv := run_record_input_upBankInvariant initial rows selected rewards start count hspan
    hmode hinitial record hrecord
  have hcut' := hcut
  rw [record.output_eq] at hcut'
  change isActualCutoffChosen (ReferenceActivePhysicalStep.dispatch record.input) at hcut'
  cases hphase : record.input.state.coordinator with
  | first =>
      rcases hcut' with ⟨registers, owned, base, outcome, hstate, _, _⟩
      simp [hphase] at hstate
  | live registers owned base =>
      simp [upBankInvariant, coordinatorBankInvariant, hphase] at hInv
      exact hInv.2
  | collection payload ledger proposal =>
      rcases hcut' with ⟨registers, owned, base, outcome, hstate, _, _⟩
      simp [hphase] at hstate
  | dagger =>
      rcases hcut' with ⟨registers, owned, base, outcome, hstate, _, _⟩
      simp [hphase] at hstate

/-- Exact initial `pendingLength` and vacuous `pendingOlder` inputs supplied
to `WaitedWordWindow.up_acceptance_window` at each actual physical cutoff.
This supplies only those two empty-batch premises. -/
theorem run_cutoff_up_acceptance_pending_inputs
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : upBankInvariant initial)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan hmode).records)
    (hcut : isActualCutoffChosen record.output.preparation.coordinator)
    (i : Fin (p.m - 1)) (rounds : List (Fin p.T)) :
    let s := record.input.state.upDecoderBank i
    s.pending.length = 0 ∧
      ∀ e, e ∈ s.pending → ∀ t, t ∈ rounds → e.time.val < t.val := by
  dsimp
  have hempty := run_cutoff_up_pending_empty initial rows selected rewards start count hspan hmode
    hinitial record hrecord hcut i
  constructor
  · simp [hempty]
  · intro e he t ht
    simp [hempty] at he

/-- The actual row-local reception input uses the bank whose well-formedness
is guaranteed by the source invariant, satisfying its named executable bank
check consumer. -/
theorem actualReception_decoderBankCheck
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hInv : upBankInvariant x.state) :
    CoordinatorUpReception.decoderBankCheck p
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).upDecoderBank = true := by
  have hbank := hInv.1
  apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p _).2
  change CoordinatorUpReception.decoderBankWellFormed p
    (CoordinatorUpMeasurability.receptionInputAtRow x.row
      (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).upDecoderBank
  rw [CoordinatorUpMeasurability.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtControl_upDecoderBank]
  simpa [ReferenceActivePhysicalStep.upInputs] using hbank

/-- On either non-invalid result of the actual filtered receiver, the returned
bank is exactly `decoderBankAfter` at that same row-local reception input. -/
theorem actualFilteredReceive_decoderBankAfter
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hpending : ∀ i, i ∉ ledger.pending → (x.state.upDecoderBank i).pending = [])
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hresult : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .success out ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .rejected out) :
    out.2 = CoordinatorUpReception.decoderBankAfter
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) :=
  (filteredReceive_upBankInvariant prepared ledger hpending out hresult).2.2

/-- `collectionFinish` keeps the old bank for an invalid receiver result. On
success or ordinary rejection it carries the advanced bank through every
later ledger and clock finish outcome. -/
theorem collectionFinish_upDecoderBank_alternatives
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).upDecoderBank =
        x.state.upDecoderBank ∨
      ∃ out, (cut.result = .success out ∨ cut.result = .rejected out) ∧
        (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).upDecoderBank =
          out.2 := by
  cases hresult : cut.result with
  | invalid =>
      left
      simp [ReferenceActivePhysicalStep.collectionFinish, hresult,
        ReferenceActivePhysicalStep.coordinatorFailure]
  | success out =>
      right
      refine ⟨out, Or.inl rfl, ?_⟩
      cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected _ =>
          simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock ledgerFinished.pending x.row with
          | error _ =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish, hclock,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | ok clockFinished =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish, hclock]
  | rejected out =>
      right
      refine ⟨out, Or.inr rfl, ?_⟩
      cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected _ =>
          simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock ledgerFinished.pending x.row with
          | error _ =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish, hclock,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | ok clockFinished =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish, hclock]

end Bandits.Support.ReferenceUpDecoderBankInvariant

end
