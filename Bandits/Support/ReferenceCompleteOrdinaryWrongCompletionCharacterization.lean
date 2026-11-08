/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSelectedDownErrorCoverage

import Lean.Elab.Tactic.Omega

/-!
# Complete ordinary wrong-completion characterization

This module characterizes the actual accepted unique wrong UP and DOWN
completions in physical records, together with ordinary prelaunch DOWN
completions on the original source input. It makes no probability or overflow
cutoff claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ReferenceCompleteOrdinaryWrongCompletionCharacterization

variable {p : ConstructorDimensions.Parameters}

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

def uniqueSolution (B : List
    (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : Prop :=
  AffineBatchDecoder.satisfies (AffineBatchDecoder.samples B) w ∧
    ∀ v, AffineBatchDecoder.satisfies (AffineBatchDecoder.samples B) v → v = w

def parsedDown (rate : ReferenceActivePhysicalStep.RateInput p)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
  OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat
      (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w))

def parsedUp (rate : ReferenceActivePhysicalStep.RateInput p)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) :=
  CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val) (some w)

/-- An actual retained DOWN completion whose unique decoded message passes
the ordinary receiver test and differs from the encoded channel word. -/
def completedOrdinaryWrongDown
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (i : Fin (p.m - 1)) : Prop :=
  ∃ logged B w M,
    (r.output.followers i).downInput = some logged ∧
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some B ∧
    uniqueSolution B w ∧
    parsedDown rate w = some M ∧
    OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M ∧
    some w ≠ ReferenceDownReception.expectedDownFlatWord
      r.output.preparation.coordinator.downView i r.input.row r.input.time

/-- An actual retained UP completion whose unique decoded message passes the
coordinator receiver test and differs from the current selected UP word. -/
def completedOrdinaryWrongUp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (i : Fin (p.m - 1)) : Prop :=
  ∃ d B w M,
    r.output.coordinator.up = some d ∧
    d.input.selectedFollower = i ∧
    ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some B ∧
    uniqueSolution B w ∧
    parsedUp rate w = some M ∧
    CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M = true ∧
    some w ≠ d.expected

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The ordinary accepted unique wrong DOWN decision at the actual prelaunch
physical update. The active selector, own entry, inherited bank and current
positive observation are all read from the same generated source branch. -/
def ordinaryWrongPrelaunchDownAt
    (z : SourceInput p) (i : Fin (p.m - 1)) (t : Fin p.T) : Prop :=
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z
  ∃ active : ReferenceGeneratedPrelaunchDownPrefix.ActiveProjection p i t.val x.row
      (Nat.le_of_lt t.isLt) x (BootstrapDimensions.roundBlockIndex p t),
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t = .inl (.inl active) ∧
    let own := ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) t
    let bank := active.val.2.2.2.downBatch
    let tr := ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own
    let B := bank.pending ++ AffineBatchDecoder.positiveAt p tr t
    ∃ w M,
      (ReferencePrelaunchFollower.decodeAt i x.row active.val.2.1 t own bank).2 = some w ∧
      B.length = AffineBatchDecoder.quota p ∧
      uniqueSolution B w ∧
      parsedDown rate w = some M ∧
      OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        0 (t.val + 1) M ∧
      some w ≠ (none : Option
        (AffineChannelLaw.Word (AffineBatchDecoder.width p)))

/-- The source-level union of ordinary prelaunch decisions and saved
postlaunch diagnostics on the complete physical suffix. -/
def ordinaryWrongCompletionAt
    (t : Fin p.T) (z : SourceInput p) : Prop :=
  (∃ i, ordinaryWrongPrelaunchDownAt rate rewards C_star C_h z i t) ∨
  ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r ∧
    ((∃ i, completedOrdinaryWrongDown rate r i) ∨
      ∃ i, completedOrdinaryWrongUp rate r i)

/-- A retained DOWN wrong-acceptance flag is exactly a quota-completed batch
with one raw solution, an ordinary accepted parse, and a different current
channel word. -/
theorem completedOrdinaryWrongDown_iff_flag
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (i : Fin (p.m - 1)) :
    completedOrdinaryWrongDown rate r i ↔
      ∃ cut, (r.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut := by
  constructor
  · rintro ⟨logged, B, w, M, hlogged, hB, hunique, hparsed, haccept, hwrongWord⟩
    obtain ⟨logged', cut, hlogged', hcut, hcompared, _hquota, _happended⟩ :=
      (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i B).mp hB
    have _hsameLogged : logged' = logged :=
      Option.some.inj (hlogged'.symm.trans hlogged)
    have hrawWord : cut.raw = some w := by
      unfold uniqueSolution at hunique
      exact (ReferenceFirstLiveDownCompletionReadout.completed_raw_some_iff
        r i B hB cut hcut w).mpr hunique
    rcases ReferenceFirstLiveDownCompletionReadout.retained_call_fields
        r i logged cut hlogged hcut hcompared with
      ⟨_, _, _, _, _, hrawCurrent, hexpected, hparse, hacceptance, hcomparison⟩
    have hrawNeExpected : cut.raw ≠ cut.expectedWord := by
      intro heq
      apply hwrongWord
      rw [← hrawWord, ← hexpected]
      exact heq
    have hdecFalse : decide (cut.raw = cut.expectedWord) = false := by
      simp [hrawNeExpected]
    have hwrong : ReferenceDownReception.wrongUniqueAccepted cut := by
      rw [ReferenceDownReception.wrongUniqueAccepted]
      refine ⟨?_, ?_, ?_⟩
      · rw [hcomparison, hdecFalse]
      · rw [hrawWord]
        exact Option.some_ne_none _
      · have hordinaryAcceptance : cut.ordinaryAcceptance := by
          rw [hacceptance, hrawWord]
          have hparser : OrdinaryMessageCodec.parseDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat
                (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w)) = some M := by
            simpa [parsedDown] using hparsed
          change (match OrdinaryMessageCodec.parseDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat
                (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w)) with
            | none => False
            | some parsed => OrdinaryMessageCodec.acceptDown
                (ReferencePrelaunchFollower.codecParams p rate.eta)
                (ReferencePrelaunchFollower.acceptedStart logged)
                (r.input.time.val + 1) parsed)
          rw [hparser]
          exact haccept
        exact hordinaryAcceptance
    exact ⟨cut, hcut, hwrong⟩
  · rintro ⟨cut, hcut, hwrong⟩
    rcases ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hcut with
      ⟨_, _, logged, _, _, _, hlogged, _⟩
    have hcompared : cut.rawComparison.isSome = true := by
      rw [hwrong.1]
      rfl
    rcases ReferenceFirstLiveDownCompletionReadout.retained_call_fields
        r i logged cut hlogged hcut hcompared with
      ⟨_, _, _, _, _, hrawCurrent, hexpected, hparse, hacceptance, hcomparison⟩
    obtain ⟨w, hrawWord⟩ : ∃ w, cut.raw = some w := by
      cases hraw : cut.raw with
      | none => exact (hwrong.2.1 hraw).elim
      | some w => exact ⟨w, rfl⟩
    let tr := ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
    have hstepOutput : AffineBatchDecoder.stepOutput p tr logged.downBatch r.input.time =
        some w := by
      simpa only [ActiveFollowerDownAcceptance.currentDecodeStep,
        AffineBatchDecoder.decodeStep, tr] using hrawCurrent.symm.trans hrawWord
    rcases (AffineBatchDecoder.stepOutput_eq_some_iff p tr logged.downBatch
        r.input.time w).mp hstepOutput with ⟨hquota, hsolves, hunique⟩
    let B := ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r i logged
    have hB : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some B := by
      apply (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i B).2
      refine ⟨logged, cut, hlogged, hcut, ?_, ?_, rfl⟩
      · exact hcompared
      · simpa [B, ReferenceFirstLiveDownCompletionReadout.appendedDownBatch,
          tr, ActiveFollowerDownAcceptance.currentInputExtension,
          ActiveFollowerDownAcceptance.currentRoundInput] using hquota
    have huniqueB : uniqueSolution B w := by
      unfold uniqueSolution
      simpa [B, ReferenceFirstLiveDownCompletionReadout.appendedDownBatch,
        tr, ActiveFollowerDownAcceptance.currentInputExtension,
        ActiveFollowerDownAcceptance.currentRoundInput] using And.intro hsolves hunique
    have hparsed : parsedDown rate w = cut.ordinaryParse := by
      rw [hparse, hrawWord]
      rfl
    have hlocal : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
        r.input.time logged cut.ordinaryParse := by
      have hlocal' := hwrong.2.2
      rw [hacceptance] at hlocal'
      rw [← hparse] at hlocal'
      exact hlocal'
    cases hparsedM : parsedDown rate w with
    | none =>
        have hparsedCut : cut.ordinaryParse = none :=
          hparsed.symm.trans hparsedM
        rw [hparsedCut, ReferenceDownReception.ordinaryLocalAcceptanceTest] at hlocal
        exact hlocal.elim
    | some M =>
        have hparsedCut : cut.ordinaryParse = some M :=
          hparsed.symm.trans hparsedM
        have hacceptedM : OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M := by
          rw [hparsedCut, ReferenceDownReception.ordinaryLocalAcceptanceTest] at hlocal
          exact hlocal
        have hwrongWord : some w ≠ ReferenceDownReception.expectedDownFlatWord
            r.output.preparation.coordinator.downView i r.input.row r.input.time := by
          intro heq
          have hrawEqExpected : cut.raw = cut.expectedWord := by
            rw [hrawWord, hexpected]
            exact heq
          have hdecTrue : decide (cut.raw = cut.expectedWord) = true := by
            simp [hrawEqExpected]
          have hfalse := hwrong.1
          rw [hcomparison, hdecTrue] at hfalse
          cases hfalse
        exact ⟨logged, B, w, M, hlogged, hB, huniqueB, hparsedM,
          hacceptedM, hwrongWord⟩

private theorem collectionPostChoice_up_diagnostic_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).up = some d) :
    ∃ ledgerStarted,
      ReferenceCoordinatorUpPhysicalCall.tailLedger?
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights =
          some ledgerStarted ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).2 ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare x) ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) ∧
      d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate x.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare x) ledgerStarted) x.time
        ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x))
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare x) payload started weights)
  cases hrecording : recordingInput with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording,
        recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | success ledgerStarted =>
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, hstart] at hd
          rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
          let inputs := ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) ledgerStarted
          let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
          have hinput : input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted := rfl
          have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
            by_contra hnot
            have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
              cases hval : CoordinatorUpReception.receptionInputCheck input with
              | false => rfl
              | true => exact (hnot hval).elim
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hfalse] at hd
          have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger?
              (ReferenceActivePhysicalStep.prepare x) payload ledger started weights =
                some ledgerStarted := by
            simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
              hrecording, hstart]
          have hdiagnosticInput : d.input = input := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.input) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hdecoderAfter : d.decoderAfter =
              (CoordinatorUpReception.decoderTransition input).1 := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hraw : d.raw = (CoordinatorUpReception.decoderTransition input).2 := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.raw) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hexpected : d.expected = ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare x) := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.expected) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hparsed : d.parsed = ReferenceUpReception.rawParsedOutput rate input := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.parsed) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hlocal : d.locallyAccepted =
              ReferenceUpReception.rawParsedLocalAcceptance rate input := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.locallyAccepted) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          have hwrong : d.wrongUniqueAccepted =
              ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row inputs x.time
                ((ReferenceActivePhysicalStep.prepare x).followers.followers
                  (ReferenceActivePhysicalStep.upSenderIndex x))
                ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
                ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
                ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl := by
            have hmap := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.wrongUniqueAccepted) hd
            simpa [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] using hmap.symm
          refine ⟨ledgerStarted, htail, ?_, ?_, hdecoderAfter, ?_, hexpected,
            ?_, ?_, hwrong⟩
          · simpa [hinput] using hcheck
          · exact hdiagnosticInput.trans hinput
          · simpa [hinput] using hraw
          · simpa [hinput] using hparsed
          · simpa [hinput] using hlocal

private theorem upDiagnosticLogicalFields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hinput : d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)
    (hraw : d.raw = (CoordinatorUpReception.decoderTransition
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).2)
    (hexpected : d.expected = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input))
    (hparsed : d.parsed = ReferenceUpReception.rawParsedOutput rate
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger))
    (hlocal : d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger))
    (hwrong : d.wrongUniqueAccepted =
      ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) ledger) r.input.time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input))
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl) :
    d.parsed = CoordinatorUpReception.parseDecoderOutput d.raw ∧
    d.locallyAccepted = (match d.parsed with
      | none => false
      | some M => CoordinatorCollectionLedger.acceptUpCheck d.input.ledger
          d.input.selectedFollower M) ∧
    (d.wrongUniqueAccepted = true ↔
      ∃ w M, d.raw = some w ∧
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (some w) = some M ∧
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger
          d.input.selectedFollower M = true ∧
        some w ≠ d.expected) := by
  let input := ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger
  let inputs := ReferenceActivePhysicalStep.upInputs
    (ReferenceActivePhysicalStep.prepare r.input) ledger
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let sender := prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex r.input)
  have hrow := prepared.follower_alignment (ReferenceActivePhysicalStep.upSenderIndex r.input)
  have hparsedField : d.parsed = CoordinatorUpReception.parseDecoderOutput d.raw := by
    calc
      d.parsed = ReferenceUpReception.rawParsedOutput rate input := hparsed
      _ = CoordinatorUpReception.parseDecoderOutput d.raw := by
        simp only [ReferenceUpReception.rawParsedOutput]
        rw [hraw]
  have hrawD : d.raw = (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time)).2 := by
    simpa [input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, inputs] using hraw
  have hinputD : d.input =
      ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time := by
    simpa [input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, inputs] using hinput
  have hlocalField : d.locallyAccepted = (match d.parsed with
      | none => false
      | some M => CoordinatorCollectionLedger.acceptUpCheck d.input.ledger
          d.input.selectedFollower M) := by
    have h := hlocal
    rw [← hinput, ReferenceUpReception.rawParsedLocalAcceptance,
      ReferenceUpReception.rawParsedOutput] at h
    rw [hinputD, ← hrawD, ← hparsedField, ← hinputD] at h
    exact h
  have hwrongIff := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
    rate r.input.row inputs r.input.time sender hrow.1 hrow.2.1 hrow.2.2.1 rfl
  have hcurrent : d.expected = ReferenceUpReception.currentOfferWord rate r.input.row
      (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).selectedFollower
      (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).time
      sender hrow.1 hrow.2.1 hrow.2.2.1 := by
    calc
      d.expected = ReferenceActivePhysicalStep.upExpected prepared := hexpected
      _ = ReferenceUpReception.currentOfferWord rate r.input.row
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).selectedFollower
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).time
          sender hrow.1 hrow.2.1 hrow.2.2.1 := by rfl
  have hflag : d.wrongUniqueAccepted = true ↔
      ∃ w M, (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time)).2 =
            some w ∧
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (some w) = some M ∧
        CoordinatorCollectionLedger.acceptUpCheck
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).ledger
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).selectedFollower
          M = true ∧
        some w ≠ ReferenceUpReception.currentOfferWord rate r.input.row
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).selectedFollower
          (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time).time
          sender hrow.1 hrow.2.1 hrow.2.2.1 := by
    rw [hwrong]
    exact hwrongIff
  refine ⟨hparsedField, hlocalField, ?_⟩
  rw [hflag]
  constructor
  · rintro ⟨w, M, hraw', hparse', haccept', hneq'⟩
    refine ⟨w, M, ?_, hparse', ?_, ?_⟩
    · exact hrawD.trans hraw'
    · simpa [hinputD] using haccept'
    · simpa [hcurrent] using hneq'
  · rintro ⟨w, M, hraw', hparse', haccept', hneq'⟩
    refine ⟨w, M, ?_, hparse', ?_, ?_⟩
    · exact hrawD.symm.trans hraw'
    · simpa [hinputD] using haccept'
    · simpa [hcurrent] using hneq'

/-- Full unconditional fields of an actually retained UP diagnostic. The
diagnostic survives all result and finish failures at the actual physical
collection receiver. Its row, time and affine coordinate are the ones in the
original record. -/
theorem retainedUpDiagnosticFields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    ∃ ledger, ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).2 ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.parsed = CoordinatorUpReception.parseDecoderOutput d.raw ∧
      d.locallyAccepted = (match d.parsed with
        | none => false
        | some M => CoordinatorCollectionLedger.acceptUpCheck d.input.ledger
            d.input.selectedFollower M) ∧
      (d.wrongUniqueAccepted = true ↔
        ∃ w M, d.raw = some w ∧
          CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
            (some w) = some M ∧
          CoordinatorCollectionLedger.acceptUpCheck d.input.ledger
            d.input.selectedFollower M = true ∧
          some w ≠ d.expected) ∧
      d.input.time = r.input.time ∧
      d.input.selectedFollower = CoordinatorUpMeasurability.selectedFollowerIndex
        ((r.input.rows r.input.selected).2 r.input.time) ∧
      d.input.affineSample = ((r.input.rows r.input.selected).2 r.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((r.input.rows r.input.selected).2 r.input.time)) := by
  have hdOriginal := hd
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hdOriginal
  rcases hfields with ⟨_, _, _, _, htime, _, hselected, hsample, _, _, _, _, _, _⟩
  have hstep : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  rw [hstep] at hd
  classical
  let x := r.input
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | recorderBoundaryFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | choiceRejected installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | chosen installation selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.first (.chosen installation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                (ReferenceActivePhysicalStep.prepare x) (.chosen installation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure dispatched _ reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoassignment selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
                  hnoassignment selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hd
            obtain ⟨ledgerStarted, htail, hcheck, hinput, hafter, hraw, hexpected,
                hparsed, hlocal, hwrong⟩ :=
              collectionPostChoice_up_diagnostic_fields rate x registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
                d hd
            have hlogical := upDiagnosticLogicalFields rate r d ledgerStarted
              hinput hraw hexpected hparsed hlocal hwrong
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter, hraw, hexpected,
              hlogical.1, hlogical.2.1, hlogical.2.2, htime, hselected, hsample⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, x, hcoord, hsel] using htail
      | continuingChosen dispatched startRoundEq continuation selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.continuingChosen dispatched startRoundEq continuation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
                (ReferenceActivePhysicalStep.prepare x) registers owned base
                (.continuingChosen dispatched startRoundEq continuation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | coreFailure core started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | continuing core snapshot boundary scores =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hd
            let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            obtain ⟨ledgerStarted, htail, hcheck, hinput, hafter, hraw, hexpected,
                hparsed, hlocal, hwrong⟩ :=
              collectionPostChoice_up_diagnostic_fields rate x payload ledger
                snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                d hd
            have hlogical := upDiagnosticLogicalFields rate r d ledgerStarted
              hinput hraw hexpected hparsed hlocal hwrong
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter, hraw, hexpected,
              hlogical.1, hlogical.2.1, hlogical.2.2, htime, hselected, hsample⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, x, hcoord, hsel, source] using htail
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq output
          localEq clockData installed selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure] at hd
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] at hd

/-- At an actual selected UP receiver site, the saved wrong flag is exactly a
quota-completed unique batch whose parsed record passes the local ledger test
and differs from the expected UP word. -/
theorem completedOrdinaryWrongUp_iff_flag
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : Record rate) (i : Fin (p.m - 1)) :
    completedOrdinaryWrongUp rate r i ↔
      ∃ d, r.output.coordinator.up = some d ∧
        d.input.selectedFollower = i ∧ d.wrongUniqueAccepted = true := by
  constructor
  · rintro ⟨d, B, w, M, hd, hselected, hB, hunique, hparsed, haccept, hwrong⟩
    obtain ⟨ledger, hsite, hcheck, hinput, hafter, hraw, hexpected,
      hparsedField, hlocalField, hflag, htime, hselectedField, hsample⟩ :=
      retainedUpDiagnosticFields rate r d hd
    obtain ⟨_, d', hd', _, _, hrawBatch⟩ :=
      ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i B hB
    cases hd.symm.trans hd'
    have hrawD : d.raw = AffineBatchDecoder.batchOutput B := hrawBatch
    have hrawWord : d.raw = some w := by
      rw [hrawD]
      unfold uniqueSolution at hunique
      have hs := (AffineBatchDecoder.solve_eq_some_iff
        (AffineBatchDecoder.samples B) w).2 hunique
      exact hs
    have hparsedD : d.parsed = some M := by
      calc
        d.parsed = CoordinatorUpReception.parseDecoderOutput d.raw := hparsedField
        _ = CoordinatorUpReception.parseDecoderOutput (some w) := by rw [hrawWord]
        _ = some M := hparsed
    have hlocalEq : d.locallyAccepted =
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M := by
      rw [hlocalField, hparsedD, hselected]
    have hacceptI : CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M = true := by
      simpa [hselected] using haccept
    have hlocalTrue : d.locallyAccepted = true := hlocalEq.trans hacceptI
    have hacceptSelected : CoordinatorCollectionLedger.acceptUpCheck
        d.input.ledger d.input.selectedFollower M = true := by
      rw [hselected]
      exact haccept
    have hflagTrue := hflag.mpr ⟨w, M, hrawWord, hparsed, hacceptSelected, hwrong⟩
    exact ⟨d, hd, hselected, hflagTrue⟩
  · rintro ⟨d, hd, hselected, hwrong⟩
    obtain ⟨ledger, hsite, hcheck, hinput, hafter, hrawField, hexpected,
      hparsedField, hlocalField, hflag, htime, hselectedField, hsample⟩ :=
      retainedUpDiagnosticFields rate r d hd
    obtain ⟨w, M, hrawWord, hparsed, haccept, hwrongWord⟩ := hflag.mp hwrong
    have hparser : CoordinatorUpReception.parseDecoderOutput d.raw = some M := by
      rw [hrawWord]
      exact hparsed
    have hparsedD : d.parsed = some M := hparsedField.trans hparser
    have hlocalEq : d.locallyAccepted =
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M := by
      rw [hlocalField, hparsedD, hselected]
    have hacceptI : CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M = true := by
      simpa [hselected] using haccept
    have hlocalTrue : d.locallyAccepted = true := hlocalEq.trans hacceptI
    have hrawForStep : (CoordinatorUpReception.decoderTransition d.input).2 = some w := by
      rw [← hinput] at hrawField
      exact hrawField.symm.trans hrawWord
    have hstepOutput : AffineBatchDecoder.stepOutput p
        (CoordinatorUpReception.traceAt d.input)
        (d.input.upDecoderBank d.input.selectedFollower) d.input.time = some w := by
      simpa only [CoordinatorUpReception.decoderTransition,
        AffineBatchDecoder.decodeStep] using hrawForStep
    let B := ReferenceCollectionUpFailureReadoutV2.appendedUp rate d
    have hquotaUnique := (AffineBatchDecoder.stepOutput_eq_some_iff p
      (CoordinatorUpReception.traceAt d.input)
      (d.input.upDecoderBank d.input.selectedFollower) d.input.time w).mp hstepOutput
    have hcheckD : CoordinatorUpReception.receptionInputCheck d.input = true := by
      rw [hinput]
      exact hcheck
    have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheckD
    obtain ⟨_, _, _, _, _, _, _, hbank⟩ :=
      CoordinatorUpReception.receptionInputDomain_parts d.input hdomain
    have hpending := (hbank d.input.selectedFollower).1
    have heligible : AffineBatchDecoder.eligible
        (CoordinatorUpReception.roundInput d.input) := by
      by_contra hnot
      have hnotTrace : ¬ AffineBatchDecoder.eligible
          (CoordinatorUpReception.traceAt d.input d.input.time) := by
        change ¬ AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
        exact hnot
      have hpositive : AffineBatchDecoder.positiveAt p
          (CoordinatorUpReception.traceAt d.input) d.input.time = [] := by
        simp [AffineBatchDecoder.positiveAt, hnotTrace]
      have hquotaPending : AffineBatchDecoder.quota p ≤
          (d.input.upDecoderBank d.input.selectedFollower).pending.length := by
        simpa [B, ReferenceCollectionUpFailureReadoutV2.appendedUp, hpositive] using
          hquotaUnique.1
      omega
    have hB : ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some B := by
      apply (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i B).2
      refine ⟨d, hd, hselected, hcheckD, heligible, ?_, rfl⟩
      simpa [B, ReferenceCollectionUpFailureReadoutV2.appendedUp] using hquotaUnique.1
    obtain ⟨_, d', hd', _, _, hrawBatch⟩ :=
      ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i B hB
    cases hd.symm.trans hd'
    have hbatchRaw : AffineBatchDecoder.batchOutput B = some w := by
      exact hrawBatch.symm.trans hrawWord
    have hunique : uniqueSolution B w := by
      unfold uniqueSolution
      exact (AffineBatchDecoder.solve_eq_some_iff
        (AffineBatchDecoder.samples B) w).mp hbatchRaw
    have hacceptI : CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M = true := by
      simpa [hselected] using haccept
    exact ⟨d, B, w, M, hd, hselected, hB, hunique,
      by simpa [parsedUp] using hparsed, hacceptI, hwrongWord⟩

/-- The literal saved suffix flag is exactly the union of the two actual
completed ordinary receiver decisions in its physical record. -/
theorem savedWrongRecordFlag_eq_true_iff
    (r : Record rate) :
    ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true ↔
      (∃ i, completedOrdinaryWrongDown rate r i) ∨
        ∃ i, completedOrdinaryWrongUp rate r i := by
  have hflag :
      ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true ↔
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
    simp [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag]
  rw [hflag,
    ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted]
  constructor
  · rintro (⟨d, hd, hwrong⟩ | ⟨i, cut, hcut, hwrong⟩)
    · right
      refine ⟨d.input.selectedFollower, ?_⟩
      exact (completedOrdinaryWrongUp_iff_flag rate r d.input.selectedFollower).2
        ⟨d, hd, rfl, hwrong⟩
    · left
      exact ⟨i, (completedOrdinaryWrongDown_iff_flag rate r i).2
        ⟨cut, hcut, hwrong⟩⟩
  · rintro (⟨i, hdown⟩ | ⟨i, hup⟩)
    · right
      obtain ⟨cut, hcut, hwrong⟩ :=
        (completedOrdinaryWrongDown_iff_flag rate r i).1 hdown
      exact ⟨i, cut, hcut, hwrong⟩
    · left
      obtain ⟨d, hd, _hselected, hwrong⟩ :=
        (completedOrdinaryWrongUp_iff_flag rate r i).1 hup
      exact ⟨d, hd, hwrong⟩

/-- The actual ordinary prelaunch decision readout agrees with the local
literal batch characterization built from the same active projection,
private own entry, inherited bank and current positive equation. -/
theorem ordinaryWrongPrelaunchDownAt_iff_readout
    (z : SourceInput p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    ordinaryWrongPrelaunchDownAt rate rewards C_star C_h z i t ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true := by
  rw [ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_completedBatch_iff
    rate rewards C_star C_h z i t]
  constructor
  · rintro ⟨active, hpref, w, M, hraw, hlength, hunique, hparse, haccept, _hnotNone⟩
    let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
      rate rewards C_star C_h z
    let own := ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) t
    let bank := active.val.2.2.2.downBatch
    have hparsedAt : ReferencePrelaunchFollower.parsedAt rate.eta i x.row
        active.val.2.1 t own bank = some M := by
      change OrdinaryMessageCodec.parseDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        ((ReferencePrelaunchFollower.decodeAt i x.row active.val.2.1 t own bank).2.map
          (OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M
      rw [hraw]
      change OrdinaryMessageCodec.parseDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (Option.map (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm (some w)) = some M
      rw [show Option.map (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm (some w) =
          some ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w) from rfl]
      simpa [parsedDown] using hparse
    obtain ⟨w', hraw', _hquota, hbatchOutput, hencode⟩ :=
      ReferencePrelaunchFollower.parsedAt_some_completed rate.eta i x.row
        active.val.2.1 t own bank M hparsedAt
    have hword : w' = w := Option.some.inj (hraw'.symm.trans hraw)
    subst w'
    have hsolution : AffineBatchDecoder.satisfies
        (AffineBatchDecoder.samples
          (bank.pending ++ AffineBatchDecoder.positiveAt p
            (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own) t)) w ∧
        (∀ v, AffineBatchDecoder.satisfies
          (AffineBatchDecoder.samples
            (bank.pending ++ AffineBatchDecoder.positiveAt p
              (ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 t own) t)) v →
            v = w) := by
      simpa [uniqueSolution] using hunique
    exact ⟨active, hpref, w, M, hraw, hlength, hbatchOutput,
      hsolution.1, hsolution.2, hparse, hencode, haccept⟩
  · rintro ⟨active, hpref, w, M, hraw, hlength, _hbatchOutput,
      hsolves, hunique, hparse, _hencode, haccept⟩
    have hreadout :=
      (ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_completedBatch_iff
        rate rewards C_star C_h z i t).2
        ⟨active, hpref, w, M, hraw, hlength, _hbatchOutput, hsolves,
          hunique, hparse, _hencode, haccept⟩
    obtain ⟨_, _, test, _, hsent, _⟩ :=
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_currentAbsentWord
        rate rewards C_star C_h z i t hreadout
    have hnotNone : (some w : Option
        (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠ none := by
      have hnotTest : (some w : Option
          (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠ test.sent := by
        rw [hsent]
        exact Option.some_ne_none _
      simp
    exact ⟨active, hpref, w, M, hraw, hlength, ⟨hsolves, hunique⟩,
      hparse, haccept, hnotNone⟩

/-- Dated source-level union of ordinary active prelaunch batches and saved
postlaunch record flags on the original unrestricted physical source. -/
theorem ordinaryWrongCompletionAt_iff
    (t : Fin p.T) (z : SourceInput p) :
    ordinaryWrongCompletionAt rate rewards C_star C_h t z ↔
      (∃ i, ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true) ∨
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
        ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true := by
  unfold ordinaryWrongCompletionAt
  constructor
  · rintro (⟨i, hpre⟩ | ⟨r, hrecord, hlocal⟩)
    · exact Or.inl ⟨i,
        (ordinaryWrongPrelaunchDownAt_iff_readout rate rewards C_star C_h z i t).1 hpre⟩
    · exact Or.inr ⟨r, hrecord,
        (savedWrongRecordFlag_eq_true_iff rate r).2 hlocal⟩
  · rintro (⟨i, hpre⟩ | ⟨r, hrecord, hflag⟩)
    · exact Or.inl ⟨i,
        (ordinaryWrongPrelaunchDownAt_iff_readout rate rewards C_star C_h z i t).2 hpre⟩
    · exact Or.inr ⟨r, hrecord,
        (savedWrongRecordFlag_eq_true_iff rate r).1 hflag⟩

end Bandits.Support.ReferenceCompleteOrdinaryWrongCompletionCharacterization
