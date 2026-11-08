/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Literal collection service/UP/finish continuation

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-60`.

This module replaces only the first recorder call of the existing collection
post-choice operation by its primitive optional output. All later calls are
literal. Its temporary output code retains the
existing coordinator configuration, complete UP diagnostic, bank, recording
output, and all failure tags. The returned configuration is encoded with the
canonical `encodeCoordinator`; this file defines no second state or transition.

The code proves local measurability and same-input reconstruction only. It
does not establish dispatch measurability, chronology, state invariants,
initialization, horizon measurability, or a manuscript theorem. Recorder gate,
floor and Borel proofs belong to the independent recorder producer. The named
consumer is a fresh full collection-tail composer after both producers pass
independent review and BOTH integration gates, then the whole-step/horizon
composition with the other branch producers. No such consumption is asserted
here. All service, terminal, disabled, zero-arrival, clipped and overflow paths
are retained by the exact equality to the existing checked operations.

Accepted direct project dependency:
`Bandits.Support.ReferenceActivePhysicalStepMeasurability`, SHA-256
`11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314`,
independent review-0347 PASS and both clean gate sets recorded in
`private-audit-archive/turn-00127-dependency-evidence.json`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionServiceTailMeasurability

open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ReferenceUpReception
open Bandits.Support.ReferenceUpReceptionMeasurability
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.AssignmentPayloadDerivedMeasurability
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.CoordinatorRecordingMeasurability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.ActiveRoundActions

instance startRoundResultMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

instance startRoundResultDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) :=
  ⟨fun _ => trivial⟩

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The selected sender is always the same follower selected by this row's
UP adapter. -/
def selectedUpFollower (x : RoundInput p rate) : Fin (p.m - 1) :=
  ReferenceActivePhysicalStep.upSenderIndex x

/-- The selected sender's original activation, read from the canonical
round's full activation vector. -/
def selectedUpActivation (x : RoundInput p rate) :
    ReferencePrelaunchFollower.Activation p :=
  x.state.activations (selectedUpFollower x)

/-- The selected sender's original incoming configuration, with its original
saved-real buffer fibers. -/
def selectedUpIncoming (x : RoundInput p rate) :
    FollowerPrepareJointMeasurability.IncomingConfiguration p rate :=
  FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
    (x.state.followers (selectedUpFollower x))

/-- The selected sender's active-time proof is the original `RoundInput`
typing field at that same row-selected follower. -/
theorem selectedUpActivation_valid (x : RoundInput p rate) :
    (selectedUpActivation x).val ≤ x.time.val + 1 :=
  x.active (selectedUpFollower x)

/-- The PREPARE used by the UP adapter is exactly the accepted prepared round
formed from the same row, time, activation, and incoming local configuration.
This is pointwise reconstruction; no prepared or dispatched map is assumed
measurable. -/
theorem selectedUpPrepared_reconstruct (x : RoundInput p rate) :
    ReferenceUpReceptionMeasurability.preparedRoundAtComponents rate
        (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
        (selectedUpActivation_valid x) =
      (ReferenceActivePhysicalStep.prepare x).followers.followers
        (selectedUpFollower x) := by
  simpa [selectedUpActivation, selectedUpIncoming, selectedUpFollower,
    ReferenceUpReceptionMeasurability.preparedRoundAtComponents,
    ReferenceUpReceptionMeasurability.preparedOutputAtComponents,
    ReferenceUpReceptionMeasurability.selectedFollowerAtComponents,
    ReferenceActivePhysicalStep.upSenderIndex,
    ReferenceActivePhysicalStepMeasurability.preparedFollowerCode] using
    ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct x
      (selectedUpFollower x)

/-- Countable coordinates of the existing complete UP diagnostic, in the
source record's field order. -/
structure UpDiagnosticCode (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) where
  input : ReferenceUpReceptionMeasurability.ReceptionInput p rate
  expected : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  decoderAfter : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)
  raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  parsed : Option (OrdinaryMessageCodec.UpRecord
    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
  locallyAccepted : Bool
  rawMatches : Bool
  wrongUniqueAccepted : Bool
  deriving Countable

instance upDiagnosticCodeMeasurableSpace (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    MeasurableSpace (UpDiagnosticCode p rate) := ⊤

instance upDiagnosticCodeDiscreteMeasurableSpace (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    DiscreteMeasurableSpace (UpDiagnosticCode p rate) := ⟨fun _ => trivial⟩

instance upDiagnosticOptionMeasurableSpace (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    MeasurableSpace (Option (UpDiagnosticCode p rate)) := ⊤

/-- Product coordinates used to assemble the complete actual receiver
diagnostic. Its reception input and every decoder/parse result are retained. -/
abbrev CollectionUpDiagnosticRead (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceUpReceptionMeasurability.ReceptionInput p rate ×
    (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) ×
      (AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) ×
        (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) ×
          (Option (OrdinaryMessageCodec.UpRecord
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)) ×
            (Bool × (Bool × Bool))))))

instance collectionDecoderAfterMeasurableSpace (p : Parameters) :
    MeasurableSpace (AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := ⊤

instance coordinatorFailureMeasurableSpace :
    MeasurableSpace (ReferenceActivePhysicalStep.CoordinatorFailure) := ⊤

instance collectionClockRegistersMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorPhaseClock.ClockRegisters p) := ⊤

instance collectionFinishRoundResultMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorPhaseClock.FinishRoundResult p) := ⊤

instance collectionClockFailureMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.ClockFailure) := ⊤

instance collectionClockFailureCountable :
    Countable (CoordinatorPhaseClock.ClockFailure) :=
  Bandits.Support.CoordinatorCollectionRunMeasurabilityRepair.clockFailureCode_injective.countable

instance collectionClockFinishOutputMeasurableSpace (p : Parameters) :
    MeasurableSpace (Except CoordinatorPhaseClock.ClockFailure
      (CoordinatorPhaseClock.FinishRoundResult p)) := ⊤

def collectionClockFinishOutputCode (p : Parameters) :
    Except CoordinatorPhaseClock.ClockFailure
      (CoordinatorPhaseClock.FinishRoundResult p) →
        CoordinatorPhaseClock.ClockFailure ⊕ CoordinatorPhaseClock.FinishRoundResult p
  | .error failure => .inl failure
  | .ok result => .inr result

theorem collectionClockFinishOutputCode_injective (p : Parameters) :
    Function.Injective (collectionClockFinishOutputCode p) := by
  intro x y h
  cases x with
  | error a =>
      cases y with
      | error b => simp [collectionClockFinishOutputCode] at h; cases h; rfl
      | ok b => cases h
  | ok a =>
      cases y with
      | error b => cases h
      | ok b => simp [collectionClockFinishOutputCode] at h; cases h; rfl

instance collectionClockFinishOutputCountable (p : Parameters) :
    Countable (Except CoordinatorPhaseClock.ClockFailure
      (CoordinatorPhaseClock.FinishRoundResult p)) :=
  (collectionClockFinishOutputCode_injective p).countable

abbrev CollectionClockFinishRead (p : Parameters) :=
  CoordinatorPhaseClock.ClockRegisters p ×
    (Finset (Fin (p.m - 1)) × (Fin p.T × Bool))

private theorem collectionClockFinish_eq_of_proposalBit_eq {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) (time : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₁ time =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row₂ time) :
    CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending row₁ =
      CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending row₂ := by
  unfold CoordinatorPhaseClock.finishRound
  rw [hbit]

/-- The literal phase-clock finish is Borel on arbitrary original start
registers. Its sole row-dependent read is the public proposal bit; the
accepted complete-row proposal API supplies that exact Borel coordinate. -/
theorem measurable_collectionPhaseClockFinish {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (started : Ω → StartRoundResult p)
    (pending : Ω → Finset (Fin (p.m - 1)))
    (hround : Measurable round) (hstarted : Measurable started)
    (hpending : Measurable pending) :
    Measurable (fun ω => CoordinatorPhaseClock.finishRound p ρ.eta.val
      (round ω).time (started ω).clock (pending ω) (round ω).row) := by
  let proposal := fun ω => FollowerCutoffScan.completeRowProposalBit p ρ.eta.val
    (round ω).row (round ω).time
  let read : Ω → CollectionClockFinishRead p := fun ω =>
    ((started ω).clock, (pending ω, ((round ω).time, proposal ω)))
  have hclock : Measurable (fun ω => (started ω).clock) := by
    exact (Measurable.of_discrete : Measurable
      (fun s : StartRoundResult p => s.clock)).comp hstarted
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hproposal : Measurable proposal := by
    have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
    have hrowTime : Measurable (fun ω => ((round ω).row, (round ω).time)) :=
      hrow.prodMk htime
    exact FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt
      p ρ.eta.val |>.comp hrowTime
  have hread : Measurable read := hclock.prodMk (hpending.prodMk (htime.prodMk hproposal))
  apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    read hread (fun ω => CoordinatorPhaseClock.finishRound p ρ.eta.val
      (round ω).time (started ω).clock (pending ω) (round ω).row)
  intro x y hreadEq
  rcases Prod.mk.inj hreadEq with ⟨hclockEq, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hpendingEq, hrest⟩
  rcases Prod.mk.inj hrest with ⟨htimeEq, hbitEq⟩
  change proposal x = proposal y at hbitEq
  have hbit : FollowerCutoffScan.completeRowProposalBit p ρ.eta.val
      (round x).row (round x).time = FollowerCutoffScan.completeRowProposalBit p ρ.eta.val
        (round y).row (round x).time := by
    exact hbitEq.trans (congrArg
      (FollowerCutoffScan.completeRowProposalBit p ρ.eta.val (round y).row) htimeEq.symm)
  calc
    _ = CoordinatorPhaseClock.finishRound p ρ.eta.val (round x).time
        (started x).clock (pending x) (round y).row :=
      collectionClockFinish_eq_of_proposalBit_eq ρ _ _ _ _ _ hbit
    _ = _ := by rw [hclockEq, hpendingEq, htimeEq]

/-- Losslessly pack the full local receiver read into its diagnostic code.
The false reception-input check branch remains `none`. -/
def packCollectionUpDiagnosticRead {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (read : CollectionUpDiagnosticRead p rate) : Option (UpDiagnosticCode p rate) :=
  if CoordinatorUpReception.receptionInputCheck read.1 = true then
    some {
      input := read.1
      expected := read.2.1
      decoderAfter := read.2.2.1
      raw := read.2.2.2.1
      parsed := read.2.2.2.2.1
      locallyAccepted := read.2.2.2.2.2.1
      rawMatches := read.2.2.2.2.2.2.1
      wrongUniqueAccepted := read.2.2.2.2.2.2.2 }
  else none

def encodeUpDiagnostic {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) :
    UpDiagnosticCode p rate := {
  input := diagnostic.input
  expected := diagnostic.expected
  decoderAfter := diagnostic.decoderAfter
  raw := diagnostic.raw
  parsed := diagnostic.parsed
  locallyAccepted := diagnostic.locallyAccepted
  rawMatches := diagnostic.rawMatches
  wrongUniqueAccepted := diagnostic.wrongUniqueAccepted
}

def decodeUpDiagnostic {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (code : UpDiagnosticCode p rate) : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
  input := code.input
  expected := code.expected
  decoderAfter := code.decoderAfter
  raw := code.raw
  parsed := code.parsed
  locallyAccepted := code.locallyAccepted
  rawMatches := code.rawMatches
  wrongUniqueAccepted := code.wrongUniqueAccepted
}

theorem decodeUpDiagnostic_encodeUpDiagnostic {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) :
    decodeUpDiagnostic (encodeUpDiagnostic diagnostic) = diagnostic := by
  cases diagnostic
  rfl

/-- Lossless product coordinates for the existing collection observation.
The coordinator configuration uses the accepted canonical encoder. The UP
diagnostic code retains every field, including the reception input and the
wrong-unique/local-acceptance result. -/
abbrev CollectionTailCode (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorCode p rate ×
    (CoordinatorUpReception.UpDecoderBank p ×
      (Option (ReferenceActivePhysicalStep.CoordinatorFailure) ×
        (Option (CoordinatorRecordingOperation.Output p) ×
          Option (UpDiagnosticCode p rate))))

def encodeCollectionObservation {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    CollectionTailCode p rate :=
  (encodeCoordinator observation.configuration,
    (observation.upDecoderBank,
      (observation.failure,
        (observation.recording, observation.up.map encodeUpDiagnostic))))

def decodeCollectionObservation {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (code : CollectionTailCode p rate) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := {
  configuration := decodeCoordinator code.1
  upDecoderBank := code.2.1
  failure := code.2.2.1
  recording := code.2.2.2.1
  up := code.2.2.2.2.map decodeUpDiagnostic
}

theorem decodeCollectionObservation_encodeCollectionObservation {p : Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    decodeCollectionObservation (encodeCollectionObservation observation) = observation := by
  cases observation with
  | mk configuration bank failure recording diagnostic =>
      cases diagnostic with
      | none => simp [encodeCollectionObservation, decodeCollectionObservation,
          decodeCoordinator_encodeCoordinator]
      | some diagnostic =>
          simp [encodeCollectionObservation, decodeCollectionObservation,
            decodeCoordinator_encodeCoordinator,
            decodeUpDiagnostic_encodeUpDiagnostic]

/-- Build the same actual reception input as the canonical receiver from the
returned ledger, old persistent bank, original time, and own grid observation. -/
def collectionReceptionInputMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (feedback : Ω → Fin (D p + 1)) :
    Ω → ReferenceUpReceptionMeasurability.ReceptionInput p rate :=
  fun ω => ReferenceUpReception.receptionInputAtRow rate (round ω).row
    (ReferenceUpReceptionMeasurability.receptionInputsOfComponents rate
      ledger (fun ω => (round ω).state.upDecoderBank)
      (fun ω => (round ω).time) feedback ω) (round ω).time

/-- The exact current PREPARE offer selected by the same row's UP adapter. -/
def collectionExpectedMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate) :
    Ω → Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  ReferenceUpReceptionMeasurability.currentOfferWordAtComponents rate
    (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time)
    (fun ω => selectedUpActivation_valid (round ω))

/-- Actual pre-effect filtered UP reception, using the accepted component API
on the original sender's PREPARE, moving ledger, bank, row, time, and own
observation. -/
def collectionReceiveUpMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (feedback : Ω → Fin (D p + 1)) :
    Ω → CoordinatorCollectionLedger.Checked
      (ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p) :=
  ReferenceUpReceptionMeasurability.receiveUpFilteredAtComponents rate
    (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time) ledger
    (fun ω => (round ω).state.upDecoderBank) feedback
    (fun ω => selectedUpActivation_valid (round ω))

/-- The selected sender's actual suppression diagnostic from the accepted
component API. -/
def collectionWrongUniqueMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (feedback : Ω → Fin (D p + 1)) : Ω → Bool :=
  ReferenceUpReceptionMeasurability.wrongUniqueAndLocalAcceptanceAtComponents rate
    (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time) ledger
    (fun ω => (round ω).state.upDecoderBank) feedback
    (fun ω => selectedUpActivation_valid (round ω))

/-- Preserve the actual diagnostic constructor: it exists exactly when the
actual reception input passes its source check. In particular an invalid
reception input has no diagnostic, while the receiver itself returns its
ordinary invalid tag. -/
def collectionUpDiagnosticMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (feedback : Ω → Fin (D p + 1)) :
    Ω → Option (ReferenceActivePhysicalStep.UpDiagnostic p rate) := by
  classical
  exact fun ω =>
    let input := collectionReceptionInputMap rate round ledger feedback ω
    let expected := collectionExpectedMap rate round ω
    if CoordinatorUpReception.receptionInputCheck input = true then
      let transition := CoordinatorUpReception.decoderTransition input
      some {
        input := input
        expected := expected
        decoderAfter := transition.1
        raw := transition.2
        parsed := ReferenceUpReception.rawParsedOutput rate input
        locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate input
        rawMatches := decide (transition.2 = expected)
        wrongUniqueAccepted := collectionWrongUniqueMap rate round ledger feedback ω
      }
    else none

/-- The exact `UpCut` made from the component receiver and its full diagnostic. -/
def collectionUpCutMap {Ω : Type*} {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (round : Ω → RoundInput p rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (feedback : Ω → Fin (D p + 1)) : Ω → ReferenceActivePhysicalStep.UpCut p rate :=
  fun ω => ⟨collectionReceiveUpMap rate round ledger feedback ω,
    collectionUpDiagnosticMap rate round ledger feedback ω⟩

/-- The component current-offer word is the offer in the actual UP adapter's
same-row prepared call. -/
theorem collectionExpectedMap_reconstruct {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    collectionExpectedMap rate (fun _ : Unit => x) () =
      ReferenceActivePhysicalStep.upExpected prepared := by
  have hprepared : ReferenceUpReceptionMeasurability.preparedRoundAtComponents rate
      (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
      (selectedUpActivation_valid x) =
        prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x) := by
    calc
      _ = (ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x) :=
        selectedUpPrepared_reconstruct x
      _ = ReferenceActiveFeedbackCut.prepareFollowers
          (ReferenceActivePhysicalStep.followerInput x)
          (ReferenceActivePhysicalStep.upSenderIndex x) :=
        (ReferenceActivePhysicalStep.prepare x).followers.followers_eq _
      _ = prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x) :=
        (prepared.followers.followers_eq _).symm
  unfold collectionExpectedMap
  have hactivation :
      (preparedOutputAtComponents rate (selectedUpActivation x) (selectedUpIncoming x)
        x.row x.time (selectedUpActivation_valid x)).1 = selectedUpActivation x := by
    rfl
  cases hactivation
  change preparedOutputCurrentOfferWord rate
      (selectedFollowerAtComponents x.row x.time) (selectedUpActivation x)
      (preparedOutputAtComponents rate (selectedUpActivation x) (selectedUpIncoming x)
        x.row x.time (selectedUpActivation_valid x)).2 =
    ReferenceActivePhysicalStep.upExpected prepared
  have hcurrent := currentOfferWordAtComponents_eq_reference rate
    (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
    (selectedUpActivation_valid x) (ReferenceActivePhysicalStep.upInputs prepared ledger) rfl
  rw [hcurrent]
  simp [ReferenceActivePhysicalStep.upExpected, ReferenceActivePhysicalStep.upInputs,
    ReferenceActivePhysicalStep.upSenderIndex, hprepared]

/-- The literal current-offer expression used inside the accepted filtered
receiver equals the same-row UP adapter's `upExpected`. -/
theorem collectionSelectedCurrentOffer_reconstruct {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    ReferenceUpReception.currentOfferWord rate x.row
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).time
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_row rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_follower rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x) (ReferenceActivePhysicalStep.upInputs prepared ledger))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_time rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x)) = ReferenceActivePhysicalStep.upExpected prepared := by
  have hcurrent := currentOfferWordAtComponents_eq_reference rate
    (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
    (selectedUpActivation_valid x) (ReferenceActivePhysicalStep.upInputs prepared ledger) rfl
  have hmap := collectionExpectedMap_reconstruct prepared ledger
  have hmap' : preparedOutputCurrentOfferWord rate
      (selectedFollowerAtComponents x.row x.time) (selectedUpActivation x)
      (preparedOutputAtComponents rate (selectedUpActivation x) (selectedUpIncoming x)
        x.row x.time (selectedUpActivation_valid x)).2 =
        ReferenceActivePhysicalStep.upExpected prepared := by
    simpa [collectionExpectedMap, currentOfferWordAtComponents,
      selectedUpActivation, selectedUpIncoming, selectedUpFollower,
      ReferenceActivePhysicalStep.upSenderIndex, selectedFollowerAtComponents,
      preparedOutputAtComponents,
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput] using hmap
  exact hcurrent.symm.trans hmap'

/-- Reconstruction of the component receiver to the original prepared call.
The full incoming ledger, decoder bank, time, and own observation are kept;
the same row-selected sender PREPARE is identified pointwise. -/
theorem collectionReceiveUpMap_reconstruct {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (observation : Fin (D p + 1)) (hobs : observation = prepared.coordinatorObservation) :
    collectionReceiveUpMap rate (fun _ : Unit => x) (fun _ => ledger)
        (fun _ => observation) () =
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result := by
  subst observation
  have hcurrent := collectionSelectedCurrentOffer_reconstruct prepared ledger
  have hcurrent' :
      ReferenceUpReception.currentOfferWord rate x.row
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time).time
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_row rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_follower rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x) (ReferenceActivePhysicalStep.upInputs prepared ledger))
        (ReferenceUpReceptionMeasurability.preparedRoundAtComponents_time rate
          (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
          (selectedUpActivation_valid x)) = ReferenceActivePhysicalStep.upExpected prepared := by
    simpa [ReferenceUpReception.receptionInputAtRow,
      ReferenceActivePhysicalStep.upInputs] using hcurrent
  have hcurrent'' := by
    simpa [ReferenceActivePhysicalStep.upExpected, ReferenceActivePhysicalStep.upInputs,
      ReferenceActivePhysicalStep.upSenderIndex,
      ReferenceUpReception.receptionInputAtRow] using hcurrent'
  simp only [collectionReceiveUpMap,
    ReferenceUpReceptionMeasurability.receiveUpFilteredAtComponents,
    ReferenceActivePhysicalStep.receiveUp, receptionInputsOfComponents,
    ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receiveUpFilteredAtRow,
    ReferenceUpReception.receptionInputAtRow]
  rw [hcurrent'']
  simp [CoordinatorUpMeasurability.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtControl,
    CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
    ReferenceActivePhysicalStep.upSenderIndex]

/-- The accepted wrong-unique/local-acceptance computation is reconstructed
on the exact input and selected PREPARE used by the original receiveUp. -/
theorem collectionWrongUniqueMap_reconstruct {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (observation : Fin (D p + 1)) (hobs : observation = prepared.coordinatorObservation) :
    collectionWrongUniqueMap rate (fun _ : Unit => x) (fun _ => ledger)
        (fun _ => observation) () =
      ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time
        (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
        (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
        (prepared.follower_alignment _).2.2.1 rfl := by
  subst observation
  have hprepared : ReferenceUpReceptionMeasurability.preparedRoundAtComponents rate
      (selectedUpActivation x) (selectedUpIncoming x) x.row x.time
      (selectedUpActivation_valid x) =
        prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x) := by
    calc
      _ = (ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x) :=
        selectedUpPrepared_reconstruct x
      _ = ReferenceActiveFeedbackCut.prepareFollowers
          (ReferenceActivePhysicalStep.followerInput x)
          (ReferenceActivePhysicalStep.upSenderIndex x) :=
        (ReferenceActivePhysicalStep.prepare x).followers.followers_eq _
      _ = prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x) :=
        (prepared.followers.followers_eq _).symm
  simp only [collectionWrongUniqueMap,
    ReferenceUpReceptionMeasurability.wrongUniqueAndLocalAcceptanceAtComponents,
    receptionInputsOfComponents, ReferenceActivePhysicalStep.upInputs,
    ReferenceActivePhysicalStep.upSenderIndex, hprepared]

/-- The complete local UP cut, including its exact full diagnostic, is the
original canonical receiver result. -/
theorem collectionUpCutMap_reconstruct {x : RoundInput p rate}
    (prepared : PreparedRound x) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (observation : Fin (D p + 1)) (hobs : observation = prepared.coordinatorObservation) :
    collectionUpCutMap rate (fun _ : Unit => x) (fun _ => ledger)
        (fun _ => observation) () =
      ReferenceActivePhysicalStep.receiveUp prepared ledger := by
  subst observation
  have hexpected := collectionExpectedMap_reconstruct prepared ledger
  have hwrong := collectionWrongUniqueMap_reconstruct prepared ledger
    prepared.coordinatorObservation rfl
  have hresult := collectionReceiveUpMap_reconstruct prepared ledger
    prepared.coordinatorObservation rfl
  unfold collectionUpCutMap
  apply congrArg₂ (fun result diagnostic =>
    (⟨result, diagnostic⟩ : ReferenceActivePhysicalStep.UpCut p rate)) hresult
  simp [collectionUpDiagnosticMap, collectionReceptionInputMap,
    receptionInputsOfComponents, ReferenceActivePhysicalStep.upInputs,
    ReferenceActivePhysicalStep.upExpected, hexpected, hwrong]
  rfl

/-- Finite choice is measurable by countable product sections. -/
private theorem measurable_choose_finite {Ω α β : Type*}
    [MeasurableSpace Ω] [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (choice : Ω → α) (family : α → Ω → β)
    (hchoice : Measurable choice) (hfamily : ∀ a, Measurable (family a)) :
    Measurable (fun ω => family (choice ω) ω) := by
  have hf : Measurable (fun z : Ω × α => family z.2 z.1) :=
    measurable_from_prod_countable_left hfamily
  exact hf.comp (measurable_id.prodMk hchoice)

private theorem measurable_collectionTimeControl {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (fun ω => ((round ω).row.2 (round ω).time)) := by
  let domain := ReferenceActivePhysicalStep.RoundInput p ρ
  let family : Fin p.T → domain → ContinuousLearningRows.TimeControl p :=
    fun t x => x.row.2 t
  have hfamily : ∀ t, Measurable (family t) := by
    intro t
    have hrow : Measurable (fun x : domain => x.row) :=
      ReferenceActivePhysicalStepMeasurability.measurable_row
    have hrows : Measurable (fun x : domain => x.row.2) := measurable_snd.comp hrow
    exact (measurable_pi_apply t).comp hrows
  have hselected : Measurable (fun x : domain => family x.time x) :=
    measurable_choose_finite (fun x => x.time) family
      ReferenceActivePhysicalStepMeasurability.measurable_time hfamily
  exact hselected.comp hround

private theorem measurable_collectionSelectedFollower {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (fun ω => selectedUpFollower (round ω)) := by
  let convert : Fin (PublicDiscreteDraws.followerCount p.m) → Fin (p.m - 1) :=
    fun i => ⟨i.val, by simpa [PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hconvert : Measurable convert := Measurable.of_discrete
  have hdraw : Measurable (fun ω => PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K ((round ω).row.2 (round ω).time).1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_fst.comp (measurable_collectionTimeControl round hround))
  change Measurable (convert ∘ fun ω => PublicDiscreteDraws.selectedFollowerDraw
    p.two_le_m p.m_lt_K ((round ω).row.2 (round ω).time).1)
  exact hconvert.comp hdraw

private theorem measurable_collectionSelectedActivation {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (fun ω => selectedUpActivation (round ω)) := by
  let follower := fun ω => selectedUpFollower (round ω)
  let family : Fin (p.m - 1) → Ω → ReferencePrelaunchFollower.Activation p :=
    fun i ω => (round ω).state.activations i
  have hfamily : ∀ i, Measurable (family i) := by
    intro i
    exact (ReferenceActivePhysicalStepMeasurability.measurable_activation i).comp hround
  change Measurable (fun ω => family (follower ω) ω)
  exact measurable_choose_finite follower family
    (measurable_collectionSelectedFollower round hround) hfamily

private theorem measurable_collectionSelectedIncoming {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (fun ω => selectedUpIncoming (round ω)) := by
  let follower := fun ω => selectedUpFollower (round ω)
  let family : Fin (p.m - 1) → Ω →
      FollowerPrepareJointMeasurability.IncomingConfiguration p ρ :=
    fun i ω => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration ρ
      ((round ω).state.followers i)
  have hfamily : ∀ i, Measurable (family i) := by
    intro i
    exact (ReferenceActivePhysicalStepMeasurability.measurable_incomingFollower i).comp
      hround
  change Measurable (fun ω => family (follower ω) ω)
  exact measurable_choose_finite follower family
    (measurable_collectionSelectedFollower round hround) hfamily

/-- The same-row current PREPARE offer is Borel in the canonical original
round input. This is the public expected word used by the actual filtered
receiver, not a supplied matching trace. -/
theorem measurable_collectionExpectedMap {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ) (hround : Measurable round) :
    Measurable (collectionExpectedMap ρ round) := by
  have hactivation := measurable_collectionSelectedActivation round hround
  have hincoming := measurable_collectionSelectedIncoming round hround
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  exact ReferenceUpReceptionMeasurability.measurable_currentOfferWordAtComponents ρ
    (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time)
    hactivation hincoming hrow htime
    (fun ω => selectedUpActivation_valid (round ω))

/-- The actual filtered receiver is Borel when supplied its actual returned
ledger and own grid observation as separate measurable local inputs. -/
theorem measurable_collectionReceiveUpMap {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger ρ)
    (feedback : Ω → Fin (D p + 1))
    (hround : Measurable round) (hledger : Measurable ledger)
    (hfeedback : Measurable feedback) :
    Measurable (collectionReceiveUpMap ρ round ledger feedback) := by
  have hactivation := measurable_collectionSelectedActivation round hround
  have hincoming := measurable_collectionSelectedIncoming round hround
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hbank := (ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank).comp
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hround)
  exact ReferenceUpReceptionMeasurability.measurable_receiveUpFilteredAtComponents ρ
    (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time) ledger
    (fun ω => (round ω).state.upDecoderBank) feedback
    hactivation hincoming hrow htime hledger hbank hfeedback
    (fun ω => selectedUpActivation_valid (round ω))

/-- Wrong-unique suppression and local acceptance are Borel on that same
moving ledger and decoder-bank input. -/
theorem measurable_collectionWrongUniqueMap {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger ρ)
    (feedback : Ω → Fin (D p + 1))
    (hround : Measurable round) (hledger : Measurable ledger)
    (hfeedback : Measurable feedback) :
    Measurable (collectionWrongUniqueMap ρ round ledger feedback) := by
  have hactivation := measurable_collectionSelectedActivation round hround
  have hincoming := measurable_collectionSelectedIncoming round hround
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hbank := (ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank).comp
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hround)
  exact ReferenceUpReceptionMeasurability.measurable_wrongUniqueAndLocalAcceptanceAtComponents
    ρ (fun ω => selectedUpActivation (round ω))
    (fun ω => selectedUpIncoming (round ω))
    (fun ω => (round ω).row) (fun ω => (round ω).time) ledger
    (fun ω => (round ω).state.upDecoderBank) feedback
    hactivation hincoming hrow htime hledger hbank hfeedback
    (fun ω => selectedUpActivation_valid (round ω))

/-- The actual reception input assembled from the moving ledger, old UP bank,
full original row/time and current own observation is Borel. Its selected
sample remains the same row-adapted public input used by the receiver. -/
theorem measurable_collectionReceptionInputMap {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger ρ)
    (feedback : Ω → Fin (D p + 1))
    (hround : Measurable round) (hledger : Measurable ledger)
    (hfeedback : Measurable feedback) :
    Measurable (collectionReceptionInputMap ρ round ledger feedback) := by
  let row := fun ω => (round ω).row
  let time := fun ω => (round ω).time
  let bank := fun ω => (round ω).state.upDecoderBank
  let localInputs := ReferenceUpReceptionMeasurability.receptionInputsOfComponents ρ
    ledger bank time feedback
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hbank := (ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank).comp
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hround)
  have hlocal : Measurable localInputs :=
    hledger.prodMk (hbank.prodMk (htime.prodMk hfeedback))
  let family : Fin p.T →
      ((CompletePublicTable.CompleteRow p ×
        ReferenceUpReception.ReceptionLocalInputs ρ) × Fin p.T) →
        ReferenceUpReceptionMeasurability.ReceptionInput p ρ :=
    fun t z => ReferenceUpReception.receptionInputAtRow ρ z.1.1 z.1.2 t
  have hfamily : ∀ t, Measurable (family t) := by
    intro t
    exact (CoordinatorUpMeasurability.measurable_receptionInputAtRow
      (p := p) (eta := ρ.eta.val) (heta := ρ.eta.property)
      (hcap := ReferenceUpReception.sourceCap_forLedger ρ)
      (n := ρ.n) (hn := ρ.n_scale) t).comp measurable_fst
  have hselected : Measurable (fun z :
      (CompletePublicTable.CompleteRow p ×
        ReferenceUpReception.ReceptionLocalInputs ρ) × Fin p.T =>
          family z.2 z) :=
    measurable_choose_finite (fun z => z.2) family measurable_snd hfamily
  have hrowLocal : Measurable (fun ω => (row ω, localInputs ω)) := hrow.prodMk hlocal
  exact hselected.comp (hrowLocal.prodMk htime)

/-- The full actual UP diagnostic code is Borel on its original varying
round, ledger and own observation. The accepted raw decoder, parsed output,
local-acceptance and same-row expected-word APIs supply its product fields. -/
theorem measurable_collectionUpDiagnosticCodeMap {Ω : Type*}
    [MeasurableSpace Ω] {ρ : ReferenceActivePhysicalStep.RateInput p}
    (round : Ω → RoundInput p ρ)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger ρ)
    (feedback : Ω → Fin (D p + 1))
    (hround : Measurable round) (hledger : Measurable ledger)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => (collectionUpDiagnosticMap ρ round ledger feedback ω).map
      encodeUpDiagnostic) := by
  let input := collectionReceptionInputMap ρ round ledger feedback
  let expected := collectionExpectedMap ρ round
  let row := fun ω => (round ω).row
  let time := fun ω => (round ω).time
  let bank := fun ω => (round ω).state.upDecoderBank
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row.comp hround
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hbank := (ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank).comp
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hround)
  have hinput : Measurable input :=
    measurable_collectionReceptionInputMap round ledger feedback hround hledger hfeedback
  have hexpected : Measurable expected := measurable_collectionExpectedMap round hround
  have hraw := ReferenceUpReceptionMeasurability.measurable_rawDecoderOutputAtComponents
    ρ row time ledger bank feedback hrow htime hledger hbank hfeedback
  have hparsed := ReferenceUpReceptionMeasurability.measurable_rawParsedOutputAtComponents
    ρ row time ledger bank feedback hrow htime hledger hbank hfeedback
  have haccepted := ReferenceUpReceptionMeasurability.measurable_rawParsedLocalAcceptanceAtComponents
    ρ row time ledger bank feedback hrow htime hledger hbank hfeedback
  have hwrong := measurable_collectionWrongUniqueMap round ledger feedback
    hround hledger hfeedback
  have hafter : Measurable (fun ω =>
      (CoordinatorUpReception.decoderTransition (input ω)).1) :=
    (Measurable.of_discrete : Measurable
      (fun z : ReferenceUpReceptionMeasurability.ReceptionInput p ρ =>
        (CoordinatorUpReception.decoderTransition z).1)).comp hinput
  have hrawMatches : Measurable (fun ω =>
      decide ((CoordinatorUpReception.decoderTransition (input ω)).2 = expected ω)) := by
    let relation : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) ×
        Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) → Bool :=
      fun z => decide (z.1 = z.2)
    have hrelation : Measurable relation := Measurable.of_discrete
    exact hrelation.comp (hraw.prodMk hexpected)
  let read : Ω → CollectionUpDiagnosticRead p ρ := fun ω =>
    (input ω, (expected ω,
      ((CoordinatorUpReception.decoderTransition (input ω)).1,
        ((CoordinatorUpReception.decoderTransition (input ω)).2,
          (ReferenceUpReception.rawParsedOutput ρ (input ω),
            (ReferenceUpReception.rawParsedLocalAcceptance ρ (input ω),
              (decide ((CoordinatorUpReception.decoderTransition (input ω)).2 =
                expected ω), collectionWrongUniqueMap ρ round ledger feedback ω)))))))
  have hread : Measurable read :=
    hinput.prodMk (hexpected.prodMk (hafter.prodMk (hraw.prodMk
      (hparsed.prodMk (haccepted.prodMk (hrawMatches.prodMk hwrong))))))
  let pack : CollectionUpDiagnosticRead p ρ → Option (UpDiagnosticCode p ρ) :=
    packCollectionUpDiagnosticRead
  have hpack : Measurable pack := Measurable.of_discrete
  have hEq : (fun ω => (collectionUpDiagnosticMap ρ round ledger feedback ω).map
      encodeUpDiagnostic) = fun ω => pack (read ω) := by
    funext ω
    change (if CoordinatorUpReception.receptionInputCheck (input ω) = true then
      some _ else none).map encodeUpDiagnostic = pack (read ω)
    dsimp only [pack, packCollectionUpDiagnosticRead, read]
    split <;> rfl
  rw [hEq]
  exact hpack.comp hread

/-- The literal post-recorder continuation. Only the first recorder call of
`collectionPostChoice` is replaced by the primitive `recording`. The same
original round supplies PREPARE, bank, row and time. No successful-domain,
current-word, reachability or chronology premise is imposed. -/
def collectionServiceTail (x : RoundInput p rate) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (started : StartRoundResult p)
    (recording : Option (CoordinatorRecordingOperation.Output p))
    (observation : Fin (D p + 1)) : CoordinatorObservation p rate :=
  match recording with
  | none => coordinatorFailure x.state.upDecoderBank (.collection .recorderDomain) none none
  | some output =>
      match CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (collectionEnabled ledger x.time) (InputsValid.rawInputOfRecorder output) with
      | .invalid | .rejected _ => coordinatorFailure x.state.upDecoderBank
          (.collection .ledgerStartDomain) (some output) none
      | .success ledgerStarted => collectionFinish (x := x) payload started output
          (collectionUpCutMap rate (fun _ : Unit => x) (fun _ => ledgerStarted)
            (fun _ => observation) ())

/-- Substituting the actual recorder call recovers the ENTIRE original
observation for every original prepared round, including every failure path. -/
theorem collectionServiceTail_eq_collectionPostChoice {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (started : StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionServiceTail x payload ledger started
        (CoordinatorRecorderComplementBridge.run
          (collectionRecordingInput prepared payload started weights))
        prepared.coordinatorObservation =
      collectionPostChoice prepared payload ledger started weights := by
  unfold collectionServiceTail collectionPostChoice
  cases hr : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared payload started weights) with
  | none => rfl
  | some output =>
      cases hs : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (collectionEnabled ledger x.time) (InputsValid.rawInputOfRecorder output) with
      | invalid => simp only [hs]
      | rejected returned => simp only [hs]
      | success returned =>
          simp only [hs]
          rw [collectionUpCutMap_reconstruct prepared returned
            prepared.coordinatorObservation rfl]

abbrev CheckedLedger (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorCollectionLedger.Checked (ReferenceActivePhysicalStep.Ledger rate)
abbrev UpResult (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorCollectionLedger.Checked
    (ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
abbrev ClockResult (p : Parameters) :=
  Except CoordinatorPhaseClock.ClockFailure (CoordinatorPhaseClock.FinishRoundResult p)

instance checkedLedgerMeasurableSpace : MeasurableSpace (CheckedLedger rate) := ⊤

/-- Literal start result. The primitive option is retained separately, so
recorder failure and ledger-start failure are never identified in the output. -/
def serviceStart (ledger : ReferenceActivePhysicalStep.Ledger rate) (time : Fin p.T)
    (recording : Option (CoordinatorRecordingOperation.Output p)) : CheckedLedger rate :=
  match recording with
  | none => .invalid
  | some output => CoordinatorCollectionLedger.startRound ledger (time.val + 1)
      (collectionEnabled ledger time) (InputsValid.rawInputOfRecorder output)

/-- A total local read for the receiver; the fallback is never consumed by
an output branch unless `serviceStart` succeeded. -/
def serviceReceptionLedger (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    CheckedLedger rate → ReferenceActivePhysicalStep.Ledger rate
  | .success returned => returned
  | _ => ledger

/-- Ordinary rejection still reaches ledger finish with its returned bank.
Invalid reception does not reach finish in the continuation. -/
def serviceFinishLedger : UpResult rate → CheckedLedger rate
  | .invalid => .invalid
  | .success (ledger, _) | .rejected (ledger, _) =>
      CoordinatorCollectionLedger.finishRound ledger

def serviceFinishPending : CheckedLedger rate → Finset (Fin (p.m - 1))
  | .success ledger => ledger.pending
  | _ => ∅

/-- A transient product of actual local stage results. The original bank,
recorder option, checked tags, full diagnostic and clock result are retained.
It is not a second state, transition, or prescribed successful trace. -/
abbrev ServiceRead (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorUpReception.UpDecoderBank p ×
    (Option (CoordinatorRecordingOperation.Output p) ×
      (CheckedLedger rate × (UpResult rate ×
        (Option (UpDiagnosticCode p rate) × (CheckedLedger rate × ClockResult p)))))

/-- Read the existing operations in source order. Total reads for unused
branches have no effects; `serviceObservation` consumes only the actual branch. -/
def serviceRead (x : RoundInput p rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : StartRoundResult p) (recording : Option (CoordinatorRecordingOperation.Output p))
    (observation : Fin (D p + 1)) : ServiceRead p rate :=
  let start := serviceStart ledger x.time recording
  let cut := collectionUpCutMap rate (fun _ : Unit => x)
    (fun _ => serviceReceptionLedger ledger start) (fun _ => observation) ()
  let finished := serviceFinishLedger cut.result
  (x.state.upDecoderBank, recording, start, cut.result,
    cut.diagnostic.map encodeUpDiagnostic, finished,
    CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      (serviceFinishPending finished) x.row)

/-- Reconstruct solely from retained data; no decoder reruns any continuation.
Invalid reception keeps the old bank; every later failure keeps the returned
bank and all diagnostic fields. The successful configuration uses the exact
ledger and `lastProposal` returned by the two finish calls. -/
def serviceObservation (payload : Payload rate) (read : ServiceRead p rate) :
    CoordinatorObservation p rate :=
  let oldBank := read.1
  let diagnostic := read.2.2.2.2.1.map decodeUpDiagnostic
  match read.2.1 with
  | none => coordinatorFailure oldBank (.collection .recorderDomain) none none
  | some recording =>
      match read.2.2.1 with
      | .invalid | .rejected _ => coordinatorFailure oldBank
          (.collection .ledgerStartDomain) (some recording) none
      | .success _ =>
          let finish := fun bank =>
            match read.2.2.2.2.2.1 with
            | .invalid | .rejected _ => coordinatorFailure bank
                (.collection .ledgerFinishDomain) (some recording) diagnostic
            | .success ledger =>
                match read.2.2.2.2.2.2 with
                | .error reason => coordinatorFailure bank (.collection (.clockFinish reason))
                    (some recording) diagnostic
                | .ok clock => ⟨.collection payload ledger clock.clock.lastProposal,
                    bank, none, some recording, diagnostic⟩
          match read.2.2.2.1 with
          | .invalid => coordinatorFailure oldBank (.collection .upReceptionDomain)
              (some recording) diagnostic
          | .success (_, bank) | .rejected (_, bank) => finish bank

private theorem diagnostic_map_decode_encode (diagnostic : Option (UpDiagnostic p rate)) :
    (diagnostic.map encodeUpDiagnostic).map decodeUpDiagnostic = diagnostic := by
  cases diagnostic with
  | none => rfl
  | some value => exact congrArg some (decodeUpDiagnostic_encodeUpDiagnostic value)

/-- Exact factorization, with all original primitive arguments free. -/
theorem collectionServiceTail_eq_serviceObservation (x : RoundInput p rate)
    (payload : Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : StartRoundResult p) (recording : Option (CoordinatorRecordingOperation.Output p))
    (observation : Fin (D p + 1)) :
    collectionServiceTail x payload ledger started recording observation =
      serviceObservation payload (serviceRead x ledger started recording observation) := by
  cases recording with
  | none => rfl
  | some output =>
      cases hs : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (collectionEnabled ledger x.time) (InputsValid.rawInputOfRecorder output) with
      | invalid => simp only [collectionServiceTail, serviceRead, serviceStart, hs,
          serviceObservation]
      | rejected returned => simp only [collectionServiceTail, serviceRead, serviceStart, hs,
          serviceObservation]
      | success returned =>
          simp only [collectionServiceTail, serviceRead, serviceStart, hs,
            serviceReceptionLedger, serviceObservation, collectionFinish,
            diagnostic_map_decode_encode]
          cases hc : (collectionUpCutMap rate (fun _ : Unit => x) (fun _ => returned)
              (fun _ => observation) ()).result with
          | invalid => rfl
          | success pair | rejected pair =>
              rcases pair with ⟨received, bank⟩
              cases hf : CoordinatorCollectionLedger.finishRound received with
              | invalid => simp only [serviceFinishLedger, hf]
              | rejected returned => simp only [serviceFinishLedger, hf]
              | success finished =>
                  simp only [serviceFinishLedger, hf, serviceFinishPending]
                  rfl

/-- For each discrete read the sole varying output coordinate is the actual
preserved payload, embedded in the canonical coordinator code. -/
theorem measurable_serviceObservationCode : Measurable (fun z : Payload rate × ServiceRead p rate =>
    encodeCollectionObservation (serviceObservation z.1 z.2)) := by
  apply measurable_from_prod_countable_left
  rintro ⟨oldBank, recording, start, received, diagnostic, finished, clock⟩
  cases recording with
  | none =>
      simp only [serviceObservation]
      exact measurable_const
  | some output =>
      cases start with
      | invalid =>
          simp only [serviceObservation]
          exact measurable_const
      | rejected ledger =>
          simp only [serviceObservation]
          exact measurable_const
      | success ledger =>
          have hfinish : ∀ bank, Measurable (fun payload : Payload rate =>
              encodeCollectionObservation
                (match finished with
                | .invalid | .rejected _ => coordinatorFailure bank
                    (.collection .ledgerFinishDomain) (some output) (diagnostic.map decodeUpDiagnostic)
                | .success ledger => match clock with
                    | .error reason => coordinatorFailure bank (.collection (.clockFinish reason))
                        (some output) (diagnostic.map decodeUpDiagnostic)
                    | .ok clock => ⟨.collection payload ledger clock.clock.lastProposal,
                        bank, none, some output, diagnostic.map decodeUpDiagnostic⟩)) := by
            intro bank
            cases finished with
            | invalid =>
                dsimp only
                exact measurable_const
            | rejected ledger =>
                dsimp only
                exact measurable_const
            | success ledger =>
                cases clock with
                | error reason =>
                    dsimp only
                    exact measurable_const
                | ok clock =>
                    change Measurable (fun payload : Payload rate =>
                      (Sum.inr (Sum.inr (Sum.inl (payload, (ledger, clock.clock.lastProposal)))),
                        (bank, none, some output,
                          (diagnostic.map decodeUpDiagnostic).map encodeUpDiagnostic)))
                    exact (measurable_inr.comp (measurable_inr.comp (measurable_inl.comp
                      (measurable_id.prodMk measurable_const)))).prodMk measurable_const
          cases received with
          | invalid =>
              simp only [serviceObservation]
              exact measurable_const
          | success pair | rejected pair =>
              rcases pair with ⟨receivedLedger, bank⟩
              cases finished <;> simpa only [serviceObservation] using hfinish bank

/-- Every discrete stage is Borel by composition from its REAL inputs.
Countability is used only for functions whose DOMAIN is discrete. -/
theorem measurable_serviceRead_comp {Ω : Type*} [MeasurableSpace Ω]
    (round : Ω → RoundInput p rate) (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (started : Ω → StartRoundResult p) (recording : Ω → Option (CoordinatorRecordingOperation.Output p))
    (observation : Ω → Fin (D p + 1)) (hround : Measurable round)
    (hledger : Measurable ledger) (hstarted : Measurable started)
    (hrecording : Measurable recording) (hobs : Measurable observation) :
    Measurable (fun ω => serviceRead (round ω) (ledger ω) (started ω)
      (recording ω) (observation ω)) := by
  let start := fun ω => serviceStart (ledger ω) (round ω).time (recording ω)
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hround
  have hbank := ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank.comp
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hround)
  have hstart : Measurable start :=
    (Measurable.of_discrete : Measurable (fun z : ReferenceActivePhysicalStep.Ledger rate ×
      (Fin p.T × Option (CoordinatorRecordingOperation.Output p)) =>
        serviceStart z.1 z.2.1 z.2.2)).comp
      (hledger.prodMk (htime.prodMk hrecording))
  let receptionLedger := fun ω => serviceReceptionLedger (ledger ω) (start ω)
  have hreceptionLedger : Measurable receptionLedger :=
    (Measurable.of_discrete : Measurable (fun z : ReferenceActivePhysicalStep.Ledger rate ×
      CheckedLedger rate => serviceReceptionLedger z.1 z.2)).comp (hledger.prodMk hstart)
  have hreceived := measurable_collectionReceiveUpMap round receptionLedger observation
    hround hreceptionLedger hobs
  have hdiagnostic := measurable_collectionUpDiagnosticCodeMap round receptionLedger observation
    hround hreceptionLedger hobs
  have hfinished := (Measurable.of_discrete : Measurable
    (serviceFinishLedger (rate := rate))).comp hreceived
  have hpending := (Measurable.of_discrete : Measurable
    (serviceFinishPending (rate := rate))).comp hfinished
  have hclock := measurable_collectionPhaseClockFinish round started
    (fun ω => serviceFinishPending (serviceFinishLedger
      (collectionReceiveUpMap rate round receptionLedger observation ω)))
    hround hstarted hpending
  exact hbank.prodMk (hrecording.prodMk (hstart.prodMk (hreceived.prodMk
    (hdiagnostic.prodMk (hfinished.prodMk hclock)))))

/-- Complete direct joint Borel code: original canonical round input,
payload, moving ledger, retained start result, primitive recording option,
and own grid observation ALL vary. No target-measurability premise. -/
abbrev ServiceInputs (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  RoundInput p rate × (Payload rate × (ReferenceActivePhysicalStep.Ledger rate ×
    (StartRoundResult p × (Option (CoordinatorRecordingOperation.Output p) × Fin (D p + 1)))))

def collectionServiceTailCode (z : ServiceInputs p rate) : CollectionTailCode p rate :=
  encodeCollectionObservation
    (collectionServiceTail z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2)

/-- Arbitrary measurable substitution into the complete literal continuation. -/
theorem measurable_collectionServiceTailCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate) (started : Ω → StartRoundResult p)
    (recording : Ω → Option (CoordinatorRecordingOperation.Output p))
    (observation : Ω → Fin (D p + 1))
    (hround : Measurable round) (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hstarted : Measurable started) (hrecording : Measurable recording) (hobs : Measurable observation) :
    Measurable (fun ω => encodeCollectionObservation (collectionServiceTail
      (round ω) (payload ω) (ledger ω) (started ω) (recording ω) (observation ω))) := by
  simp_rw [collectionServiceTail_eq_serviceObservation]
  exact measurable_serviceObservationCode.comp (hpayload.prodMk
    (measurable_serviceRead_comp round ledger started recording observation
      hround hledger hstarted hrecording hobs))

theorem measurable_collectionServiceTailCode :
    Measurable (collectionServiceTailCode (p := p) (rate := rate)) :=
  measurable_collectionServiceTailCode_comp (fun z : ServiceInputs p rate => z.1) (fun z => z.2.1)
    (fun z => z.2.2.1) (fun z => z.2.2.2.1) (fun z => z.2.2.2.2.1) (fun z => z.2.2.2.2.2)
    measurable_fst (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))))
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))))

/-- Lossless output reconstruction uses retained canonical and diagnostic data. -/
theorem collectionServiceTailCode_reconstruct (z : ServiceInputs p rate) :
    decodeCollectionObservation (collectionServiceTailCode z) =
      collectionServiceTail z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2 :=
  decodeCollectionObservation_encodeCollectionObservation _

/-- The returned bank is a measurable field of the complete lossless code. -/
theorem measurable_collectionServiceTailBank : Measurable (fun z : ServiceInputs p rate =>
    (collectionServiceTailCode z).2.1) :=
  measurable_fst.comp (measurable_snd.comp measurable_collectionServiceTailCode)

/-- Every original failure tag is retained and measurable. -/
theorem measurable_collectionServiceTailFailure : Measurable (fun z : ServiceInputs p rate =>
    (collectionServiceTailCode z).2.2.1) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_collectionServiceTailCode))

/-- Recorder failure versus the full successful recorder output is retained. -/
theorem measurable_collectionServiceTailRecording : Measurable (fun z : ServiceInputs p rate =>
    (collectionServiceTailCode z).2.2.2.1) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_collectionServiceTailCode)))

/-- All eight diagnostic fields, including invalid-input absence, are Borel. -/
theorem measurable_collectionServiceTailDiagnostic : Measurable (fun z : ServiceInputs p rate =>
    (collectionServiceTailCode z).2.2.2.2) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_collectionServiceTailCode)))

/-- Exact entire output code after substituting the actual recorder, with no
recorder-measurability or physical-identity assumption. A later composer must
supply the independently checked joint recorder and physical input producers. -/
theorem collectionServiceTailCode_eq_encodeCollectionPostChoice {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (started : StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionServiceTailCode
        (x, payload, ledger, started, CoordinatorRecorderComplementBridge.run
          (collectionRecordingInput prepared payload started weights), prepared.coordinatorObservation) =
      encodeCollectionObservation (collectionPostChoice prepared payload ledger started weights) :=
  congrArg encodeCollectionObservation
    (collectionServiceTail_eq_collectionPostChoice prepared payload ledger started weights)

end Bandits.Support.ReferenceCollectionServiceTailMeasurability
