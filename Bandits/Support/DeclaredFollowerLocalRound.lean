/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerLifecycle
public import Bandits.Support.ActiveFollowerArmChoice
public import Bandits.Support.ActiveFollowerQueueOperation
public import Bandits.Support.ActiveFollowerLogging
public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ReferencePrelaunchFollower

/-!
# One actual local round for a declared follower

This module composes the accepted local operations on one follower's own
declared row. Its operation order follows
`sources/zip4/manuscript/06_interruptions.tex:108-177,192-209,239-297`,
`sources/zip4/manuscript/07_public_setup.tex:52-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The continuation carries the state after `startRound`, which is the actual
choice-time snapshot. It also carries the selected arm, row, activation time,
calendar coordinate, and rate; observation cannot replace any of those values
or supply a post-service snapshot. This is a local-input construction only:
it proves no physical feedback provenance, message authenticity, shared-row
property, probability law, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.DeclaredFollowerLocalRound

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.AffineChannelLaw
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.ActiveFollowerDownAcceptance

/-- The active fallback arm for source player `i.val + 1`: its `Fin` coordinate is
`i.val + 1`, so its one-based source arm label is `i.val + 2`. -/
def fallbackArm (p : Parameters) (i : Fin (p.m - 1)) : Fin p.K :=
  ⟨i.val + 1, by have hi := i.isLt; have hm := p.m_lt_K; omega⟩

/-- The local ordinary registers and proposal memory, or the absorbing local
dagger tag. Dagger carries no mutable learning or transport state. -/
inductive LocalConfiguration (p : Parameters) (rate : RateInput p) where
  | ordinary (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
  | dagger

/-- The one-round continuation returned by arm preparation. An `ordinary`
configuration is exactly the snapshot after the beginning-of-round lifecycle
operation and before arm choice. -/
structure PreparedRound (p : Parameters) (rate : RateInput p) where
  follower : Fin (p.m - 1)
  row : CompletePublicTable.CompleteRow p
  activation : ReferencePrelaunchFollower.Activation p
  time : Fin p.T
  active : activation.val ≤ time.val + 1
  arm : Fin p.K
  configuration : LocalConfiguration p rate

/-- Local failure stages are kept visible for later first-failure equations.
Decoder rejection and parsed-but-unaccepted results are ordinary outcomes,
not failure constructors. -/
inductive RoundFailure where
  | logging (reason : ActiveFollowerLogging.LoggingFailure)
  | service
  | downInput (reason : ActiveFollowerDownAcceptance.InputFailure)
  | downOutput (reason : ActiveFollowerDownAcceptance.OutputFailure)
  | release (reason : ActiveFollowerLifecycle.LifecycleFailure)
  | finish (reason : ActiveFollowerLifecycle.LifecycleFailure)

/-- An observed round retains the prepared arm verbatim and returns only this
follower's next local configuration. -/
structure ObservedRound (p : Parameters) (rate : RateInput p) where
  arm : Fin p.K
  configuration : LocalConfiguration p rate

/-- Convert the result of the actual DOWN transition into its next state.
Rejected and parsed-but-unaccepted words keep the decoder's returned batch;
accepted words install the exact state returned by recovery. -/
def consumeDownResult {p : Parameters} (rate : RateInput p)
    (result : ActiveFollowerDownAcceptance.LocalDownResult p rate) :
    Except RoundFailure (ReferencePrelaunchFollower.State p rate.eta) :=
  match result with
  | .skipped before _ => .ok before
  | .inputFailure _ reason => .error (.downInput reason)
  | .decodeOrParseRejected _ after _ => .ok after
  | .parsedButUnaccepted _ after _ _ => .ok after
  | .outputFailure _ reason => .error (.downOutput reason)
  | .accepted _ after _ _ _ _ _ => .ok after

/-- Run the first observation-side local operation. Unoccupied-at-choice
followers log first and then run the actual DOWN transition on that logged
state. Occupied-at-choice followers instead run enabled service on the exact
choice snapshot, including a zero-arrival transition. No coordinator launch
state is an input. -/
def recordOrServiceThenDown {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (_hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta) :
    Except RoundFailure (ReferencePrelaunchFollower.State p rate.eta) := by
  classical
  if hunoccupied : choiceState.status = .unoccupied then
    match ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
        choiceState with
    | .error reason => exact .error (.logging reason)
    | .ok logged =>
        exact consumeDownResult rate
          (ActiveFollowerDownAcceptance.downTransition p i row t observation rate logged)
  else
    match ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale i row activation t observation choiceState with
    | .failure => exact .error .service
    | .success result => exact .ok result.output

/-- Release from the saved choice snapshot, then perform the final proposal
read from this same declared row. The lifecycle operation itself checks only
the pre-choice pending state for release eligibility. -/
def releaseAndFinish {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (postServiceOrDown : ReferencePrelaunchFollower.State p rate.eta) :
    Except RoundFailure
      (ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p) :=
  match ActiveFollowerLifecycle.releaseAfterService rate.eta
      i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation
      choiceState postServiceOrDown with
  | .error reason => .error (.release reason)
  | .ok afterRelease =>
      match ActiveFollowerLifecycle.finishRound rate.eta t row afterRelease memory with
      | .error reason => .error (.finish reason)
      | .ok result => .ok result

/-- The complete ordinary observation continuation. Every helper receives the
carried row and choice snapshot; failures stop the composition at their first
stage. -/
def observeOrdinary {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) :
    Except RoundFailure
      (ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p) := by
  match recordOrServiceThenDown rate i row activation t hactive arm observation choiceState with
  | .error reason => exact .error reason
  | .ok postServiceOrDown =>
      exact releaseAndFinish rate i row t observation choiceState memory postServiceOrDown

/-- Prepare this activated follower's arm. The caller supplies the checked
source-domain proof `activation ≤ t+1`, so inactive bootstrap remains the
caller's branch. `startRound` precedes UP-offer validation and arm choice. -/
def prepare {p : Parameters} (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (input : LocalConfiguration p rate) : PreparedRound p rate := by
  classical
  match input with
  | .dagger =>
      exact ⟨i, row, activation, t, hactive, fallbackArm p i, .dagger⟩
  | .ordinary state memory =>
      match ActiveFollowerLifecycle.startRound rate.eta t state memory with
      | .error _ =>
          exact ⟨i, row, activation, t, hactive, fallbackArm p i, .dagger⟩
      | .ok (choiceState, choiceMemory) =>
          match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
              choiceState with
          | .failure =>
              exact ⟨i, row, activation, t, hactive, fallbackArm p i, .dagger⟩
          | .noOffer =>
              match ActiveFollowerArmChoice.followerArmChoice choiceState row t i none with
              | none =>
                  exact ⟨i, row, activation, t, hactive, fallbackArm p i, .dagger⟩
              | some arm =>
                  exact ⟨i, row, activation, t, hactive, arm,
                    .ordinary choiceState choiceMemory⟩
          | .offer offered =>
              match ActiveFollowerArmChoice.followerArmChoice choiceState row t i
                  (some offered) with
              | none =>
                  exact ⟨i, row, activation, t, hactive, fallbackArm p i, .dagger⟩
              | some arm =>
                  exact ⟨i, row, activation, t, hactive, arm,
                    .ordinary choiceState choiceMemory⟩

/-- Observe only this player's typed quantized observation. A failure from the
ordinary local composition enters the absorbing local dagger immediately. -/
def observe {p : Parameters} {rate : RateInput p} (prepared : PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) : ObservedRound p rate := by
  classical
  match prepared.configuration with
  | .dagger => exact ⟨prepared.arm, .dagger⟩
  | .ordinary choiceState memory =>
      match observeOrdinary rate prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation
          choiceState memory with
      | .error _ => exact ⟨prepared.arm, .dagger⟩
      | .ok (state, nextMemory) =>
          exact ⟨prepared.arm, .ordinary state nextMemory⟩

/-- The fallback arm's source label is the mapped source player's label plus
one, equivalently the follower index plus two. -/
theorem fallbackArm_source_label (p : Parameters) (i : Fin (p.m - 1)) :
    (fallbackArm p i).val + 1 =
        (PublicDiscreteDraws.followerPlayer p.two_le_m i).val + 1 ∧
      (fallbackArm p i).val + 1 = i.val + 2 := by
  constructor
  · rfl
  · simp only [fallbackArm, Fin.val_mk]

/-- The first follower is source player 1 and falls back to source arm 2. -/
theorem fallbackArm_first_follower_source_label (p : Parameters) :
    (fallbackArm p ⟨0, by have hm := p.two_le_m; omega⟩).val + 1 = 2 := rfl

/-- The beginning-of-round operation preserves the reference-only marker in
the actual choice snapshot whenever it succeeds. -/
theorem startRound_initializationMarker {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory =
      .ok (choiceState, choiceMemory)) :
    choiceState.initializationFailure = state.initializationFailure := by
  rcases ActiveFollowerLifecycle.startRound_frame rate.eta t state choiceState memory
      choiceMemory hstart with ⟨_, _, _, _, _, _, hmarker, _⟩
  exact hmarker

/-- A carried dagger prepares the fallback arm and remains dagger. -/
theorem prepare_dagger {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) :
    (prepare rate i row activation t hactive .dagger).arm = fallbackArm p i ∧
      (prepare rate i row activation t hactive .dagger).configuration =
      LocalConfiguration.dagger := by
  simp [prepare]

/-- A failed beginning-of-round lifecycle check returns the real fallback arm
before any offer or arm-choice operation is evaluated. -/
theorem prepare_start_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (reason : LifecycleFailure)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory = .error reason) :
    (prepare rate i row activation t hactive (.ordinary state memory)).arm = fallbackArm p i ∧
      (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
        LocalConfiguration.dagger := by
  dsimp only [prepare]
  rw [hstart]
  simp only
  constructor <;> trivial

/-- A failed checked UP offer stops before follower arm choice and returns the
prescribed fallback action. -/
theorem prepare_offer_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
      choiceState = .failure) :
    (prepare rate i row activation t hactive (.ordinary state memory)).arm = fallbackArm p i ∧
      (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
        LocalConfiguration.dagger := by
  dsimp only [prepare]
  rw [hstart]
  simp only
  rw [hoff]
  simp only
  constructor <;> trivial

/-- A local arm-choice rejection enters dagger and emits the source fallback
arm; successful arm choice carries the actual post-start snapshot forward. -/
theorem prepare_no_offer_arm_equation {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
      choiceState = .noOffer) :
    (ActiveFollowerArmChoice.followerArmChoice choiceState row t i none = none →
      (prepare rate i row activation t hactive (.ordinary state memory)).arm = fallbackArm p i ∧
        (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
          LocalConfiguration.dagger) ∧
    (∀ arm, ActiveFollowerArmChoice.followerArmChoice choiceState row t i none = some arm →
      (prepare rate i row activation t hactive (.ordinary state memory)).arm = arm ∧
        (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
          LocalConfiguration.ordinary choiceState choiceMemory) := by
  constructor
  · intro hchoice
    dsimp only [prepare]
    rw [hstart]
    simp only
    rw [hoff]
    simp only
    simp only [hchoice]
    constructor <;> trivial
  · intro arm hchoice
    dsimp only [prepare]
    rw [hstart]
    simp only
    rw [hoff]
    simp only
    simp only [hchoice]
    constructor <;> trivial

/-- A locally checked UP offer is passed unchanged to arm choice. Rejection
uses the fallback arm; success keeps the actual choice-time snapshot. -/
theorem prepare_offer_arm_equation {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory =
      .ok (choiceState, choiceMemory))
    (offered : UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
      choiceState = .offer offered) :
    (ActiveFollowerArmChoice.followerArmChoice choiceState row t i (some offered) = none →
      (prepare rate i row activation t hactive (.ordinary state memory)).arm = fallbackArm p i ∧
        (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
          LocalConfiguration.dagger) ∧
    (∀ arm, ActiveFollowerArmChoice.followerArmChoice choiceState row t i
        (some offered) = some arm →
      (prepare rate i row activation t hactive (.ordinary state memory)).arm = arm ∧
        (prepare rate i row activation t hactive (.ordinary state memory)).configuration =
          LocalConfiguration.ordinary choiceState choiceMemory) := by
  constructor
  · intro hchoice
    dsimp only [prepare]
    rw [hstart]
    simp only
    rw [hoff]
    simp only
    simp only [hchoice]
    constructor <;> trivial
  · intro arm hchoice
    dsimp only [prepare]
    rw [hstart]
    simp only
    rw [hoff]
    simp only
    simp only [hchoice]
    constructor <;> trivial

/-- Exact local failure routing for returned DOWN results. -/
theorem consumeDownResult_rejected {p : Parameters} (rate : RateInput p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :
    consumeDownResult rate (.decodeOrParseRejected before after raw) = .ok after := rfl

theorem consumeDownResult_unaccepted {p : Parameters} (rate : RateInput p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    consumeDownResult rate (.parsedButUnaccepted before after raw reply) = .ok after := rfl

theorem consumeDownResult_accepted {p : Parameters} (rate : RateInput p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ) :
    consumeDownResult rate
      (.accepted before after raw reply scan registers lastService) = .ok after := rfl

theorem consumeDownResult_inputFailure {p : Parameters} (rate : RateInput p)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (reason : ActiveFollowerDownAcceptance.InputFailure) :
    consumeDownResult rate (.inputFailure before reason) = .error (.downInput reason) := rfl

theorem consumeDownResult_outputFailure {p : Parameters} (rate : RateInput p)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (reason : ActiveFollowerDownAcceptance.OutputFailure) :
    consumeDownResult rate (.outputFailure before reason) = .error (.downOutput reason) := rfl

/-- Successful checked logging preserves the separate reference-only failure
marker carried in `ReferencePrelaunchFollower.State`. -/
theorem checkedLogging_initializationMarker {p : Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state after : ReferencePrelaunchFollower.State p eta)
    (h : ActiveFollowerLogging.checkedLogging i row activation t own state = .ok after) :
    after.initializationFailure = state.initializationFailure := by
  rcases ActiveFollowerLogging.checkedLogging_success_frame i row activation t own state after h
    with ⟨_, _, _, _, _, _, hmarker⟩
  exact hmarker

/-- A successful actual occupied service result preserves the inert carried
initialization marker, including on a zero-arrival service round. -/
theorem serviceSuccess_initializationMarker {p : Parameters} {eta : LearningRate}
    {n : ℕ} {i : Fin (p.m - 1)} {row : CompletePublicTable.CompleteRow p}
    {activation : ReferencePrelaunchFollower.Activation p} {t : Fin p.T}
    {observation : ReferencePrelaunchFollower.Observation p}
    {state : ReferencePrelaunchFollower.State p eta}
    (result : ActiveFollowerQueueOperation.ServiceSuccess p eta n i row activation t
      observation state) :
    result.output.initializationFailure = state.initializationFailure := by
  rw [result.queueUpdate]
  rcases ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers n state
      result.arrival with ⟨_, _, _, _, hmarker⟩
  exact hmarker

/-- Rejected decoder output preserves the reference-only marker while keeping
the actual decoder result in the returned state. The hypotheses are precisely
the checked input domains and local parse rejection used by the accepted DOWN
operation. -/
theorem downTransition_rejected_initializationMarker {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (feedback : ReferencePrelaunchFollower.Observation p) (rate : RateInput p)
    (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer)
    (hparsed : ActiveFollowerDownAcceptance.parsedCurrentOutput p i row t feedback rate state =
      none)
    (hresult : ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state =
      .decodeOrParseRejected state after raw) :
    after.initializationFailure = state.initializationFailure := by
  have heq := ActiveFollowerDownAcceptance.downTransition_rejected_equation p i row t feedback
    rate state hselected hstatus hregisters hbatch hbuffer hparsed
  rw [heq] at hresult
  injection hresult with _ hafter _
  rw [← hafter]

/-- A parsed-but-unaccepted DOWN reply likewise retains the actual advanced
decoder bank and leaves the reference-only marker unchanged. -/
theorem downTransition_unaccepted_initializationMarker {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (feedback : ReferencePrelaunchFollower.Observation p) (rate : RateInput p)
    (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer)
    (hparsed : ActiveFollowerDownAcceptance.parsedCurrentOutput p i row t feedback rate state =
      some reply)
    (hnotaccepted : ¬ OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) reply)
    (hresult : ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state =
      .parsedButUnaccepted state after raw reply) :
    after.initializationFailure = state.initializationFailure := by
  have heq := ActiveFollowerDownAcceptance.downTransition_unaccepted_equation p i row t feedback
    rate state hselected hstatus hregisters hbatch hbuffer reply hparsed hnotaccepted
  rw [heq] at hresult
  injection hresult with _ hafter _ _
  rw [← hafter]

/-- An accepted DOWN result installs the exact recovered state and preserves
the inert initialization marker. No sent-word or authenticity premise occurs. -/
theorem downTransition_accepted_initializationMarker {p : Parameters}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (feedback : ReferencePrelaunchFollower.Observation p) (rate : RateInput p)
    (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hresult : ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state =
      .accepted state after raw reply scan registers lastService) :
    after.initializationFailure = state.initializationFailure := by
  rcases ActiveFollowerDownAcceptance.downTransition_accepted_checked p i row t feedback rate
      state after raw reply scan registers lastService hresult with
    ⟨_, _, _, _, _, _, hafter⟩
  rw [hafter]

/-- The actual unoccupied chronology is checked logging, then DOWN on the
returned logged state. -/
theorem recordOrServiceThenDown_unoccupied {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (h : choiceState.status = .unoccupied) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      match ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
          choiceState with
      | .error reason => .error (.logging reason)
      | .ok logged => consumeDownResult rate
          (ActiveFollowerDownAcceptance.downTransition p i row t observation rate logged) := by
  simp [recordOrServiceThenDown, h]

/-- The occupied-at-choice chronology services the same carried snapshot; the
successful checked result, including zero-arrival service, is consumed. -/
theorem recordOrServiceThenDown_occupied {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (h : choiceState.status ≠ .unoccupied) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      match ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
          rate.n rate.n_scale i row activation t observation choiceState with
      | .failure => .error .service
      | .success result => .ok result.output := by
  simp [recordOrServiceThenDown, h]

/-- The first logging, service, DOWN-domain, or DOWN-output failure is
returned unchanged by the later lifecycle stages. -/
theorem observeOrdinary_first_stage_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (reason : RoundFailure)
    (hfirst : recordOrServiceThenDown rate i row activation t hactive arm observation
      choiceState = .error reason) :
    observeOrdinary rate i row activation t hactive arm observation choiceState memory =
      .error reason := by
  simp [observeOrdinary, hfirst]

/-- A failed lifecycle release is the first later failure and prevents the
proposal-bit read. -/
theorem observeOrdinary_release_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState post : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hpost : recordOrServiceThenDown rate i row activation t hactive arm observation
      choiceState = .ok post)
    (reason : LifecycleFailure)
    (hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post =
        .error reason) :
    observeOrdinary rate i row activation t hactive arm observation choiceState memory =
      .error (.release reason) := by
  simp [observeOrdinary, hpost, releaseAndFinish, hrelease]

/-- A failed final lifecycle read is routed to dagger after a successful
release, with the exact finish reason preserved. -/
theorem observeOrdinary_finish_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState post released : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hpost : recordOrServiceThenDown rate i row activation t hactive arm observation
      choiceState = .ok post)
    (hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post =
        .ok released)
    (reason : LifecycleFailure)
    (hfinish : ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
      .error reason) :
    observeOrdinary rate i row activation t hactive arm observation choiceState memory =
      .error (.finish reason) := by
  simp [observeOrdinary, hpost, releaseAndFinish, hrelease, hfinish]

/-- If logging fails, no DOWN decode, service, release, or proposal read is
performed; the exact logging reason is the first failure. -/
theorem recordOrServiceThenDown_logging_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : choiceState.status = .unoccupied)
    (reason : ActiveFollowerLogging.LoggingFailure)
    (hlog : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
      choiceState = .error reason) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      .error (.logging reason) := by
  rw [recordOrServiceThenDown_unoccupied rate i row activation t hactive arm observation
    choiceState hstatus, hlog]

/-- A checked occupied-service failure is the first observation-side failure. -/
theorem recordOrServiceThenDown_service_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : choiceState.status ≠ .unoccupied)
    (hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i row activation t observation choiceState = .failure) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      .error .service := by
  rw [recordOrServiceThenDown_occupied rate i row activation t hactive arm observation
    choiceState hstatus]
  simp [hservice]

/-- An input-domain rejection from the actual DOWN operation enters the local
dagger route after successful unoccupied logging. -/
theorem recordOrServiceThenDown_down_input_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : choiceState.status = .unoccupied)
    (hlog : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
      choiceState = .ok logged)
    (reason : ActiveFollowerDownAcceptance.InputFailure)
    (hdown : ActiveFollowerDownAcceptance.downTransition p i row t observation rate logged =
      .inputFailure logged reason) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      .error (.downInput reason) := by
  rw [recordOrServiceThenDown_unoccupied rate i row activation t hactive arm observation
    choiceState hstatus]
  simp only [hlog]
  rw [hdown]
  rfl

/-- An output-domain rejection from the actual DOWN operation enters local
dagger after the real decoder/recovery attempt has been computed. -/
theorem recordOrServiceThenDown_down_output_failure {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : choiceState.status = .unoccupied)
    (hlog : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
      choiceState = .ok logged)
    (reason : ActiveFollowerDownAcceptance.OutputFailure)
    (hdown : ActiveFollowerDownAcceptance.downTransition p i row t observation rate logged =
      .outputFailure logged reason) :
    recordOrServiceThenDown rate i row activation t hactive arm observation choiceState =
      .error (.downOutput reason) := by
  rw [recordOrServiceThenDown_unoccupied rate i row activation t hactive arm observation
    choiceState hstatus]
  simp only [hlog]
  rw [hdown]
  rfl

/-- A parsed-but-unaccepted DOWN reply consumes the returned advanced decoder
bank and does not enter dagger. -/
theorem observeOrdinary_unaccepted_keeps_decoder_result {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState after : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstatus : choiceState.status = .unoccupied)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlog : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation)
      choiceState = .ok logged)
    (reply : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) )
    (hunaccepted : ActiveFollowerDownAcceptance.downTransition p i row t observation rate
      logged = .parsedButUnaccepted logged after raw reply)
    (hfinish : ActiveFollowerLifecycle.releaseAfterService rate.eta
      i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState after =
        .ok after)
    (hfinal : ActiveFollowerLifecycle.finishRound rate.eta t row after memory =
      .ok (after, memory)) :
    observeOrdinary rate i row activation t hactive arm observation choiceState memory =
      .ok (after, memory) := by
  simp [observeOrdinary, recordOrServiceThenDown_unoccupied rate i row activation t hactive arm
    observation choiceState hstatus, hlog, consumeDownResult, hunaccepted,
    releaseAndFinish, hfinish, hfinal]

/-- An unoccupied-at-choice follower cannot be released in the acceptance
round. If the DOWN operation returns a newly pending accepted state, the
later release stage is the lifecycle no-op on this saved choice snapshot. -/
theorem observeOrdinary_new_acceptance_not_released {p : Parameters}
    (rate : RateInput p) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState post : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : choiceState.status = .unoccupied)
    (hpost : recordOrServiceThenDown rate i row activation t hactive arm observation
      choiceState = .ok post)
    (hpending : post.status = .pending)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid post)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hrecord : post.lastDown = some M) (htime : M.val.sigma ≤ t.val + 1) :
    observeOrdinary rate i row activation t hactive arm observation choiceState memory =
      .ok (post, ⟨some ⟨t,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩⟩) := by
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta
    i t
    (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post hchoice
  have hfinish := ActiveFollowerLifecycle.finishRound_occupied_read rate.eta t row post memory
    (by simp [hpending]) hvalid M hrecord htime
  simp [observeOrdinary, releaseAndFinish, hpost, hrelease, hfinish]

/-- Once the ordinary observation pipeline fails, the public observer returns
local dagger while retaining the already selected arm. -/
theorem observe_ordinary_failure_is_dagger {p : Parameters} {rate : RateInput p}
    (prepared : PreparedRound p rate) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (reason : RoundFailure)
    (hlocal : prepared.configuration = LocalConfiguration.ordinary choiceState memory)
    (hfail : observeOrdinary rate prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation
      choiceState memory = .error reason) :
    (observe prepared observation).arm = prepared.arm ∧
      (observe prepared observation).configuration = LocalConfiguration.dagger := by
  unfold observe
  rw [hlocal]
  simp only
  rw [hfail]
  simp only
  constructor <;> trivial

/-- Dagger is absorbing under observation, and no learning, service, decoder,
release, or proposal-memory operation is evaluated. -/
theorem observe_dagger_absorbing {p : Parameters} {rate : RateInput p}
    (prepared : PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (h : prepared.configuration = LocalConfiguration.dagger) :
    (observe prepared observation).configuration = LocalConfiguration.dagger := by
  unfold observe
  rw [h]

/-- Observation never changes the arm chosen in the prepare phase. -/
theorem observe_arm_unchanged {p : Parameters} {rate : RateInput p}
    (prepared : PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    (observe prepared observation).arm = prepared.arm := by
  cases prepared with
  | mk follower row activation t active arm configuration =>
      cases configuration with
      | ordinary state memory =>
          dsimp only [observe]
          cases h : observeOrdinary rate follower row activation t active arm observation
              state memory <;> rfl
      | dagger => rfl

/-- The final proposal-token operation is exactly `finishRound` after release;
its input state is not supplied by the observer. -/
theorem releaseAndFinish_final_equation {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post released : ReferencePrelaunchFollower.State p rate.eta)
    (hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta
      i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post =
        .ok released) :
    releaseAndFinish rate i row t observation choiceState memory post =
      match ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | .error reason => .error (.finish reason)
      | .ok result => .ok result := by
  simp [releaseAndFinish, hrelease]

/-- If the final state is unoccupied, the exact prior proposal memory is
preserved and no current-row proposal coordinate is read. -/
theorem releaseAndFinish_unoccupied_memory {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post released : ReferencePrelaunchFollower.State p rate.eta)
    (hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta
      i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post =
        .ok released)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid released)
    (hunoccupied : released.status = .unoccupied) :
    releaseAndFinish rate i row t observation choiceState memory post =
      .ok (released, memory) := by
  rw [releaseAndFinish_final_equation rate i row t observation choiceState memory post released
    hrelease]
  rw [ActiveFollowerLifecycle.finishRound_unoccupied rate.eta t row released memory hvalid hunoccupied]

/-- If the final state is occupied, the adapter saves exactly this timestamped
own-row proposal bit; all local registers and partial batches remain intact. -/
theorem releaseAndFinish_occupied_token {p : Parameters} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post released : ReferencePrelaunchFollower.State p rate.eta)
    (hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta
      i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choiceState post =
        .ok released)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid released)
    (hoccupied : released.status ≠ .unoccupied)
    (M : DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hrecord : released.lastDown = some M) (htime : M.val.sigma ≤ t.val + 1) :
    releaseAndFinish rate i row t observation choiceState memory post =
      .ok (released, ⟨some ⟨t,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩⟩) := by
  rw [releaseAndFinish_final_equation rate i row t observation choiceState memory post released
    hrelease]
  rw [ActiveFollowerLifecycle.finishRound_occupied_read rate.eta t row released memory
    hoccupied hvalid M hrecord htime]

end Bandits.Support.DeclaredFollowerLocalRound

end
