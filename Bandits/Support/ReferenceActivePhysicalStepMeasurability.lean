/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceUpReceptionMeasurability
public import Bandits.Support.ReferenceDownCutJointMeasurability
public import Bandits.Support.DeclaredFollowerObservationMeasurability
public import Bandits.Support.CoordinatorRecordingMeasurability
public import Bandits.Support.CheckedAssignmentJointMeasurability
public import Bandits.Support.LaterAssignmentFullOutputMeasurability
public import Bandits.Support.CoordinatorCollectionRunMeasurabilityRepair

/-!
# Lossless measurable coordinates for the canonical active physical state

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,192-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-60`.

These coordinates encode the EXISTING `ReferenceActivePhysicalStep.State` and
time-valid `RoundInput`. Payload anchors keep their existing product Borel
structure. Follower buffers keep their original ordered skeleton and saved-real
fibers. No operation is used to define a measurable space. Only proof fields
are omitted, and decoding after encoding is proved on every original object.

This module does not yet prove measurability of dispatch or of the full step.
No initialization, temporal locality, provenance, horizon, probability law,
source theorem, or regret closure is asserted.

Direct-import identity evidence:
`private-audit-archive/turn-00113-dependency-evidence.json`
and `delta-verified-dependencies.json` in that same control directory.
The pinned-source check is `turn-00113-source-integrity.json`; fresh receiver
acceptance is recorded in `turn-00113-new-acceptance-evidence.json`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceActivePhysicalStepMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Literal discrete coordinates of a live phase. The three full natural
vectors extend the original complement coordinates by zero. Their restriction
recovers every stored score, queue and previous service. -/
structure LiveDiscrete (p : Parameters) where
  clockSigma : Option (Fin p.T)
  clockCutoff : Option (Fin p.T)
  clockBoundary : ℕ
  clockProposal : Option (Fin p.T × Bool)
  pending : Finset (Fin (p.m - 1))
  time : Fin p.T
  gridBoundary : ℕ
  scores : Fin p.K → ℕ
  queues : Fin p.K → ℕ
  previousServices : Fin p.K → ℕ
  baseScores : Fin (p.m - 1) → ℕ
  deriving Countable

instance liveDiscreteMeasurableSpace : MeasurableSpace (LiveDiscrete p) := ⊤
instance liveDiscreteDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (LiveDiscrete p) := ⟨fun _ => trivial⟩

/-- Extend only discrete complement coordinates; payload weights are never
subject to a discrete measurable-space instance. -/
def extendComplement (payload : ReferenceActivePhysicalStep.Payload rate)
    (values : CanonicalFastSampling.FastArm payload.slowSet → ℕ)
    (a : Fin p.K) : ℕ :=
  if ha : a ∈ CanonicalFastSampling.fastArmFinset payload.slowSet then
    values ⟨a, ha⟩ else 0

theorem extendComplement_apply (payload : ReferenceActivePhysicalStep.Payload rate)
    (values : CanonicalFastSampling.FastArm payload.slowSet → ℕ)
    (a : CanonicalFastSampling.FastArm payload.slowSet) :
    extendComplement payload values a.val = values a := by
  simp only [extendComplement, dite_eq_left a.property]

def encodeLive (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) : LiveDiscrete p := {
  clockSigma := r.priorClock.sigma
  clockCutoff := r.priorClock.u
  clockBoundary := r.priorClock.g
  clockProposal := r.priorClock.lastProposal
  pending := r.pendingAtChoice
  time := r.time
  gridBoundary := r.gridBoundary
  scores := extendComplement r.payload r.complementScores
  queues := extendComplement r.payload owned.queue
  previousServices := extendComplement r.payload owned.previousService
  baseScores := base }

def decodeLiveRegisters (payload : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p) :
    CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
  payload := payload
  priorClock := ⟨code.clockSigma, code.clockCutoff, code.clockBoundary, code.clockProposal⟩
  pendingAtChoice := code.pending
  time := code.time
  gridBoundary := code.gridBoundary
  complementScores := fun a => code.scores a.val }

def decodeLiveOwned (payload : ReferenceActivePhysicalStep.Payload rate) (code : LiveDiscrete p) :
    CoordinatorLiveServiceFinish.OwnedRegisters (decodeLiveRegisters payload code) := {
  queue := fun a => code.queues a.val
  previousService := fun a => code.previousServices a.val }

/-- Sum tags preserve first/live/collection/dagger. Collection's original
payload, actual moving ledger, and saved proposal are separate coordinates.
`Payload` inherits the accepted lossless anchor observation, and `Ledger`
inherits the accepted countable structure on its entirely discrete fields. -/
abbrev CoordinatorCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Unit ⊕ ((ReferenceActivePhysicalStep.Payload rate × LiveDiscrete p) ⊕
    ((ReferenceActivePhysicalStep.Payload rate × (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit))

def encodeCoordinator : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate → CoordinatorCode p rate
  | .first => .inl ()
  | .live registers owned base => .inr (.inl
      (registers.payload, encodeLive registers owned base))
  | .collection payload ledger proposal => .inr (.inr (.inl (payload, ledger, proposal)))
  | .dagger => .inr (.inr (.inr ()))

def decodeCoordinator : CoordinatorCode p rate → ReferenceActivePhysicalStep.CoordinatorConfiguration p rate
  | .inl _ => .first
  | .inr (.inl (payload, code)) => .live (decodeLiveRegisters payload code)
      (decodeLiveOwned payload code) code.baseScores
  | .inr (.inr (.inl (payload, ledger, proposal))) => .collection payload ledger proposal
  | .inr (.inr (.inr _)) => .dagger

theorem decodeCoordinator_encodeCoordinator (state : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
    decodeCoordinator (encodeCoordinator state) = state := by
  cases state with
  | first => rfl
  | dagger => rfl
  | collection payload ledger proposal => rfl
  | live registers owned base =>
      cases registers with
      | mk payload clock pending time boundary scores =>
        obtain ⟨sigma, cutoff, grid, proposal⟩ := clock
        cases owned with
        | mk queues previous =>
          let assemble (s q v : CanonicalFastSampling.FastArm payload.slowSet → ℕ) :
              ReferenceActivePhysicalStep.CoordinatorConfiguration p rate :=
            .live { payload := payload
                    priorClock := ⟨sigma, cutoff, grid, proposal⟩
                    pendingAtChoice := pending, time := time, gridBoundary := boundary
                    complementScores := s }
              { queue := q, previousService := v } base
          have hs : (fun a : CanonicalFastSampling.FastArm payload.slowSet =>
              extendComplement payload scores a.val) = scores :=
            funext (extendComplement_apply payload scores)
          have hq : (fun a : CanonicalFastSampling.FastArm payload.slowSet =>
              extendComplement payload queues a.val) = queues :=
            funext (extendComplement_apply payload queues)
          have hp : (fun a : CanonicalFastSampling.FastArm payload.slowSet =>
              extendComplement payload previous a.val) = previous :=
            funext (extendComplement_apply payload previous)
          change assemble (fun a => extendComplement payload scores a.val)
            (fun a => extendComplement payload queues a.val)
            (fun a => extendComplement payload previous a.val) = assemble scores queues previous
          rw [hs, hq, hp]

theorem encodeCoordinator_injective : Function.Injective
    (encodeCoordinator (p := p) (rate := rate)) :=
  Function.LeftInverse.injective decodeCoordinator_encodeCoordinator

/-- Product coordinates of the original state, retaining the sole UP bank,
all actual activations, ordinary/dagger tags and complete local memories. -/
abbrev StateCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  CoordinatorCode p rate × (CoordinatorUpReception.UpDecoderBank p ×
    ((Fin (p.m - 1) → ReferencePrelaunchFollower.Activation p) ×
      (Fin (p.m - 1) → FollowerPrepareJointMeasurability.IncomingConfiguration p rate)))

def encodeState (state : ReferenceActivePhysicalStep.State p rate) : StateCode p rate :=
  (encodeCoordinator state.coordinator, state.upDecoderBank, state.activations,
    fun i => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (state.followers i))

def decodeState (code : StateCode p rate) : ReferenceActivePhysicalStep.State p rate := {
  coordinator := decodeCoordinator code.1
  upDecoderBank := code.2.1
  activations := code.2.2.1
  followers := fun i => FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate (code.2.2.2 i) }

theorem decodeState_encodeState (state : ReferenceActivePhysicalStep.State p rate) :
    decodeState (encodeState state) = state := by
  have hf : (fun i => FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (state.followers i))) = state.followers :=
    funext fun i => FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration
      rate (state.followers i)
  cases state
  simp only [decodeState, encodeState, decodeCoordinator_encodeCoordinator, hf]

theorem encodeState_injective : Function.Injective (encodeState (p := p) (rate := rate)) :=
  Function.LeftInverse.injective decodeState_encodeState

/-- Pull back along the proved lossless STORE code, independently of dispatch,
feedback or the transition. Real anchors and buffers retain their Borel spaces. -/
instance stateMeasurableSpace : MeasurableSpace (ReferenceActivePhysicalStep.State p rate) :=
  MeasurableSpace.comap encodeState inferInstance

theorem measurable_encodeState : Measurable (encodeState (p := p) (rate := rate)) :=
  comap_measurable _

theorem measurable_coordinatorCode : Measurable
    (fun state : ReferenceActivePhysicalStep.State p rate => encodeCoordinator state.coordinator) :=
  measurable_fst.comp measurable_encodeState

theorem measurable_upDecoderBank : Measurable
    (fun state : ReferenceActivePhysicalStep.State p rate => state.upDecoderBank) :=
  measurable_fst.comp (measurable_snd.comp measurable_encodeState)

theorem measurable_activations : Measurable
    (fun state : ReferenceActivePhysicalStep.State p rate => state.activations) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_encodeState))

theorem measurable_followerCodes : Measurable
    (fun state : ReferenceActivePhysicalStep.State p rate =>
      fun i => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (state.followers i)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_encodeState))

/-- All original transient input coordinates, including EVERY row and the
ENTIRE grid reward table. Time validity is the original typing proof below. -/
abbrev RoundCoordinates (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalStep.State p rate × (CompletePublicTable.CompleteRows p ×
    (Fin (M p) × (Fin p.T × ActualInitializationPhysicalStep.GridRewardTable p)))

abbrev ActiveRoundCoordinates (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  {z : RoundCoordinates p rate // ∀ i, (z.1.activations i).val ≤ z.2.2.2.1.val + 1}

def encodeRoundInput (x : ReferenceActivePhysicalStep.RoundInput p rate) : ActiveRoundCoordinates p rate :=
  ⟨(x.state, x.rows, x.selected, x.time, x.rewards), x.active⟩

def decodeRoundInput (code : ActiveRoundCoordinates p rate) : ReferenceActivePhysicalStep.RoundInput p rate := {
  state := code.val.1
  rows := code.val.2.1
  selected := code.val.2.2.1
  time := code.val.2.2.2.1
  active := code.property
  rewards := code.val.2.2.2.2 }

theorem decodeRoundInput_encodeRoundInput (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    decodeRoundInput (encodeRoundInput x) = x := rfl

theorem encodeRoundInput_decodeRoundInput (code : ActiveRoundCoordinates p rate) :
    encodeRoundInput (decodeRoundInput code) = code := rfl

/-- The original input is equivalent to its precise active-time subtype.
Proof irrelevance accounts for its sole omitted typing proof. -/
def roundInputEquiv : ReferenceActivePhysicalStep.RoundInput p rate ≃ ActiveRoundCoordinates p rate where
  toFun := encodeRoundInput
  invFun := decodeRoundInput
  left_inv := decodeRoundInput_encodeRoundInput
  right_inv := encodeRoundInput_decodeRoundInput

instance roundInputMeasurableSpace : MeasurableSpace (ReferenceActivePhysicalStep.RoundInput p rate) :=
  MeasurableSpace.comap encodeRoundInput inferInstance

theorem measurable_encodeRoundInput :
    Measurable (encodeRoundInput (p := p) (rate := rate)) := comap_measurable _

theorem measurable_decodeRoundInput :
    Measurable (decodeRoundInput (p := p) (rate := rate)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun code : ActiveRoundCoordinates p rate =>
    encodeRoundInput (decodeRoundInput code))
  have heq : (fun code : ActiveRoundCoordinates p rate =>
      encodeRoundInput (decodeRoundInput code)) = id :=
    funext encodeRoundInput_decodeRoundInput
  rw [heq]
  exact measurable_id

theorem measurable_roundCoordinates : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => (encodeRoundInput x).val) :=
  measurable_subtype_coe.comp measurable_encodeRoundInput

theorem measurable_state : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.state) :=
  measurable_fst.comp measurable_roundCoordinates

theorem measurable_rows : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.rows) :=
  measurable_fst.comp (measurable_snd.comp measurable_roundCoordinates)

theorem measurable_selected : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.selected) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_roundCoordinates))

theorem measurable_time : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.time) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_roundCoordinates)))

theorem measurable_rewards : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.rewards) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_roundCoordinates)))

/-- Actual active subtypes are derived from the input's explicit typing proof;
they do not restrict the state to a favorable execution. -/
def followerActiveTime (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    FollowerLoggingDownMeasurability.ActiveTime p (x.state.activations i) :=
  ⟨x.time, x.active i⟩

theorem followerActiveTime_val (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    (followerActiveTime x i).val = x.time := rfl

/-- Selection retains the complete original continuous row. -/
theorem measurable_row : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.row) := by
  have heval : Measurable (fun z : CompletePublicTable.CompleteRows p × Fin (M p) =>
      z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro i
    exact measurable_pi_apply i
  exact heval.comp (measurable_rows.prodMk measurable_selected)

theorem measurable_activation (i : Fin (p.m - 1)) : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.state.activations i) :=
  (measurable_pi_apply i).comp (measurable_activations.comp measurable_state)

theorem measurable_incomingFollower (i : Fin (p.m - 1)) : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (x.state.followers i)) :=
  (measurable_pi_apply i).comp (measurable_followerCodes.comp measurable_state)

/-- The accepted prepared-output code of the actual follower preparation,
formed from its original incoming configuration, activation, full row and time. -/
def preparedFollowerCode (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate :=
  FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      (x.state.activations i)
      (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (x.state.followers i)) x.row x.time (x.active i))

theorem measurable_preparedFollowerCode (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      preparedFollowerCode x i) :=
  FollowerVaryingActivationMeasurability.measurable_varyingPreparedOutput_atComponents
    rate i (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.state.activations i)
      (fun x => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (x.state.followers i)) (fun x => x.row) (fun x => x.time)
      (measurable_activation i) (measurable_incomingFollower i)
      measurable_row measurable_time (fun x => x.active i)

/-- Reconstruction identifies the code with PREPARE in the very same
canonical round, including all checked preparation failures and dagger. -/
theorem preparedFollowerCode_reconstruct (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i
        (preparedFollowerCode x i).1 (preparedFollowerCode x i).2 =
      (ReferenceActivePhysicalStep.prepare x).followers.followers i := by
  have h := FollowerVaryingActivationMeasurability.assembledPrepare_reconstructs_prepare
    rate i (x.state.activations i)
    (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (x.state.followers i))
    x.row x.time (x.active i)
  rw [FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration]
    at h
  change FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i
      (x.state.activations i)
      (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i (x.state.activations i)
        (FollowerPrepareJointMeasurability.assemblePrepareInput
          (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            (x.state.followers i)) x.row (followerActiveTime x i))) = _
  exact h.trans (ReferenceActiveFeedbackCut.prepareFollowers_apply
    (ReferenceActivePhysicalStep.followerInput x) i).symm

/-- Actual follower actions are measurable on the full canonical input;
there is no measurable-coordinator or physical-history premise. -/
theorem measurable_followerArm (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  have hm := FollowerVaryingActivationMeasurability.measurable_varyingPreparedArm_atComponents
    rate i (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.state.activations i)
      (fun x => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (x.state.followers i)) (fun x => x.row) (fun x => x.time)
      (measurable_activation i) (measurable_incomingFollower i)
      measurable_row measurable_time (fun x => x.active i)
  have heq (x : ReferenceActivePhysicalStep.RoundInput p rate) :
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        FollowerVaryingActivationMeasurability.varyingPreparedArm (rate := rate) i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (x.state.activations i)
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (x.state.followers i)) x.row x.time (x.active i)) := by
    rw [(ReferenceActivePhysicalStep.prepare x).arms.actions_follower]
    change ((ReferenceActivePhysicalStep.prepare x).followers.followers i).arm = _
    rw [← preparedFollowerCode_reconstruct x i]
    rfl
  simp_rw [heq]
  exact hm

/-- Finite numerical coordinates of feedback. These are the original full
grid table, original time and an entire simultaneous action profile. -/
abbrev FeedbackCoordinates (p : Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p ×
    (Fin p.T × (Fin p.m → Fin p.K))

def gridFeedback (z : FeedbackCoordinates p) (player : Fin p.m) : Fin (D p + 1) := by
  classical
  exact if FiniteBanditModel.collisionFreeFor z.2.2 player then
    z.1 z.2.1 (z.2.2 player) else 0

theorem measurable_gridFeedback : Measurable
    (fun z : FeedbackCoordinates p => fun player => gridFeedback z player) :=
  measurable_of_countable _

/-- Exact identification with the existing simultaneous feedback cut. This
equality assumes no successful decoding, no collision or desired history. -/
theorem gridFeedback_eq_actual (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (player : Fin p.m) :
    gridFeedback (x.rewards, x.time, (ReferenceActivePhysicalStep.prepare x).arms.actions) player =
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback player :=
  ((ReferenceActivePhysicalStep.prepare x).feedback_rule player).symm

def ownEntryCode (x : ReferenceActivePhysicalStep.RoundInput p rate) (player : Fin p.m) :
    Fin p.K × Fin (D p + 1) :=
  ((ReferenceActivePhysicalStep.prepare x).arms.actions player,
    (ReferenceActivePhysicalStep.prepare x).feedback.feedback player)

/-- Decode the numerical own entry to the exact canonical step output. This
does not yet assert measurability of the actual coordinator action. -/
theorem ownEntryCode_reconstruct (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (player : Fin p.m) :
    ((ownEntryCode x player).1,
        ActualInitializationPhysicalStep.observationOfGrid p (ownEntryCode x player).2) =
      (ReferenceActivePhysicalStep.step x).ownEntries player :=
  (ReferenceActivePhysicalStep.step_own_entry x player).symm

/-- Literal projection of the actual successor into the lossless store
coordinates. No measurable space is defined using this operation. -/
def successorCode (x : ReferenceActivePhysicalStep.RoundInput p rate) : StateCode p rate :=
  encodeState (ReferenceActivePhysicalStep.step x).next

theorem successorCode_reconstruct (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    decodeState (successorCode x) = (ReferenceActivePhysicalStep.step x).next :=
  decodeState_encodeState _

end Bandits.Support.ReferenceActivePhysicalStepMeasurability

end
