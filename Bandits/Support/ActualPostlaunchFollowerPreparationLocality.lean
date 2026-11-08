/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchSuffixMeasurability

/-!
# Own-information locality of actual follower preparation

This module factors the actual mixed postlaunch follower's operational
preparation code and physical action through that follower's own preparation
coordinates. The equality premise on incoming follower storage is explicit;
it is an internal condition for later local-history work, not a history law.

The source ranges are `sources/zip4/manuscript/01_introduction.tex:20-28`,
`sources/zip4/manuscript/07_public_setup.tex:28-34,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

These deterministic equalities make no probability, independence,
measurability, or complete-history claim. Declared prepared codes omit the
retained full row from the physical prepared snapshot, while each side is
evaluated on its own original source.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchPreparationMeasurability
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ActualPostlaunchFollowerPreparationLocality

abbrev Parameters := ActualPostlaunchSuffixMeasurability.Parameters
abbrev RateInput := ActualPostlaunchSuffixMeasurability.RateInput

variable {p : Parameters} {rate : RateInput p}

abbrev PreparationCurrentCoordinates :=
  BootstrapPrivateRoundStreams.Scalar ×
    (BootstrapPrivateRoundStreams.Scalar ×
      ((Fin p.m → BootstrapPrivateRoundStreams.Scalar) ×
        (BootstrapPrivateRoundStreams.Scalar ×
          AffineChannelLaw.Sample (ContinuousLearningRows.B p))))

/-- The ordered sufficient coordinate envelope for one follower's PREPARE.
The sum distinguishes its existing bootstrap inactive, bootstrap active,
declared dagger, and declared ordinary branches. -/
abbrev PreparationSourceCoordinates :=
  Unit ⊕ (BootstrapPrivateRoundStreams.Scalar ⊕
    ((Bool × BootstrapPrivateRoundStreams.Scalar) ⊕
      PreparationCurrentCoordinates (p := p)))

/-- Project only the current preparation inputs actually used by this
follower's branch of the existing local operation. -/
def preparationSourceCoordinates {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor) :
    PreparationSourceCoordinates (p := p) := by
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let source := ActualPostlaunchFollowerMeasurability.localSource x
  let ownScalar := BootstrapPhysicalInput.playerRoundScalarAt p
    (ActualBootstrapObservationCode.sourcePrivate p source) player time
  match ActualPostlaunchFollowerMeasurability.localFollower x with
  | .bootstrap startup =>
      match startup.blockCase with
      | .inactive =>
          exact Sum.inr (Sum.inl ownScalar)
      | .active _ privateID _ _ =>
          exact Sum.inr (Sum.inr (Sum.inl
            (ActualBootstrapObservationCode.sourceIDs p source privateID time,
              ownScalar)))
  | .declared rowIndex _ configuration =>
      match configuration with
      | .dagger => exact Sum.inl ()
      | .ordinary _ _ =>
          let current :=
            ActualBootstrapObservationCode.sourceRows p source rowIndex
          let control := (current.2 time).1
          let affine := (current.2 time).2
          exact Sum.inr (Sum.inr (Sum.inr
            (control ContinuousControlSlice.Label.slot,
              (control ContinuousControlSlice.Label.sel,
                ((fun k : Fin p.m => control (ContinuousControlSlice.Label.tuple k)),
                  (control (ContinuousControlSlice.Label.pilot player),
                    affine (1, i)))))))

private theorem preparation_control_draws_eq
    (i : Fin (p.m - 1))
    (left right : ContinuousLearningRows.TimeControl p)
    (hslot : left.1 ContinuousControlSlice.Label.slot =
      right.1 ContinuousControlSlice.Label.slot)
    (hsel : left.1 ContinuousControlSlice.Label.sel =
      right.1 ContinuousControlSlice.Label.sel)
    (htuple : ∀ k : Fin p.m,
      left.1 (ContinuousControlSlice.Label.tuple k) =
        right.1 (ContinuousControlSlice.Label.tuple k))
    (hpilot : left.1
      (ContinuousControlSlice.Label.pilot
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      right.1 (ContinuousControlSlice.Label.pilot
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    (haffine : left.2 (1, i) = right.2 (1, i)) :
    PublicDiscreteDraws.slotDraw left.1 = PublicDiscreteDraws.slotDraw right.1 ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K left.1 =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K right.1 ∧
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K left.1 =
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K right.1 ∧
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) left.1 =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) right.1 ∧
      left.2 (1, i) = right.2 (1, i) := by
  have hslotDraw : PublicDiscreteDraws.slotDraw left.1 =
      PublicDiscreteDraws.slotDraw right.1 := by
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hslot]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K left.1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K right.1 := by
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hsel]
  have htupleDraw : OrderedTupleSampler.sample p.two_le_m p.m_lt_K left.1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K right.1 := by
    exact OrderedTupleSampler.sample_eq_of_tupleInputs_eq p.two_le_m p.m_lt_K htuple
  have hpilotDraw : PublicDiscreteDraws.pilotDraw (K_pos p)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) left.1 =
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) right.1 := by
    unfold PublicDiscreteDraws.pilotDraw ContinuousControlSlice.coordinate
    rw [hpilot]
  exact ⟨hslotDraw, hselected, htupleDraw, hpilotDraw, haffine⟩

private theorem actual_preparedRoundCode_eq_of_local_draws
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerLifecycleMeasurability.LocalConfigurationCode p rate)
    {n : ℕ} (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerLifecycleMeasurability.ActiveCalendarTime p activation)
    (hdraws : PublicDiscreteDraws.slotDraw (row.2 time.1).1 =
        PublicDiscreteDraws.slotDraw (row'.2 time.1).1 ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time.1).1 =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row'.2 time.1).1 ∧
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time.1).1 =
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time.1).1 ∧
      PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 time.1).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row'.2 time.1).1 ∧
      (row.2 time.1).2 (1, i) = (row'.2 time.1).2 (1, i)) :
    FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation incoming
      skeleton row time values =
    FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation incoming
      skeleton row' time values := by
  rcases hdraws with ⟨hslot, hselected, htuple, hpilot, haffine⟩
  unfold FollowerLifecycleMeasurability.prepareRoundCodeAt
  cases FollowerLifecycleMeasurability.localConfigurationOfCode
      rate incoming (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
        skeleton values) with
  | dagger =>
      simp [DeclaredFollowerLocalRound.prepare,
        FollowerLifecycleMeasurability.preparedRoundCode]
  | ordinary state memory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta time.1 state memory with
      | error reason =>
          simp [DeclaredFollowerLocalRound.prepare, hstart,
            FollowerLifecycleMeasurability.preparedRoundCode]
      | ok result =>
          rcases result with ⟨choiceState, choiceMemory⟩
          have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound
              i row activation time.1 =
            ActiveFollowerQueueOperation.selectedUpRound i row' activation time.1 := by
            unfold ActiveFollowerQueueOperation.selectedUpRound
            rw [hslot, hselected]
          have hoffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row
              activation time.1 choiceState =
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row'
              activation time.1 choiceState := by
            unfold ActiveFollowerQueueOperation.checkedUpOffer
            rw [hselectedUp]
          have harmChoice :
              ActiveFollowerArmChoice.followerArmChoice choiceState row time.1 i none =
                ActiveFollowerArmChoice.followerArmChoice choiceState row' time.1 i none := by
            rw [ActiveFollowerArmChoice.followerArmChoice_eq_core,
              ActiveFollowerArmChoice.followerArmChoice_eq_core]
            exact ActiveFollowerArmChoice.followerArmChoiceCore_eq_of_same_local_draws
              choiceState (row.2 time.1) (row'.2 time.1) i none
              hslot hselected htuple hpilot haffine
          have harmChoiceOffer (offered : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)) :
              ActiveFollowerArmChoice.followerArmChoice choiceState row time.1 i
                  (some offered) =
                ActiveFollowerArmChoice.followerArmChoice choiceState row' time.1 i
                  (some offered) := by
            rw [ActiveFollowerArmChoice.followerArmChoice_eq_core,
              ActiveFollowerArmChoice.followerArmChoice_eq_core]
            exact ActiveFollowerArmChoice.followerArmChoiceCore_eq_of_same_local_draws
              choiceState (row.2 time.1) (row'.2 time.1) i (some offered)
              hslot hselected htuple hpilot haffine
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row
              activation time.1 choiceState with
          | failure =>
              have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row'
                  activation time.1 choiceState = .failure := by
                rw [← hoffer, hoff]
              simp [DeclaredFollowerLocalRound.prepare, hstart,
                hoff, hoff', FollowerLifecycleMeasurability.preparedRoundCode]
          | noOffer =>
              have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row'
                  activation time.1 choiceState = .noOffer := by
                rw [← hoffer, hoff]
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                  choiceState row time.1 i none with
              | none =>
                  have hchoice' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row' time.1 i none = none := by
                    rw [← harmChoice, hchoice]
                  simp [DeclaredFollowerLocalRound.prepare, hstart,
                    hoff, hoff', hchoice, hchoice',
                    FollowerLifecycleMeasurability.preparedRoundCode]
              | some arm =>
                  have hchoice' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row' time.1 i none = some arm := by
                    rw [← harmChoice, hchoice]
                  simp [DeclaredFollowerLocalRound.prepare, hstart,
                    hoff, hoff', hchoice, hchoice',
                    FollowerLifecycleMeasurability.preparedRoundCode]
          | offer offered =>
              have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row'
                  activation time.1 choiceState = .offer offered := by
                rw [← hoffer, hoff]
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice
                  choiceState row time.1 i (some offered) with
              | none =>
                  have hchoice' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row' time.1 i (some offered) = none := by
                    rw [← harmChoiceOffer offered, hchoice]
                  simp [DeclaredFollowerLocalRound.prepare, hstart,
                    hoff, hoff', hchoice, hchoice',
                    FollowerLifecycleMeasurability.preparedRoundCode]
              | some arm =>
                  have hchoice' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row' time.1 i (some offered) = some arm := by
                    rw [← harmChoiceOffer offered, hchoice]
                  simp [DeclaredFollowerLocalRound.prepare, hstart,
                    hoff, hoff', hchoice, hchoice',
                    FollowerLifecycleMeasurability.preparedRoundCode]

private theorem prepareOutputData_eq_of_input_eq
    (i : Fin (p.m - 1))
    {activation activation' : ReferencePrelaunchFollower.Activation p}
    (hactivation : activation = activation')
    {incoming incoming' : FollowerPrepareJointMeasurability.IncomingConfiguration p rate}
    (hincoming : incoming = incoming')
    {row row' : CompletePublicTable.CompleteRow p}
    (hrow : row = row') (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1)
    (hactive' : activation'.val ≤ time.val + 1) :
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row
        ⟨time, hactive⟩)).2 =
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation'
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming' row'
        ⟨time, hactive'⟩)).2 := by
  cases hactivation
  cases hincoming
  cases hrow
  have hproof : hactive = hactive' := Subsingleton.elim _ _
  cases hproof
  rfl

private theorem varyingPreparedOutput_arm_configuration_eq
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1)
    (hdraws : PublicDiscreteDraws.slotDraw (row.2 time).1 =
        PublicDiscreteDraws.slotDraw (row'.2 time).1 ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time).1 =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row'.2 time).1 ∧
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1 =
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time).1 ∧
      PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 time).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row'.2 time).1 ∧
      (row.2 time).2 (1, i) = (row'.2 time).2 (1, i)) :
    (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        activation incoming row time hactive)).2.2 =
    (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        activation incoming row' time hactive)).2.2 := by
  simp only [FollowerVaryingActivationMeasurability.varyingPreparedOutput,
    FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput]
  cases hincoming : incoming with
  | none =>
      simp [FollowerPrepareJointMeasurability.assemblePrepareInput,
        FollowerPrepareJointMeasurability.prepareOutputOnInput,
        FollowerPrepareJointMeasurability.prepareOutputConfiguration,
        FollowerPrepareJointMeasurability.prepareRoundCodeOnInput,
        FollowerLifecycleMeasurability.fallbackPreparedRoundCode]
  | some data =>
      rcases data with ⟨state, memory⟩
      let index := (state.1, memory)
      have hcode :
          FollowerPrepareJointMeasurability.prepareRoundCodeOnInput rate i
              (activation := activation)
              (FollowerPrepareJointMeasurability.assemblePrepareInput
                (some (state, memory)) row ⟨time, hactive⟩) =
            FollowerPrepareJointMeasurability.prepareRoundCodeOnInput rate i
              (activation := activation)
              (FollowerPrepareJointMeasurability.assemblePrepareInput
                (some (state, memory)) row' ⟨time, hactive⟩) := by
        exact actual_preparedRoundCode_eq_of_local_draws i activation
          (some (state.1.1, memory)) state.1.2.2 state.2 row row'
          ⟨time, hactive⟩ hdraws
      unfold FollowerPrepareJointMeasurability.prepareOutputOnInput
      simp only [FollowerPrepareJointMeasurability.assemblePrepareInput]
      simp only [FollowerPrepareJointMeasurability.assemblePrepareInput] at hcode
      simp only [FollowerPrepareJointMeasurability.prepareOutputConfiguration]
      rw [hcode]

/-- Equal operational coordinates and equal incoming follower storage imply
equality of the lossless PREPARE codes. -/
theorem preparedCodeOnCursor_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hp : preparationSourceCoordinates (rate := rate) hcursor i x =
      preparationSourceCoordinates (rate := rate) hcursor i x') :
    ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
        (rate := rate) hcursor i x' := by
  cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
  | bootstrap startup =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .bootstrap startup := hf.symm.trans hlocal
      have hlocalValue : x.2.1.1 = .bootstrap startup := by
        simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal
      have hlocalValue' : x'.2.1.1 = .bootstrap startup := by
        simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal'
      have hx : x ∈ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x ∈ Set.range Sum.inl
        unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
        rw [hlocal]
        simp [ActualInitializationRoundMeasurability.followerCodeOfState]
      have hx' : x' ∈ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x' ∈ Set.range Sum.inl
        unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
        rw [hlocal']
        simp [ActualInitializationRoundMeasurability.followerCodeOfState]
      cases hcase : startup.blockCase with
      | inactive =>
          have hscalar :
              BootstrapPhysicalInput.playerRoundScalarAt p
                  (ActualBootstrapObservationCode.sourcePrivate p
                    (ActualPostlaunchFollowerMeasurability.localSource x))
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
                BootstrapPhysicalInput.playerRoundScalarAt p
                  (ActualBootstrapObservationCode.sourcePrivate p
                    (ActualPostlaunchFollowerMeasurability.localSource x'))
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) := by
            have hcoordinates := hp
            simp only [preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              hlocalValue, hlocalValue', hcase] at hcoordinates
            exact Sum.inl.inj (Sum.inr.inj hcoordinates)
          simp [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
            hx, hx', ActualPostlaunchFollowerMeasurability.preparedCodeOnBootstrap,
            ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap,
            ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
            ActualPostlaunchFollowerMeasurability.localFollower,
            ActualInitializationRoundMeasurability.followerCodeOfState,
            ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents,
            BootstrapObservedFollower.localArm, hlocalValue, hlocalValue', hcase, hscalar]
      | active held privateID gain registers =>
          have hpair :
              (ActualBootstrapObservationCode.sourceIDs p
                  (ActualPostlaunchFollowerMeasurability.localSource x) privateID
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor),
                BootstrapPhysicalInput.playerRoundScalarAt p
                  (ActualBootstrapObservationCode.sourcePrivate p
                    (ActualPostlaunchFollowerMeasurability.localSource x))
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor)) =
              (ActualBootstrapObservationCode.sourceIDs p
                  (ActualPostlaunchFollowerMeasurability.localSource x') privateID
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor),
                BootstrapPhysicalInput.playerRoundScalarAt p
                  (ActualBootstrapObservationCode.sourcePrivate p
                    (ActualPostlaunchFollowerMeasurability.localSource x'))
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor)) := by
            have hcoordinates := hp
            simp only [preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              hlocalValue, hlocalValue', hcase] at hcoordinates
            exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj hcoordinates))
          have hids : ActualBootstrapObservationCode.sourceIDs p
              (ActualPostlaunchFollowerMeasurability.localSource x) privateID
              (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
            ActualBootstrapObservationCode.sourceIDs p
              (ActualPostlaunchFollowerMeasurability.localSource x') privateID
              (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) := by
            simpa using congrArg Prod.fst hpair
          have hscalar : BootstrapPhysicalInput.playerRoundScalarAt p
              (ActualBootstrapObservationCode.sourcePrivate p
                (ActualPostlaunchFollowerMeasurability.localSource x))
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
            BootstrapPhysicalInput.playerRoundScalarAt p
              (ActualBootstrapObservationCode.sourcePrivate p
                (ActualPostlaunchFollowerMeasurability.localSource x'))
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) := by
            simpa using congrArg Prod.snd hpair
          simp [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
            hx, hx', ActualPostlaunchFollowerMeasurability.preparedCodeOnBootstrap,
            ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap,
            ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
            ActualPostlaunchFollowerMeasurability.localFollower,
            ActualInitializationRoundMeasurability.followerCodeOfState,
            ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents,
            BootstrapObservedFollower.localArm, hlocalValue, hlocalValue', hcase, hids, hscalar]
  | declared rowIndex activation configuration =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .declared rowIndex activation configuration := hf.symm.trans hlocal
      have hlocalValue : x.2.1.1 = .declared rowIndex activation configuration := by
        simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal
      have hlocalValue' : x'.2.1.1 = .declared rowIndex activation configuration := by
        simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal'
      have hnot : x ∉ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x ∉ Set.range Sum.inl
        unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
        rw [hlocal]
        simp [ActualInitializationRoundMeasurability.followerCodeOfState]
      have hnot' : x' ∉ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x' ∉ Set.range Sum.inl
        unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
        rw [hlocal']
        simp [ActualInitializationRoundMeasurability.followerCodeOfState]
      have hfields :
          ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
              (rate := rate) ⟨x, hnot⟩ =
            (rowIndex, (activation,
              FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
                rate configuration)) := by
        simp [ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualInitializationRoundMeasurability.followerCodeOfState, hlocal]
      have hfields' :
          ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
              (rate := rate) ⟨x', hnot'⟩ =
            (rowIndex, (activation,
              FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
                rate configuration)) := by
        simp [ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualInitializationRoundMeasurability.followerCodeOfState, hlocal']
      have hrow :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x, hnot⟩).1 = rowIndex := by
        exact congrArg Prod.fst hfields
      have hactivation :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x, hnot⟩).2.1 = activation := by
        exact congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
          hfields
      have hincoming :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x, hnot⟩).2.2 =
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration := by
        exact congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.2)
          hfields
      have hrow' :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x', hnot'⟩).1 = rowIndex := by
        exact congrArg Prod.fst hfields'
      have hactivation' :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x', hnot'⟩).2.1 = activation := by
        exact congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
          hfields'
      have hincoming' :
          (ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x', hnot'⟩).2.2 =
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration := by
        exact congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.2)
          hfields'
      cases configuration with
      | dagger =>
          have hpreparedDeclared :
              ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                  (rate := rate) hcursor i ⟨x, hnot⟩ =
                ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                  (rate := rate) hcursor i ⟨x', hnot'⟩ := by
            unfold ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
            simp [hfields, hfields', FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
              FollowerVaryingActivationMeasurability.varyingPreparedOutput,
              FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
              FollowerPrepareJointMeasurability.assemblePrepareInput,
              FollowerPrepareJointMeasurability.prepareOutputOnInput,
              FollowerPrepareJointMeasurability.prepareOutputConfiguration,
              FollowerPrepareJointMeasurability.prepareRoundCodeOnInput,
              FollowerLifecycleMeasurability.fallbackPreparedRoundCode]
          simpa [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
            hnot, hnot'] using hpreparedDeclared
      | ordinary state memory =>
          let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
          let current := ActualBootstrapObservationCode.sourceRows p
            (ActualPostlaunchFollowerMeasurability.localSource x) rowIndex
          let current' := ActualBootstrapObservationCode.sourceRows p
            (ActualPostlaunchFollowerMeasurability.localSource x') rowIndex
          let control := (current.2 time).1
          let control' := (current'.2 time).1
          let affine := (current.2 time).2
          let affine' := (current'.2 time).2
          let coords : PreparationCurrentCoordinates (p := p) :=
            (control ContinuousControlSlice.Label.slot,
              (control ContinuousControlSlice.Label.sel,
                ((fun k : Fin p.m => control (ContinuousControlSlice.Label.tuple k)),
                  (control (ContinuousControlSlice.Label.pilot
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)), affine (1, i)))))
          let coords' : PreparationCurrentCoordinates (p := p) :=
            (control' ContinuousControlSlice.Label.slot,
              (control' ContinuousControlSlice.Label.sel,
                ((fun k : Fin p.m => control' (ContinuousControlSlice.Label.tuple k)),
                  (control' (ContinuousControlSlice.Label.pilot
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)), affine' (1, i)))))
          have hcoord : preparationSourceCoordinates (rate := rate) hcursor i x =
              Sum.inr (Sum.inr (Sum.inr coords)) := by
            unfold preparationSourceCoordinates
            rw [hlocal]
          have hcoord' : preparationSourceCoordinates (rate := rate) hcursor i x' =
              Sum.inr (Sum.inr (Sum.inr coords')) := by
            unfold preparationSourceCoordinates
            rw [hlocal']
          have hcp : coords = coords' := by
            rw [hcoord, hcoord'] at hp
            exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hp))
          have hslot := congrArg Prod.fst hcp
          have htail1 := congrArg Prod.snd hcp
          have hsel := congrArg Prod.fst htail1
          have htail2 := congrArg Prod.snd htail1
          have htuple : ∀ k : Fin p.m,
              control (ContinuousControlSlice.Label.tuple k) =
                control' (ContinuousControlSlice.Label.tuple k) := by
            intro k
            exact congrFun (congrArg Prod.fst htail2) k
          have htail3 := congrArg Prod.snd htail2
          have hpilot := congrArg Prod.fst htail3
          have haffine := congrArg Prod.snd htail3
          have hdraws := preparation_control_draws_eq i (current.2 time) (current'.2 time)
            hslot hsel htuple hpilot haffine
          have hactive : activation.val ≤ time.val + 1 := by
            have hstateCursor := x.2.1.2
            change ActualInitializationRun.followerAtCursor p rate block cursor
              (ActualPostlaunchFollowerMeasurability.localFollower x) at hstateCursor
            rw [hlocal] at hstateCursor
            simpa [ActualInitializationRun.followerAtCursor,
              ActualPostlaunchFollowerMeasurability.localTime,
              ActualInitializationRun.blockTime, time] using hstateCursor
          have houtput := varyingPreparedOutput_arm_configuration_eq
            i activation
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (.ordinary state memory))
            current current' time hactive hdraws
          let fieldsX := ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x, hnot⟩
          let fieldsX' := ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
            (rate := rate) ⟨x', hnot'⟩
          let rowX := ActualBootstrapObservationCode.sourceRows p
            (ActualPostlaunchFollowerMeasurability.localSource x) fieldsX.1
          let rowX' := ActualBootstrapObservationCode.sourceRows p
            (ActualPostlaunchFollowerMeasurability.localSource x') fieldsX'.1
          have hrowX : fieldsX.1 = rowIndex := congrArg Prod.fst hfields
          have hrowX' : fieldsX'.1 = rowIndex := congrArg Prod.fst hfields'
          have hactivationX : fieldsX.2.1 = activation :=
            congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
              hfields
          have hactivationX' : fieldsX'.2.1 = activation :=
            congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
              hfields'
          have hincomingX : fieldsX.2.2 =
              FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (.ordinary state memory) :=
            congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.2)
              hfields
          have hincomingX' : fieldsX'.2.2 =
              FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (.ordinary state memory) :=
            congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.2)
              hfields'
          have hrowSourceX : rowX = current := by
            simpa [rowX, current, ActualPostlaunchFollowerMeasurability.localSource] using
              congrArg (fun j => ActualBootstrapObservationCode.sourceRows p
                (ActualPostlaunchFollowerMeasurability.localSource x) j) hrowX
          have hrowSourceX' : rowX' = current' := by
            simpa [rowX', current', ActualPostlaunchFollowerMeasurability.localSource] using
              congrArg (fun j => ActualBootstrapObservationCode.sourceRows p
                (ActualPostlaunchFollowerMeasurability.localSource x') j) hrowX'
          have hactiveX : fieldsX.2.1.val ≤ time.val + 1 := by
            rw [hactivationX]
            exact hactive
          have hactiveX' : fieldsX'.2.1.val ≤ time.val + 1 := by
            rw [hactivationX']
            exact hactive
          have hvalidX := ActualPostlaunchFollowerMeasurability.declaredActivation_le_time_of_code
            (rate := rate) hcursor x fieldsX
            (ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
              (rate := rate) ⟨x, hnot⟩)
          have hvalidX' := ActualPostlaunchFollowerMeasurability.declaredActivation_le_time_of_code
            (rate := rate) hcursor x' fieldsX'
            (ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
              (rate := rate) ⟨x', hnot'⟩)
          let outputX := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              fieldsX.2.1 fieldsX.2.2 rowX time hvalidX)
          let outputX' := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              fieldsX'.2.1 fieldsX'.2.2 rowX' time hvalidX')
          let commonOutput := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              activation
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (.ordinary state memory)) current time hactive)
          let commonOutput' := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              activation
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (.ordinary state memory)) current' time hactive)
          have houtputX : outputX.2.2 = commonOutput.2.2 := by
            dsimp only [outputX, commonOutput,
              FollowerVaryingActivationMeasurability.varyingPreparedOutput,
              FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput]
            exact prepareOutputData_eq_of_input_eq i hactivationX hincomingX hrowSourceX
              time hvalidX hactive
          have houtputX' : outputX'.2.2 = commonOutput'.2.2 := by
            dsimp only [outputX', commonOutput',
              FollowerVaryingActivationMeasurability.varyingPreparedOutput,
              FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput]
            exact prepareOutputData_eq_of_input_eq i hactivationX' hincomingX' hrowSourceX'
              time hvalidX' hactive
          have hcommonOutput : commonOutput.2.2 = commonOutput'.2.2 := houtput
          have hpreparedDeclared :
              ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                  (rate := rate) hcursor i ⟨x, hnot⟩ =
                ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                  (rate := rate) hcursor i ⟨x', hnot'⟩ := by
            have hleft :
                ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                    (rate := rate) hcursor i ⟨x, hnot⟩ =
                  Sum.inr (rowIndex, (activation, commonOutput.2.2)) := by
              change Sum.inr (fieldsX.1, (fieldsX.2.1, outputX.2.2)) = _
              rw [hrowX, hactivationX, houtputX]
            have hmiddle :
                (Sum.inr (rowIndex, (activation, commonOutput.2.2)) :
                  ActualPostlaunchFollowerMeasurability.PreparedFollowerCode p rate block) =
                (Sum.inr (rowIndex, (activation, commonOutput'.2.2)) :
                  ActualPostlaunchFollowerMeasurability.PreparedFollowerCode p rate block) := by
              exact congrArg (fun z : Fin p.K ×
                FollowerPrepareJointMeasurability.IncomingConfiguration p rate =>
                  (Sum.inr (rowIndex, (activation, z)) :
                    ActualPostlaunchFollowerMeasurability.PreparedFollowerCode p rate block))
                hcommonOutput
            have hright :
                ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
                    (rate := rate) hcursor i ⟨x', hnot'⟩ =
                  Sum.inr (rowIndex, (activation, commonOutput'.2.2)) := by
              change Sum.inr (fieldsX'.1, (fieldsX'.2.1, outputX'.2.2)) = _
              rw [hrowX', hactivationX', houtputX']
            exact hleft.trans (hmiddle.trans hright.symm)
          simpa [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
            hnot, hnot'] using hpreparedDeclared

/-- Actual physical play uses exactly the preparation-local coordinates of
the same follower. No equality of rewards, other storage, or other players'
private coordinates is required. -/
theorem physical_follower_action_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (i : Fin (p.m - 1))
    (a b : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower
      (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerMeasurability.localFollower
        (ActualPostlaunchStepMeasurability.followerInput i b))
    (hp : preparationSourceCoordinates (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      preparationSourceCoordinates (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i b)) :
    ActualPostlaunchPhysicalStep.actionProfile (ActualPostlaunchPhysicalStep.prepare a)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ActualPostlaunchPhysicalStep.actionProfile (ActualPostlaunchPhysicalStep.prepare b)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  let x := ActualPostlaunchStepMeasurability.followerInput i a
  let x' := ActualPostlaunchStepMeasurability.followerInput i b
  have hcode := preparedCodeOnCursor_eq_of_own_coordinates
    (rate := rate) a.cursor_lt i x x' hf hp
  have hprepared :
      ActualPostlaunchPreparationMeasurability.followerPreparationCode i a =
        ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
          (rate := rate) a.cursor_lt i x' := by
    calc
      ActualPostlaunchPreparationMeasurability.followerPreparationCode i a =
          ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
            (rate := rate) a.cursor_lt i x :=
        ActualPostlaunchPreparationMeasurability.followerPreparationCode_eq_at_feedback
          a i (ActualPostlaunchPhysicalStep.physicalFeedback
            (ActualPostlaunchPhysicalStep.prepare a)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      _ = ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
            (rate := rate) a.cursor_lt i x' := hcode
  have harmCode := congrArg
    (ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
      (p := p) (rate := rate) (block := block)) hprepared
  have harm :
      ((ActualPostlaunchPhysicalStep.prepare a).followers i).arm =
        ((ActualPostlaunchPhysicalStep.prepare b).followers i).arm := by
    rw [← ActualPostlaunchPreparationMeasurability.followerPreparationCode_arm a i,
      ← ActualPostlaunchPreparationMeasurability.followerPreparationCode_arm b i]
    exact harmCode
  calc
    ActualPostlaunchPhysicalStep.actionProfile
        (ActualPostlaunchPhysicalStep.prepare a)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ((ActualPostlaunchPhysicalStep.prepare a).followers i).arm :=
        ActualPostlaunchPhysicalStep.actionProfile_follower (ActualPostlaunchPhysicalStep.prepare a) i
    _ = ((ActualPostlaunchPhysicalStep.prepare b).followers i).arm := harm
    _ = ActualPostlaunchPhysicalStep.actionProfile
        (ActualPostlaunchPhysicalStep.prepare b)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
      (ActualPostlaunchPhysicalStep.actionProfile_follower
        (ActualPostlaunchPhysicalStep.prepare b) i).symm

end Bandits.Support.ActualPostlaunchFollowerPreparationLocality

end
