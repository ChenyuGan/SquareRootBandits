/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchStepMeasurability

/-!
# Actual completed-block boundary and successor measurability

This module codes every completed follower boundary output from the original
source and the existing postlaunch storage. It retains the three boundary tags,
the updated bootstrap weights, pending declarations, and each declared
follower's own row, activation, ordinary-or-dagger configuration, buffer, and
saved real coordinates. Completion follows from the stored cursor invariant.

At a genuine successor block, the coordinator and UP bank are copied, while
each follower is started from the carry read out of that same boundary code
and the original source's next-block private scalars. The target storage is the
existing preparation module's encoding at cursor zero.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

The boundary observations also apply at the final clipped block. The
successor theorem requires a genuine next block and introduces no action at
the horizon. This is a fixed-boundary joint composition for the later actual
mixed cross-block suffix Borel composer. It does not prove that composer's
fold measurability, a source-initialized launch, a whole history, or any
probability, information, coupling, or regret result.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ActualPostlaunchBoundaryMeasurability

abbrev Parameters := ActualPostlaunchPhysicalStep.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}
  {block : Fin (n_boot p)}

open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchPreparationMeasurability
open Bandits.Support.ActualInitializationFollowerBoundaryMeasurability
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationBeginJointMeasurability
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.FollowerLifecycleMeasurability

/-- The complete retained boundary output for every heterogeneous follower.
Its source field keeps the original joint private input in the domain even
though this local boundary observation reads the completed state. -/
def boundaryOutputCode
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block)) :
    Fin (p.m - 1) → BoundaryOutputCode p rate :=
  fun i => boundaryOutputFromFollowerCode p rate block
    (followerCodeOfState p rate block (input.2.followers i))

/-- The separate bootstrap numerator observation, present exactly on startup
followers and retaining the actual completed-block weight update. -/
def boundaryUpdatedNumeratorsObservationCode
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block)) :
    Fin (p.m - 1) → Option (Fin p.K → ℕ) :=
  fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode p rate block
    (followerCodeOfState p rate block (input.2.followers i))

/-- Each complete output code is Borel in the original source and the actual
completed state, using the same follower code and measurable storage space. -/
theorem measurable_boundaryOutputCode : Measurable
    (boundaryOutputCode (p := p) (rate := rate) (block := block)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_boundaryOutputFromFollowerCode p rate block).comp <|
    (measurable_followerCodeOfState p rate block).comp <|
      (measurable_stateFollower i).comp measurable_snd

/-- The separately retained updated-numerator observable is jointly Borel. -/
theorem measurable_boundaryUpdatedNumeratorsObservationCode : Measurable
    (boundaryUpdatedNumeratorsObservationCode (p := p) (rate := rate) (block := block)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryUpdatedNumeratorsCode p rate block).comp <|
    (measurable_followerCodeOfState p rate block).comp <|
      (measurable_stateFollower i).comp measurable_snd

/-- A completed stored follower really supplies the finish-block premise:
the existing cursor proof is transported through the exact follower codec. -/
theorem boundaryFollower_complete
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block)
      (followerStateOfCode p rate block
        (followerCodeOfState p rate block (input.2.followers i))) := by
  rw [followerStateOfCode_encode]
  exact input.2.followers_at_cursor i

/-- Decoding the retained unchecked boundary observation gives the exact
accepted physical boundary output. The checked/unchecked agreement is applied
with completion derived above, and output uniqueness follows from `Except.ok`.
This includes the final clipped block. -/
theorem boundaryOutputCode_reconstructs
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    decodeBoundaryOutputCode p rate (boundaryOutputCode input i) =
      boundaryOutput input.2 i := by
  let follower := followerCodeOfState p rate block (input.2.followers i)
  have hstate : followerStateOfCode p rate block follower = input.2.followers i := by
    exact followerStateOfCode_encode p rate block _
  have hchecked := checked_boundaryOutput_agrees_of_complete p rate block follower
    (boundaryFollower_complete input i)
  have hphysical : decodeBoundaryFollowerCode p rate block
      (boundaryFollowerCode p rate block follower) =
      .ok (boundaryOutput input.2 i) := by
    rw [decode_boundaryFollowerCode, hstate]
    exact boundaryOutput_accepted input.2 i
  have houtputs : boundaryOutput input.2 i =
      decodeBoundaryOutputCode p rate
        (boundaryOutputFromFollowerCode p rate block follower) := by
    apply Except.ok.inj
    exact hphysical.symm.trans hchecked
  exact houtputs.symm

/-! The carry code is a literal readout of the three existing boundary tags.
The first-declaration branch wraps its already retained carried state and
memory codes in the existing incoming-configuration option. -/

/-- Read the exact carry coordinates from one retained boundary output. No
boundary operation, state reconstruction, or bootstrap draw is run here. -/
def boundaryCarryCode (code : BoundaryOutputCode p rate) :
    FollowerCarryCode p rate :=
  match code with
  | .inl (weights, _activation) => .inl weights
  | .inr (.inl (row, (activation, fields))) =>
      .inr (row, (activation, some fields))
  | .inr (.inr (row, (activation, configuration))) =>
      .inr (row, (activation, configuration))

private theorem measurable_someIncomingConfiguration :
    Measurable (fun fields : FirstDeclarationFields p rate =>
      (some fields : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun fields : FirstDeclarationFields p rate =>
    Sum.inr fields)
  exact measurable_inr

/-- The three-tag readout is measurable and preserves the continuous declared
configuration fibres instead of replacing them by countable codes. -/
theorem measurable_boundaryCarryCode :
    Measurable (boundaryCarryCode (p := p) (rate := rate)) := by
  apply measurable_fun_sum
  · change Measurable (fun x : BoundaryWeightsCode p × Activation p =>
      Sum.inl x.1)
    exact measurable_inl.comp measurable_fst
  · apply measurable_fun_sum
    · change Measurable (fun x : Fin (M p) ×
        (Activation p × FirstDeclarationFields p rate) =>
          Sum.inr (x.1, (x.2.1, some x.2.2)))
      exact measurable_inr.comp <|
        measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk
            (measurable_someIncomingConfiguration.comp
              (measurable_snd.comp measurable_snd)))
    · change Measurable (fun x : Fin (M p) ×
        (Activation p × FollowerPrepareJointMeasurability.IncomingConfiguration p rate) =>
          Sum.inr x)
      exact measurable_inr.comp measurable_id

/-- On a real follower's boundary code, the literal tag readout equals the
existing `followerCarryOfBoundaryOutput` followed by its admitted carry
encoder. -/
theorem boundaryCarryCode_reconstructs
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    boundaryCarryCode (boundaryOutputCode input i) =
      followerCarryCodeOf (followerCarryOfBoundaryOutput rate
        (decodeBoundaryOutputCode p rate (boundaryOutputCode input i))) := by
  cases hfollower : input.2.followers i with
  | bootstrap startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp [boundaryOutputCode, boundaryCarryCode, hfollower,
            followerCodeOfState, boundaryOutputFromFollowerCode,
            decodeBoundaryOutputCode, followerCarryOfBoundaryOutput,
            ActualInitializationBlockMeasurability.followerCarryCodeOf, hpending,
            ActualBootstrapObservationCode.updatedNumeratorsCode_reconstruction]
      | some row =>
          simp only [boundaryOutputCode, boundaryCarryCode, hfollower,
            followerCodeOfState, boundaryOutputFromFollowerCode, hpending]
          rw [decode_firstDeclarationOutput p rate row
            (BootstrapObservedFollower.nextActivationRound p block)]
          simp [followerCarryOfBoundaryOutput,
            ActualInitializationBlockMeasurability.followerCarryCodeOf,
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
            firstDeclarationFields,
            FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
            FollowerLifecycleMeasurability.localMemoryCode]
  | declared row activation configuration =>
      simp only [boundaryOutputCode, boundaryCarryCode, hfollower,
        followerCodeOfState, boundaryOutputFromFollowerCode,
        decodeBoundaryOutputCode, followerCarryOfBoundaryOutput,
        ActualInitializationBlockMeasurability.followerCarryCodeOf]
      rw [FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration
        rate configuration]

/-- The carry readout is the actual carry at the completed physical boundary.
This composes the retained-code reconstruction with the admitted
`boundaryCarry_reconstruction` and the unique actual boundary observation. -/
theorem boundaryCarryCode_eq_actual
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    boundaryCarryCode (boundaryOutputCode input i) =
      followerCarryCodeOf (boundaryCarry input.2 i) := by
  let follower := followerCodeOfState p rate block (input.2.followers i)
  have hstate : followerStateOfCode p rate block follower = input.2.followers i := by
    exact followerStateOfCode_encode p rate block _
  have hcarry := boundaryCarry_reconstruction p rate block follower
  have hboundary : boundaryCarry input.2 i =
      followerCarryOfBoundaryOutput rate
        (decodeBoundaryOutputCode p rate (boundaryOutputCode input i)) := by
    rw [boundaryCarry_eq_actual_boundary, ← hstate]
    exact hcarry
  calc
    boundaryCarryCode (boundaryOutputCode input i) =
        followerCarryCodeOf (followerCarryOfBoundaryOutput rate
          (decodeBoundaryOutputCode p rate (boundaryOutputCode input i))) :=
      boundaryCarryCode_reconstructs input i
    _ = followerCarryCodeOf (boundaryCarry input.2 i) :=
      congrArg followerCarryCodeOf hboundary.symm

/-! ## Genuine successor boundary -/

/-- The next state's existing storage coordinates: coordinator and UP bank
are copied, and each heterogeneous follower code is begun from the carry
readout and this same original source. -/
def successorBoundaryCoordinates {next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (_hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block)) :
    StateCoordinates p rate next :=
  (ReferenceActivePhysicalStepMeasurability.encodeCoordinator input.2.coordinator,
    (input.2.upDecoderBank, fun i =>
      beginFollowerCodeOfCarryCode next input.1 i
        (boundaryCarryCode (boundaryOutputCode input i))))

/-- Every successor storage coordinate is Borel. Follower starts compose the
admitted `measurable_beginFollowerCodeOfCarryCode` with the literal measured
carry readout. -/
theorem measurable_successorBoundaryCoordinates {next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext) :
    Measurable (successorBoundaryCoordinates (p := p) (rate := rate)
      (block := block) hnext hnext_eq) := by
  have hsource : Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) => input.1) := measurable_fst
  have hcoord : Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) =>
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator input.2.coordinator) :=
    (measurable_stateCoordinatorCode (p := p) (rate := rate) (block := block)
      (cursor := BootstrapObservedFollower.blockLength p block)).comp measurable_snd
  have hbank : Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) => input.2.upDecoderBank) :=
    (measurable_stateBank (p := p) (rate := rate) (block := block)
      (cursor := BootstrapObservedFollower.blockLength p block)).comp measurable_snd
  have hfollowers : Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) =>
      fun i : Fin (p.m - 1) =>
        beginFollowerCodeOfCarryCode next input.1 i
          (boundaryCarryCode (boundaryOutputCode input i))) := by
    apply measurable_pi_iff.mpr
    intro i
    have hcarry : Measurable (fun input : SourceInput p ×
        PostlaunchState (p := p) (rate := rate) block
          (BootstrapObservedFollower.blockLength p block) =>
        boundaryCarryCode (boundaryOutputCode input i)) :=
      (measurable_boundaryCarryCode (p := p) (rate := rate)).comp
        ((measurable_pi_apply i).comp measurable_boundaryOutputCode)
    exact (measurable_beginFollowerCodeOfCarryCode next i).comp
      (hsource.prodMk hcarry)
  exact hcoord.prodMk (hbank.prodMk hfollowers)

/-- The encoded actual cross-boundary state is exactly the retained
coordinator/bank/follower code, including the source-driven bootstrap begin. -/
theorem encode_crossSuccessorBoundary {next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block)) :
    encodeState (p := p) (rate := rate) (block := next) (cursor := 0)
      (crossSuccessorBoundary hnext hnext_eq input.1 input.2) =
    successorBoundaryCoordinates hnext hnext_eq input := by
  cases hnext_eq
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply funext
      intro i
      have hcarry := boundaryCarryCode_eq_actual input i
      have hbegin := beginFollowerCodeOfCarryCode_followerCarryCodeOf
        (ActualInitializationRun.successorBlock p block hnext) input.1 i
        (boundaryCarry input.2 i)
      change followerCodeOfState p rate
          (ActualInitializationRun.successorBlock p block hnext)
          (beginSuccessorFollower hnext rfl input.1 input.2 i) =
        beginFollowerCodeOfCarryCode (ActualInitializationRun.successorBlock p block hnext)
          input.1 i (boundaryCarryCode (boundaryOutputCode input i))
      calc
        followerCodeOfState p rate (ActualInitializationRun.successorBlock p block hnext)
            (beginSuccessorFollower hnext rfl input.1 input.2 i) =
          ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry
            (ActualInitializationRun.successorBlock p block hnext) input.1 i
              (boundaryCarry input.2 i) := rfl
        _ = beginFollowerCodeOfCarryCode
              (ActualInitializationRun.successorBlock p block hnext) input.1 i
              (followerCarryCodeOf (boundaryCarry input.2 i)) := hbegin.symm
        _ = beginFollowerCodeOfCarryCode
              (ActualInitializationRun.successorBlock p block hnext) input.1 i
              (boundaryCarryCode (boundaryOutputCode input i)) :=
          congrArg (beginFollowerCodeOfCarryCode
            (ActualInitializationRun.successorBlock p block hnext) input.1 i)
              hcarry.symm

/-- Decode the exact encoded successor coordinates back to the existing
cross-boundary state in P's same storage space at the genuine next block and
cursor zero. The image witness supplies typing only; decoded data are read
from the retained coordinates. -/
theorem decode_crossSuccessorBoundary {next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block)) :
    decodeState (p := p) (rate := rate) (block := next) (cursor := 0)
      ⟨successorBoundaryCoordinates hnext hnext_eq input,
        ⟨crossSuccessorBoundary hnext hnext_eq input.1 input.2,
          encode_crossSuccessorBoundary hnext hnext_eq input⟩⟩ =
      crossSuccessorBoundary hnext hnext_eq input.1 input.2 := by
  let successor := crossSuccessorBoundary hnext hnext_eq input.1 input.2
  have hcode :
      (⟨successorBoundaryCoordinates hnext hnext_eq input,
        ⟨successor, encode_crossSuccessorBoundary hnext hnext_eq input⟩⟩ :
        Set.range (encodeState (p := p) (rate := rate)
          (block := next) (cursor := 0))) =
      ⟨encodeState (p := p) (rate := rate) (block := next) (cursor := 0) successor,
        ⟨successor, rfl⟩⟩ :=
    Subtype.ext (encode_crossSuccessorBoundary hnext hnext_eq input).symm
  rw [hcode, decode_encodeState]

/-- The actual mixed successor boundary is Borel on the original source and
completed state, into P's same storage space at cursor zero. The only calendar
premises are the genuine successor bound and its successor-block typing
equality; no future activation or follower success is assumed. -/
theorem measurable_crossSuccessorBoundary {next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext) :
    Measurable (fun input : SourceInput p ×
      PostlaunchState (p := p) (rate := rate) block
        (BootstrapObservedFollower.blockLength p block) =>
      crossSuccessorBoundary hnext hnext_eq input.1 input.2) := by
  apply measurable_comap_iff.mpr
  have heq :
      (encodeState (p := p) (rate := rate) (block := next) (cursor := 0) ∘
        (fun input : SourceInput p ×
          PostlaunchState (p := p) (rate := rate) block
            (BootstrapObservedFollower.blockLength p block) =>
          crossSuccessorBoundary hnext hnext_eq input.1 input.2)) =
      successorBoundaryCoordinates hnext hnext_eq := by
    funext input
    exact encode_crossSuccessorBoundary hnext hnext_eq input
  rw [heq]
  exact measurable_successorBoundaryCoordinates hnext hnext_eq

end Bandits.Support.ActualPostlaunchBoundaryMeasurability

end
