/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationStepMeasurability
public import Bandits.Support.ActualInitializationRun

/-!
# Measurable code for one actual initialization block

This module defines a lossless code for the existing `BlockCarry`, the
accepted actual block-start code, and the target output shape for the existing
`ActualInitializationRun.foldBlock`. The start code has exact coordinator and
follower reconstruction and is Borel in the original source for each fixed
admissible carry, including the actual `initialCarry`. The recursive producer
and relative decoder for the full block-fold output remain unproved here.
The fixed constants and full reward grid stay fixed parameters. The target
round-code list uses the accepted total same-input code from
`ActualInitializationStepMeasurability`, retaining the actual actions, grid
feedback, coordinator monitor/launch information, and each follower's
heterogeneous successor.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`,
`sources/zip4/manuscript/06_interruptions.tex:235-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.ActualInitializationStepMeasurability
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.FollowerPrepareJointMeasurability

namespace Bandits.Support.ActualInitializationBlockMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

/-! ## A lossless code for the existing carried block input -/

/-- The accepted numerator vector together with its actual positivity proof. -/
abbrev ValidNumeratorCode (p : Parameters) :=
  { n : Fin p.K → ℕ // ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) n a }

/-- One existing follower carry, retaining bootstrap numerators or the exact
declared row, literal activation subtype, and complete ordinary/dagger input
code with its original continuous saved-real fibers. -/
abbrev FollowerCarryCode (p : Parameters) (rate : RateInput p) :=
  Sum (ValidNumeratorCode p)
    (Fin (M p) × (ReferencePrelaunchFollower.Activation p ×
      FollowerPrepareJointMeasurability.IncomingConfiguration p rate))

/-- The existing no-crossing monitor subtype, expressed in the accepted
countable monitor code. -/
abbrev UnlaunchedMonitorCode (p : Parameters) :=
  { m : BootstrapCoordinatorRoundMeasurability.MonitorCode p //
    m.crossingBlock = none ∧ m.launchPosition = p.T }

/-- Literal code fields for the existing `ActualInitializationRun.BlockCarry`.
The two real constants are fixed theorem parameters and are therefore omitted
from this code. -/
structure BlockCarryCodeFields (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  coordinator : BootstrapCoordinatorRoundMeasurability.CoordinatorStateCode p
  monitor : UnlaunchedMonitorCode p
  followers : Fin (p.m - 1) → FollowerCarryCode p rate

/-- The product coordinates which induce the measurable space on the local
code for the existing carry. Continuous incoming follower fibers retain their
accepted measurable spaces. -/
def blockCarryCodeFieldsCoordinates {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (fields : BlockCarryCodeFields p rate block) :=
  (fields.coordinator, (fields.monitor, fields.followers))

instance blockCarryCodeFieldsMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) : MeasurableSpace (BlockCarryCodeFields p rate block) :=
  MeasurableSpace.comap blockCarryCodeFieldsCoordinates inferInstance

/-- The activation timing condition carried by the existing block carry,
transcribed on the corresponding follower codes. -/
def BlockCarryCodeFields.activationReady {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (fields : BlockCarryCodeFields p rate block) : Prop :=
  ∀ i, match fields.followers i with
    | .inl _ => True
    | .inr (_, (activation, _)) =>
        activation.val ≤ BootstrapObservedFollower.blockStart p block + 1

/-- A code for exactly the existing carried coordinator, monitor, and follower
family, restricted by its original activation-ready invariant. -/
abbrev BlockCarryCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  { fields : BlockCarryCodeFields p rate block // fields.activationReady }

/-- Encode the original follower carry without altering its branch or payload. -/
def followerCarryCodeOf {p : Parameters} {rate : RateInput p}
    (carried : ActualInitializationRun.FollowerCarry p rate) :
    FollowerCarryCode p rate :=
  match carried with
  | .bootstrap numerators lowerBound => .inl ⟨numerators, lowerBound⟩
  | .declared row activation configuration =>
      .inr (row, (activation,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration))

/-- Decode an existing follower carry code back to the original carry type. -/
def followerCarryOfCode {p : Parameters} {rate : RateInput p}
    (code : FollowerCarryCode p rate) : ActualInitializationRun.FollowerCarry p rate :=
  match code with
  | .inl numerators => .bootstrap numerators.1 numerators.2
  | .inr (row, (activation, configuration)) =>
      .declared row activation
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate configuration)

/-- Decoding an encoded follower carry recovers its full original state. -/
theorem followerCarryOfCode_encode {p : Parameters} {rate : RateInput p}
    (carried : ActualInitializationRun.FollowerCarry p rate) :
    followerCarryOfCode (followerCarryCodeOf carried) = carried := by
  cases carried with
  | bootstrap numerators lowerBound => rfl
  | declared row activation configuration =>
      simp [followerCarryOfCode, followerCarryCodeOf,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration]

/-- Encode every field of the actual `BlockCarry`, retaining its original
activation-ready proof. -/
def blockCarryCodeOf {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)}
    (carry : ActualInitializationRun.BlockCarry p rate block) :
    BlockCarryCode p rate block := by
  refine ⟨⟨BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p carry.coordinator,
    ⟨BootstrapCoordinatorRoundMeasurability.monitorCode p carry.monitor.1, ?_⟩,
    fun i => followerCarryCodeOf (carry.followers i)⟩, ?_⟩
  · exact ⟨by simpa [BootstrapCoordinatorRoundMeasurability.monitorCode] using carry.monitor.2.1,
      by simpa [BootstrapCoordinatorRoundMeasurability.monitorCode] using carry.monitor.2.2⟩
  · intro i
    cases h : carry.followers i with
    | bootstrap numerators lowerBound => simp [followerCarryCodeOf, h]
    | declared row activation configuration =>
        simpa [followerCarryCodeOf, h] using carry.activation_ready i

/-- Reconstruct the original `BlockCarry`; only the fixed real constants are
provided externally. -/
def blockCarryOfCode {p : Parameters} (rate : RateInput p)
    {block : Fin (n_boot p)} (C_star C_h : ℝ)
    (code : BlockCarryCode p rate block) :
    ActualInitializationRun.BlockCarry p rate block := by
  refine ⟨BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode p
      code.1.coordinator,
    ⟨BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p code.1.monitor.1,
      code.1.monitor.2⟩,
    C_star, C_h, fun i => followerCarryOfCode (code.1.followers i), ?_⟩
  intro i
  cases h : code.1.followers i with
  | inl numerators => simp [followerCarryOfCode]
  | inr declared => simpa [followerCarryOfCode, h] using code.2 i

/-- Encoding and decoding an existing carry with the fixed constants returns
that exact carry. -/
theorem blockCarryOfCode_encode {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (C_star C_h : ℝ)
    (carry : ActualInitializationRun.BlockCarry p rate block)
    (hstar : carry.C_star = C_star) (hh : carry.C_h = C_h) :
    blockCarryOfCode rate C_star C_h (blockCarryCodeOf carry) = carry := by
  cases carry with
  | mk coordinator monitor carriedStar carriedH followers activationReady =>
    cases monitor with
    | mk monitor hmonitor =>
      change carriedStar = C_star at hstar
      change carriedH = C_h at hh
      subst carriedStar
      subst carriedH
      simp only [blockCarryOfCode, blockCarryCodeOf,
        BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode_encode,
        BootstrapCoordinatorRoundMeasurability.monitorStateOfCode_encode,
        followerCarryOfCode_encode]

/-! ## Joint source and carried-input carrier -/

/-- The existing carry restricted to its two fixed manuscript constants. -/
abbrev FixedConstantsBlockCarry (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  {carry : ActualInitializationRun.BlockCarry p rate block //
    carry.C_star = C_star ∧ carry.C_h = C_h}

/-- The carried block state receives a local measurable structure pulled back
through its accepted literal code. All saved-real fibers keep the structures
already supplied by `IncomingConfiguration`. -/
instance fixedConstantsBlockCarryMeasurableSpace (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSpace (FixedConstantsBlockCarry p rate block C_star C_h) :=
  MeasurableSpace.comap (fun input => blockCarryCodeOf input.1) inferInstance

/-- Jointly vary the whole original source, including `J` and all private
arrays, and an actual existing carry, while keeping `C_star` and `C_h` fixed. -/
abbrev BlockInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  BootstrapPrivateRoundStreams.SourceInput p ×
    FixedConstantsBlockCarry p rate block C_star C_h

/-- Recover the existing carried state from the joint input. -/
def carriedBlockInput {p : Parameters} (rate : RateInput p)
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    ActualInitializationRun.BlockCarry p rate block :=
  input.2.1

/-- Encode the carried state as its existing accepted code. -/
def blockInputCodeOf {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    BootstrapPrivateRoundStreams.SourceInput p × BlockCarryCode p rate block :=
  (input.1, blockCarryCodeOf input.2.1)

/-- The joint source/carry code is measurable on its original product and
code-induced carry measurable spaces. -/
theorem measurable_blockInputCodeOf {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ} :
    Measurable (blockInputCodeOf (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h)) := by
  exact measurable_fst.prodMk ((comap_measurable _).comp measurable_snd)

/-- Decoding the accepted carry code recovers the exact original carry. -/
theorem blockCarryOf_blockInputCodeOf {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    blockCarryOfCode rate C_star C_h (blockInputCodeOf input).2 = input.2.1 :=
  blockCarryOfCode_encode C_star C_h input.2.1 input.2.2.1 input.2.2.2

/-! ## Accepted begin-block adapters -/

/-- The original three block-labelled private scalars at one source follower. -/
def sourceBlockScalars {p : Parameters} (block : Fin (n_boot p))
    (i : Fin (p.m - 1)) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    PrivateSourceStreams.BlockScalars :=
  source.2.1.1 block i

theorem measurable_sourceBlockScalars {p : Parameters} (block : Fin (n_boot p))
    (i : Fin (p.m - 1)) :
    Measurable (sourceBlockScalars block i :
      BootstrapPrivateRoundStreams.SourceInput p → PrivateSourceStreams.BlockScalars) := by
  exact (measurable_pi_apply i).comp <|
    (measurable_pi_apply block).comp <|
      (measurable_fst.comp (measurable_fst.comp measurable_snd))

/-- A bootstrap start state assembled from the already exposed finite
activity, held-arm, and private-ID draw values. -/
def bootstrapBeginStateFromDraw {p : Parameters} (block : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (draw : PrivateSourceStreams.BlockDraw p) :
    BootstrapObservedFollower.StartupState p block := by
  rcases draw with ⟨active, held, privateID⟩
  if hactive : active = true then
      exact {
        numerators := numerators
        numerators_lower_bound := lowerBound
        processed := ⟨0, BootstrapObservedFollower.zero_cursor_lt p block⟩
        blockCase := .active held privateID 0
          (BootstrapAllCandidateController.initialRegisters p)
        gain_le_processed := by simp [BootstrapObservedFollower.StartupBlockCase.gain] }
  else
      exact {
        numerators := numerators
        numerators_lower_bound := lowerBound
        processed := ⟨0, BootstrapObservedFollower.zero_cursor_lt p block⟩
        blockCase := .inactive
        gain_le_processed := by simp [BootstrapObservedFollower.StartupBlockCase.gain] }

/-- The explicit finite-key adapter is exactly the accepted local startup
`beginBlock`, including the inactive branch and the active held-arm/ID data. -/
theorem bootstrapBeginStateFromDraw_eq {p : Parameters} (block : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (scalars : PrivateSourceStreams.BlockScalars) :
    bootstrapBeginStateFromDraw block numerators lowerBound
        (PrivateSourceStreams.privateBlockDrawMap p numerators lowerBound scalars) =
      BootstrapObservedFollower.beginBlock p block numerators lowerBound scalars := by
  by_cases hactive : PrivateSourceStreams.activityScalarDraw p scalars.1 = true
  · simp [bootstrapBeginStateFromDraw, BootstrapObservedFollower.beginBlock,
      PrivateSourceStreams.privateBlockDrawMap, hactive]
  · simp [bootstrapBeginStateFromDraw, BootstrapObservedFollower.beginBlock,
      PrivateSourceStreams.privateBlockDrawMap, hactive]

/-- The bounded startup decoder is measurable on its countable accepted draw
carrier. -/
theorem measurable_bootstrapBeginStateFromDraw {p : Parameters}
    (block : Fin (n_boot p)) (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a) :
    Measurable (bootstrapBeginStateFromDraw block numerators lowerBound) :=
  measurable_of_countable _

/-- The actual bootstrap follower start is Borel in its original whole-source
coordinate. It reads only this follower's original block scalar triple. -/
theorem measurable_bootstrapBeginBlockSource {p : Parameters}
    (block : Fin (n_boot p)) (i : Fin (p.m - 1))
    (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      BootstrapObservedFollower.beginBlock p block numerators lowerBound
        (sourceBlockScalars block i source)) := by
  rw [show (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      BootstrapObservedFollower.beginBlock p block numerators lowerBound
        (sourceBlockScalars block i source)) =
      fun source => bootstrapBeginStateFromDraw block numerators lowerBound
        (PrivateSourceStreams.privateBlockDrawMap p numerators lowerBound
          (sourceBlockScalars block i source)) by
        funext source
        rw [bootstrapBeginStateFromDraw_eq]]
  exact (measurable_bootstrapBeginStateFromDraw block numerators lowerBound).comp <|
    (PrivateSourceStreams.measurable_privateBlockDrawMap p numerators lowerBound).comp
      (measurable_sourceBlockScalars block i)

/-- The exact started follower code for one original carry branch. -/
def beginFollowerCodeOfCarry {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (carry : ActualInitializationRun.FollowerCarry p rate) :
    ActualInitializationRoundMeasurability.FollowerCode p rate block :=
  ActualInitializationRoundMeasurability.followerCodeOfState p rate block
    (ActualInitializationRun.beginFollowerBlock p rate block source i carry)

/-- With the carry fixed, both the bootstrap start adapter and the preserved
declared ordinary/dagger code are measurable in the original source. -/
theorem measurable_beginFollowerCodeOfCarry {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) (i : Fin (p.m - 1))
    (carry : ActualInitializationRun.FollowerCarry p rate) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      beginFollowerCodeOfCarry block source i carry) := by
  cases carry with
  | bootstrap numerators lowerBound =>
      change Measurable (fun source =>
        Sum.inl (BootstrapObservedFollower.beginBlock p block numerators lowerBound
          (sourceBlockScalars block i source)))
      exact measurable_inl.comp
        (measurable_bootstrapBeginBlockSource block i numerators lowerBound)
  | declared row activation configuration =>
      exact measurable_const

/-- Decoding the started follower code returns the accepted source-order
`beginFollowerBlock`, including an unchanged declared ordinary/dagger state. -/
theorem beginFollowerCodeOfCarry_reconstructs {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (carry : ActualInitializationRun.FollowerCarry p rate) :
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block
      (beginFollowerCodeOfCarry block source i carry) =
      ActualInitializationRun.beginFollowerBlock p rate block source i carry := by
  cases carry with
  | bootstrap numerators lowerBound =>
      rfl
  | declared row activation configuration =>
      simp [beginFollowerCodeOfCarry,
        ActualInitializationRun.beginFollowerBlock,
        ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualInitializationRoundMeasurability.followerCodeOfState,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration]

/-- The accepted coordinator begin code is fed the original complete source,
the fixed constants, this block's original target scalar, and the exact
carried coordinator and monitor fields. -/
def coordinatorBeginBlockInputOfBlockInput {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorBeginBlockInput p :=
  ⟨BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p input.1 C_star C_h,
    block,
    BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p input.2.1.coordinator,
    ⟨BootstrapCoordinatorRoundMeasurability.monitorCode p input.2.1.monitor.1,
      by simpa [BootstrapCoordinatorRoundMeasurability.monitorCode] using
        input.2.1.monitor.2⟩,
    BootstrapPhysicalInput.coordinatorTargetScalarAt p block input.1.2⟩

/-- All coordinates of the accepted coordinator begin input are measurable on
the joint whole-source and actual-carry carrier. -/
theorem measurable_coordinatorBeginBlockInputOfBlockInput {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {C_star C_h : ℝ} :
    Measurable (coordinatorBeginBlockInputOfBlockInput
      (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h)) := by
  have hsource : Measurable (fun input : BlockInput p rate block C_star C_h => input.1) :=
    measurable_fst
  have hcode : Measurable (fun input : BlockInput p rate block C_star C_h =>
      blockCarryCodeOf input.2.1) :=
    (comap_measurable _).comp measurable_snd
  have hfields : Measurable (fun input : BlockInput p rate block C_star C_h =>
      (blockCarryCodeOf input.2.1).1) :=
    measurable_subtype_coe.comp hcode
  have hfieldsCoordinates : Measurable (fun input : BlockInput p rate block C_star C_h =>
      blockCarryCodeFieldsCoordinates ((blockCarryCodeOf input.2.1).1)) :=
    (comap_measurable _).comp hfields
  have hcoordinator : Measurable (fun input : BlockInput p rate block C_star C_h =>
      ((blockCarryCodeOf input.2.1).1).coordinator) :=
    measurable_fst.comp hfieldsCoordinates
  have hmonitor : Measurable (fun input : BlockInput p rate block C_star C_h =>
      ((blockCarryCodeOf input.2.1).1).monitor) :=
    measurable_fst.comp (measurable_snd.comp hfieldsCoordinates)
  have hbase := (BootstrapCoordinatorRoundMeasurability.measurable_selectedCoordinatorBase
    p C_star C_h).comp hsource
  have htarget := (BootstrapPhysicalInput.measurable_coordinatorTargetScalarAt p block).comp
    (measurable_snd.comp hsource)
  have hcoordinates : Measurable
      (BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockInputCoordinates p ∘
        coordinatorBeginBlockInputOfBlockInput
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h)) := by
    change Measurable (fun input : BlockInput p rate block C_star C_h =>
      Prod.mk (BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p
        input.1 C_star C_h)
        (Prod.mk block
          (Prod.mk (BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p
              input.2.1.coordinator)
            (Prod.mk
              (⟨BootstrapCoordinatorRoundMeasurability.monitorCode p input.2.1.monitor.1,
                by simpa [BootstrapCoordinatorRoundMeasurability.monitorCode] using
                  input.2.1.monitor.2⟩ : UnlaunchedMonitorCode p)
              (BootstrapPhysicalInput.coordinatorTargetScalarAt p block input.1.2)))))
    exact hbase.prodMk (measurable_const.prodMk
      (hcoordinator.prodMk (hmonitor.prodMk htarget)))
  exact (measurable_comap_iff).2 hcoordinates

/-- The actual coordinator returned by `R.beginBlock` is the reconstruction
of the accepted measurable begin code on this same input. -/
theorem reconstruct_actualBeginBlockCoordinator {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
      (BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
        (coordinatorBeginBlockInputOfBlockInput input)).1
      (BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
        (coordinatorBeginBlockInputOfBlockInput input)).2 =
      (ActualInitializationRun.beginBlock p rate block input.1 input.2.1).coordinator := by
  rw [BootstrapCoordinatorRoundMeasurability.reconstruct_coordinatorBeginBlockCode]
  simp [BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlock,
    coordinatorBeginBlockInputOfBlockInput,
    BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ActualInitializationRun.beginBlock,
    BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode_encode,
    BootstrapCoordinatorRoundMeasurability.monitorStateOfCode_encode,
    input.2.2.1, input.2.2.2]

/-- The source-dependent startup code at the actual initial carry is Borel in
the complete original source, including all private coordinates. -/
theorem measurable_initialCarryBeginFollowerCode {p : Parameters} {rate : RateInput p}
    (i : Fin (p.m - 1)) (C_star C_h : ℝ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      beginFollowerCodeOfCarry (ActualInitializationRun.firstBlock p) source i
        ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i)) :=
  measurable_beginFollowerCodeOfCarry (ActualInitializationRun.firstBlock p) i _

/-! ## Target output code shape -/

/-- Countable projection of the actual final continuation. The option retains
the no-launch versus launched tag and the actual launch trigger; the monitor
code retains every counter, crossing block, and launch position. -/
abbrev ContinuationCode (p : Parameters) :=
  Fin (n_boot p) × (Fin p.K ×
    (BootstrapCoordinatorRoundMeasurability.CoordinatorStateCode p ×
      (BootstrapCoordinatorRoundMeasurability.MonitorCode p × Option (Fin p.T))))

/-- The full countable output of the actual block-start adapter. -/
abbrev BlockStartCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p ×
    (Fin (p.m - 1) → ActualInitializationRoundMeasurability.FollowerCode p rate block)

/-- Project the unchanged countable fields of an actual coordinator
continuation. Its complete row, IDs, target-source scalar, and fixed constants
are decoded relative to the original source input. -/
def continuationCodeOf {p : Parameters}
    (phase : BootstrapCoordinatorLocalRound.Continuation p) : ContinuationCode p :=
  ((ActualInitializationRun.continuationData p phase).block,
    ((ActualInitializationRun.continuationData p phase).target,
      (BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p
        (BootstrapCoordinatorLocalRound.Continuation.coordinatorState phase),
        (BootstrapCoordinatorRoundMeasurability.monitorCode p
          (BootstrapCoordinatorLocalRound.Continuation.monitorState phase),
          match phase with
          | .prelaunch _ => none
          | .launched launch => some launch.triggerRound))))

/-- Target code shape for a clipped block's actual final continuation, all
heterogeneous follower successors, and chronological full round codes. -/
structure BlockFoldCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) where
  phase : ContinuationCode p
  followers : Fin (p.m - 1) → ActualInitializationRoundMeasurability.FollowerCode p rate block
  rounds : List (ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block)

/-- The same-step physical action and complete denominator-`D` feedback code.
The error tag is retained, so this projection does not discard an off-ready
branch. -/
def roundJointCode {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)}
    (code : ActualInitializationStepMeasurability.ActualRoundOutputCode
      p rate block) : Unit ⊕ ActualInitializationRoundMeasurability.JointPhysicalCode p :=
  Sum.elim (fun _ => Sum.inl ()) (fun successful => Sum.inr successful.2.1) code

/-- Chronological actions projected from the same full round-code list. -/
def BlockFoldCode.actions {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (code : BlockFoldCode p rate block C_star C_h) :
    List (Unit ⊕ FiniteBanditModel.ActionProfile p.m p.K) :=
  code.rounds.map fun round => Sum.elim (fun _ => Sum.inl ())
    (fun successful => Sum.inr successful.2.1.1) round

/-- Chronological full grid-feedback vectors projected from those same round
codes. -/
def BlockFoldCode.feedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (code : BlockFoldCode p rate block C_star C_h) :
    List (Unit ⊕ (Fin p.m → Fin (D p + 1))) :=
  code.rounds.map fun round => Sum.elim (fun _ => Sum.inl ())
    (fun successful => Sum.inr successful.2.1.2) round

/-! ## Actual block-start code and fixed-carry source measurability -/

/-- The lossless code of the actual `R.beginBlock`: its accepted coordinator
local code and every follower's exact source-order started state. The original
source is retained as the relative decoding input for the continuous fields. -/
def actualBeginBlockCodeOfInput {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    BlockStartCode p rate block :=
  ((BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
      (coordinatorBeginBlockInputOfBlockInput input)).2,
    fun i => beginFollowerCodeOfCarry block input.1 i (input.2.1.followers i))

/-- The block-start code reconstructs the exact coordinator and each actual
heterogeneous follower state returned by `R.beginBlock`. -/
theorem actualBeginBlockCodeOfInput_reconstructs {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : BlockInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
        (BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p
          input.1 C_star C_h)
        (actualBeginBlockCodeOfInput input).1 =
        (ActualInitializationRun.beginBlock p rate block input.1 input.2.1).coordinator ∧
      (∀ i, ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        ((actualBeginBlockCodeOfInput input).2 i) =
          (ActualInitializationRun.beginBlock p rate block input.1 input.2.1).followers i) := by
  constructor
  · simpa [actualBeginBlockCodeOfInput,
      BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode,
      coordinatorBeginBlockInputOfBlockInput,
      BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase] using
      reconstruct_actualBeginBlockCoordinator input
  · intro i
    simpa [actualBeginBlockCodeOfInput, ActualInitializationRun.beginBlock] using
      beginFollowerCodeOfCarry_reconstructs block input.1 i (input.2.1.followers i)

/-- With any fixed admissible existing carry, the actual block-start code is
Borel in the entire original source. No source coordinates are projected away. -/
theorem measurable_actualBeginBlockCodeOfFixedCarry {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (carry : ActualInitializationRun.BlockCarry p rate block)
    (hstar : carry.C_star = C_star) (hh : carry.C_h = C_h) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      actualBeginBlockCodeOfInput
        ((source, ⟨carry, hstar, hh⟩) : BlockInput p rate block C_star C_h)) := by
  let fixedInput : BootstrapPrivateRoundStreams.SourceInput p →
      BlockInput p rate block C_star C_h := fun source => (source, ⟨carry, hstar, hh⟩)
  have hfixedInput : Measurable fixedInput := measurable_id.prodMk measurable_const
  have hbeginInput :=
    (measurable_coordinatorBeginBlockInputOfBlockInput
      (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)).comp
      hfixedInput
  have hbeginCode :=
    (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorBeginBlockCode p).comp
      hbeginInput
  have hcoordinator : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
        (coordinatorBeginBlockInputOfBlockInput (fixedInput source))).2) :=
    measurable_snd.comp hbeginCode
  have hfollowers : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      fun i : Fin (p.m - 1) =>
        beginFollowerCodeOfCarry block source i (carry.followers i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_beginFollowerCodeOfCarry block i (carry.followers i)
  change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
    ((BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
        (coordinatorBeginBlockInputOfBlockInput (fixedInput source))).2,
      fun i : Fin (p.m - 1) =>
        beginFollowerCodeOfCarry block source i (carry.followers i)))
  exact hcoordinator.prodMk hfollowers

/-- The actual initial block-start code is Borel in the full original source,
including its original coordinator index and every private scalar array. -/
theorem measurable_actualInitialBlockStartCode {p : Parameters} {rate : RateInput p}
    (C_star C_h : ℝ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      actualBeginBlockCodeOfInput
        ((source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, ⟨rfl, rfl⟩⟩) :
          BlockInput p rate (ActualInitializationRun.firstBlock p) C_star C_h)) := by
  exact measurable_actualBeginBlockCodeOfFixedCarry
    (ActualInitializationRun.firstBlock p) C_star C_h
    (ActualInitializationRun.initialCarry p rate C_star C_h) rfl rfl

end Bandits.Support.ActualInitializationBlockMeasurability

end
