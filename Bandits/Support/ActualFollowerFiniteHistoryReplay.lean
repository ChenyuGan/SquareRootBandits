/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteFollowerOwnHistoryLocality
public import Bandits.Support.FiniteBoundedLocalHistoryCode

import Lean.Elab.Tactic.Omega

/-!
# Source-free finite-history replay for an actual follower

This module replays one follower's actual initialization protocol from its own
block triples, its own round scalars, the complete public table, and a finite
history of bounded grid observations. The replay retains the existing
bootstrap and declared follower codes, including the original queue, sparse
buffer, saved real coordinates, proposal memory, and ordinary or dagger
configuration. At a clipped-block boundary it uses the existing boundary
code and the run's original carry conversion.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:163-168`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.DeclaredFollowerObservationMeasurability
open Bandits.Support.ActualInitializationStepMeasurability
open Bandits.Support.ActualInitializationFollowerBoundaryMeasurability
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualCompletePhysicalHistory
open Bandits.Support.FiniteBoundedLocalHistoryCode

namespace Bandits.Support.ActualFollowerFiniteHistoryReplay

abbrev Parameters := ActualFollowerCalendarContinuity.Parameters
abbrev RateInput := ActualFollowerCalendarContinuity.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Published (p : Parameters) := CompletePublicTable.PublishedOutput p
abbrev Own (p : Parameters) :=
  PrivateSourceStreams.FollowerStream p ×
    BootstrapPrivateRoundStreams.PlayerRoundScalarStream p
abbrev HistoryCode (p : Parameters) (n : Nat) :=
  FiniteBoundedLocalHistoryCode.HistoryCode p n

variable {p : Parameters} {rate : RateInput p}

/-- Project exactly this follower's original private coordinates. -/
def ownProjection (p : Parameters) (source : SourceInput p)
    (i : Fin (p.m - 1)) : Own p :=
  ((fun block => source.2.1.1 block i),
    fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)

/-- The source's original private coordinates projected to this follower. -/
@[simp] theorem ownProjection_block (source : SourceInput p) (i : Fin (p.m - 1))
    (block : Fin (n_boot p)) : (ownProjection p source i).1 block = source.2.1.1 block i := rfl

@[simp] theorem ownProjection_scalar (source : SourceInput p) (i : Fin (p.m - 1))
    (t : Fin p.T) : (ownProjection p source i).2 t =
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) t := rfl

abbrev ReplayFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := ActualInitializationRoundMeasurability.FollowerCode p rate block

abbrev ReplayPreparedCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block

abbrev ReplayObservationCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := ActualInitializationStepMeasurability.FollowerObservationCode p rate block

abbrev ReplayLocalCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := ActualPostlaunchFollowerMeasurability.LocalCode (rate := rate) block

/-- Begin the existing follower state from its original carry and only its
own block triple. -/
def beginCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (own : Own p) (carry : ActualInitializationRun.FollowerCarry p rate) :
    ReplayFollowerCode p rate block :=
  match carry with
  | .bootstrap numerators lowerBound =>
      .inl (BootstrapObservedFollower.beginBlock p block numerators lowerBound (own.1 block))
  | .declared row activation configuration =>
      .inr (row, (activation,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration))

/-- The initial follower state is the original initialization carry. -/
def initialReplayCode (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (own : Own p) :
    ReplayFollowerCode p rate (ActualInitializationRun.firstBlock p) :=
  beginCode p rate (ActualInitializationRun.firstBlock p) own
    ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i)

/-- The original begin-block adapter decodes to the run's actual
`beginFollowerBlock` when the supplied triple is the source's own triple. -/
theorem beginCode_state_eq (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : SourceInput p) (own : Own p)
    (i : Fin (p.m - 1)) (carry : ActualInitializationRun.FollowerCarry p rate)
    (htriple : source.2.1.1 block i = own.1 block) :
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (beginCode p rate block own carry) =
      ActualInitializationRun.beginFollowerBlock p rate block source i carry := by
  cases carry with
  | bootstrap numerators lowerBound =>
      simp [beginCode, ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualInitializationRun.beginFollowerBlock, htriple]
  | declared row activation configuration =>
      simp [beginCode, ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualInitializationRun.beginFollowerBlock,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration]

/-- A block-start code satisfies the genuine zero-cursor invariant whenever
the original carry activation bound is met. -/
theorem beginCode_cursor_zero (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (own : Own p)
    (carry : ActualInitializationRun.FollowerCarry p rate)
    (hready : match carry with
      | .bootstrap _ _ => True
      | .declared _ activation _ => activation.val ≤ BootstrapObservedFollower.blockStart p block + 1) :
    ActualInitializationRun.followerAtCursor p rate block 0
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (beginCode p rate block own carry)) := by
  cases carry with
  | bootstrap numerators lowerBound =>
      change (BootstrapObservedFollower.beginBlock p block numerators lowerBound
        (own.1 block)).processed.val = 0
      simp only [BootstrapObservedFollower.beginBlock]
      split_ifs <;> rfl
  | declared row activation configuration =>
      change activation.val ≤ BootstrapObservedFollower.blockStart p block + 0 + 1
      simpa using hready

/-- Apply the public boundary output code and the run's original carry
conversion to one replay successor. -/
def carryFromFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (code : ReplayFollowerCode p rate block) :
    ActualInitializationRun.FollowerCarry p rate :=
  ActualInitializationRun.followerCarryOfBoundaryOutput rate
    (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
      (ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
        p rate block code))

/-- A completed nonfinal replay cursor makes the original boundary carry
ready at the next block start. -/
theorem carryFromFollowerCode_ready (p : Parameters) (rate : RateInput p)
    (block next : Fin (n_boot p)) (code : ReplayFollowerCode p rate block)
    (hcomplete : ActualInitializationRun.followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code))
    (hnext : next.val = block.val + 1)
    (hstop : BootstrapObservedFollower.blockStop p block =
      BootstrapObservedFollower.blockStart p next) :
    match carryFromFollowerCode p rate block code with
    | .bootstrap _ _ => True
    | .declared _ activation _ =>
        activation.val ≤ BootstrapObservedFollower.blockStart p next + 1 := by
  unfold carryFromFollowerCode
  rw [ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode_reconstruction]
  cases code with
  | inl startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp [ActualInitializationRoundMeasurability.followerStateOfCode,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpending]
      | some row =>
          have hactivation := ActualInitializationHorizon.nextActivationRound_eq_successor_start
            block next hnext
          simpa [ActualInitializationRoundMeasurability.followerStateOfCode,
            ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpending] using
              le_of_eq hactivation
  | inr fields =>
      have hactivation : fields.2.1.val ≤
          BootstrapObservedFollower.blockStart p block +
            BootstrapObservedFollower.blockLength p block + 1 := by
        simpa [ActualInitializationRun.followerAtCursor,
          ActualInitializationRoundMeasurability.followerStateOfCode] using hcomplete
      rw [ActualInitializationRun.blockStart_add_length_eq_stop p block] at hactivation
      rw [hstop] at hactivation
      simpa [ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualInitializationRun.followerCarryAtBlockBoundary,
        ActualInitializationRun.followerCarryOfBoundaryOutput,
        ActualInitializationRun.boundaryOutputFromFollower]
        using hactivation

/-- Transport the existing cursor invariant along casts of a block and a
cursor index. -/
theorem followerAtCursor_cast {p : Parameters} {rate : RateInput p}
    {block block' : Fin (n_boot p)} {cursor cursor' : Nat}
    (eblock : block = block') (ecursor : cursor = cursor')
    (state : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor state) :
    ActualInitializationRun.followerAtCursor p rate block' cursor'
      (cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) eblock) state) := by
  cases eblock
  cases ecursor
  exact hstate

/-- The existing follower decoder commutes with transport along an equality of
block indices. -/
theorem followerStateOfCode_cast {p : Parameters} {rate : RateInput p}
    {block block' : Fin (n_boot p)} (eblock : block = block')
    (code : ReplayFollowerCode p rate block) :
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block'
      (cast (congrArg (ReplayFollowerCode p rate) eblock) code) =
    cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) eblock)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code) := by
  cases eblock
  rfl

/-- The existing DOWN decoder batch is recovered exactly from its code. -/
theorem decoderBatchCode_decoderBatchOfCode {p : Parameters}
    (batch : FollowerDownMeasurability.DecoderBatchCode p) :
    FollowerDownMeasurability.decoderBatchCode
      (FollowerDownMeasurability.decoderBatchOfCode batch) = batch := by
  rcases batch with ⟨pending, completed⟩
  simp [FollowerDownMeasurability.decoderBatchCode,
    FollowerDownMeasurability.decoderBatchOfCode,
    FollowerDownMeasurability.decoderEntryCode,
    FollowerDownMeasurability.decoderEntryOfCode,
    List.map_map, Function.comp_def]

/-- Splitting an original sparse buffer into its discrete skeleton and
saved-real stream, then rebuilding it, preserves both coded projections. -/
theorem bufferCodes_ofFn {p : Parameters} {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧
      HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values).length = n := List.length_ofFn
  constructor
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].calendarRound,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].pilot) = _
    simp only [List.getElem_ofFn]
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].observation,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].thinScalar) = _
    simp only [List.getElem_ofFn]

/-- Re-encoding a reconstructed carried follower recovers its exact original
countable state, sparse buffer skeleton, and saved real coordinates. -/
theorem carriedStateOfReconstruction_eq {p : Parameters} {rate : RateInput p}
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
    FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        carry.1 carry.2) = carry := by
  cases carry with
  | mk index values =>
    rcases index with ⟨code, ⟨length, skeleton⟩⟩
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values
    have hcode : FollowerDownMeasurability.followerStateCode rate
        (FollowerDownMeasurability.followerStateOfCode rate code buffer) = code := by
      cases code with
      | mk lastDown score lastService backlog status batch failed =>
        fin_cases status <;>
          simp [FollowerDownMeasurability.followerStateCode,
            FollowerDownMeasurability.followerStateOfCode,
            FollowerDownMeasurability.followerStatusCode,
            FollowerDownMeasurability.followerStatusOfCode,
            decoderBatchCode_decoderBatchOfCode]
    have hlength : buffer.length = length := by
      simp [buffer, FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
    have hbuffer := bufferCodes_ofFn (p := p) skeleton values
    have hskeleton : HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer)
        skeleton := by
      simpa only [buffer] using hbuffer.1
    have hvalues : HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer)
        values := by
      simpa only [buffer] using hbuffer.2
    have hindex :
        (FollowerDownMeasurability.followerStateCode rate
          (FollowerDownMeasurability.followerStateOfCode rate code buffer),
          (⟨buffer.length, FollowerDownJointMeasurability.bufferSkeletonCode buffer⟩ :
            Sigma fun n => FollowerDownJointMeasurability.BufferSkeletonCode p n)) =
        (code, (⟨length, skeleton⟩ :
          Sigma fun n => FollowerDownJointMeasurability.BufferSkeletonCode p n)) :=
      Prod.ext hcode (Sigma.ext hlength hskeleton)
    simp only [FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState]
    exact Sigma.ext hindex hvalues

/-- The ordinary/dagger incoming code is an exact two-sided encoding of the
original follower configuration, including its saved real buffer fibres. -/
theorem incomingOfLocalConfiguration_localConfigurationOfIncoming
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming) =
      incoming := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨carry, memory⟩
    simp only [FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration]
    rw [FollowerLifecycleMeasurability.localMemoryCodeOfCode,
      carriedStateOfReconstruction_eq]

/-- Assemble the original bootstrap PREPARE arm from the startup code, public
IDs, local time, and this follower's current private scalar. -/
def prepareBootstrap (p : Parameters) (block : Fin (n_boot p))
    (startup : BootstrapObservedFollower.StartupState p block)
    (pub : CompletePublicTable.PublishedOutput p) (time : Fin p.T) (u : Scalar) : Fin p.K :=
  ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents block
    (startup, (pub.1, (time, u)))

/-- The exact source-free PREPARE code for one cursor state. -/
def prepareCodeFor (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (own : Own p)
    (pub : CompletePublicTable.PublishedOutput p) (time : Fin p.T)
    (state : ReplayFollowerCode p rate block)
    (valid : match state with
      | .inl _ => True
      | .inr fields => fields.2.1.val ≤ time.val + 1) : ReplayPreparedCode p rate block := by
  cases state with
  | inl startup =>
      exact .inl (startup, prepareBootstrap p block startup pub time (own.2 time))
  | inr fields =>
      let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          fields.2.1 fields.2.2 (pub.2 fields.1) time valid)
      exact .inr (fields.1, (fields.2.1, (output.2.2.1, output.2.2.2)))

/-- Run the original bootstrap OBSERVE operation on one typed grid value. -/
def observeBootstrap (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (startup : BootstrapObservedFollower.StartupState p block)
    (pub : CompletePublicTable.PublishedOutput p) (time : Fin p.T)
    (hready : ActualInitializationPhysicalStep.followerAtNextCursor (rate := rate) time
      (.bootstrap startup)) (y : Fin (D p + 1)) : ReplayObservationCode p rate block := by
  rcases hready with ⟨hin, hopen, hnext⟩
  exact .inl (.accepted (BootstrapObservedFollower.observeOne p block startup
    pub.1 pub.2 time (ActualInitializationPhysicalStep.observationOfGrid p y)
    hin hopen hnext))

/-- Run PREPARE and OBSERVE using only the existing follower code, the full
public table, one current private scalar, and its supplied grid value. -/
def localCodeAtScalar (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : CompletePublicTable.PublishedOutput p) (u : Scalar)
    (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) : ReplayLocalCode p rate block := by
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
  cases state with
  | inl startup =>
      have hs' : ActualInitializationRun.followerAtCursor p rate block cursor
          (ActualInitializationPhysicalStep.FollowerState.bootstrap (rate := rate) startup) := by
        simpa [ActualInitializationRoundMeasurability.followerStateOfCode] using hs
      let prepared : ReplayPreparedCode p rate block :=
        .inl (startup, prepareBootstrap p block startup pub time u)
      have hready := ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
        (rate := rate) hc ⟨.bootstrap startup, hs'⟩
      let observed := observeBootstrap p rate block startup pub time hready y
      let partialCode := ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput
        rate block (prepared, observed)
      have hpartial : partialCode ∈ Set.range Sum.inr := by
        simp [partialCode, prepared, observed, observeBootstrap,
          ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput]
      let successor := Equiv.Set.rangeInr _ _ ⟨partialCode, hpartial⟩
      exact (prepared, (observed, successor))

  | inr fields =>
      have hbound := hs
      simp [ActualInitializationRun.followerAtCursor,
        ActualInitializationRoundMeasurability.followerStateOfCode] at hbound
      have hcursor : fields.2.1.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1 := by
        simpa using hbound
      have hvalid : fields.2.1.val ≤ time.val + 1 := by
        simpa [time, ActualPostlaunchFollowerMeasurability.localTime,
          ActualInitializationRun.blockTime] using hcursor
      let preparedOutput := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          fields.2.1 fields.2.2 (pub.2 fields.1) time hvalid)
      let prepared : ReplayPreparedCode p rate block :=
        .inr (fields.1, (fields.2.1, (preparedOutput.2.2.1, preparedOutput.2.2.2)))
      let observed : ReplayObservationCode p rate block := .inr
        (DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
          rate i (fun _ : Unit => fields.2.1)
          (fun _ => preparedOutput.2.2.2) (fun _ => pub.2 fields.1)
          (fun _ => time) (fun _ => preparedOutput.2.2.1) (fun _ => y)
          (by intro _; exact hvalid) ())
      let partialCode := ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput
        rate block (prepared, observed)
      have hpartial : partialCode ∈ Set.range Sum.inr := by
        simp [partialCode, observed, prepared,
          ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput]
      let successor := Equiv.Set.rangeInr _ _ ⟨partialCode, hpartial⟩
      exact (prepared, (observed, successor))

/-- Project only the private scalar at this cursor into the literal local operation. -/
def localCode (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Own p) (pub : Published p) (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) : ReplayLocalCode p rate block :=
  localCodeAtScalar p rate i block cursor hc pub
    (own.2 (ActualPostlaunchFollowerMeasurability.localTime block cursor hc)) state hs y

/-- The source-free PREPARE/OBSERVE code is the original local code after
replacing its source reads by this follower's literal projections. -/
theorem localCodeAtScalar_eq_actualLocalCode (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Published p) (u : Scalar) (source : SourceInput p)
    (hpublic : source.1 = pub)
    (hscalar : u =
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hc))
    (code : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code))
    (y : Fin (D p + 1)) :
    localCodeAtScalar p rate i block cursor hc pub u code hs y =
      ActualPostlaunchFollowerMeasurability.localCodeOnCursor (rate := rate) hc i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents (rate := rate)
          source (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code)
          hs y) := by
  classical
  cases code with
  | inl startup =>
      let x := ActualPostlaunchFollowerMeasurability.localInputOfComponents
        (rate := rate) source
        (ActualInitializationPhysicalStep.FollowerState.bootstrap (rate := rate) startup)
        hs y
      have hmem : x ∈ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x ∈ Set.range Sum.inl
        simp [x, ActualPostlaunchFollowerMeasurability.localInputOfComponents,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      have hx : (source, (⟨FollowerState.bootstrap startup, hs⟩, y)) ∈
          ActualPostlaunchFollowerMeasurability.bootstrapLocalSet (rate := rate) := by
        simpa [x, ActualPostlaunchFollowerMeasurability.localInputOfComponents] using hmem
      have hstartup' : ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap
          (rate := rate) ⟨(source, (⟨FollowerState.bootstrap startup, hs⟩, y)), hx⟩ = startup := by
        simp [ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      have hready := ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
        (rate := rate) hc ⟨.bootstrap startup, hs⟩
      rcases hready with ⟨hin, hopen, hnext⟩
      have hobs : BootstrapObservedFollower.observe p block startup pub.1 pub.2
          (ActualPostlaunchFollowerMeasurability.localTime block cursor hc)
          (ActualInitializationPhysicalStep.observationOfGrid p y) =
          .accepted (BootstrapObservedFollower.observeOne p block startup pub.1 pub.2
            (ActualPostlaunchFollowerMeasurability.localTime block cursor hc)
            (ActualInitializationPhysicalStep.observationOfGrid p y) hin hopen hnext) :=
        BootstrapObservedFollower.observe_accepted_processed p block startup pub.1 pub.2
          (ActualPostlaunchFollowerMeasurability.localTime block cursor hc)
          (ActualInitializationPhysicalStep.observationOfGrid p y) hin hopen hnext
      simp [localCodeAtScalar, prepareBootstrap, observeBootstrap,
        ActualPostlaunchFollowerMeasurability.localCodeOnCursor,
        ActualPostlaunchFollowerMeasurability.localInputOfComponents,
        ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
        hx,
        ActualPostlaunchFollowerMeasurability.preparedCodeOnBootstrap,
        hstartup',
        ActualPostlaunchFollowerMeasurability.observationCodeOnCursor,
        ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor,
        ActualPostlaunchFollowerMeasurability.successorCodeOnCursor,
        ActualPostlaunchFollowerMeasurability.partialSuccessorCodeOnCursor,
        ActualPostlaunchFollowerMeasurability.localSource,
        ActualPostlaunchFollowerMeasurability.localFeedback,
        ActualBootstrapObservationCode.sourceIDs, ActualBootstrapObservationCode.sourceRows,
        ActualBootstrapObservationCode.sourcePrivate,
        ActualInitializationRoundMeasurability.followerStateOfCode,
        hobs,
        hpublic, hscalar]
  | inr fields =>
      have hrows : ActualBootstrapObservationCode.sourceRows p source = pub.2 := by
        change source.1.2 = pub.2
        exact congrArg Prod.snd hpublic
      have hstateEq : ActualInitializationRoundMeasurability.followerStateOfCode
          p rate block (.inr fields) =
          ActualInitializationPhysicalStep.FollowerState.declared fields.1 fields.2.1
            (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2) := by
        simp [ActualInitializationRoundMeasurability.followerStateOfCode]
      have hsDirect : ActualInitializationRun.followerAtCursor p rate block cursor
          (ActualInitializationPhysicalStep.FollowerState.declared fields.1 fields.2.1
            (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2)) := by
        rw [← hstateEq]
        exact hs
      let replayState : ActualInitializationPhysicalStep.FollowerState p rate block :=
        ActualInitializationPhysicalStep.FollowerState.declared fields.1 fields.2.1
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2)
      let x : ActualPostlaunchFollowerMeasurability.LocalInput
          (rate := rate) block cursor := (source, (⟨replayState, hsDirect⟩, y))
      have hnot : x ∉ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
          (rate := rate) := by
        change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x ∉ Set.range Sum.inl
        simp [x, ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState,
          replayState,
          incomingOfLocalConfiguration_localConfigurationOfIncoming]
      have hx : (source, (⟨replayState, hsDirect⟩,
          y)) ∈ (ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
            (rate := rate))ᶜ := by
        change (source, (⟨replayState, hsDirect⟩, y)) ∉
          ActualPostlaunchFollowerMeasurability.bootstrapLocalSet (rate := rate)
        simpa [x] using hnot
      have hstatecode : ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) x = Sum.inr fields := by
        simp [x,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          replayState,
          ActualInitializationRoundMeasurability.followerCodeOfState,
          incomingOfLocalConfiguration_localConfigurationOfIncoming]
      have hstatecode' : ActualPostlaunchFollowerMeasurability.localFollowerStateCode
          (rate := rate) (source, (⟨replayState, hsDirect⟩, y)) =
          Sum.inr fields := by
        simp [
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          replayState,
          ActualInitializationRoundMeasurability.followerCodeOfState,
          incomingOfLocalConfiguration_localConfigurationOfIncoming]
      have hrow : ActualBootstrapObservationCode.sourceRows p source fields.1 =
          pub.2 fields.1 := congrFun hrows fields.1
      let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
      have hactivationBound : fields.2.1.val ≤ time.val + 1 := by
        have hb := hsDirect
        simp [ActualInitializationRun.followerAtCursor] at hb
        simpa [time, ActualPostlaunchFollowerMeasurability.localTime,
          ActualInitializationRun.blockTime] using hb
      let preparedOutput := FollowerVaryingActivationMeasurability.varyingPreparedOutput
        rate i (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          fields.2.1 fields.2.2 (pub.2 fields.1) time hactivationBound)
      let prepared : ReplayPreparedCode p rate block :=
        .inr (fields.1, (fields.2.1,
          (preparedOutput.2.2.1, preparedOutput.2.2.2)))
      have hpreparedSource : (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).1 = prepared := by
        simp [localCodeAtScalar,  time, prepared, preparedOutput,
          ActualPostlaunchFollowerMeasurability.localTime,
          ActualInitializationRun.blockTime]
      let actualValid := ActualPostlaunchFollowerMeasurability.declaredActivation_le_time_of_code
        (rate := rate) hc (source, (⟨replayState, hsDirect⟩, y)) fields hstatecode'
      have houtputEq : FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            fields.2.1
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2))
            (ActualBootstrapObservationCode.sourceRows p source fields.1)
            (ActualPostlaunchFollowerMeasurability.localTime block cursor hc) actualValid) =
          preparedOutput := by
        rw [incomingOfLocalConfiguration_localConfigurationOfIncoming, hrow]
      have hpreparedActual : ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
          (rate := rate) hc i x = prepared := by
        simp only [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
          dite_eq_right hnot]
        unfold ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared
        dsimp only [x, ActualPostlaunchFollowerMeasurability.localInputOfComponents,
          ActualPostlaunchFollowerMeasurability.localSource]
        simp [ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState,
          replayState]
        rw [houtputEq]
      let observed := Bandits.Support.DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
        rate i (fun _ : Unit => fields.2.1)
        (fun _ => preparedOutput.2.2.2) (fun _ => pub.2 fields.1)
        (fun _ => time) (fun _ => preparedOutput.2.2.1)
        (fun _ => y) (fun _ => hactivationBound) ()
      have hobservedSource : (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).2.1 = Sum.inr observed := by
        simp [localCodeAtScalar, time, preparedOutput, observed,
          ActualPostlaunchFollowerMeasurability.localTime,
          ActualInitializationRun.blockTime]
      have hobservedActual : ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
          (rate := rate) hc i x = Sum.inr observed := by
        simp only [ActualPostlaunchFollowerMeasurability.observationCodeOnCursor,
          dite_eq_right hnot]
        unfold ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
        dsimp only [x, ActualPostlaunchFollowerMeasurability.localInputOfComponents,
          ActualPostlaunchFollowerMeasurability.localSource,
          ActualPostlaunchFollowerMeasurability.localFeedback]
        simp [ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement,
          ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState,
          replayState]
        rw [houtputEq, hrow]
      have hprepared : (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).1 =
        ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
          (rate := rate) hc i x := hpreparedSource.trans hpreparedActual.symm
      have hobserved : (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).2.1 =
        ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
          (rate := rate) hc i x := hobservedSource.trans hobservedActual.symm
      have hpair : ((localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).1, (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).2.1) =
          (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
            (rate := rate) hc i x,
            ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
              (rate := rate) hc i x) := Prod.ext hprepared hobserved
      have hpartial := congrArg
        (fun z => ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput
          rate block z) hpair
      have hsuccessor : (localCodeAtScalar p rate i block cursor hc pub u
          (.inr fields) hs y).2.2 =
        ActualPostlaunchFollowerMeasurability.successorCodeOnCursor
          (rate := rate) hc i x := by
        simpa [localCodeAtScalar, ActualPostlaunchFollowerMeasurability.successorCodeOnCursor,
          ActualPostlaunchFollowerMeasurability.partialSuccessorCodeOnCursor] using hpartial
      simp only [ActualPostlaunchFollowerMeasurability.localCodeOnCursor]
      exact Prod.ext hprepared (Prod.ext hobserved hsuccessor)

/-- The own-stream adapter has the same source comparison, with its one
current-scalar equality stated explicitly. -/
theorem localCode_eq_actualLocalCode (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Own p) (pub : Published p) (source : SourceInput p)
    (hpublic : source.1 = pub)
    (hscalar : own.2 (ActualPostlaunchFollowerMeasurability.localTime block cursor hc) =
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hc))
    (code : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code))
    (y : Fin (D p + 1)) :
    localCode p rate i block cursor hc own pub code hs y =
      ActualPostlaunchFollowerMeasurability.localCodeOnCursor (rate := rate) hc i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents (rate := rate)
          source (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code)
          hs y) :=
  localCodeAtScalar_eq_actualLocalCode p rate i block cursor hc pub _ source
    hpublic hscalar code hs y

/-- Every supplied grid value advances the genuine follower cursor by one. -/
theorem localCodeAtScalar_successor_cursor (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : CompletePublicTable.PublishedOutput p) (u : Scalar)
    (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (localCodeAtScalar p rate i block cursor hc pub u state hs y).2.2) := by
  cases state with
  | inl startup =>
      have hprocessed : startup.processed.val = cursor := by
        simpa [ActualInitializationRun.followerAtCursor,
          ActualInitializationRoundMeasurability.followerStateOfCode] using hs
      simp [localCodeAtScalar, prepareBootstrap, observeBootstrap,
        ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput,
        ActualInitializationRun.followerAtCursor,
        ActualInitializationRoundMeasurability.followerStateOfCode,
        BootstrapObservedFollower.observe_accepted_cursor, hprocessed]
  | inr fields =>
      have hactivation : fields.2.1.val ≤
          BootstrapObservedFollower.blockStart p block + cursor + 1 := by
        simpa [ActualInitializationRun.followerAtCursor,
          ActualInitializationRoundMeasurability.followerStateOfCode] using hs
      simp [localCodeAtScalar, ActualInitializationRun.followerAtCursor,
        ActualInitializationRoundMeasurability.followerStateOfCode]
      calc
        fields.2.1.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1 := hactivation
        _ ≤ BootstrapObservedFollower.blockStart p block + (cursor + 1) + 1 := by omega

/-- The own-stream projection inherits the scalar operation's cursor proof. -/
theorem localCode_successor_cursor (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Own p) (pub : Published p) (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (localCode p rate i block cursor hc own pub state hs y).2.2) :=
  localCodeAtScalar_successor_cursor p rate i block cursor hc pub _ state hs y

open Classical in
/-- A pending declaration freezes candidate registers while the actual
positive-stay gain continues. The boundary weight observable uses that successor,
even when its pending declaration will discard the weights on activation. -/
theorem localCodeAtScalar_bootstrap_pending (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Published p) (u : Scalar) (startup : BootstrapObservedFollower.StartupState p block)
    (hs : startup.processed.val = cursor) (y : Fin (D p + 1))
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hcase : startup.blockCase = .active held privateID gain registers)
    (hpending : registers.pending.isSome = true) :
    let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
    let ready := ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
      (rate := rate) hc ⟨ActualInitializationPhysicalStep.FollowerState.bootstrap startup, hs⟩
    let next := BootstrapObservedFollower.observeOne p block startup pub.1 pub.2 time
      (ActualInitializationPhysicalStep.observationOfGrid p y) ready.1 ready.2.1 ready.2.2
    let out := localCodeAtScalar p rate i block cursor hc pub u (.inl startup) hs y
    out.2.2 = Sum.inl next ∧
      next.blockCase = .active held privateID
        (if BootstrapObservedFollower.positiveStay pub.1 privateID time
          (ActualInitializationPhysicalStep.observationOfGrid p y) then gain + 1 else gain)
        registers ∧
      next.blockCase.gain =
        (if BootstrapObservedFollower.positiveStay pub.1 privateID time
          (ActualInitializationPhysicalStep.observationOfGrid p y) then gain + 1 else gain) ∧
      ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
        p rate block out.2.2 = some (BootstrapObservedFollower.updatedNumerators p block next) := by
  dsimp only
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
  have ready := ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
    (rate := rate) hc ⟨ActualInitializationPhysicalStep.FollowerState.bootstrap startup, hs⟩
  let next := BootstrapObservedFollower.observeOne p block startup pub.1 pub.2 time
    (ActualInitializationPhysicalStep.observationOfGrid p y) ready.1 ready.2.1 ready.2.2
  have hcode : (localCodeAtScalar p rate i block cursor hc pub u (.inl startup) hs y).2.2 =
      Sum.inl next := by
    simp [localCodeAtScalar, observeBootstrap, next, time,
      ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput]
  refine ⟨hcode, ?_, ?_, ?_⟩
  · exact BootstrapObservedFollower.observeOne_pending_persists
      p block startup pub.1 pub.2 _ _ _ _ _ held privateID gain registers hcase hpending
  · exact BootstrapObservedFollower.observeOne_active_gain_eq
      p block startup pub.1 pub.2 _ _ _ _ _ held privateID gain registers hcase
  · rw [hcode]
    rfl

/-- The separate weight observable retains the original bootstrap update on
both pending and nonpending states; declared inputs have already discarded it. -/
theorem boundaryUpdatedNumeratorsCode_eq (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (code : ReplayFollowerCode p rate block) :
    ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
        p rate block code =
      match ActualInitializationRoundMeasurability.followerStateOfCode p rate block code with
      | .bootstrap startup => some (BootstrapObservedFollower.updatedNumerators p block startup)
      | .declared _ _ _ => none := by
  cases code <;> rfl

/-- Pure calendar arithmetic for consecutive rounds. A block change occurs
only at the clipped endpoint, and the next round starts at cursor zero. -/
theorem calendar_successor_geometry (p : Parameters)
    (t u : Fin p.T) (hnext : u.val = t.val + 1) :
    if ActualFollowerCalendarContinuity.calendarBlockIndex t =
        ActualFollowerCalendarContinuity.calendarBlockIndex u then
      ActualFollowerCalendarContinuity.calendarCursor u =
        ActualFollowerCalendarContinuity.calendarCursor t + 1
    else
      (ActualFollowerCalendarContinuity.calendarBlockIndex t).val + 1 =
          (ActualFollowerCalendarContinuity.calendarBlockIndex u).val ∧
        t.val + 1 = BootstrapObservedFollower.blockStop p
          (ActualFollowerCalendarContinuity.calendarBlockIndex t) ∧
        u.val = BootstrapObservedFollower.blockStart p
          (ActualFollowerCalendarContinuity.calendarBlockIndex u) ∧
        ActualFollowerCalendarContinuity.calendarCursor t + 1 =
          BootstrapObservedFollower.blockLength p
            (ActualFollowerCalendarContinuity.calendarBlockIndex t) ∧
        ActualFollowerCalendarContinuity.calendarCursor u = 0 := by
  classical
  let q := t.val / B_boot p
  let q' := u.val / B_boot p
  have hqle : q ≤ q' := by
    dsimp [q, q']
    exact Nat.div_le_div_right (by omega)
  have hquotientBound : t.val < (q + 1) * B_boot p := by
    dsimp [q]
    have hmod := Nat.mod_lt t.val (Nat.pos_of_ne_zero (Nat.ne_of_gt (B_boot_pos p)))
    have hdecomp := Nat.div_add_mod' t.val (B_boot p)
    calc
      t.val = (t.val / B_boot p) * B_boot p + t.val % B_boot p := hdecomp.symm
      _ < (t.val / B_boot p) * B_boot p + B_boot p := by omega
      _ = (t.val / B_boot p + 1) * B_boot p := by
        rw [Nat.add_mul, one_mul]
  have huBound : u.val < (q + 2) * B_boot p := by
    have hboundary : u.val ≤ (q + 1) * B_boot p := by
      rw [hnext]
      exact Nat.succ_le_of_lt hquotientBound
    have hrewrite : (q + 2) * B_boot p = (q + 1) * B_boot p + B_boot p := by
      rw [show q + 2 = (q + 1) + 1 by omega, Nat.add_mul, one_mul]
    rw [hrewrite]
    exact Nat.lt_of_le_of_lt hboundary (Nat.lt_add_of_pos_right (B_boot_pos p))
  have hqUpper : q' < q + 2 := by
    apply (Nat.div_lt_iff_lt_mul
      (Nat.pos_of_ne_zero (Nat.ne_of_gt (B_boot_pos p)))).2
    exact huBound
  by_cases e : ActualFollowerCalendarContinuity.calendarBlockIndex t =
      ActualFollowerCalendarContinuity.calendarBlockIndex u
  · have hcursorEq : q = q' := by
      have hv := congrArg Fin.val e
      simpa [ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q, q'] using hv
    simp only [ite_eq_left e]
    have hblockVal := congrArg Fin.val e
    have hstart : BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) =
        BootstrapObservedFollower.blockStart p
          (ActualFollowerCalendarContinuity.calendarBlockIndex u) :=
      congrArg (BootstrapObservedFollower.blockStart p) e
    have hblockVal : (ActualFollowerCalendarContinuity.calendarBlockIndex u).val =
        (ActualFollowerCalendarContinuity.calendarBlockIndex t).val :=
      (congrArg Fin.val e).symm
    have hmem := BootstrapDimensions.round_mem_quotient_block p t
    have hstartle := (BootstrapDimensions.mem_calendarBlock_iff p
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) t).mp hmem |>.1
    change BootstrapObservedFollower.blockStart p
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) ≤ t.val at hstartle
    simp only [BootstrapObservedFollower.blockStart] at hstartle
    change u.val -
        BootstrapObservedFollower.blockStart p
          (ActualFollowerCalendarContinuity.calendarBlockIndex u) =
      t.val - BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) + 1
    simp only [
      BootstrapObservedFollower.blockStart]
    rw [hblockVal]
    omega
  · have hqne : q ≠ q' := by
      intro h
      apply e
      apply Fin.ext
      simpa [ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q, q'] using h
    have hqnext : q' = q + 1 := by omega
    have hprevMem := (BootstrapDimensions.mem_calendarBlock_iff p
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) t).mp
      (BootstrapDimensions.round_mem_quotient_block p t)
    have hnextMem := (BootstrapDimensions.mem_calendarBlock_iff p
      (ActualFollowerCalendarContinuity.calendarBlockIndex u) u).mp
      (BootstrapDimensions.round_mem_quotient_block p u)
    change BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) ≤ t.val ∧
      t.val < BootstrapObservedFollower.blockStop p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) at hprevMem
    change BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) ≤ u.val ∧
      u.val < BootstrapObservedFollower.blockStop p
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) at hnextMem
    have hstartPrev : BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) = q * B_boot p := by
      simp [BootstrapObservedFollower.blockStart,
        ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q]
    have hstartNext : BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) = (q + 1) * B_boot p := by
      simp [BootstrapObservedFollower.blockStart,
        ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q', hqnext]
    have huBoundary : u.val = (q + 1) * B_boot p := by
      have htMin : t.val < min p.T ((q + 1) * B_boot p) := by
        simpa [BootstrapObservedFollower.blockStop,
          ActualFollowerCalendarContinuity.calendarBlockIndex,
          BootstrapDimensions.roundBlockIndex, q] using hprevMem.2
      rw [hstartNext] at hnextMem
      have hminLe := Nat.min_le_right p.T ((q + 1) * B_boot p)
      omega
    have hstopEq : BootstrapObservedFollower.blockStop p
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) = u.val := by
      have hTle : (q + 1) * B_boot p ≤ p.T := by
        rw [← huBoundary]
        exact Nat.le_of_lt u.isLt
      simp [BootstrapObservedFollower.blockStop,
        ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q, Nat.min_eq_right hTle, huBoundary]
    have hstartNextEq : BootstrapObservedFollower.blockStart p
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) = u.val := by
      rw [hstartNext, huBoundary]
    have hlength : ActualFollowerCalendarContinuity.calendarCursor t + 1 =
        BootstrapObservedFollower.blockLength p
          (ActualFollowerCalendarContinuity.calendarBlockIndex t) := by
      simp only [ActualFollowerCalendarContinuity.calendarCursor,
        BootstrapObservedFollower.blockLength, hstartPrev, hstopEq]
      omega
    have hcursorNext : ActualFollowerCalendarContinuity.calendarCursor u = 0 := by
      simp [ActualFollowerCalendarContinuity.calendarCursor, hstartNextEq]
    simp only [ite_eq_right e]
    refine ⟨?_, ?_, ?_, hlength, hcursorNext⟩
    have hvals : (ActualFollowerCalendarContinuity.calendarBlockIndex t).val = q ∧
        (ActualFollowerCalendarContinuity.calendarBlockIndex u).val = q' := by
      simp [ActualFollowerCalendarContinuity.calendarBlockIndex,
        BootstrapDimensions.roundBlockIndex, q, q']
    · omega
    · exact hnext.symm.trans hstopEq.symm
    · exact hstartNextEq.symm

/-- Advance the source-free follower by one recorded grid observation. -/
def replayAdvance (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (n : Nat) (hnprev : n < p.T) (hnnext : n + 1 < p.T)
    (previous : {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩)
        (ActualFollowerCalendarContinuity.calendarCursor ⟨n, hnprev⟩)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩) code)})
    (y : Fin (D p + 1)) :
    {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n + 1, hnnext⟩) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n + 1, hnnext⟩)
        (ActualFollowerCalendarContinuity.calendarCursor ⟨n + 1, hnnext⟩)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n + 1, hnnext⟩) code)} := by
  let t : Fin p.T := ⟨n, hnprev⟩
  let u : Fin p.T := ⟨n + 1, hnnext⟩
  let block := ActualFollowerCalendarContinuity.calendarBlockIndex t
  let cursor := ActualFollowerCalendarContinuity.calendarCursor t
  let replayStepCode := localCode p rate i block cursor
    (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t) own pub
    previous.1 previous.2 y
  let afterCode := replayStepCode.2.2
  have hafter := localCode_successor_cursor p rate i block cursor
    (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t) own pub
    previous.1 previous.2 y
  have hgeometry := calendar_successor_geometry p t u (by rfl)
  by_cases e : ActualFollowerCalendarContinuity.calendarBlockIndex t =
      ActualFollowerCalendarContinuity.calendarBlockIndex u
  · have hcursor : ActualFollowerCalendarContinuity.calendarCursor u = cursor + 1 := by
      simpa [e, cursor] using hgeometry
    let nextCode : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) :=
      cast (congrArg (ReplayFollowerCode p rate) e) afterCode
    refine ⟨nextCode, ?_⟩
    have hstate := followerAtCursor_cast e hcursor.symm
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block afterCode)
      hafter
    have hcode := followerStateOfCode_cast e afterCode
    simpa [nextCode, hcode, block, t, u] using hstate
  · have hchanged :
        (ActualFollowerCalendarContinuity.calendarBlockIndex t).val + 1 =
            (ActualFollowerCalendarContinuity.calendarBlockIndex u).val ∧
          t.val + 1 = BootstrapObservedFollower.blockStop p
            (ActualFollowerCalendarContinuity.calendarBlockIndex t) ∧
          u.val = BootstrapObservedFollower.blockStart p
            (ActualFollowerCalendarContinuity.calendarBlockIndex u) ∧
          ActualFollowerCalendarContinuity.calendarCursor t + 1 =
            BootstrapObservedFollower.blockLength p
              (ActualFollowerCalendarContinuity.calendarBlockIndex t) ∧
          ActualFollowerCalendarContinuity.calendarCursor u = 0 := by
      simpa [e] using hgeometry
    have hcomplete : ActualInitializationRun.followerAtCursor p rate block
        (BootstrapObservedFollower.blockLength p block)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block afterCode) := by
      simpa [block, cursor, hchanged.2.2.2.1] using hafter
    let carry := carryFromFollowerCode p rate block afterCode
    have hstopNext : BootstrapObservedFollower.blockStop p block =
        BootstrapObservedFollower.blockStart p
          (ActualFollowerCalendarContinuity.calendarBlockIndex u) := by
      calc
        BootstrapObservedFollower.blockStop p block = t.val + 1 := hchanged.2.1.symm
        _ = u.val := by rfl
        _ = BootstrapObservedFollower.blockStart p
            (ActualFollowerCalendarContinuity.calendarBlockIndex u) := hchanged.2.2.1
    have hready := carryFromFollowerCode_ready p rate block
      (ActualFollowerCalendarContinuity.calendarBlockIndex u) afterCode hcomplete
      hchanged.1.symm hstopNext
    let nextCode := beginCode p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex u) own carry
    have hzero := beginCode_cursor_zero p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex u) own carry hready
    refine ⟨nextCode, ?_⟩
    change ActualInitializationRun.followerAtCursor p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex u)
      (ActualFollowerCalendarContinuity.calendarCursor u)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex u) nextCode)
    simpa [nextCode, hchanged.2.2.2.2] using hzero

/-- Replay a finite prefix. Each recursive step consumes only the preceding
grid feedback; recorded arm entries remain present in `h` but do not steer the
source-free local operation. -/
def replayPrefix (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (n : Nat) (hn : n < p.T) (h : HistoryCode p n) :
    {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hn⟩) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hn⟩)
        (ActualFollowerCalendarContinuity.calendarCursor ⟨n, hn⟩)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hn⟩) code)} := by
  cases n with
  | zero =>
      let t : Fin p.T := ⟨0, hn⟩
      have hblock : ActualFollowerCalendarContinuity.calendarBlockIndex t =
          ActualInitializationRun.firstBlock p := by
        apply Fin.ext
        simp [t, ActualFollowerCalendarContinuity.calendarBlockIndex,
          BootstrapDimensions.roundBlockIndex, ActualInitializationRun.firstBlock]
      have hcursor : ActualFollowerCalendarContinuity.calendarCursor t = 0 := by
        simp [t, ActualFollowerCalendarContinuity.calendarCursor,
          ActualFollowerCalendarContinuity.calendarBlockIndex,
          BootstrapDimensions.roundBlockIndex, BootstrapObservedFollower.blockStart]
      let startCode := initialReplayCode p rate C_star C_h i own
      have hstart := beginCode_cursor_zero p rate (ActualInitializationRun.firstBlock p)
        own ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i) (by trivial)
      refine ⟨cast (congrArg (ReplayFollowerCode p rate) hblock.symm) startCode, ?_⟩
      have hcast := followerStateOfCode_cast hblock.symm startCode
      simpa [t, hblock, hcursor, startCode, hcast] using
        followerAtCursor_cast hblock.symm hcursor.symm
          (ActualInitializationRoundMeasurability.followerStateOfCode p rate
            (ActualInitializationRun.firstBlock p) startCode) hstart
  | succ n =>
      have hnprev : n < p.T := by omega
      let hprev : HistoryCode p n := fun j => h ⟨j.val, by omega⟩
      let previous := replayPrefix p rate C_star C_h i pub own n hnprev hprev
      exact replayAdvance p rate i pub own n hnprev hn previous
        (h ⟨n, by omega⟩).2
termination_by n
decreasing_by omega

/-- The canonical source-free follower code before round `t`, for every
arbitrary supplied finite grid history of the matching length. -/
def followerReplayCode {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h : HistoryCode p t.val) :
    {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t)
        (ActualFollowerCalendarContinuity.calendarCursor t)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex t) code)} := by
  exact replayPrefix p rate C_star C_h i pub own t.val t.isLt h

/-- The complete existing follower state decoded from the source-free replay
code before round `t`. -/
def followerReplayBefore {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h : HistoryCode p t.val) :
    ActualInitializationPhysicalStep.FollowerState p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) :=
  ActualInitializationRoundMeasurability.followerStateOfCode p rate
    (ActualFollowerCalendarContinuity.calendarBlockIndex t)
    (followerReplayCode (p := p) rate C_star C_h i pub own t h).1

/-- Prepare at a genuine cursor, before receiving the current feedback. -/
def prepareAtCursor (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Own p) (pub : Published p) (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state)) :
    ReplayPreparedCode p rate block :=
  prepareCodeFor p rate i block own pub
    (ActualPostlaunchFollowerMeasurability.localTime block cursor hc) state (by
      cases state with
      | inl _ => trivial
      | inr fields =>
          simpa only [ActualInitializationRun.followerAtCursor,
            ActualInitializationRoundMeasurability.followerStateOfCode,
            ActualPostlaunchFollowerMeasurability.localTime,
            ActualInitializationRun.blockTime] using hs)

/-- PREPARE in the local output does not depend on the current grid value. -/
theorem localCode_prepared_eq_prepareAtCursor (p : Parameters) (rate : RateInput p)
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Own p) (pub : Published p) (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) :
    (localCode p rate i block cursor hc own pub state hs y).1 =
      prepareAtCursor p rate i block cursor hc own pub state hs := by
  cases state <;> rfl

/-- The original prepared arm computed from a source-free replay prefix.
The current round's feedback does not occur in this definition. -/
def followerGridDecision {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h : HistoryCode p t.val) : Fin p.K :=
  let replay := followerReplayCode rate C_star C_h i pub own t h
  ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
    (prepareCodeFor p rate i (ActualFollowerCalendarContinuity.calendarBlockIndex t)
      own pub t replay.1 (by
        have hr := ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
          (rate := rate) (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
          ⟨ActualInitializationRoundMeasurability.followerStateOfCode p rate
            (ActualFollowerCalendarContinuity.calendarBlockIndex t) replay.1, replay.2⟩
        rw [ActualFollowerCalendarContinuity.calendarLocalTime_eq_time t] at hr
        cases he : replay.1 with
        | inl _ => trivial
        | inr fields =>
            simpa only [he, ActualInitializationRoundMeasurability.followerStateOfCode,
              ActualInitializationPhysicalStep.followerAtNextCursor] using hr))

/-- The arm projection is the preparation component of any local replay output. -/
theorem followerGridDecision_eq_localCodeArm (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h : HistoryCode p t.val) (y : Fin (D p + 1)) :
    followerGridDecision (p := p) rate C_star C_h i pub own t h =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
        (localCode p rate i (ActualFollowerCalendarContinuity.calendarBlockIndex t)
          (ActualFollowerCalendarContinuity.calendarCursor t)
          (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
          own pub (followerReplayCode (p := p) rate C_star C_h i pub own t h).1
          (followerReplayCode (p := p) rate C_star C_h i pub own t h).2 y).1 := by
  rw [localCode_prepared_eq_prepareAtCursor]
  simp only [followerGridDecision, prepareAtCursor,
    ActualFollowerCalendarContinuity.calendarLocalTime_eq_time t]

/-- Advance one source-free prefix through its supplied grid observation. -/
def followerReplayAfter (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h : HistoryCode p t.val) (y : Fin (D p + 1)) :
    {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t)
        (ActualFollowerCalendarContinuity.calendarCursor t + 1)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex t) code)} := by
  let before := followerReplayCode (p := p) rate C_star C_h i pub own t h
  let cursor := ActualFollowerCalendarContinuity.calendarCursor t
  let hcursor := ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t
  let step := localCode p rate i
    (ActualFollowerCalendarContinuity.calendarBlockIndex t) cursor hcursor
    own pub before.1 before.2 y
  refine (⟨step.2.2, ?_⟩ : {code : ReplayFollowerCode p rate
      (ActualFollowerCalendarContinuity.calendarBlockIndex t) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t) (cursor + 1)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex t) code)})
  exact localCode_successor_cursor p rate i
    (ActualFollowerCalendarContinuity.calendarBlockIndex t) cursor hcursor
    own pub before.1 before.2 y

/-- The source-free successor after the actual horizon's last round. -/
def followerReplayAfterLast (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (h : HistoryCode p p.T) :=
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  let hlast : p.T - 1 < p.T := by have := p.one_le_T; omega
  let past : HistoryCode p (p.T - 1) := fun j => h ⟨j.val, by omega⟩
  followerReplayAfter p rate C_star C_h i pub own last past (h last).2

/-- The checked existing terminal follower output code after replaying every
bounded grid entry. -/
def followerTerminalCode {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (h : HistoryCode p p.T) :
    ActualInitializationFollowerBoundaryMeasurability.BoundaryOutputCode p rate :=
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
    p rate
    (ActualFollowerCalendarContinuity.calendarBlockIndex last)
    (followerReplayAfterLast p rate C_star C_h i pub own h).1

/-- Keep the actual last bootstrap weight update as a separate observable,
including a first declaration whose terminal carry drops those weights. -/
def followerTerminalUpdatedNumerators {p : Parameters} (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (h : HistoryCode p p.T) : Option (Fin p.K → ℕ) :=
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
    p rate (ActualFollowerCalendarContinuity.calendarBlockIndex last)
    (followerReplayAfterLast p rate C_star C_h i pub own h).1

/-- One arm entry of the original source-initialized complete history. -/
def sourceFollowerArm (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) : Fin p.K :=
  (ActualCompletePhysicalHistory.playerArmHistory
    (ActualFollowerCalendarContinuity.actualHistory rate source rewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
      have hlen := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
        p rate source rewards C_star C_h
      have h : (ActualCompletePhysicalHistory.playerArmHistory
          (ActualFollowerCalendarContinuity.actualHistory rate source rewards C_star C_h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
        simpa [ActualCompletePhysicalHistory.playerArmHistory,
          ActualCompletePhysicalHistory.actionHistory,
          ActualFollowerCalendarContinuity.actualHistory] using hlen.1
      rw [h]
      exact t.isLt)

/-- One grid observation entry of the original source-initialized complete
history. -/
def sourceFollowerGridFeedback (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) : Fin (D p + 1) :=
  (ActualCompletePhysicalHistory.playerGridFeedbackHistory
    (ActualFollowerCalendarContinuity.actualHistory rate source rewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
      have hlen := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
        p rate source rewards C_star C_h
      have h : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualFollowerCalendarContinuity.actualHistory rate source rewards C_star C_h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
        simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
          ActualCompletePhysicalHistory.feedbackHistory,
          ActualFollowerCalendarContinuity.actualHistory] using hlen.1
      rw [h]
      exact t.isLt)

/-- The actual finite prefix as a history code. The recorded past arms remain
in every entry, while replay consumes only each entry's grid feedback. -/
def sourceFollowerHistoryCode (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : Nat) (hn : n ≤ p.T) :
    HistoryCode p n := fun j =>
      let t : Fin p.T := ⟨j.val, by omega⟩
      (sourceFollowerArm p rate source rewards C_star C_h i t,
        sourceFollowerGridFeedback p rate source rewards C_star C_h i t)

/-- Each coded actual prefix entry retains that round's actual arm and grid
feedback. -/
theorem sourceFollowerHistoryCode_entry (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : Nat) (hn : n ≤ p.T)
    (j : Fin n) :
    sourceFollowerHistoryCode p rate source rewards C_star C_h i n hn j =
      (sourceFollowerArm p rate source rewards C_star C_h i ⟨j.val, by omega⟩,
        sourceFollowerGridFeedback p rate source rewards C_star C_h i ⟨j.val, by omega⟩) := rfl

open Bandits.Support.ActualFollowerCalendarContinuity

/-- Compare one replay operation with the same source's actual record. The
state identity is the induction input; no realizability of other histories is used. -/
theorem localCode_source_record (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (code : ReplayFollowerCode p rate (calendarBlockIndex t))
    (hs : followerAtCursor p rate (calendarBlockIndex t) (calendarCursor t)
      (followerStateOfCode p rate (calendarBlockIndex t) code))
    (hbefore : followerStateOfCode p rate (calendarBlockIndex t) code =
      calendarFollowerBefore rate source rewards C_star C_h i t) :
    let out := localCode p rate i (calendarBlockIndex t) (calendarCursor t)
      (calendarCursor_lt_blockLength t) (ownProjection p source i) source.1 code hs
      (sourceFollowerGridFeedback p rate source rewards C_star C_h i t)
    followerStateOfCode p rate (calendarBlockIndex t) out.2.2 =
        calendarFollowerAfter rate source rewards C_star C_h i t ∧
      preparedFollowerCodeArm out.1 =
        sourceFollowerArm p rate source rewards C_star C_h i t := by
  obtain ⟨ha, htime, hdecode, harm⟩ :=
    calendar_record_localCode rate source rewards C_star C_h i t
  let y := sourceFollowerGridFeedback p rate source rewards C_star C_h i t
  have hin : localInputOfComponents source
      (followerStateOfCode p rate (calendarBlockIndex t) code) hs y =
      localInputOfComponents source
        (calendarFollowerBefore rate source rewards C_star C_h i t) ha y := by
    apply congrArg (fun x : CursorFollowerInput (rate := rate)
      (calendarBlockIndex t) (calendarCursor t) => (source, (x, y)))
    exact Subtype.ext hbefore
  have heq := localCode_eq_actualLocalCode p rate i (calendarBlockIndex t)
    (calendarCursor t) (calendarCursor_lt_blockLength t)
    (ownProjection p source i) source.1 source rfl rfl code hs y
  rw [hin] at heq
  have hd := decode_localCodeOnComponents (rate := rate)
    (calendarCursor_lt_blockLength t) i source
    (calendarFollowerBefore rate source rewards C_star C_h i t) ha y
  rw (occs := .pos [1]) [htime] at hd
  have hout := Option.some.inj (hd.symm.trans hdecode)
  dsimp only
  rw [heq]
  constructor
  · exact congrArg (fun o : ActualInitializationPhysicalStep.FollowerOutcome p rate
      (calendarBlockIndex t) => o.next) hout
  · exact harm.symm

/-- On the source's own bounded history, the replay before-state is the
source's actual whole follower storage. -/
theorem source_initialized_follower_before_replay {p : Parameters} (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    followerReplayBefore (p := p) rate C_star C_h i source.1 (ownProjection p source i) t
      (sourceFollowerHistoryCode p rate source rewards C_star C_h i t.val
        (Nat.le_of_lt t.isLt)) =
      calendarFollowerBefore rate source rewards C_star C_h i t := by
  rcases t with ⟨n, hn⟩
  induction n with
  | zero =>
      have hinit := calendar_follower_initial rate source rewards C_star C_h i
      unfold followerReplayBefore followerReplayCode
      unfold replayPrefix
      change followerStateOfCode p rate (calendarBlockIndex ⟨0, hn⟩)
        (cast _ (initialReplayCode p rate C_star C_h i (ownProjection p source i))) = _
      unfold initialReplayCode
      rw [followerStateOfCode_cast (show firstBlock p = calendarBlockIndex ⟨0, hn⟩ from
        by apply Fin.ext; exact (Nat.zero_div _).symm)]
      rw [beginCode_state_eq p rate _ source _ i _ rfl]
      exact hinit.symm
  | succ n ih =>
      have hnprev : n < p.T := by omega
      let t : Fin p.T := ⟨n, hnprev⟩
      let u : Fin p.T := ⟨n + 1, hn⟩
      let past := sourceFollowerHistoryCode p rate source rewards C_star C_h i n
        (Nat.le_of_lt hnprev)
      let previous := followerReplayCode (p := p) rate C_star C_h i source.1
        (ownProjection p source i) t past
      have hbefore : followerStateOfCode p rate (calendarBlockIndex t) previous.1 =
          calendarFollowerBefore rate source rewards C_star C_h i t := ih hnprev
      have hafter := (localCode_source_record p rate source rewards C_star C_h i t
        previous.1 previous.2 hbefore).1
      have hsucc := calendar_follower_successor rate source rewards C_star C_h i t hn
      dsimp only [t, Fin.val_mk] at hsucc
      unfold followerReplayBefore followerReplayCode
      unfold replayPrefix
      change followerStateOfCode p rate (calendarBlockIndex u)
        (replayAdvance p rate i source.1 (ownProjection p source i) n hnprev hn
          previous (sourceFollowerGridFeedback p rate source rewards C_star C_h i t)).1 = _
      by_cases e : calendarBlockIndex t = calendarBlockIndex u
      · dsimp only [t, u] at e
        simp only [replayAdvance, dite_eq_left e, Subtype.coe_mk]
        rw [followerStateOfCode_cast e, hafter]
        exact (show calendarFollowerBefore rate source rewards C_star C_h i u = _ from
          by simpa only [dite_eq_left e] using hsucc).symm
      · dsimp only [t, u] at e
        simp only [replayAdvance, dite_eq_right e, Subtype.coe_mk]
        rw [beginCode_state_eq p rate _ source _ i _ rfl]
        unfold carryFromFollowerCode
        rw [boundaryOutputFromFollowerCode_reconstruction, hafter]
        exact (show _ ∧ _ ∧ _ ∧ calendarFollowerBefore rate source rewards C_star C_h i u = _
          from by simpa only [dite_eq_right e, followerCarryAtBlockBoundary] using hsucc).2.2.2.symm

/-- The same source's actual bounded strict-past arm/feedback history produces
its complete before-state and its actual current arm, without hypotheses. -/
theorem source_initialized_follower_replay {p : Parameters} (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    let h := sourceFollowerHistoryCode p rate source rewards C_star C_h i t.val
      (Nat.le_of_lt t.isLt)
    followerReplayBefore (p := p) rate C_star C_h i source.1 (ownProjection p source i) t h =
        calendarFollowerBefore rate source rewards C_star C_h i t ∧
      followerGridDecision (p := p) rate C_star C_h i source.1 (ownProjection p source i) t h =
        sourceFollowerArm p rate source rewards C_star C_h i t := by
  dsimp only
  have hb := source_initialized_follower_before_replay (p := p) rate source rewards C_star C_h i t
  refine ⟨hb, ?_⟩
  rw [followerGridDecision_eq_localCodeArm p rate C_star C_h i source.1
    (ownProjection p source i) t _ (sourceFollowerGridFeedback p rate source rewards C_star C_h i t)]
  exact (localCode_source_record p rate source rewards C_star C_h i t _ _ hb).2

/-- The terminal code decodes to the actual final boundary output of this
same source, after precisely T rounds, including T = 1. -/
theorem source_initialized_follower_terminal_replay {p : Parameters} (rate : RateInput p)
    (source : SourceInput p) (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    decodeBoundaryOutputCode p rate
      (followerTerminalCode (p := p) rate C_star C_h i source.1 (ownProjection p source i)
        (sourceFollowerHistoryCode p rate source rewards C_star C_h i p.T (Nat.le_refl _))) =
      terminalFollowerOutput rate source rewards C_star C_h i := by
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  have hb := source_initialized_follower_before_replay (p := p) rate source rewards C_star C_h i last
  let replay := followerReplayCode (p := p) rate C_star C_h i source.1 (ownProjection p source i) last
    (sourceFollowerHistoryCode p rate source rewards C_star C_h i last.val
      (Nat.le_of_lt last.isLt))
  have ha := (localCode_source_record p rate source rewards C_star C_h i last
    replay.1 replay.2 hb).1
  unfold followerTerminalCode followerReplayAfterLast followerReplayAfter
  rw [boundaryOutputFromFollowerCode_reconstruction]
  exact (congrArg (boundaryOutputFromFollower p rate (calendarBlockIndex last)) ha).trans
    (calendar_follower_terminal rate source rewards C_star C_h i).symm

/-- The retained last weight observable is the same source's original
bootstrap boundary update, regardless of whether it declares a row there. -/
theorem source_initialized_follower_terminal_updatedNumerators {p : Parameters}
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
    followerTerminalUpdatedNumerators rate C_star C_h i source.1 (ownProjection p source i)
        (sourceFollowerHistoryCode p rate source rewards C_star C_h i p.T (Nat.le_refl _)) =
      match calendarFollowerAfter rate source rewards C_star C_h i last with
      | .bootstrap startup => some (BootstrapObservedFollower.updatedNumerators p
          (calendarBlockIndex last) startup)
      | .declared _ _ _ => none := by
  dsimp only
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  let replay := followerReplayCode rate C_star C_h i source.1 (ownProjection p source i) last
    (sourceFollowerHistoryCode p rate source rewards C_star C_h i last.val
      (Nat.le_of_lt last.isLt))
  have hb := source_initialized_follower_before_replay rate source rewards C_star C_h i last
  have ha := (localCode_source_record p rate source rewards C_star C_h i last
    replay.1 replay.2 hb).1
  have haLast : followerStateOfCode p rate (calendarBlockIndex last)
      (followerReplayAfterLast p rate C_star C_h i source.1 (ownProjection p source i)
        (sourceFollowerHistoryCode p rate source rewards C_star C_h i p.T (Nat.le_refl _))).1 =
      calendarFollowerAfter rate source rewards C_star C_h i last := by
    unfold followerReplayAfterLast followerReplayAfter
    exact ha
  unfold followerTerminalUpdatedNumerators
  rw [boundaryUpdatedNumeratorsCode_eq, haLast]
  simp only [last]
  cases calendarFollowerAfter rate source rewards C_star C_h i last <;> rfl

/-- Replacing past recorded arms while retaining every feedback entry leaves
the exact replay code unchanged on arbitrary supplied grid histories. -/
theorem replayPrefix_eq_of_feedback (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (n : Nat) (hn : n < p.T) (h h' : HistoryCode p n)
    (hy : ∀ j, (h j).2 = (h' j).2) :
    replayPrefix p rate C_star C_h i pub own n hn h =
      replayPrefix p rate C_star C_h i pub own n hn h' := by
  induction n with
  | zero =>
      unfold replayPrefix
      rfl
  | succ n ih =>
      unfold replayPrefix
      change replayAdvance p rate i pub own n (by omega) hn
          (replayPrefix p rate C_star C_h i pub own n (by omega)
            (fun j => h ⟨j.val, by omega⟩)) (h ⟨n, by omega⟩).2 =
        replayAdvance p rate i pub own n (by omega) hn
          (replayPrefix p rate C_star C_h i pub own n (by omega)
            (fun j => h' ⟨j.val, by omega⟩)) (h' ⟨n, by omega⟩).2
      rw [ih (by omega) _ _ (fun j => hy ⟨j.val, by omega⟩), hy ⟨n, by omega⟩]

/-- The literal before-code ignores only the recorded arm components. -/
theorem followerReplayCode_eq_of_feedback (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h h' : HistoryCode p t.val)
    (hy : ∀ j, (h j).2 = (h' j).2) :
    followerReplayCode (p := p) rate C_star C_h i pub own t h =
      followerReplayCode (p := p) rate C_star C_h i pub own t h' :=
  replayPrefix_eq_of_feedback p rate C_star C_h i pub own t.val t.isLt h h' hy

/-- Decisions preserve feedback fibres of arbitrary supplied finite histories. -/
theorem followerGridDecision_eq_of_feedback (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (pub : Published p) (own : Own p)
    (t : Fin p.T) (h h' : HistoryCode p t.val)
    (hy : ∀ j, (h j).2 = (h' j).2) :
    followerGridDecision (p := p) rate C_star C_h i pub own t h =
      followerGridDecision (p := p) rate C_star C_h i pub own t h' := by
  have hcode := followerReplayCode_eq_of_feedback p rate C_star C_h i pub own t h h' hy
  simp only [followerGridDecision, hcode]

end Bandits.Support.ActualFollowerFiniteHistoryReplay

end
