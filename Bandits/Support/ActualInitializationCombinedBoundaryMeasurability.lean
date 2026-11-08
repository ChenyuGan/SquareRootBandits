/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockMeasurability
public import Bandits.Support.ActualInitializationFollowerBoundaryMeasurability

/-!
# Joint endpoint coordinates for one completed actual initialization block

The endpoint carrier keeps the original whole source, the accepted countable
continuation code, and every full follower code. Its only restrictions are the
actual endpoint alignment and completion facts supplied by `BlockInvariant`.
The observation is assembled from these independent coordinates and decodes
back to the existing combined handoff. On the continuing branch, the actual
next carry is measurable into the existing fixed-constant carry space: its
code projection is proved from the literal coordinator, monitor, and full
incoming follower codec bodies. This is one completed-block boundary bridge;
it does not assert measurability of the fold or the initialization recursion.

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:99-131,160-165`, and
`sources/zip4/manuscript/06_interruptions.tex:253-255,296`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationFollowerBoundaryMeasurability

namespace Bandits.Support.ActualInitializationCombinedBoundaryMeasurability

abbrev Parameters := ActualInitializationRun.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev PhaseCode (p : Parameters) := ActualInitializationBlockMeasurability.ContinuationCode p
abbrev FollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationFollowerBoundaryMeasurability.FollowerCode p rate block
abbrev EndpointBase (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  SourceInput p × (PhaseCode p × (Fin (p.m - 1) → FollowerCode p rate block))

instance endpointBaseMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) : MeasurableSpace (EndpointBase p rate block) := inferInstance

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

/-! ## Aligned endpoint coordinates -/

/-- The continuation code agrees with the original target coordinate and is
an actual prelaunch or launched endpoint. This is precisely the phase typing
data needed to rebuild the existing continuation from its stored fields. -/
def endpointPhaseValid (p : Parameters) (block : Fin (n_boot p))
    (C_star C_h : ℝ) (source : SourceInput p) (code : PhaseCode p) : Prop :=
  code.1 = block ∧
    code.2.1 = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
    match code.2.2.2.2 with
    | none =>
        (BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p
          code.2.2.2.1).crossingBlock = none ∧
        (BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p
          code.2.2.2.1).launchPosition = p.T
    | some trigger =>
        (BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p
          code.2.2.2.1).crossingBlock = some code.1 ∧
        trigger ∈ BootstrapDimensions.calendarBlock p code.1 ∧
        BootstrapLaunchMonitor.calendarBlockEnd p trigger ∧
        (BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p
          code.2.2.2.1).launchPosition =
            BootstrapDimensions.manuscriptRound p trigger ∧
        BootstrapLaunchMonitor.monitorValue p code.2.2.2.1.counters >
          4 * BootstrapStartupCostScale.Q C_star C_h p

/-- The product of the original source, one existing continuation code, and
all independent full follower codes, restricted only by the real boundary
alignment and each follower's completed-block cursor. -/
def endpointCoordinatesValid (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (x : EndpointBase p rate block) : Prop :=
  endpointPhaseValid p block C_star C_h x.1 x.2.1 ∧
    ∀ i, ActualInitializationRun.followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.2.2 i))

/-- Endpoint input in natural product/subtype coordinates. No fold output or
combined handoff is an input. The subtype proof exposes only endpoint
alignment, phase typing, and actual follower completion. -/
abbrev BoundaryEndpointInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  {x : EndpointBase p rate block // endpointCoordinatesValid p rate block C_star C_h x}

instance boundaryEndpointInputMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSpace (BoundaryEndpointInput p rate block C_star C_h) :=
  MeasurableSpace.comap
    (fun x : BoundaryEndpointInput p rate block C_star C_h =>
      (x : EndpointBase p rate block)) inferInstance

/-- The explicit no-launch endpoint subtype consumed by the next-carry
constructor. It is used only for the actual `continueNext` branch. -/
abbrev PrelaunchEndpointInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  {x : BoundaryEndpointInput p rate block C_star C_h //
    x.1.2.1.2.2.2.2 = none}

instance prelaunchEndpointInputMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSpace (PrelaunchEndpointInput p rate block C_star C_h) :=
  MeasurableSpace.comap
    (fun x : PrelaunchEndpointInput p rate block C_star C_h =>
      (x : BoundaryEndpointInput p rate block C_star C_h)) inferInstance

/-- The monitor code on a no-launch endpoint, including the actual no-crossing
and horizon-sentinel facts retained by the phase subtype. -/
def endpointUnlaunchedMonitorCode {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (input : PrelaunchEndpointInput p rate block C_star C_h) :
    ActualInitializationBlockMeasurability.UnlaunchedMonitorCode p := by
  let code := input.1.1.2.1
  have hvalid := input.1.2.1
  have hnone : code.2.2.2.2 = none := by
    simpa [code] using input.2
  unfold endpointPhaseValid at hvalid
  rw [hnone] at hvalid
  rcases hvalid with ⟨_, _, hmonitor⟩
  exact ⟨code.2.2.2.1, hmonitor⟩

/-- The source-derived local data fields used to rebuild the continuation;
the row, IDs, and constants stay visible in the original coordinates. -/
def endpointLocalData (p : Parameters) (_block : Fin (n_boot p))
    (C_star C_h : ℝ) (source : SourceInput p) (code : PhaseCode p) :
    BootstrapCoordinatorLocalRound.LocalData p :=
  { block := code.1
    row := source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    ids := source.1.1
    target := code.2.1
    coordinator := BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode p
      code.2.2.1
    C_star := C_star
    C_h := C_h }

/-- Decode the stored continuation code by assembling its fields against the
original source and the endpoint alignment proofs. -/
def continuationOfEndpointCode (p : Parameters) (block : Fin (n_boot p))
    (C_star C_h : ℝ) (source : SourceInput p) (code : PhaseCode p)
    (hvalid : endpointPhaseValid p block C_star C_h source code) :
    BootstrapCoordinatorLocalRound.Continuation p := by
  cases htrigger : code.2.2.2.2 with
  | none =>
    unfold endpointPhaseValid at hvalid
    rw [htrigger] at hvalid
    rcases hvalid with ⟨hblock, htarget, hmonitor⟩
    rcases hmonitor with ⟨hcross, hposition⟩
    exact .prelaunch ⟨endpointLocalData p block C_star C_h source code,
      ⟨BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p code.2.2.2.1,
        hcross, hposition⟩⟩
  | some trigger =>
    unfold endpointPhaseValid at hvalid
    rw [htrigger] at hvalid
    rcases hvalid with ⟨hblock, htarget, hlaunch⟩
    rcases hlaunch with ⟨hcross, htriggerIn, hend, hposition, hstrict⟩
    exact .launched ⟨endpointLocalData p block C_star C_h source code,
      trigger, htriggerIn,
      BootstrapCoordinatorRoundMeasurability.monitorStateOfCode p code.2.2.2.1,
      hcross,
      hend, hstrict, hposition⟩

/-- The original actual fold supplies phase alignment and launch/exhaustion
typing for its retained continuation code. -/
theorem endpointPhaseValid_of_aligned {p : Parameters}
    {block : Fin (n_boot p)} {source : SourceInput p} {C_star C_h : ℝ}
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (halign : ActualInitializationRun.continuationAligned p block source C_star C_h phase) :
    endpointPhaseValid p block C_star C_h source
      (ActualInitializationBlockMeasurability.continuationCodeOf phase) := by
  cases phase with
  | prelaunch live =>
      change ActualInitializationRun.continuationAligned p block source C_star C_h
        (.prelaunch live) at halign
      rcases halign with ⟨hblock, hids, hrow, htarget, hstar, hh⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData] using hblock
      · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData] using htarget
      · exact ⟨by simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            BootstrapCoordinatorLocalRound.Continuation.monitorState,
            BootstrapCoordinatorRoundMeasurability.monitorCode,
            BootstrapCoordinatorRoundMeasurability.monitorStateOfCode] using live.monitor.2.1,
          by simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            BootstrapCoordinatorLocalRound.Continuation.monitorState,
            BootstrapCoordinatorRoundMeasurability.monitorCode,
            BootstrapCoordinatorRoundMeasurability.monitorStateOfCode] using live.monitor.2.2⟩
  | launched launch =>
      change ActualInitializationRun.continuationAligned p block source C_star C_h
        (.launched launch) at halign
      rcases halign with ⟨hblock, hids, hrow, htarget, hstar, hh⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData] using hblock
      · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData] using htarget
      · refine ⟨?_, ?_, launch.triggerAtBlockEnd, ?_, ?_⟩
        · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            ActualInitializationRun.continuationData,
            BootstrapCoordinatorLocalRound.Continuation.monitorState,
            BootstrapCoordinatorRoundMeasurability.monitorCode,
            BootstrapCoordinatorRoundMeasurability.monitorStateOfCode] using launch.crossing
        · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            ActualInitializationRun.continuationData] using launch.triggerInBlock
        · simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            BootstrapCoordinatorLocalRound.Continuation.monitorState,
            BootstrapCoordinatorRoundMeasurability.monitorCode,
            BootstrapCoordinatorRoundMeasurability.monitorStateOfCode] using launch.launchPosition
        · rw [← hstar, ← hh]
          simpa [ActualInitializationBlockMeasurability.continuationCodeOf,
            ActualInitializationRun.continuationData,
            BootstrapCoordinatorLocalRound.Continuation.monitorState,
            BootstrapCoordinatorRoundMeasurability.monitorCode,
            BootstrapCoordinatorRoundMeasurability.monitorStateOfCode] using launch.strictThreshold

/-- The fold's actual continuation meets the source and fixed-constant
alignment required by the endpoint coordinates. -/
theorem endpointPhaseValid_of_blockFold {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {cursor : ℕ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h cursor) :
    endpointPhaseValid p block C_star C_h source
      (ActualInitializationBlockMeasurability.continuationCodeOf folded.phase) :=
  endpointPhaseValid_of_aligned folded.phase folded.invariant.1

/-- The independently coded endpoint extracted from an existing fold. Its
completion facts come from `blockFold_follower_complete`, not a global success
assumption. -/
def endpointInputOfBlockFold {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {cursor : ℕ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h cursor) : BoundaryEndpointInput p rate block C_star C_h :=
  ⟨(source, (ActualInitializationBlockMeasurability.continuationCodeOf folded.phase,
    fun i => ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      (folded.followers i))),
    ⟨endpointPhaseValid_of_blockFold folded, fun i => by
      simpa [ActualInitializationRoundMeasurability.followerStateOfCode_encode] using
        ActualInitializationRun.blockFold_follower_complete folded i⟩⟩

/-- Decoding a valid aligned continuation code recovers its exact original
phase, including the original complete row, IDs, and fixed constants. -/
theorem continuationOfEndpointCode_of_aligned {p : Parameters}
    {block : Fin (n_boot p)} {source : SourceInput p}
    {C_star C_h : ℝ} (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (halign : ActualInitializationRun.continuationAligned p block source C_star C_h phase) :
    continuationOfEndpointCode p block C_star C_h source
      (ActualInitializationBlockMeasurability.continuationCodeOf phase)
      (endpointPhaseValid_of_aligned phase halign) = phase := by
  cases phase with
  | prelaunch live =>
      rcases halign with ⟨hblock, hids, hrow, htarget, hstar, hh⟩
      change live.data.block = block at hblock
      change live.data.ids = source.1.1 at hids
      change live.data.row = source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) at hrow
      change live.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 at htarget
      change live.data.C_star = C_star at hstar
      change live.data.C_h = C_h at hh
      apply congrArg BootstrapCoordinatorLocalRound.Continuation.prelaunch
      cases live with
      | mk data monitor =>
        cases data with
        | mk liveBlock liveRow liveIds liveTarget liveCoordinator liveStar liveH =>
          cases monitor with
          | mk liveMonitor liveMonitorProperty =>
            have hrow' : liveRow = source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
              simpa using hrow
            have hids' : liveIds = source.1.1 := by simpa using hids
            have hstar' : liveStar = C_star := by simpa using hstar
            have hh' : liveH = C_h := by simpa using hh
            simp_all [endpointLocalData,
          ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData,
          BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
          BootstrapCoordinatorLocalRound.Continuation.monitorState,
          BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode_encode,
          BootstrapCoordinatorRoundMeasurability.monitorStateOfCode_encode]
  | launched launch =>
      rcases halign with ⟨hblock, hids, hrow, htarget, hstar, hh⟩
      change launch.data.block = block at hblock
      change launch.data.ids = source.1.1 at hids
      change launch.data.row = source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) at hrow
      change launch.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 at htarget
      change launch.data.C_star = C_star at hstar
      change launch.data.C_h = C_h at hh
      apply congrArg BootstrapCoordinatorLocalRound.Continuation.launched
      cases launch with
      | mk data trigger triggerIn monitor crossing hend strict hposition =>
        cases data with
        | mk liveBlock liveRow liveIds liveTarget liveCoordinator liveStar liveH =>
          have hrow' : liveRow = source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
            simpa using hrow
          have hids' : liveIds = source.1.1 := by simpa using hids
          have hstar' : liveStar = C_star := by simpa using hstar
          have hh' : liveH = C_h := by simpa using hh
          simp_all [endpointLocalData,
          ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData,
          BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
          BootstrapCoordinatorLocalRound.Continuation.monitorState,
          BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode_encode,
          BootstrapCoordinatorRoundMeasurability.monitorStateOfCode_encode]

/-- Decoding the endpoint phase recovers the fold's actual continuation. -/
theorem continuationOfEndpointCode_endpointInputOfBlockFold
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {cursor : ℕ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h cursor) :
    continuationOfEndpointCode p block C_star C_h source
      (ActualInitializationBlockMeasurability.continuationCodeOf folded.phase)
      (endpointPhaseValid_of_blockFold folded) = folded.phase := by
  exact continuationOfEndpointCode_of_aligned (p := p) (block := block)
    (source := source) (C_star := C_star) (C_h := C_h)
    folded.phase folded.invariant.1

/-! ## Boundary carry coordinates -/

/-- Rebuilding a finite buffer and extracting its coordinates preserves both
the discrete skeleton and every original saved observation/thinning scalar. -/
private theorem buffer_codes_ofFn {p : Parameters} {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧
      HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values).length = n := List.length_ofFn
  constructor
  · apply (Fin.heq_fun_iff hlen).mpr
    intro i
    change ((List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].calendarRound,
      (List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].pilot) = _
    simp only [List.getElem_ofFn]
  · apply (Fin.heq_fun_iff hlen).mpr
    intro i
    change ((List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].observation,
      (List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].thinScalar) = _
    simp only [List.getElem_ofFn]

/-- The incoming configuration codec is lossless in the encoding direction
too, including every decoder-bank entry, failure flag, and continuous buffer
coordinate. This is a literal codec identity, with no measurability premise. -/
theorem incomingOfLocalConfiguration_decode {p : Parameters} (rate : RateInput p)
    (code : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate code) = code := by
  cases code with
  | none => rfl
  | some data =>
      rcases data with ⟨⟨⟨registers, ⟨n, skeleton⟩⟩, values⟩, memory⟩
      cases registers with
      | mk lastDown score delta backlog status batch failure =>
          fin_cases status <;>
            simp [FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
              FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
              FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
              FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
              FollowerDownMeasurability.followerStateCode,
              FollowerDownMeasurability.followerStateOfCode,
              FollowerDownMeasurability.followerStatusCode,
              FollowerDownMeasurability.followerStatusOfCode,
              FollowerDownMeasurability.decoderBatchCode,
              FollowerDownMeasurability.decoderBatchOfCode,
              FollowerDownMeasurability.decoderEntryCode,
              FollowerDownMeasurability.decoderEntryOfCode,
              FollowerDownJointMeasurability.bufferFromSkeletonAndScalars,
              FollowerLifecycleMeasurability.localMemoryCodeOfCode,
              List.map_map, Function.comp_def]
          all_goals exact buffer_codes_ofFn skeleton values

/-- Re-encoding the existing follower carry decoder preserves its complete
accepted code, including the full ordinary/dagger incoming configuration. -/
theorem followerCarryCodeOf_decode {p : Parameters} {rate : RateInput p}
    (code : ActualInitializationBlockMeasurability.FollowerCarryCode p rate) :
    ActualInitializationBlockMeasurability.followerCarryCodeOf
      (ActualInitializationBlockMeasurability.followerCarryOfCode code) = code := by
  cases code with
  | inl numerators => rfl
  | inr fields =>
      rcases fields with ⟨row, activation, configuration⟩
      simp only [ActualInitializationBlockMeasurability.followerCarryCodeOf,
        ActualInitializationBlockMeasurability.followerCarryOfCode,
        incomingOfLocalConfiguration_decode]

/-- Re-encoding the sole existing block-carry decoder preserves each literal
coordinate. In particular this proves, rather than assumes, the reverse
codec law needed by its fixed-constant comap measurable space. -/
theorem blockCarryCodeOf_decode {p : Parameters} (rate : RateInput p)
    {block : Fin (n_boot p)} (C_star C_h : ℝ)
    (code : ActualInitializationBlockMeasurability.BlockCarryCode p rate block) :
    ActualInitializationBlockMeasurability.blockCarryCodeOf
      (ActualInitializationBlockMeasurability.blockCarryOfCode rate C_star C_h code) =
        code := by
  apply Subtype.ext
  have hfollowers : (fun i => ActualInitializationBlockMeasurability.followerCarryCodeOf
      (ActualInitializationBlockMeasurability.followerCarryOfCode
        (code.1.followers i))) = code.1.followers :=
    funext fun i => followerCarryCodeOf_decode (code.1.followers i)
  change (⟨code.1.coordinator, code.1.monitor,
    fun i => ActualInitializationBlockMeasurability.followerCarryCodeOf
      (ActualInitializationBlockMeasurability.followerCarryOfCode
        (code.1.followers i))⟩ :
      ActualInitializationBlockMeasurability.BlockCarryCodeFields p rate block) = code.1
  rw [hfollowers]

/-- Encode the exact boundary carry of one follower directly in the already
accepted `BlockCarryCode`. First declaration retains the source-prescribed
initial state and memory; declared followers keep every incoming continuous
ordinary/dagger coordinate. -/
def boundaryFollowerCarryCode {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    ActualInitializationBlockMeasurability.FollowerCarryCode p rate :=
  match follower with
  | .inl startup =>
      match BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none => .inl ⟨ActualBootstrapObservationCode.updatedNumeratorsCode p block startup,
          BootstrapObservedFollower.updatedNumerators_lower_bound p block startup⟩
      | some row => .inr (row, (BootstrapObservedFollower.nextActivationRound p block,
          some (ActualInitializationFollowerBoundaryMeasurability.firstDeclarationFields
            p rate)))
  | .inr (row, (activation, configuration)) =>
      .inr (row, (activation, configuration))

/-- The direct endpoint carry coordinate reconstructs the existing carry
conversion of the decoded follower boundary output. -/
theorem boundaryFollowerCarryCode_reconstruction {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (follower : FollowerCode p rate block) :
    ActualInitializationBlockMeasurability.followerCarryOfCode
      (boundaryFollowerCarryCode rate block follower) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode p rate
          (ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
            p rate block follower)) := by
  cases follower with
  | inl startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
        simp [boundaryFollowerCarryCode,
          ActualInitializationBlockMeasurability.followerCarryOfCode,
          ActualInitializationRun.followerCarryOfBoundaryOutput,
          ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode,
          ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode,
          hpending]
      | some row =>
        simp only [boundaryFollowerCarryCode, hpending,
          ActualInitializationBlockMeasurability.followerCarryOfCode,
          ActualInitializationRun.followerCarryOfBoundaryOutput,
          ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode,
          ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode]
        apply congrArg (fun configuration => ActualInitializationRun.FollowerCarry.declared
          row (BootstrapObservedFollower.nextActivationRound p block) configuration)
        rfl
  | inr declared =>
      rcases declared with ⟨row, activation, configuration⟩
      simp [boundaryFollowerCarryCode,
        ActualInitializationBlockMeasurability.followerCarryOfCode,
        ActualInitializationRun.followerCarryOfBoundaryOutput,
        ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode,
        ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode]

/-- The accepted follower bridge also reconstructs the actual unchecked
boundary carry, via its separately reviewed carry reconstruction theorem. -/
theorem boundaryFollowerCarryCode_reconstructs_actual {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (follower : FollowerCode p rate block) :
    ActualInitializationBlockMeasurability.followerCarryOfCode
      (boundaryFollowerCarryCode rate block follower) =
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower) := by
  rw [boundaryFollowerCarryCode_reconstruction]
  exact (ActualInitializationFollowerBoundaryMeasurability.boundaryCarry_reconstruction
    p rate block follower).symm

/-- The existing follower carry projection is Borel on its full input code. -/
theorem measurable_boundaryFollowerCarryCode {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) :
    Measurable (boundaryFollowerCarryCode rate block) := by
  apply measurable_fun_sum
  · exact measurable_of_countable _
  · change Measurable (fun x : Fin (M p) ×
      (ReferencePrelaunchFollower.Activation p ×
        FollowerPrepareJointMeasurability.IncomingConfiguration p rate) =>
          Sum.inr (x.1, (x.2.1, x.2.2)))
    exact measurable_inr.comp measurable_id

/-- Local arithmetic for the next activation bound when a block has a real
successor. -/
theorem nextActivation_le_successorStart (p : Parameters)
    (block : Fin (n_boot p)) (hnext : block.val + 1 < n_boot p) :
    (BootstrapObservedFollower.nextActivationRound p block).val ≤
      BootstrapObservedFollower.blockStart p
        (ActualInitializationRun.successorBlock p block hnext) + 1 := by
  have h := BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnext
  simpa [ActualInitializationRun.successorBlock,
    BootstrapObservedFollower.blockStart] using le_of_eq h

/-- The clipped block stop is exactly the next block's start away from the
horizon. -/
theorem stop_eq_successorStart (p : Parameters) (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p) :
    BootstrapObservedFollower.blockStop p block =
      BootstrapObservedFollower.blockStart p
        (ActualInitializationRun.successorBlock p block hnext) := by
  have hactivation := BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart
    p block hnext
  change BootstrapObservedFollower.blockStop p block + 1 =
    (block.val + 1) * B_boot p + 1 at hactivation
  have hstop : BootstrapObservedFollower.blockStop p block =
      (block.val + 1) * B_boot p := by omega
  simpa [ActualInitializationRun.successorBlock,
    BootstrapObservedFollower.blockStart] using hstop

/-- The actual continuing carry is assembled from the existing coordinator,
monitor, fixed constants, and every endpoint follower carry code. No new carry
schema is introduced. -/
def endpointNextCarryCode {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : PrelaunchEndpointInput p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    ActualInitializationBlockMeasurability.BlockCarryCode p rate
      (ActualInitializationRun.successorBlock p block hnext) := by
  let code := input.1.1.2.1
  let fields : ActualInitializationBlockMeasurability.BlockCarryCodeFields p rate
      (ActualInitializationRun.successorBlock p block hnext) := {
    coordinator := code.2.2.1
    monitor := endpointUnlaunchedMonitorCode input
    followers := fun i => boundaryFollowerCarryCode rate block (input.1.1.2.2 i) }
  refine ⟨fields, ?_⟩
  ·
    intro i
    cases hf : input.1.1.2.2 i with
    | inl startup =>
        cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
        | none => simp [fields, hf, boundaryFollowerCarryCode, hpending]
        | some row =>
          simpa [fields, hf, boundaryFollowerCarryCode, hpending] using
            nextActivation_le_successorStart p block hnext
    | inr declared =>
        rcases declared with ⟨row, activation, configuration⟩
        have hcomplete := input.1.2.2 i
        simp only [ActualInitializationRoundMeasurability.followerStateOfCode, hf,
          ActualInitializationRun.followerAtCursor] at hcomplete
        have hactivation : activation.val ≤
            BootstrapObservedFollower.blockStop p block + 1 := by
          rw [← ActualInitializationRun.blockStart_add_length_eq_stop p block]
          exact hcomplete
        rw [stop_eq_successorStart p block hnext] at hactivation
        simpa [fields, hf, boundaryFollowerCarryCode,
          ActualInitializationBlockMeasurability.BlockCarryCodeFields.activationReady] using
          hactivation

/-- Measurability of the accepted block-carry code constructor, coordinate by
coordinate in the original source and every full follower endpoint code. -/
theorem measurable_endpointNextCarryCode {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (hnext : block.val + 1 < n_boot p) :
    Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      endpointNextCarryCode rate block C_star C_h input hnext) := by
  let hbase : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      (input.1.1 : EndpointBase p rate block)) :=
    (measurable_subtype_coe : Measurable
      (fun x : BoundaryEndpointInput p rate block C_star C_h =>
        (x : EndpointBase p rate block))).comp
      (measurable_subtype_coe : Measurable
        (fun x : PrelaunchEndpointInput p rate block C_star C_h =>
          (x : BoundaryEndpointInput p rate block C_star C_h)))
  let hphase : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      (input.1.1.2.1 : PhaseCode p)) :=
    measurable_fst.comp (measurable_snd.comp hbase)
  let hfollows : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      input.1.1.2.2) := measurable_snd.comp (measurable_snd.comp hbase)
  have hcoordinator : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      (input.1.1.2.1).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hphase))
  have hmonitorCode : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        (input.1.1.2.1).2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hphase)))
  have hmonitor : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        endpointUnlaunchedMonitorCode input) := by
    exact hmonitorCode.subtype_mk
      (p := fun m => m.crossingBlock = none ∧ m.launchPosition = p.T)
      (h := fun input => (endpointUnlaunchedMonitorCode input).property)
  have hfollowers : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        fun i => boundaryFollowerCarryCode rate block (input.1.1.2.2 i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_boundaryFollowerCarryCode rate block).comp
      ((measurable_pi_apply i).comp hfollows)
  have hfields : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        ( (input.1.1.2.1).2.2.1,
          (endpointUnlaunchedMonitorCode input,
            fun i => boundaryFollowerCarryCode rate block (input.1.1.2.2 i)))) := by
    exact hcoordinator.prodMk (hmonitor.prodMk hfollowers)
  have hcodeFields : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        ActualInitializationBlockMeasurability.blockCarryCodeFieldsCoordinates
          (endpointNextCarryCode rate block C_star C_h input hnext).1) := by
    simpa [endpointNextCarryCode,
      ActualInitializationBlockMeasurability.blockCarryCodeFieldsCoordinates] using hfields
  have hfields' : Measurable
      (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        (endpointNextCarryCode rate block C_star C_h input hnext).1) :=
    (measurable_comap_iff).2 hcodeFields
  exact hfields'.subtype_mk (h := fun input =>
    (endpointNextCarryCode rate block C_star C_h input hnext).2)

/-- Decode the existing block carry code with the original fixed constants. -/
def endpointNextCarry {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : PrelaunchEndpointInput p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    ActualInitializationBlockMeasurability.FixedConstantsBlockCarry p rate
      (ActualInitializationRun.successorBlock p block hnext) C_star C_h :=
  ⟨ActualInitializationBlockMeasurability.blockCarryOfCode rate C_star C_h
    (endpointNextCarryCode rate block C_star C_h input hnext), rfl, rfl⟩

/-- The actual fixed-constant carry is reconstructed by the sole accepted
`BlockCarryCode` decoder; its two retained constants are exactly the fixed
parameters. -/
theorem endpointNextCarry_reconstruction {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : PrelaunchEndpointInput p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    (endpointNextCarry rate block C_star C_h input hnext).1 =
      ActualInitializationBlockMeasurability.blockCarryOfCode rate C_star C_h
        (endpointNextCarryCode rate block C_star C_h input hnext) := rfl

theorem endpointNextCarry_constants {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : PrelaunchEndpointInput p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    (endpointNextCarry rate block C_star C_h input hnext).1.C_star = C_star ∧
      (endpointNextCarry rate block C_star C_h input hnext).1.C_h = C_h :=
  (endpointNextCarry rate block C_star C_h input hnext).2

/-- The actual decoded next carry projects to the directly constructed
accepted code. No reverse codec identity is an assumption of this bridge. -/
theorem blockCarryCodeOf_endpointNextCarry {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : PrelaunchEndpointInput p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    ActualInitializationBlockMeasurability.blockCarryCodeOf
      (endpointNextCarry rate block C_star C_h input hnext).1 =
        endpointNextCarryCode rate block C_star C_h input hnext :=
  blockCarryCodeOf_decode rate C_star C_h
    (endpointNextCarryCode rate block C_star C_h input hnext)

/-- The actual fixed-constant next carry is Borel into the block owner's
existing comap measurable space. Its projection is the separately proved
measurable carry-code constructor, including all incoming continuous fibres. -/
theorem measurable_endpointNextCarry {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (hnext : block.val + 1 < n_boot p) :
    Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
      endpointNextCarry rate block C_star C_h input hnext) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
    ActualInitializationBlockMeasurability.blockCarryCodeOf
      (endpointNextCarry rate block C_star C_h input hnext).1)
  simp only [blockCarryCodeOf_endpointNextCarry]
  exact measurable_endpointNextCarryCode rate block C_star C_h hnext

/-! ## Joint completed-boundary observation -/

/-- A dependent sum of the possible successor indices and the already
accepted carry code at that index. It has no value representing a successor at
the final clipped block. -/
abbrev EndpointNextCarryCode (p : Parameters) (rate : RateInput p) :=
  Σ next : Fin (n_boot p), ActualInitializationBlockMeasurability.BlockCarryCode p rate next

/-- The existing carry subtype inherits the measurable structure of its
accepted `BlockCarryCodeFields` coordinates. -/
instance endpointBlockCarryCodeMeasurableSpace {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) :
    MeasurableSpace (ActualInitializationBlockMeasurability.BlockCarryCode p rate block) :=
  MeasurableSpace.comap
    (fun code : ActualInitializationBlockMeasurability.BlockCarryCode p rate block => code.1)
    (inferInstance : MeasurableSpace
      (ActualInitializationBlockMeasurability.BlockCarryCodeFields p rate block))

instance endpointNextCarryCodeMeasurableSpace {p : Parameters} {rate : RateInput p} :
    MeasurableSpace (EndpointNextCarryCode p rate) :=
  ⨅ next : Fin (n_boot p),
    (inferInstance : MeasurableSpace
      (ActualInitializationBlockMeasurability.BlockCarryCode p rate next)).map
        (fun code => (⟨next, code⟩ : EndpointNextCarryCode p rate))

/-- The next-carry coordinate is absent for launch and exhaustion, and present
only for a real continuing successor. -/
abbrev EndpointNextCarryObservation (p : Parameters) (rate : RateInput p)
    (_block : Fin (n_boot p)) := Unit ⊕ EndpointNextCarryCode p rate

/-- Insertion into the dependent product carrier is measurable by the
sigma-algebra generated by its existing block-indexed carry coordinates. -/
theorem measurable_endpointNextCarrySigmaMk {p : Parameters} {rate : RateInput p}
    (next : Fin (n_boot p)) :
    Measurable (fun code : ActualInitializationBlockMeasurability.BlockCarryCode p rate next =>
      (⟨next, code⟩ : EndpointNextCarryCode p rate)) := by
  intro s hs
  change MeasurableSet[⨅ i : Fin (n_boot p),
    (inferInstance : MeasurableSpace
      (ActualInitializationBlockMeasurability.BlockCarryCode p rate i)).map
        (fun code => (⟨i, code⟩ : EndpointNextCarryCode p rate))] s at hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  have h := hs next
  simpa [MeasurableSpace.map_def] using h

/-- The prelaunch region of the natural independent endpoint coordinates. -/
def endpointPrelaunchSet (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Set (BoundaryEndpointInput p rate block C_star C_h) :=
  {input | input.1.2.1.2.2.2.2 = none}

/-- The tag projection from the original phase code is measurable on the
aligned endpoint subtype. -/
theorem measurable_endpointPhaseTag {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (input.1.2.1).2.2.2.2) := by
  let hbase : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (input.1 : EndpointBase p rate block)) :=
    (measurable_subtype_coe : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (input : EndpointBase p rate block)))
  let hphase : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (input.1.2.1 : PhaseCode p)) :=
    measurable_fst.comp (measurable_snd.comp hbase)
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp hphase)))

/-- The exact prelaunch slice is measurable in the endpoint coordinates. -/
theorem measurableSet_endpointPrelaunchSet {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSet (endpointPrelaunchSet p rate block C_star C_h) := by
  change MeasurableSet {input : BoundaryEndpointInput p rate block C_star C_h |
    (input.1.2.1).2.2.2.2 = none}
  exact measurableSet_eq_fun (measurable_endpointPhaseTag rate block C_star C_h)
    measurable_const

/-- Retain the existing next-block carry code exactly on the no-launch
endpoint, and no carry on a launch. The terminal block has no successor
coordinate at all. -/
def endpointNextCarryObservation {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : BoundaryEndpointInput p rate block C_star C_h) :
    EndpointNextCarryObservation p rate block := by
  classical
  by_cases hnext : block.val + 1 < n_boot p
  · by_cases hpre : input ∈ endpointPrelaunchSet p rate block C_star C_h
    · change input.1.2.1.2.2.2.2 = none at hpre
      exact Sum.inr ⟨ActualInitializationRun.successorBlock p block hnext,
        endpointNextCarryCode rate block C_star C_h ⟨input, hpre⟩ hnext⟩
    · exact Sum.inl ()
  · exact Sum.inl ()

/-- A final clipped block has no successor carry observation. -/
theorem endpointNextCarryObservation_absent {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : BoundaryEndpointInput p rate block C_star C_h)
    (hfinal : ¬ block.val + 1 < n_boot p) :
    endpointNextCarryObservation rate block C_star C_h input = Sum.inl () := by
  simp [endpointNextCarryObservation, hfinal]

/-- At a nonfinal no-launch endpoint the observed carry is exactly the
existing indexed `BlockCarryCode` constructed from the retained coordinates. -/
theorem endpointNextCarryObservation_present {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : BoundaryEndpointInput p rate block C_star C_h)
    (hpre : input ∈ endpointPrelaunchSet p rate block C_star C_h)
    (hnext : block.val + 1 < n_boot p) :
    endpointNextCarryObservation rate block C_star C_h input =
      Sum.inr ⟨ActualInitializationRun.successorBlock p block hnext,
        endpointNextCarryCode rate block C_star C_h ⟨input, hpre⟩ hnext⟩ := by
  simp [endpointNextCarryObservation, hpre, hnext, id]

/-- The actual next-carry coordinate is measurable, using the previously
proved coordinatewise constructor on the existing prelaunch subtype. -/
theorem measurable_endpointNextCarryObservation {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (endpointNextCarryObservation rate block C_star C_h) := by
  classical
  by_cases hnext : block.val + 1 < n_boot p
  · have hcode : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        (⟨ActualInitializationRun.successorBlock p block hnext,
          endpointNextCarryCode rate block C_star C_h input hnext⟩ : EndpointNextCarryCode p rate)) :=
      (measurable_endpointNextCarrySigmaMk
        (ActualInitializationRun.successorBlock p block hnext)).comp
        (measurable_endpointNextCarryCode rate block C_star C_h hnext)
    have hsome : Measurable (fun input : PrelaunchEndpointInput p rate block C_star C_h =>
        Sum.inr (⟨ActualInitializationRun.successorBlock p block hnext,
          endpointNextCarryCode rate block C_star C_h input hnext⟩ : EndpointNextCarryCode p rate)) :=
      (measurable_inr : Measurable (@Sum.inr Unit (EndpointNextCarryCode p rate))).comp hcode
    have hpiece : Measurable
        (fun input : BoundaryEndpointInput p rate block C_star C_h =>
          if hpre : input ∈ endpointPrelaunchSet p rate block C_star C_h then
            Sum.inr (⟨ActualInitializationRun.successorBlock p block hnext,
              endpointNextCarryCode rate block C_star C_h ⟨input, hpre⟩ hnext⟩ :
                EndpointNextCarryCode p rate)
          else Sum.inl ()) :=
      Measurable.dite hsome measurable_const
        (measurableSet_endpointPrelaunchSet rate block C_star C_h)
    have hEq : endpointNextCarryObservation rate block C_star C_h =
        fun input : BoundaryEndpointInput p rate block C_star C_h =>
          if hpre : input ∈ endpointPrelaunchSet p rate block C_star C_h then
            Sum.inr (⟨ActualInitializationRun.successorBlock p block hnext,
              endpointNextCarryCode rate block C_star C_h ⟨input, hpre⟩ hnext⟩ :
                EndpointNextCarryCode p rate)
          else Sum.inl () := by
      funext input
      simp [endpointNextCarryObservation, hnext, endpointPrelaunchSet]
    rw [hEq]
    exact hpiece
  · have hEq : endpointNextCarryObservation rate block C_star C_h =
        fun _ : BoundaryEndpointInput p rate block C_star C_h =>
          (Sum.inl () : EndpointNextCarryObservation p rate block) := by
      funext input
      simp [endpointNextCarryObservation, hnext]
    rw [hEq]
    exact measurable_const

/-- The complete local observation of one finished block. It retains the
whole source, the selected original row and target, the phase code, every full
follower code, checked and unchecked F boundary outputs, the separate actual
bootstrap numerator update, and the existing next-carry code when a successor
exists. The proof fields record only the endpoint alignment and completion
facts supplied by the real fold. -/
structure CombinedBoundaryObservation (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) where
  originalSource : SourceInput p
  selectedRow : CompletePublicTable.CompleteRow p
  selectedRow_eq : selectedRow = originalSource.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p originalSource)
  selectedTarget : Fin p.K
  selectedTarget_eq : selectedTarget = BootstrapPhysicalInput.targetArmMap p block
    originalSource.2
  targetScalar : BootstrapPrivateRoundStreams.Scalar
  phaseCode : PhaseCode p
  phaseValid : endpointPhaseValid p block C_star C_h originalSource phaseCode
  followerCodes : Fin (p.m - 1) → FollowerCode p rate block
  followersComplete : ∀ i, ActualInitializationRun.followerAtCursor p rate block
    (BootstrapObservedFollower.blockLength p block)
    (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
      (followerCodes i))
  checkedBoundaryOutputs : Fin (p.m - 1) →
    ActualInitializationFollowerBoundaryMeasurability.TotalBoundaryCode p rate
  uncheckedBoundaryOutputs : Fin (p.m - 1) →
    ActualInitializationFollowerBoundaryMeasurability.BoundaryOutputCode p rate
  checkedOutputAgreement : ∀ i,
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryFollowerCode
      p rate block (checkedBoundaryOutputs i) =
      .ok (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
        p rate (uncheckedBoundaryOutputs i))
  updatedNumerators : Fin (p.m - 1) → Option (Fin p.K → ℕ)
  updatedNumerators_eq : ∀ i, updatedNumerators i =
    ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
      p rate block (followerCodes i)
  nextCarry : EndpointNextCarryObservation p rate block

instance combinedBoundaryObservationMeasurableSpace (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSpace (CombinedBoundaryObservation p rate block C_star C_h) :=
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.originalSource) (Prod.instMeasurableSpace) ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.selectedRow) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.selectedTarget) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.targetScalar) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.phaseCode) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.followerCodes) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.checkedBoundaryOutputs) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.uncheckedBoundaryOutputs) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.updatedNumerators) inferInstance ⊔
  MeasurableSpace.comap (fun o : CombinedBoundaryObservation p rate block C_star C_h =>
    o.nextCarry) inferInstance

/-- Build the joint observation from the independent whole-source, accepted
continuation-code, and full follower-code endpoint coordinates. -/
def combinedBoundaryObservationOfInput {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (input : BoundaryEndpointInput p rate block C_star C_h) :
    CombinedBoundaryObservation p rate block C_star C_h := by
  let source := input.1.1
  let phase := input.1.2.1
  let followers := input.1.2.2
  refine ⟨source, source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source),
    rfl, BootstrapPhysicalInput.targetArmMap p block source.2, rfl,
    BootstrapPhysicalInput.coordinatorTargetScalarAt p block source.2,
    phase, input.2.1, followers, input.2.2,
    (fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryFollowerCode
      p rate block (followers i)),
    (fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
      p rate block (followers i)),
    (fun i => ActualInitializationFollowerBoundaryMeasurability.checked_boundaryOutput_agrees_of_complete
      p rate block (followers i) (input.2.2 i)),
    (fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
      p rate block (followers i)),
    (fun _ => rfl),
    endpointNextCarryObservation rate block C_star C_h input⟩

/-- Joint endpoint observation producer, measurable in the natural original
source and product of the accepted continuation and all full follower codes. -/
theorem measurable_combinedBoundaryObservationOfInput {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (combinedBoundaryObservationOfInput rate block C_star C_h) := by
  let hbase : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (input.1 : EndpointBase p rate block)) :=
    (measurable_subtype_coe : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (input : EndpointBase p rate block)))
  let hsource := measurable_fst.comp hbase
  let hphase : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (input.1.2.1 : PhaseCode p)) := measurable_fst.comp (measurable_snd.comp hbase)
  let hfollowers : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      input.1.2.2) := measurable_snd.comp (measurable_snd.comp hbase)
  have hselectedBase : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p input.1.1 C_star C_h) :=
    (BootstrapCoordinatorRoundMeasurability.measurable_selectedCoordinatorBase p C_star C_h).comp
      hsource
  have hrow : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p input.1.1 C_star C_h).1.1) :=
    measurable_fst.comp (measurable_fst.comp hselectedBase)
  have htarget : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      BootstrapPhysicalInput.targetArmMap p block input.1.1.2) :=
    (BootstrapPhysicalInput.measurable_targetArmMap p block).comp
      (measurable_snd.comp hsource)
  have hscalar : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      BootstrapPhysicalInput.coordinatorTargetScalarAt p block input.1.1.2) :=
    (BootstrapPhysicalInput.measurable_coordinatorTargetScalarAt p block).comp
      (measurable_snd.comp hsource)
  have hchecked : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryFollowerCode
          p rate block (input.1.2.2 i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryFollowerCode
      p rate block).comp ((measurable_pi_apply i).comp hfollowers)
  have hunchecked : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
          p rate block (input.1.2.2 i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryOutputFromFollowerCode
      p rate block).comp ((measurable_pi_apply i).comp hfollowers)
  have hnumerators : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        fun i => ActualInitializationFollowerBoundaryMeasurability.boundaryUpdatedNumeratorsCode
          p rate block (input.1.2.2 i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryUpdatedNumeratorsCode
      p rate block).comp ((measurable_pi_apply i).comp hfollowers)
  have hnext := measurable_endpointNextCarryObservation rate block C_star C_h
  have hsource' : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (combinedBoundaryObservationOfInput rate block C_star C_h input).originalSource) := by
    change Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h => input.1.1)
    exact hsource
  have hrow' : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (combinedBoundaryObservationOfInput rate block C_star C_h input).selectedRow) := by
    simpa [combinedBoundaryObservationOfInput,
      BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase,
      ActualInitializationPhysicalStep.selectedRowIndex] using hrow
  have htarget' : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (combinedBoundaryObservationOfInput rate block C_star C_h input).selectedTarget) := by
    simpa [combinedBoundaryObservationOfInput] using htarget
  have hscalar' : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (combinedBoundaryObservationOfInput rate block C_star C_h input).targetScalar) := by
    simpa [combinedBoundaryObservationOfInput] using hscalar
  have hphase' : Measurable (fun input : BoundaryEndpointInput p rate block C_star C_h =>
      (combinedBoundaryObservationOfInput rate block C_star C_h input).phaseCode) := by
    simpa [combinedBoundaryObservationOfInput] using hphase
  have hfollowerCodes' : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (combinedBoundaryObservationOfInput rate block C_star C_h input).followerCodes) := by
    simpa [combinedBoundaryObservationOfInput] using hfollowers
  have hchecked' : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (combinedBoundaryObservationOfInput rate block C_star C_h input).checkedBoundaryOutputs) := by
    simpa [combinedBoundaryObservationOfInput] using hchecked
  have hunchecked' : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (combinedBoundaryObservationOfInput rate block C_star C_h input).uncheckedBoundaryOutputs) := by
    simpa [combinedBoundaryObservationOfInput] using hunchecked
  have hnumerators' : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (combinedBoundaryObservationOfInput rate block C_star C_h input).updatedNumerators) := by
    simpa [combinedBoundaryObservationOfInput] using hnumerators
  have hnext' : Measurable
      (fun input : BoundaryEndpointInput p rate block C_star C_h =>
        (combinedBoundaryObservationOfInput rate block C_star C_h input).nextCarry) := by
    simpa [combinedBoundaryObservationOfInput] using hnext
  apply Measurable.of_comap_le
  simp only [combinedBoundaryObservationMeasurableSpace,
    MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, sup_le_iff, and_assoc]
  constructor
  · simpa only [Function.comp_def] using hsource'.comap_le
  constructor
  · simpa only [Function.comp_def] using hrow'.comap_le
  constructor
  · simpa only [Function.comp_def] using htarget'.comap_le
  constructor
  · simpa only [Function.comp_def] using hscalar'.comap_le
  constructor
  · simpa only [Function.comp_def] using hphase'.comap_le
  constructor
  · simpa only [Function.comp_def] using hfollowerCodes'.comap_le
  constructor
  · simpa only [Function.comp_def] using hchecked'.comap_le
  constructor
  · simpa only [Function.comp_def] using hunchecked'.comap_le
  constructor
  · simpa only [Function.comp_def] using hnumerators'.comap_le
  · simpa only [Function.comp_def] using hnext'.comap_le

/-! ## Literal endpoint decoder -/

/-- Build a disposition from an already decoded continuation and the stored
next-carry code. -/
def endpointDispositionFromData {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (nextCarry : EndpointNextCarryObservation p rate block) :
    ActualInitializationRun.BoundaryDisposition p rate block := by
  cases phase with
  | launched launch =>
      exact .launched launch
        ⟨Bandits.Support.FirstAssignmentLaunch.Input.baseScores p, rfl,
          Bandits.Support.FirstAssignmentLaunch.Input.initialQueues p, rfl⟩
  | prelaunch live =>
      cases nextCarry with
      | inl absent => exact .exhausted live
      | inr encoded =>
          exact .continueNext encoded.1
            (ActualInitializationBlockMeasurability.blockCarryOfCode rate C_star C_h
              encoded.2)

/-- Decode the disposition from the retained phase and carry coordinates.
The continuation decoder assembles the original local coordinator and monitor
fields; an observed successor uses the existing `BlockCarryCode` decoder. -/
def endpointDispositionOfObservation {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (observation : CombinedBoundaryObservation p rate block C_star C_h) :
    ActualInitializationRun.BoundaryDisposition p rate block := by
  exact endpointDispositionFromData
    (C_star := C_star) (C_h := C_h)
    (continuationOfEndpointCode p block C_star C_h observation.originalSource
      observation.phaseCode observation.phaseValid) observation.nextCarry

/-- Assemble the existing `CombinedBoundaryHandoff` by decoding the stored
fields. This decoder reads neither a fold nor the original handoff producer. -/
def combinedBoundaryHandoffOfObservation {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (observation : CombinedBoundaryObservation p rate block C_star C_h) :
    ActualInitializationRun.CombinedBoundaryHandoff p rate block
      observation.originalSource := by
  refine ⟨observation.originalSource,
    (fun i => ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
      p rate (observation.uncheckedBoundaryOutputs i)),
    observation.selectedRow, observation.selectedRow_eq,
    observation.selectedTarget, observation.selectedTarget_eq,
    endpointDispositionOfObservation observation⟩

/-- The checked code stored beside each unchecked output really decodes to
success with that same output. -/
theorem combinedBoundaryHandoffOfObservation_checked {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (observation : CombinedBoundaryObservation p rate block C_star C_h)
    (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryFollowerCode
      p rate block (observation.checkedBoundaryOutputs i) =
      .ok ((combinedBoundaryHandoffOfObservation observation).followers i) := by
  simpa [combinedBoundaryHandoffOfObservation] using observation.checkedOutputAgreement i

/-- The real fold-specific checked-output theorem validates each stored code
against the corresponding unchecked decoded boundary output. -/
theorem combinedBoundaryObservation_checked_agrees_of_blockFold {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} (folded : ActualInitializationRun.BlockFoldOutput p rate block
      source rewards C_star C_h 0) (i : Fin (p.m - 1)) :
    ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryFollowerCode
      p rate block
        ((combinedBoundaryObservationOfInput rate block C_star C_h
          (endpointInputOfBlockFold folded)).checkedBoundaryOutputs i) =
      .ok (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
        p rate
          ((combinedBoundaryObservationOfInput rate block C_star C_h
            (endpointInputOfBlockFold folded)).uncheckedBoundaryOutputs i)) := by
  simpa [combinedBoundaryObservationOfInput, endpointInputOfBlockFold] using
    ActualInitializationFollowerBoundaryMeasurability.checked_boundaryOutput_agrees_of_blockFold
      folded i

/-- On an actual fold, decoding all stored unchecked outputs recovers the
actual completed block's simultaneous boundary followers. -/
theorem combinedBoundaryObservationOfInput_followers_of_blockFold {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0) :
    (fun i => ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
      p rate
        ((combinedBoundaryObservationOfInput rate block C_star C_h
          (endpointInputOfBlockFold folded)).uncheckedBoundaryOutputs i)) =
      ActualInitializationRun.blockBoundaryFollowers p rate block source rewards folded := by
  funext i
  simp [combinedBoundaryObservationOfInput, endpointInputOfBlockFold,
    ActualInitializationRun.blockBoundaryFollowers,
    ActualInitializationRun.boundaryOutputAtCursor,
    ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode_reconstruction,
    ActualInitializationRoundMeasurability.followerStateOfCode_encode]

/-- Equality of existing handoffs follows from equality of their stored data
and decoded disposition. -/
theorem combinedBoundaryHandoff_ext_of_fields {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {source : SourceInput p}
    (left right : ActualInitializationRun.CombinedBoundaryHandoff p rate block source)
    (hsource : left.originalSource = right.originalSource)
    (hfollowers : left.followers = right.followers)
    (hrow : left.selectedRow = right.selectedRow)
    (htarget : left.selectedTarget = right.selectedTarget)
    (hdisposition : left.disposition = right.disposition) : left = right := by
  cases left
  cases right
  simp_all

/-- Encoding a real completed fold into independent endpoint coordinates and
decoding them reconstructs the exact existing combined boundary handoff. -/
theorem combinedBoundaryObservation_reconstructs_actual {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0) :
    combinedBoundaryHandoffOfObservation
        (combinedBoundaryObservationOfInput rate block C_star C_h
          (endpointInputOfBlockFold folded)) =
      ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        C_star C_h folded := by
  classical
  cases folded with
  | mk consumed phase followers records invariant consumed_eq record_count chronological =>
      let folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
          C_star C_h 0 :=
        ⟨consumed, phase, followers, records, invariant, consumed_eq, record_count, chronological⟩
      let observation := combinedBoundaryObservationOfInput rate block C_star C_h
        (endpointInputOfBlockFold folded)
      let decoded := combinedBoundaryHandoffOfObservation observation
      let actual := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        C_star C_h folded
      have hdecoded : continuationOfEndpointCode p block C_star C_h
          observation.originalSource observation.phaseCode observation.phaseValid = folded.phase := by
        dsimp [observation, combinedBoundaryObservationOfInput, endpointInputOfBlockFold]
        exact continuationOfEndpointCode_endpointInputOfBlockFold folded
      have hfollowers : decoded.followers = actual.followers := by
        change (fun i => ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate (observation.uncheckedBoundaryOutputs i)) =
          ActualInitializationRun.blockBoundaryFollowers p rate block source rewards folded
        exact combinedBoundaryObservationOfInput_followers_of_blockFold folded
      have hrow : decoded.selectedRow = actual.selectedRow := by
        calc
          decoded.selectedRow = source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) := rfl
          _ = actual.selectedRow := actual.selectedRow_eq.symm
      have htarget : decoded.selectedTarget = actual.selectedTarget := by
        calc
          decoded.selectedTarget = BootstrapPhysicalInput.targetArmMap p block source.2 := rfl
          _ = actual.selectedTarget := actual.selectedTarget_eq.symm
      have hdisposition : decoded.disposition = actual.disposition := by
        change endpointDispositionOfObservation observation = actual.disposition
        unfold endpointDispositionOfObservation
        rw [hdecoded]
        cases phase with
        | launched launch =>
            simp [endpointDispositionFromData, actual, id,
              ActualInitializationRun.combinedBoundaryHandoff, folded]
        | prelaunch live =>
            by_cases hlast : block.val + 1 = n_boot p
            · have hnoNext : ¬ block.val + 1 < n_boot p := by omega
              have hcarry : observation.nextCarry = Sum.inl () := by
                change endpointNextCarryObservation rate block C_star C_h
                  (endpointInputOfBlockFold folded) = Sum.inl ()
                exact endpointNextCarryObservation_absent rate block C_star C_h
                  (endpointInputOfBlockFold folded) hnoNext
              rw [hcarry]
              simp [endpointDispositionFromData, actual, id,
                ActualInitializationRun.combinedBoundaryHandoff,
                folded, hlast]
            · have hnext : block.val + 1 < n_boot p := by omega
              have hpre : endpointInputOfBlockFold folded ∈
                  endpointPrelaunchSet p rate block C_star C_h := by
                simp [endpointPrelaunchSet, endpointInputOfBlockFold,
                  ActualInitializationBlockMeasurability.continuationCodeOf, folded]
              have hcarry : observation.nextCarry = Sum.inr
                  ⟨ActualInitializationRun.successorBlock p block hnext,
                    endpointNextCarryCode rate block C_star C_h
                      ⟨endpointInputOfBlockFold folded, hpre⟩ hnext⟩ := by
                change endpointNextCarryObservation rate block C_star C_h
                  (endpointInputOfBlockFold folded) = _
                exact endpointNextCarryObservation_present rate block C_star C_h
                  (endpointInputOfBlockFold folded) hpre hnext
              rw [hcarry]
              simp [endpointDispositionFromData, actual, id,
                ActualInitializationRun.combinedBoundaryHandoff,
                endpointNextCarryCode, endpointInputOfBlockFold, endpointUnlaunchedMonitorCode,
                ActualInitializationBlockMeasurability.continuationCodeOf,
                ActualInitializationRun.continuationData,
                ActualInitializationBlockMeasurability.blockCarryOfCode,
                BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode_encode,
                BootstrapCoordinatorRoundMeasurability.monitorStateOfCode_encode,
                BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
                BootstrapCoordinatorLocalRound.Continuation.monitorState,
                ActualInitializationBlockMeasurability.BlockCarryCodeFields.activationReady,
                boundaryFollowerCarryCode_reconstructs_actual,
                ActualInitializationRoundMeasurability.followerStateOfCode_encode,
                folded, hlast]
      exact combinedBoundaryHandoff_ext_of_fields decoded actual rfl hfollowers hrow htarget
        hdisposition

/-- On the actual nonterminal prelaunch branch, the existing handoff's
`continueNext` payload is precisely the measurable fixed-constant carry above.
The only branch inputs are the actual no-launch tag and a real successor. -/
theorem combinedBoundaryHandoff_continueNext_eq_endpointNextCarry
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (hpre : (ActualInitializationBlockMeasurability.continuationCodeOf
      folded.phase).2.2.2.2 = none)
    (hnext : block.val + 1 < n_boot p) :
    (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition =
        .continueNext (ActualInitializationRun.successorBlock p block hnext)
          (endpointNextCarry rate block C_star C_h
            ⟨endpointInputOfBlockFold folded, hpre⟩ hnext).1 := by
  rw [← combinedBoundaryObservation_reconstructs_actual folded]
  change endpointDispositionOfObservation
    (combinedBoundaryObservationOfInput rate block C_star C_h
      (endpointInputOfBlockFold folded)) = _
  unfold endpointDispositionOfObservation
  change endpointDispositionFromData (C_star := C_star) (C_h := C_h)
    (continuationOfEndpointCode p block C_star C_h source
      (ActualInitializationBlockMeasurability.continuationCodeOf folded.phase)
      (endpointPhaseValid_of_blockFold folded))
    (endpointNextCarryObservation rate block C_star C_h
      (endpointInputOfBlockFold folded)) = _
  rw [continuationOfEndpointCode_endpointInputOfBlockFold]
  rw [endpointNextCarryObservation_present rate block C_star C_h
    (endpointInputOfBlockFold folded) hpre hnext]
  cases hphase : folded.phase with
  | prelaunch live => rfl
  | launched launch =>
      simp only [hphase, ActualInitializationBlockMeasurability.continuationCodeOf] at hpre
      cases hpre

/-- Inspecting the actual disposition gives the exact successor, equality of
its carry with the Borel endpoint carry, and both original fixed constants.
Only the no-launch tag and real-successor branch conditions are inputs. -/
theorem endpointNextCarry_eq_actual_continueNext
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (hpre : (ActualInitializationBlockMeasurability.continuationCodeOf
      folded.phase).2.2.2.2 = none)
    (hnext : block.val + 1 < n_boot p) :
    match (ActualInitializationRun.combinedBoundaryHandoff p rate block source
      rewards C_star C_h folded).disposition with
    | .continueNext next nextCarry =>
        next = ActualInitializationRun.successorBlock p block hnext ∧
          HEq nextCarry (endpointNextCarry rate block C_star C_h
            ⟨endpointInputOfBlockFold folded, hpre⟩ hnext).1 ∧
              nextCarry.C_star = C_star ∧ nextCarry.C_h = C_h
    | .launched _ _ => False
    | .exhausted _ => False := by
  rw [combinedBoundaryHandoff_continueNext_eq_endpointNextCarry folded hpre hnext]
  exact ⟨rfl, HEq.rfl, endpointNextCarry_constants rate block C_star C_h
    ⟨endpointInputOfBlockFold folded, hpre⟩ hnext⟩

end Bandits.Support.ActualInitializationCombinedBoundaryMeasurability

end
