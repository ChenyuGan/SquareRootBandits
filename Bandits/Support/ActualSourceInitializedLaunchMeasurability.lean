/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationTerminalCarryHandoff

/-!
# Actual source-initialized pre-horizon launch input

On the literal source event of a launch strictly before the horizon, this
module packages the original run's actual next-block physical input in the
existing dependent block carrier.  Its code retains the whole original
source and reward table, the actual coordinator and decoder-bank launch
initialization, and every follower's actual terminal carry begun with that
follower's original next-block private scalar triple.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:28-34,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

These results construct and prove measurability of the actual pre-horizon
launch input on its event subtype.  They do not construct postlaunch suffix
iteration or assert measurability of a whole actual history.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.ActualInitializationRun

namespace Bandits.Support.ActualSourceInitializedLaunchMeasurability

abbrev Parameters := ActualInitializationTerminalCarryHandoff.Parameters
abbrev RateInput := ActualInitializationTerminalCarryHandoff.RateInput
abbrev GridRewardTable := ActualInitializationTerminalCarryHandoff.GridRewardTable
abbrev SourceInput (p : Parameters) :=
  ActualInitializationTerminalCarryHandoff.SourceInput p

variable {p : Parameters} {rate : RateInput p} {C_star C_h : ℝ}
  {rewards : GridRewardTable p}

/-- The actual source domain of the pre-horizon terminal launch producer. -/
abbrev LaunchDomain :=
  {source : SourceInput p // source ∈
    ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards)}

/-- The event-restricted constructor match used by
`sourceInitializedLaunchInput`.  The actual disposition and its equality to
the selected constructor are explicit inputs, so this helper cannot create a
launch on a source whose actual run has another terminal disposition. -/
def sourceInitializedLaunchInputCore
    (source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards))
    (disposition : ActualInitializationRun.BoundaryDisposition p rate
      (ActualInitializationHorizon.sourceInitializedRun p rate source.1
        rewards C_star C_h).terminalBlock)
    (hdisp : (ActualInitializationHorizon.sourceInitializedRun p rate source.1
      rewards C_star C_h).terminalDisposition = disposition) :
    Sigma (fun next : Fin (n_boot p) =>
      ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) next 0) := by
  cases disposition with
  | continueNext next carry =>
      have hfalse : False := by
        rcases (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source.1).mp source.2 with
          ⟨launch, learnerSeed, hlaunch, _⟩
        have hneq := hdisp.symm.trans hlaunch
        cases hneq
      exact False.elim hfalse
  | launched launch learnerSeed =>
      have hmem := source.2
      simp only [ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent,
        Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
      have hboundary₀ := hmem.2
      have hboundary : BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source.1
            rewards C_star C_h).terminalBlock < p.T := by
        change BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source.1
            rewards C_star C_h).terminalBlock < p.T at hboundary₀
        exact hboundary₀
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source.1 rewards C_star C_h launch learnerSeed hdisp
      have hbefore : launch.monitor.launchPosition < p.T := by
        rw [← hstrict.2.2.2] at hboundary
        exact hboundary
      exact ⟨
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate
          source.1 rewards C_star C_h launch learnerSeed hdisp hbefore,
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate
          source.1 rewards C_star C_h launch learnerSeed hdisp hbefore⟩
  | exhausted live =>
      have hfalse : False := by
        rcases (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source.1).mp source.2 with
          ⟨launch, learnerSeed, hlaunch, _⟩
        have hneq := hdisp.symm.trans hlaunch
        cases hneq
      exact False.elim hfalse

/-- The source-initialized launch input, indexed by the actual successor block.
It matches the disposition of the same source-initialized run; the event
proof rules out continuation and exhaustion, and the launched value is M's
actual successor input. -/
def sourceInitializedLaunchInput (source : LaunchDomain
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards)) :
    Sigma (fun next : Fin (n_boot p) =>
      ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) next 0) :=
  let run := ActualInitializationHorizon.sourceInitializedRun p rate
    source.1 rewards C_star C_h
  sourceInitializedLaunchInputCore (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    run.terminalDisposition rfl

/-- On an original source and actual launched constructor with strict
pre-horizon position, the value on the event subtype is exactly M's dependent
successor block and physical input. -/
theorem sourceInitializedLaunchInput_eq_actual
    (source : SourceInput p)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    sourceInitializedLaunchInput
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards)
        ⟨source, (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source).mpr
          ⟨launch, learnerSeed, hlaunch, hbefore⟩⟩ =
      ⟨ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate
          source rewards C_star C_h launch learnerSeed hlaunch hbefore,
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate
          source rewards C_star C_h launch learnerSeed hlaunch hbefore⟩ := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source
    rewards C_star C_h
  let hE : source ∈
      ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) :=
    (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).mpr
      ⟨launch, learnerSeed, hlaunch, hbefore⟩
  let source' : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) := ⟨source, hE⟩
  change sourceInitializedLaunchInputCore (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      source' run.terminalDisposition rfl = _
  let dispositionWithProof :
      {disposition : ActualInitializationRun.BoundaryDisposition p rate
          run.terminalBlock // run.terminalDisposition = disposition} :=
    ⟨run.terminalDisposition, rfl⟩
  let launchedWithProof :
      {disposition : ActualInitializationRun.BoundaryDisposition p rate
          run.terminalBlock // run.terminalDisposition = disposition} :=
    ⟨.launched launch learnerSeed, hlaunch⟩
  have harg : dispositionWithProof = launchedWithProof := by
    apply Subtype.ext
    exact hlaunch
  have hcore :
      sourceInitializedLaunchInputCore (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards)
          source' run.terminalDisposition rfl =
        sourceInitializedLaunchInputCore (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards)
          source' (.launched launch learnerSeed) hlaunch :=
    congrArg (fun witness => sourceInitializedLaunchInputCore (p := p)
      (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
      source' witness.1 witness.2) harg
  rw [hcore]
  rfl

/-- The literal code formula for the launched input, over P's existing
whole-source, whole-reward, coordinator, decoder-bank and follower-code
coordinates. -/
private def sourceInitializedLaunchInputCode (next : Fin (n_boot p))
    (source : SourceInput p) :
    ActualPostlaunchPreparationMeasurability.InputCoordinates p rate next :=
  (source, (rewards,
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator .first,
      (CoordinatorUpReception.initialUpDecoderBank p, fun i =>
        ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
          next source i
          (ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalHandoffFollowerCarryCodes
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) source i)))))

/-- P's input encoder on the composed launch value is exactly the actual
source/reward/coordinator/bank/follower formula above.  The follower equality
uses H's actual terminal carry-code identity and B's existing start-code
characterization. -/
theorem sourceInitializedLaunchInput_encodeInput
    (source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards)) :
    let input := sourceInitializedLaunchInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    ActualPostlaunchPreparationMeasurability.encodeInput
        (block := input.1) (cursor := 0) input.2 =
      (source.1, (rewards,
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator .first,
          (CoordinatorUpReception.initialUpDecoderBank p, fun i =>
            ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
              input.1 source.1 i
              (ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalHandoffFollowerCarryCodes
                (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
                (rewards := rewards) source.1 i))))) := by
  let input := sourceInitializedLaunchInput (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  rcases (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source.1).mp source.2 with
    ⟨launch, learnerSeed, hlaunch, hbefore⟩
  dsimp only [input]
  rw [sourceInitializedLaunchInput_eq_actual (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)
    source.1 launch learnerSeed hlaunch hbefore]
  dsimp [
    ActualPostlaunchPreparationMeasurability.encodeInput,
    ActualPostlaunchPreparationMeasurability.encodeState,
    ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput,
    ActualPostlaunchPhysicalStep.sourceInitializedLaunchedFollower]
  let actualNext := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock
    p rate source.1 rewards C_star C_h launch learnerSeed hlaunch hbefore
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · funext i
          let carry := ActualInitializationRun.followerCarryOfBoundaryOutput rate
            ((ActualInitializationHorizon.sourceInitializedRun p rate source.1
              rewards C_star C_h).terminalHandoff.followers i)
          have hbegin :=
            ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode_followerCarryCodeOf
              (p := p) (rate := rate) actualNext source.1 i carry
          have hactualCode :=
            ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalBoundaryFollowerCarryCodes_actual_code
              (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
              (rewards := rewards) source.1 i
          let terminalCode : ActualInitializationBlockMeasurability.FollowerCarryCode p rate :=
            (ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
              (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
              (rewards := rewards) source.1).2 i
          have hactualCode' :
              ActualInitializationBlockMeasurability.followerCarryCodeOf carry = terminalCode := by
            change ActualInitializationBlockMeasurability.followerCarryCodeOf carry =
              (ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
                (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
                (rewards := rewards) source.1).2 i
            exact hactualCode
          have hterminalToHandoff : terminalCode =
              ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalHandoffFollowerCarryCodes
                (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
                (rewards := rewards) source.1 i := by
            exact hactualCode'.symm.trans rfl
          calc
            ActualInitializationRoundMeasurability.followerCodeOfState p rate actualNext
                (ActualInitializationRun.beginFollowerBlock p rate actualNext source.1 i carry) =
              ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry
                actualNext source.1 i carry := rfl
            _ = ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
                actualNext source.1 i
                (ActualInitializationBlockMeasurability.followerCarryCodeOf carry) :=
              hbegin.symm
            _ = ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
                actualNext source.1 i terminalCode := by
              exact congrArg
                (ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
                  actualNext source.1 i) hactualCode'
            _ = ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
                actualNext source.1 i
                (ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalHandoffFollowerCarryCodes
                  (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
                  (rewards := rewards) source.1 i) := by
              exact congrArg
                (ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
                  actualNext source.1 i) hterminalToHandoff

/-- Measurability of the fixed-next-block code formula follows from H's joint
actual carry-code readout and B's joint start-code map. -/
private theorem measurable_sourceInitializedLaunchInputCode
    (next : Fin (n_boot p)) :
    Measurable (sourceInitializedLaunchInputCode (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) next) := by
  have hcarry :=
    ActualInitializationTerminalCarryHandoff.measurable_sourceInitializedTerminalHandoffFollowerCarryCodes
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards)
  have hfollowers : Measurable (fun source : SourceInput p =>
      fun i : Fin (p.m - 1) =>
        ActualInitializationBeginJointMeasurability.beginFollowerCodeOfCarryCode
          next source i
          (ActualInitializationTerminalCarryHandoff.sourceInitializedTerminalHandoffFollowerCarryCodes
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) source i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact
      (ActualInitializationBeginJointMeasurability.measurable_beginFollowerCodeOfCarryCode
        (p := p) (rate := rate) next i).comp
        (measurable_id.prodMk ((measurable_pi_apply i).comp hcarry))
  exact measurable_id.prodMk (measurable_const.prodMk
    (measurable_const.prodMk
      (measurable_const.prodMk hfollowers)))

private def sourceInitializedLaunchInputIndex
    (source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards)) : Fin (n_boot p) :=
  (sourceInitializedLaunchInput (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) source).1

private theorem measurable_sourceInitializedTerminalSuccessorIndexUnion
    (next : Fin (n_boot p)) :
    MeasurableSet
      (ActualInitializationTerminalReadout.sourceInitializedTerminalSuccessorIndexUnion
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) next) := by
  change MeasurableSet (⋃ block : Fin (n_boot p),
    {source : SourceInput p | block.val + 1 = next.val ∧
      source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchAtBlock
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) block ∧
      BootstrapObservedFollower.blockStop p block < p.T})
  apply MeasurableSet.iUnion
  intro block
  have hindex : MeasurableSet
      {source : SourceInput p | block.val + 1 = next.val} := by
    by_cases h : block.val + 1 = next.val <;> simp [h]
  have hlaunch :=
    ActualInitializationSourceObservation.measurable_sourceInitializedRunTerminalLaunchAtBlock
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) block
  have hboundary : MeasurableSet
      {source : SourceInput p | BootstrapObservedFollower.blockStop p block < p.T} := by
    by_cases h : BootstrapObservedFollower.blockStop p block < p.T <;> simp [h]
  exact hindex.inter (hlaunch.inter hboundary)

private theorem measurable_sourceInitializedLaunchInputIndex :
    Measurable (sourceInitializedLaunchInputIndex (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  apply measurable_to_countable'
  intro next
  have hfiber :
      (sourceInitializedLaunchInputIndex (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) ⁻¹' {next}) =
        (Subtype.val : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) → SourceInput p) ⁻¹'
          ActualInitializationTerminalReadout.sourceInitializedTerminalSuccessorIndexUnion
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) next := by
    ext source
    constructor
    · intro hnext
      have hlabel :
          sourceInitializedLaunchInputIndex (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) source = next := by
        simpa using hnext
      have hactual :=
        (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source.1).mp source.2
      rcases hactual with ⟨launch, learnerSeed, hlaunch, hbefore⟩
      have heq := sourceInitializedLaunchInput_eq_actual (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards)
        source.1 launch learnerSeed hlaunch hbefore
      have hblock := congrArg Sigma.fst heq
      have hblockNext :
          ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate
            source.1 rewards C_star C_h launch learnerSeed hlaunch hbefore = next := by
        exact hblock.symm.trans hlabel
      have hgraph : source.1 ∈
          ActualInitializationTerminalReadout.sourceInitializedActualSuccessorIndexGraph
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) next :=
        ⟨launch, learnerSeed, hlaunch, hbefore, hblockNext⟩
      rw [← ActualInitializationTerminalReadout.sourceInitializedTerminalSuccessorIndexUnion_eq_actualGraph
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) next] at hgraph
      exact hgraph
    · intro hsource
      have hgraph := hsource
      rw [ActualInitializationTerminalReadout.sourceInitializedTerminalSuccessorIndexUnion_eq_actualGraph
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) next] at hgraph
      change source.1 ∈ ActualInitializationTerminalReadout.sourceInitializedActualSuccessorIndexGraph
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) next at hgraph
      simp only [ActualInitializationTerminalReadout.sourceInitializedActualSuccessorIndexGraph,
        Set.mem_setOf_eq] at hgraph
      rcases hgraph with ⟨launch, learnerSeed, hlaunch, hbefore, hblock⟩
      have heq := sourceInitializedLaunchInput_eq_actual (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards)
        source.1 launch learnerSeed hlaunch hbefore
      have hindex := congrArg Sigma.fst heq
      change sourceInitializedLaunchInputIndex (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source = next
      exact hindex.trans hblock
  rw [hfiber]
  have hcoe : Measurable
    (fun source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) => source.1) := measurable_subtype_coe
  exact hcoe (measurable_sourceInitializedTerminalSuccessorIndexUnion
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) next)

private def sourceInitializedLaunchInputFiber (next : Fin (n_boot p))
    (source : {x : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) //
      sourceInitializedLaunchInputIndex (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) x = next}) :
    ActualPostlaunchPhysicalStep.PhysicalInput (p := p) (rate := rate) next 0 :=
  source.2 ▸ (sourceInitializedLaunchInput (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source.1).2

private theorem sourceInitializedLaunchInputFiber_encodeInput
    (next : Fin (n_boot p))
    (source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards))
    (hindex : sourceInitializedLaunchInputIndex (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source = next) :
    ActualPostlaunchPreparationMeasurability.encodeInput
      (block := next) (cursor := 0)
      (hindex ▸ (sourceInitializedLaunchInput (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2) =
      sourceInitializedLaunchInputCode (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) next source.1 := by
  cases hindex
  exact sourceInitializedLaunchInput_encodeInput (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source

private theorem measurable_sourceInitializedLaunchInputFiber
    (next : Fin (n_boot p)) :
    Measurable (sourceInitializedLaunchInputFiber (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) next) := by
  apply measurable_comap_iff.mpr
  have hcode :
      (fun source : {x : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) //
        sourceInitializedLaunchInputIndex (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) x = next} =>
        ActualPostlaunchPreparationMeasurability.encodeInput
          (block := next) (cursor := 0)
          (sourceInitializedLaunchInputFiber (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) next source)) =
      fun source => sourceInitializedLaunchInputCode (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) next source.1.1 := by
    funext source
    exact sourceInitializedLaunchInputFiber_encodeInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) next source.1 source.2
  change Measurable (fun source =>
    ActualPostlaunchPreparationMeasurability.encodeInput
      (block := next) (cursor := 0)
      (sourceInitializedLaunchInputFiber (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) next source))
  rw [hcode]
  exact (measurable_sourceInitializedLaunchInputCode (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) next).comp
      (measurable_subtype_coe.comp measurable_subtype_coe)

private theorem measurable_sigma_of_finite_fibers
    {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {Ω : Type*} [MeasurableSpace Ω]
    (label : Ω → ι) (hlabel : Measurable label)
    (fiber : ∀ i, {x : Ω // label x = i} → β i)
    (hfiber : ∀ i, Measurable (fiber i)) :
    Measurable (fun x => (⟨label x, fiber (label x) ⟨x, rfl⟩⟩ : Sigma β)) := by
  have hmk (i : ι) : Measurable (Sigma.mk i : β i → Sigma β) := by
    rw [measurable_iff_le_map]
    change (⨅ j, (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)) ≤ _
    exact iInf_le _ i
  intro s hs
  have hdecomp :
      (fun x => (⟨label x, fiber (label x) ⟨x, rfl⟩⟩ : Sigma β)) ⁻¹' s =
        ⋃ i, (Subtype.val : {x : Ω // label x = i} → Ω) ''
          {y | fiber i y ∈ (Sigma.mk i) ⁻¹' s} := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨label x, ?_⟩
      refine (Set.mem_image Subtype.val _ x).mpr ⟨⟨x, rfl⟩, ?_, rfl⟩
      simpa using hx
    · intro hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, hxy⟩ := (Set.mem_image Subtype.val _ x).mp hx
      have hlabel : label x = i := by
        rw [← hxy]
        exact y.2
      subst i
      have hy' : y = ⟨x, rfl⟩ := Subtype.ext hxy
      subst y
      simpa using hy
  rw [hdecomp]
  exact MeasurableSet.iUnion fun i => by
    have hbase : MeasurableSet {x : Ω | label x = i} :=
      (measurableSet_singleton i).preimage hlabel
    have hsection : MeasurableSet ((Sigma.mk i) ⁻¹' s) := hmk i hs
    exact hbase.subtype_image (hfiber i hsection)

/-- The actual launch input is jointly Borel on the entire strict pre-horizon
event subtype, including its computed successor index and full physical input
storage. -/
theorem measurable_sourceInitializedLaunchInput :
    Measurable (sourceInitializedLaunchInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  have hassembled :
      (fun source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) =>
        (⟨sourceInitializedLaunchInputIndex (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) source,
          sourceInitializedLaunchInputFiber (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards)
            (sourceInitializedLaunchInputIndex (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) (rewards := rewards) source)
            ⟨source, rfl⟩⟩ :
          Sigma (fun next : Fin (n_boot p) =>
            ActualPostlaunchPhysicalStep.PhysicalInput
              (p := p) (rate := rate) next 0))) =
        sourceInitializedLaunchInput (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
    funext source
    rfl
  rw [← hassembled]
  exact measurable_sigma_of_finite_fibers
    (sourceInitializedLaunchInputIndex (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
    (measurable_sourceInitializedLaunchInputIndex (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
    (sourceInitializedLaunchInputFiber (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
    (measurable_sourceInitializedLaunchInputFiber (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))

end Bandits.Support.ActualSourceInitializedLaunchMeasurability

end
