/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchNumericalCell
public import Bandits.Support.ReferenceFirstWindowRecordingTruth
public import Bandits.Support.ReferenceContinuingRecordingPhysicalReward

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Numerical recording inputs on the actual first-live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

This module starts from the actual corrected launch and the original complete
private input, then extracts the computed first-live record branches. Its
recording cells use the literal snapshot map on the actual assignment,
complement weights, pending set, and ordinary follower states. This is a
finite source-input result; it does not assert a recording law, queue coupling,
collection alignment, or regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceFirstWindowNumericalStream

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
variable {p : Parameters} {rate : RateInput p}
abbrev RoundRecord := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow (p := p) (rate := rate)

/-- Extend the actual live complement weights by the frozen anchor on the
assignment, as required by the existing whole-arm recording map. -/
def sourceWeights (payload : ReferenceActivePhysicalStep.Payload rate)
    (complement : FastArm payload.slowSet → ℝ) : Fin p.K → ℝ :=
  fun arm => if hslow : arm ∈ payload.slowSet.1 then payload.anchor arm else
    complement ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hslow⟩⟩

theorem sourceWeights_pos (payload : ReferenceActivePhysicalStep.Payload rate)
    (complement : FastArm payload.slowSet → ℝ)
    (u : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (hvalid : ChoiceInputsValid payload u time complement) :
    ∀ arm, 0 < sourceWeights payload complement arm := by
  intro arm
  by_cases hslow : arm ∈ payload.slowSet.1
  · simpa [sourceWeights, hslow] using hvalid.anchor_pos arm
  · simpa [sourceWeights, hslow] using
      hvalid.current_weight_pos ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hslow⟩⟩

theorem sourceWeights_lower (payload : ReferenceActivePhysicalStep.Payload rate)
    (complement : FastArm payload.slowSet → ℝ)
    (u : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (hvalid : ChoiceInputsValid payload u time complement) :
    ∀ arm, payload.anchor arm ≤ sourceWeights payload complement arm := by
  intro arm
  by_cases hslow : arm ∈ payload.slowSet.1
  · simp [sourceWeights, hslow]
  · simpa [sourceWeights, hslow] using
      hvalid.anchor_le_current ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hslow⟩⟩

theorem sourceWeights_upper (payload : ReferenceActivePhysicalStep.Payload rate)
    (complement : FastArm payload.slowSet → ℝ)
    (u : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (hvalid : ChoiceInputsValid payload u time complement) :
    ∀ arm, sourceWeights payload complement arm ≤ 2 * payload.anchor arm := by
  intro arm
  by_cases hslow : arm ∈ payload.slowSet.1
  · have hpos := hvalid.anchor_pos arm
    simp [sourceWeights, hslow]
    nlinarith
  · simpa [sourceWeights, hslow] using
      hvalid.current_le_twice_anchor
        ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hslow⟩⟩

/-- The actual whole-row source map for one live record. Its snapshot keeps
the current pending set and every follower's actual prepared status. -/
def sourceArm (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement) :
    Option (Fin p.K) :=
  SnapshotRecordingKernel.recordingMap p
    (.live payload.assignment
      { missing := pending, status := fun i => (states i).status }) true rate.eta.val
    rate.eta.property rate.sourceCap payload.anchor (sourceWeights payload complement)
    payload.anchor_pos (sourceWeights_pos payload complement cutoff record.input.time hvalid)
    (sourceWeights_lower payload complement cutoff record.input.time hvalid)
    (sourceWeights_upper payload complement cutoff record.input.time hvalid)
    (record.input.row.2 record.input.time).1

/-- The deterministic numerical input for one actual round, using the
selected payload and the current actual complement weights. -/
def sourceCell (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement) :
    RecordedQueueRun.RoundInput p.K where
  enabled := true
  recordedArm := sourceArm record payload pending states complement cutoff hvalid
  reward := fun arm => ((record.input.rewards record.input.time arm).val : ℝ) / (D p : ℝ)
  rate := payload.rate
  reward_nonneg := by
    intro arm
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  reward_le_one := by
    intro arm
    have hvalue : (record.input.rewards record.input.time arm).val ≤ D p :=
      Nat.le_of_lt_succ (record.input.rewards record.input.time arm).isLt
    apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
    exact_mod_cast hvalue
  rate_pos := by
    intro arm
    exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (AssignmentStartPayload.Input.beta_le_rate payload arm)

theorem sourceCell_enabled (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement) :
    (sourceCell record payload pending states complement cutoff hvalid).enabled = true := rfl

theorem sourceCell_quantizedArrival (record : RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (complement : FastArm payload.slowSet → ℝ)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : ChoiceInputsValid payload cutoff record.input.time complement)
    (arm : Fin p.K) :
    RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (sourceCell record payload pending states complement cutoff hvalid) arm =
      if sourceArm record payload pending states complement cutoff hvalid = some arm then
        Nat.floor ((rate.n : ℝ) *
          (((record.input.rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
            payload.rate arm)
      else 0 := by
  classical
  unfold RecordedQueueRun.quantizedArrival sourceCell
  by_cases hrecord : sourceArm record payload pending states complement cutoff hvalid = some arm
  · simp [hrecord, ReferenceFirstLaunchNumericalCell.queueParameters]
  · simp [hrecord]

/-- One actual live record's numerical source input, with its selector and
snapshot data obtained from the computed dispatcher branch. -/
structure ActualLiveSourceCell
    (record : RoundRecord (p := p) (rate := rate)) where
  states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta
  memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p
  ordinary : ∀ i,
    (record.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i)
  selected : ReferenceActivePhysicalStep.Selection record.input
  selection_actual : record.output.preparation.coordinator.selection = some selected
  assignment_live : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
    selected.view.cutoff record.input.time
  choiceInputsValid : ChoiceInputsValid selected.view.payload selected.view.cutoff
    record.input.time selected.view.complementWeights
  input : RecordedQueueRun.RoundInput p.K
  input_eq : input = sourceCell record selected.view.payload selected.view.pendingAtChoice
    states selected.view.complementWeights selected.view.cutoff choiceInputsValid
  enabled : input.enabled = true
  recordedArm_eq : input.recordedArm = sourceArm record selected.view.payload
    selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
    choiceInputsValid
  quantizedArrival_eq : ∀ arm : Fin p.K,
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      input arm =
      if sourceArm record selected.view.payload selected.view.pendingAtChoice states
          selected.view.complementWeights selected.view.cutoff choiceInputsValid = some arm then
        Nat.floor ((rate.n : ℝ) *
          (((record.input.rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
            selected.view.payload.rate arm)
      else 0
  coordinatorProjection :
    ∃ out sourceMap,
      record.output.coordinator.recording = some out ∧
      out.gateArm = sourceMap ∧
      out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
        selected.view.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (record.input.rewards record.input.time j)) sourceMap ∧
      ∀ j : Fin p.K,
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
          some (if out.gateArm = some j then out.rawArrival else 0)
  followerDataClaim :
    ReferenceFirstWindowRecordingTruth.actual_window_follower_data_claim
      record selected states record.input.rewards
  followerRawArrivalGate : ∀ i : Fin (p.m - 1),
    ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
      (selected.view.payload.downRecord i) →
    ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row record.input.time
      (selected.view.payload.downRecord i)
      (record.output.ownEntries
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
      ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta
        (selected.view.payload.downRecord i)
        (record.output.ownEntries
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
  followerRawArrivalNoGate : ∀ i : Fin (p.m - 1),
    ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
      (selected.view.payload.downRecord i) →
    ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row record.input.time
      (selected.view.payload.downRecord i)
      (record.output.ownEntries
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 = 0

/-- The full actual follower seed and every local domain condition required
by the first-live safety producer. -/
structure FirstLiveSeed (initial : ReferenceActivePhysicalHorizon.State p rate)
    (start : ℕ) where
  followers : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta
  memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p
  configuration : ∀ i, initial.followers i = .ordinary (followers i) (memory i)
  acceptedStart_zero : ∀ i, ReferencePrelaunchFollower.acceptedStart (followers i) = 0
  S_zero : ∀ i, (followers i).S = 0
  delta_zero : ∀ i, (followers i).delta = 0
  backlog_zero : ∀ i, (followers i).backlog = 0
  lastDown_none : ∀ i, (followers i).lastDown = none
  unoccupied : ∀ i, (followers i).status = .unoccupied
  localStateDomain : ∀ i, ActiveFollowerLifecycle.localStateDomainValid (followers i)
  bufferValid : ∀ i, ActiveFollowerLifecycle.localBufferValid (followers i)
  chronologicalBuffer : ∀ i,
    (followers i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound)
  bufferStamps : ∀ i saved, saved ∈ (followers i).buffer → saved.calendarRound ≤ start
  decoderValid : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (followers i)
  activeAtStart : ReferenceActivePhysicalHorizon.allActiveAtStart initial start
  coordinatorFirst : initial.coordinator = .first

/-- Construct the actual first-live seed directly from A's corrected launch.
No buffer is cleared, and the original follower initialization state is kept. -/
def actualFirstLiveSeed
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let s := ReferenceInitializationRun.elapsed p b.completed
    FirstLiveSeed
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) s := by
  classical
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let s := ReferenceInitializationRun.elapsed p b.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let followers : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i)
  let memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun _ => ActiveFollowerLifecycle.initialMemory p
  have hlaunch := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hc
  have heta : x.eta = rate.eta := rfl
  rcases hlaunch with ⟨_, hactive, _, hfirst, _, _, _, hsourceFollowers⟩
  refine {
    followers := followers
    memory := memory
    configuration := ?_
    acceptedStart_zero := ?_
    S_zero := ?_
    delta_zero := ?_
    backlog_zero := ?_
    lastDown_none := ?_
    unoccupied := ?_
    localStateDomain := ?_
    bufferValid := ?_
    chronologicalBuffer := ?_
    bufferStamps := ?_
    decoderValid := ?_
    activeAtStart := hactive
    coordinatorFirst := hfirst }
  · intro i
    rcases hsourceFollowers i with ⟨hconfiguration, -⟩
    simpa [followers, memory, initial, x, b, heta,
      ActualReferenceInitializationBlock.referenceInput] using hconfiguration
  · intro i
    rcases hsourceFollowers i with ⟨_, _, haccepted, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using haccepted
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, hS, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hS
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, hdelta, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hdelta
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, hbacklog, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hbacklog
  · intro i
    rcases hsourceFollowers i with ⟨_, hlast, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hlast
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, hstatus, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hstatus
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, _, hdomain, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hdomain
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, _, hdomain, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hdomain.2.1
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, _, _, _, hpair, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hpair
  · intro i saved hsaved
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, _, _, _, _, hstamps⟩
    simpa [followers, x, b, s, heta, ActualReferenceInitializationBlock.referenceInput]
      using hstamps saved hsaved
  · intro i
    rcases hsourceFollowers i with ⟨_, _, _, _, _, _, _, hdomain, -⟩
    simpa [followers, x, b, heta, ActualReferenceInitializationBlock.referenceInput] using hdomain.2.2

/-- The physical postlaunch run from the actual corrected launch and original
private stream. -/
def actualFirstLiveRun
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :=
  ReferenceActivePhysicalHorizon.run
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    count hspan (actualFirstLiveSeed rate source rewards C_star C_h hc).activeAtStart

/-- The actual initial live segment, selected by W's existing first-cutoff
test on the records of the physical run. -/
def actualFirstLiveWindow
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (actualFirstLiveRun rate source rewards C_star C_h hc count hspan).records

/-- Every first-live calendar record produces a numerical source input from
its computed first or continuing branch. The ordinary states, selected
payload, pending set, and complement weights are the actual prepared values;
the input retains the full row and payload rate vector. -/
theorem actual_first_live_source_cell
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length) :
    ∃ _cell : ActualLiveSourceCell
        ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]),
      ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]).input.rows = source.1.2 ∧
      ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]).input.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]).input.rewards = rewards ∧
      ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]).input.time.val ∈
        ReferenceActivePhysicalHorizon.calendar
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count := by
  classical
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let start := ReferenceInitializationRun.elapsed p b.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := actualFirstLiveSeed rate source rewards C_star C_h hc
  let E := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan seed.activeAtStart
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let record := W[k.val]
  have hwindow := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hentry := hwindow k
  rcases hentry with ⟨hinputs, _hfailure, states, memories, hordinary, hbranch⟩
  rcases hbranch with hfirstBranch | hcontinuingBranch
  · rcases hfirstBranch with
      ⟨installed, arm, hbranch, hfields, htime, selected, hselected,
        hselectionEq, _hinputSelection, _hselectedFields, out, hrecording,
        hidentity, hlive, hdata⟩
    rcases hidentity with ⟨_hcoordinatorRun, hgate, hraw, hrawArm⟩
    have hvalid : ChoiceInputsValid selected.view.payload selected.view.cutoff
        record.input.time selected.view.complementWeights := by
      rw [hselectionEq]
      have htimeRecord : record.input.time = W[k.val].input.time := rfl
      rw [htimeRecord]
      simpa [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.firstInput, htime, record, W,
        actualFirstLiveWindow, actualFirstLiveRun] using arm.choiceInputsValid
    let cell : ActualLiveSourceCell record := {
      states := states
      memories := memories
      ordinary := hordinary
      selected := selected
      selection_actual := hselected
      assignment_live := hlive
      choiceInputsValid := hvalid
      input := sourceCell record selected.view.payload selected.view.pendingAtChoice
        states selected.view.complementWeights selected.view.cutoff hvalid
      input_eq := rfl
      enabled := rfl
      recordedArm_eq := rfl
      quantizedArrival_eq := by
        intro arm
        exact sourceCell_quantizedArrival record selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          hvalid arm
      coordinatorProjection := by
        refine ⟨out, out.gateArm, ?_, rfl, ?_, ?_⟩
        · exact hrecording
        · rw [← hgate] at hraw
          simpa only [record, W, hselectionEq,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
            ReferenceActivePhysicalStep.firstInput] using hraw
        · intro j
          exact hrawArm j
      followerDataClaim := by
        have hreward : record.input.rewards = rewards := by
          simpa only [record, W] using hinputs.2.2.1
        rw [hreward]
        exact hdata
      followerRawArrivalGate := by
        intro i hgate
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hgate]
      followerRawArrivalNoGate := by
        intro i hgate
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hgate] }
    refine ⟨cell, ?_, ?_, ?_, ?_⟩
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.2.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.2.2

  · rcases hcontinuingBranch with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, hfields,
        selected, hselected, hselectionEq, _hinputSelection, _hselectedFields,
        out, hrecording, hidentity, hlive, hdata⟩
    rcases hidentity with ⟨_hcoordinatorRun, hgate, hraw, hrawArm⟩
    have hvalid : ChoiceInputsValid selected.view.payload selected.view.cutoff
        record.input.time selected.view.complementWeights := by
      rw [hselectionEq]
      simpa only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt]
        using arm.choiceInputsValid
    let cell : ActualLiveSourceCell record := {
      states := states
      memories := memories
      ordinary := hordinary
      selected := selected
      selection_actual := hselected
      assignment_live := hlive
      choiceInputsValid := hvalid
      input := sourceCell record selected.view.payload selected.view.pendingAtChoice
        states selected.view.complementWeights selected.view.cutoff hvalid
      input_eq := rfl
      enabled := rfl
      recordedArm_eq := rfl
      quantizedArrival_eq := by
        intro arm
        exact sourceCell_quantizedArrival record selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          hvalid arm
      coordinatorProjection := by
        refine ⟨out, out.gateArm, ?_, rfl, ?_, ?_⟩
        · exact hrecording
        · rw [← hgate] at hraw
          simpa only [record, W, hselectionEq,
            ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
            ReferenceActivePhysicalStep.liveRegistersAt] using hraw
        · intro j
          exact hrawArm j
      followerDataClaim := by
        have hreward : record.input.rewards = rewards := by
          simpa only [record, W] using hinputs.2.2.1
        rw [hreward]
        exact hdata
      followerRawArrivalGate := by
        intro i hgate
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hgate]
      followerRawArrivalNoGate := by
        intro i hgate
        rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
        simp [hgate] }
    refine ⟨cell, ?_, ?_, ?_, ?_⟩
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.2.1
    · simpa [record, W, actualFirstLiveWindow, actualFirstLiveRun] using hinputs.2.2.2

/-- The cell selected at an actual first-live calendar coordinate. -/
noncomputable def actualLiveSourceCellAt
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length) :
    ActualLiveSourceCell
      ((actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]) :=
  Classical.choose (actual_first_live_source_cell rate source rewards C_star C_h hc count hspan k)

/-- The calendar-ordered list of existing numerical queue inputs on the
actual first-live window. -/
noncomputable def actualLiveSourceCells
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) : List (RecordedQueueRun.RoundInput p.K) :=
  List.ofFn fun k =>
    (actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k).input

theorem actualLiveSourceCells_length
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :
    (actualLiveSourceCells rate source rewards C_star C_h hc count hspan).length =
      (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length := by
  simp [actualLiveSourceCells]

theorem actualLiveSourceCells_get
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length) :
    (actualLiveSourceCells rate source rewards C_star C_h hc count hspan)[k.val]'(by
      rw [actualLiveSourceCells_length rate source rewards C_star C_h hc count hspan]
      exact k.isLt) =
      (actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k).input := by
  simp [actualLiveSourceCells]

/-- Each selected list entry retains the original source row, selected row
index, complete reward table, actual time, payload rates, literal map, enabled
service flag, and all-arm numerical arrivals. -/
theorem actualLiveSourceCellAt_facts
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan).length) :
    let record := (actualFirstLiveWindow rate source rewards C_star C_h hc count hspan)[k.val]
    let cell := actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
    record.input.rows = source.1.2 ∧
    record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    record.input.rewards = rewards ∧
    record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count ∧
    cell.input.enabled = true ∧
    cell.input.reward = (fun arm => ((record.input.rewards record.input.time arm).val : ℝ) / (D p : ℝ)) ∧
    cell.input.rate = cell.selected.view.payload.rate ∧
    cell.input.recordedArm = sourceArm record cell.selected.view.payload
      cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
      cell.selected.view.cutoff cell.choiceInputsValid ∧
    ∀ arm : Fin p.K,
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input arm =
        if sourceArm record cell.selected.view.payload cell.selected.view.pendingAtChoice
            cell.states cell.selected.view.complementWeights cell.selected.view.cutoff
            cell.choiceInputsValid = some arm then
          Nat.floor ((rate.n : ℝ) *
            (((record.input.rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
              cell.selected.view.payload.rate arm)
        else 0 := by
  classical
  dsimp only
  let cell := actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
  have hchosen := Classical.choose_spec
    (actual_first_live_source_cell rate source rewards C_star C_h hc count hspan k)
  rcases hchosen with ⟨hrows, hselectedRow, hrewards, htime⟩
  refine ⟨hrows, hselectedRow, hrewards, htime, cell.enabled, ?_, ?_,
    cell.recordedArm_eq, cell.quantizedArrival_eq⟩
  · rw [cell.input_eq]
    rfl
  · rw [cell.input_eq]
    rfl

end Bandits.Support.ReferenceFirstWindowNumericalStream

end
