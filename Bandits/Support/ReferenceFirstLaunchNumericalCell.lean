/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedActivePrefixFactor
public import Bandits.Support.ReferenceFirstCollectionNumericalReplay
public import Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence
public import Bandits.Support.UnstoppedRecordedQueueComparison

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The actual first-launch selected-follower numerical cell

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:195-209,246-275,391-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-60`.

The launch seed below is the actual corrected launch state on the crossing
branch. The numerical result concerns one actual first physical record, one
selected follower, and the computed first dispatcher branch. It retains the
source's full private input and reward table and makes the local branch
selectors explicit. It proves no global recording law or physical/logical
queue coupling.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ReferenceFollowerBufferProvenance
open Bandits.Support.ReferenceFollowerSparseEmissionRecovery
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.CoordinatorRoundDispatch

namespace Bandits.Support.ReferenceFirstLaunchNumericalCell

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev DownRecord {p : Parameters} (eta : ReferencePrelaunchFollower.LearningRate) :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta)
abbrev RoundRecord {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters}

/-- The actual corrected launch state, obtained from C's unique nonempty
option using the crossing proof. -/
noncomputable def launchState
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceActivePhysicalStep.State p rate :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hc)

/-- The option getter is exactly C's crossing state. -/
theorem correctedLaunch_eq_some_launchState
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some (launchState rate source rewards C_star C_h hc) := by
  have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).2 hc
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none => simp [hlaunch] at hsome
  | some active => simp [launchState, hlaunch]

/-- The crossing alone produces C's actual launch state, its full ordinary
follower seeds, and the coordinator's genuine zero learner. Buffer contents
and initialization-failure flags remain those of the source ordinary states. -/
theorem actual_launch_seed
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let s := ReferenceInitializationRun.elapsed p b.completed
    let active := launchState rate source rewards C_star C_h hc
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some active ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart active s ∧
      ReferenceInitializationRun.launchRound x = s + 1 ∧
      active.coordinator = .first ∧
      active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      ReferenceInitializationRun.coordinatorLearner b =
        some (RecordedQueueRun.initialState p.K) ∧
      (∀ arm : Fin p.K,
        (RecordedQueueRun.initialState p.K).registers arm = (0, 0) ∧
        (RecordedQueueRun.initialState p.K).records arm = [] ∧
        (RecordedQueueRun.initialState p.K).overflow = false) ∧
      (∀ i : Fin (p.m - 1),
        let state := ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i)
        active.followers i = .ordinary state (ActiveFollowerLifecycle.initialMemory p) ∧
        state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
        state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        ActiveFollowerLifecycle.localBufferValid state ∧
        state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        ∀ saved ∈ state.buffer, saved.calendarRound ≤ s) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let s := ReferenceInitializationRun.elapsed p b.completed
  let active := launchState rate source rewards C_star C_h hc
  have hlaunch := correctedLaunch_eq_some_launchState rate source rewards C_star C_h hc
  obtain ⟨activeMode, hmodeLaunch, hmode⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
  have hmodeId : activeMode = active :=
    Option.some.inj (hmodeLaunch.symm.trans hlaunch)
  subst activeMode
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate source rewards C_star C_h hc
  have hfieldsId : activeFields = active :=
    Option.some.inj (hfieldsLaunch.symm.trans hlaunch)
  subst activeFields
  obtain ⟨activeCoordinator, hcoordLaunch, hcoord, hbank, _hdisabled, hlearner, hzero⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hc
  have hcoordId : activeCoordinator = active :=
    Option.some.inj (hcoordLaunch.symm.trans hlaunch)
  subst activeCoordinator
  obtain ⟨_active, _hlaunch, _hle, hlaunchRound, _hactivation⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_source
      rate source rewards C_star C_h hc
  refine ⟨hlaunch, ?_, ?_, hcoord, hbank, hlearner, hzero, ?_⟩
  · simpa [s] using hmode
  · simpa [x, b, s] using hlaunchRound
  · intro i
    let state := ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i)
    have hsource := hfields i
    have hbuffer :=
      ReferenceFollowerBufferProvenance.initialization_ordinary_buffer_valid
        x b (ActualReferenceInitializationBlock.refFollower i)
    rcases hsource with
      ⟨hconfiguration, hlast, haccepted, hS, hdelta, hbacklog, hstatus, hdomain⟩
    refine ⟨hconfiguration, hlast, haccepted, hS, hdelta, hbacklog, hstatus,
      hdomain, ?_, ?_, ?_⟩
    · simpa [state] using hbuffer.1
    · simpa [state] using hbuffer.2.1
    · simpa [state, s, x, b] using hbuffer.2.2

private theorem run_one_records
    (rate : RateInput p) (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : RewardTable p) (start : ℕ)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hspan : start + 1 ≤ p.T) :
    let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
      ⟨start, ⟨le_rfl, by omega⟩⟩
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start 0 (by omega) hmode
    let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected
      rewards start hmode prefixRun entry
    let record : RoundRecord (p := p) (rate := rate) :=
      ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start 1 hspan hmode).records =
      [record] := by
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start, ⟨le_rfl, by omega⟩⟩
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start 0 (by omega) hmode
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected
    rewards start hmode prefixRun entry
  let record : RoundRecord (p := p) (rate := rate) :=
    ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
  rw [ReferenceActivePhysicalHorizon.run_successor_step initial rows selected rewards
    start 0 hspan hmode]
  simp [ReferenceActivePhysicalHorizon.foldRound,
    ReferenceActivePhysicalHorizon.roundInputAt, record, input, prefixRun,
    ReferenceActivePhysicalHorizon.run_zero_final,
    ReferenceActivePhysicalHorizon.run_zero_records]

/-- C's crossing state already satisfies the physical horizon's activation
mode at the exact clipped elapsed boundary. -/
theorem launchState_allActiveAtStart
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (launchState rate source rewards C_star C_h hc)
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed) := by
  rcases actual_launch_seed rate source rewards C_star C_h hc with
    ⟨_, hmode, _, _, _, _, _, _⟩
  exact hmode

/-- The actual one-step physical run on the original full row array, original
selected row index, whole reward table, and C-produced crossing state. -/
noncomputable def firstPhysicalRun
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :=
  ReferenceActivePhysicalHorizon.run
    (launchState rate source rewards C_star C_h hc)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    1 (by omega) (launchState_allActiveAtStart rate source rewards C_star C_h hc)

/-- The literal record at offset zero of the actual first-launch run. Its
input comes from the zero-prefix fold and its output is the physical step. -/
noncomputable def firstPhysicalRecord
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :
    RoundRecord (p := p) (rate := rate) := by
  let initial := launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start, ⟨le_rfl, by omega⟩⟩
  let prefixRun := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start 0
    (by omega) (launchState_allActiveAtStart rate source rewards C_star C_h hc)
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
    (launchState_allActiveAtStart rate source rewards C_star C_h hc) prefixRun entry
  exact ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- The run retains exactly this actual physical record, including terminal
launches only when the caller supplies the necessary strict `s < T`. -/
theorem firstPhysicalRun_records
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :
    (firstPhysicalRun rate source rewards C_star C_h hc hs).records =
      [firstPhysicalRecord rate source rewards C_star C_h hc hs] := by
  dsimp [firstPhysicalRun, firstPhysicalRecord]
  exact run_one_records rate _ source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (launchState_allActiveAtStart rate source rewards C_star C_h hc) (by omega)

/-- The unique first actual record retains the original table coordinates. -/
theorem firstPhysicalRecord_source_inputs
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    record.input.state = launchState rate source rewards C_star C_h hc ∧
      record.input.time.val = s ∧
      record.input.rows = source.1.2 ∧
      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      record.input.rewards = rewards := by
  simp [firstPhysicalRecord, ReferenceActivePhysicalHorizon.roundInputAt,
    ReferenceActivePhysicalHorizon.run_zero_final]

/-- Every follower's first physical preparation is the true ordinary launch
state from C, passed through the actual unoccupied start/offer/arm pipeline. -/
theorem firstPhysicalRecord_prepared_seed
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    ∀ i : Fin (p.m - 1),
      (record.output.preparation.followers.followers i).configuration =
        .ordinary
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) := by
  intro record x b i
  rcases actual_launch_seed rate source rewards C_star C_h hc with
    ⟨_, _, _, _, _, _, _, hfollowers⟩
  rcases firstPhysicalRecord_source_inputs rate source rewards C_star C_h hc hs with
    ⟨hstate, htime, _, _, _⟩
  let state := ReferenceInitializationRun.ordinary x b
    (ActualReferenceInitializationBlock.refFollower i)
  rcases hfollowers i with
    ⟨hconfiguration, _hlast, haccepted, hS, hdelta, hbacklog, hstatus,
      hdomain, _hbuffer, _hpair, _hstamps⟩
  have hinputConfig : record.input.state.followers i =
      .ordinary state (ActiveFollowerLifecycle.initialMemory p) := by
    rw [hstate]
    exact hconfiguration
  have hlocal := ReferenceActiveDataOwnership.prepare_initial_unoccupied
    i record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i) state (ActiveFollowerLifecycle.initialMemory p)
    hdomain hstatus haccepted hS hdelta hbacklog
  rw [record.output_eq]
  change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
  rw [ReferenceActivePhysicalStep.prepare]
  change ((ReferenceActiveFeedbackCut.prepare
      (ReferenceActivePhysicalStep.followerInput record.input)).followers i).configuration = _
  rw [ReferenceActiveFeedbackCut.prepare]
  change (DeclaredFollowerLocalRound.prepare rate i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)).configuration = _
  rw [hinputConfig]
  exact hlocal

/-- The computed first choice keeps the actual physical dispatch, installed
payload, checked timestamp, live assignment test, and one-round boundary
together. -/
theorem first_launch_call_frame
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          (firstPhysicalRecord rate source rewards C_star C_h hc hs).input)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      (firstPhysicalRecord rate source rewards C_star C_h hc hs).input.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (firstPhysicalRecord rate source rewards C_star C_h hc hs).input) =
      .chosen installed arm) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    ReferenceActivePhysicalStep.dispatch record.input = .first (.chosen installed arm) ∧
      installed.registers.time = record.input.time ∧
      CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
        record.input.time ∧
      record.input.time.val + 1 < installed.startRoundResult.clock.g ∧
      installed.registers.payload.sigma.val = record.input.time.val := by
  intro record
  rcases firstPhysicalRecord_source_inputs rate source rewards C_star C_h hc hs with
    ⟨hstate, htime, _, _, _⟩
  rcases actual_launch_seed rate source rewards C_star C_h hc with
    ⟨_, _, _, hcoordinator, _, _, _, _⟩
  have hstateCoordinator : record.input.state.coordinator = .first := by
    rw [hstate]
    exact hcoordinator
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed arm) := by
    unfold ReferenceActivePhysicalStep.dispatch
    rw [hstateCoordinator]
    change (match CoordinatorRoundDispatch.dispatch
      (CoordinatorRoundDispatch.Input.first
        (ReferenceActivePhysicalStep.firstInput record.input)) with
      | CoordinatorRoundDispatch.Outcome.first outcome =>
          ReferenceActivePhysicalStep.DispatchCut.first outcome) = _
    rw [CoordinatorRoundDispatch.dispatch, hchosen]
    rfl
  have hframe := ReferenceCoordinatorRecorderCallCorrespondence.first_call_frame
    record.input installed arm hdispatch
  have hpayloadTime := ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
    record.input installed arm hchosen
  exact ⟨hdispatch, hframe.1, hframe.2.1, hframe.2.2, hpayloadTime⟩

/-- First-installation identities for this SAME computed payload: sampled
assignment and DOWN records, unit anchors, the dyadic rate match, the physical
sigma, and the actual zero/pending initialization fields. -/
theorem first_installation_payload_facts
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          (firstPhysicalRecord rate source rewards C_star C_h hc hs).input)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      (firstPhysicalRecord rate source rewards C_star C_h hc hs).input.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (firstPhysicalRecord rate source rewards C_star C_h hc hs).input) =
      .chosen installed arm) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let payload := installed.registers.payload
    payload.sigma.val = record.input.time.val ∧
      (∀ a : Fin p.K, payload.anchor a = 1) ∧
      (∀ i : Fin (p.m - 1),
        payload.assignment.assigned i = installed.start.assignment.assigned i ∧
        payload.downRecord i = installed.start.outgoing i ∧
        payload.rate (payload.assignment.assigned i) =
          OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h) ∧
      (∀ a : Fin p.K, payload.queues a = 0) ∧
      installed.registers.pendingAtChoice = Finset.univ ∧
      (∀ a, installed.registers.complementScores a = 0) ∧
      (∀ a, installed.ownedRegisters.queue a = 0) ∧
      (∀ a, installed.ownedRegisters.previousService a = 0) ∧
      (∀ i, installed.followerBaseScore i = 0) := by
  intro record payload
  have hinstallation := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    record.input installed arm hchosen
  have hident := CoordinatorRoundDispatch.firstInstallation_payload_identities
    (ReferenceActivePhysicalStep.firstInput record.input)
  dsimp at hident
  rw [← hinstallation] at hident
  rcases hident with ⟨hassign, hanchor, hdown, _hword, hrate, _hexponent⟩
  have hpayloadEq : payload =
      AssignmentStartPayload.Input.ofFirstAssignment
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput record.input)) := by
    change installed.registers.payload = _
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.first_registers_payload _
  have hpayloadQueues : ∀ a : Fin p.K, payload.queues a = 0 := by
    intro a
    rw [hpayloadEq]
    simp [AssignmentStartPayload.Input.ofFirstAssignment,
      FirstAssignmentLaunch.Input.initialQueues]
  have hpending : installed.registers.pendingAtChoice = Finset.univ := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.first_registers_pending _
  have hzero := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
    record.input installed arm hchosen
  have htime := first_launch_call_frame rate source rewards C_star C_h hc hs
    installed arm hchosen
  refine ⟨htime.2.2.2.2, hanchor, ?_, hpayloadQueues, hpending, hzero.1, hzero.2.1,
    hzero.2.2.1, hzero.2.2.2⟩
  intro i
  let fi : ActiveRoundActions.Follower p.m := by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using i
  have hassignI : payload.assignment.assigned i = installed.start.assignment.assigned fi := by
    simpa [fi, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hassign fi
  have hdownI : payload.downRecord i = installed.start.outgoing fi := by
    simpa [fi, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hdown fi
  refine ⟨hassignI, hdownI, ?_⟩
  calc
    payload.rate (payload.assignment.assigned i) =
        installed.start.recordingRates (installed.start.assignment.assigned fi) := by
          rw [hrate, hassignI]
    _ = OrdinaryMessageCodec.dyadicRate (installed.start.outgoing fi).val.h :=
      by
        rw [hinstallation]
        exact (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput record.input)).start_outgoing_rate fi |>.symm
    _ = OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h := by rw [hdownI]

/-- The literal DATA, selected-follower pilot, all-other-pilots mask, and
inclusive saved-candidate threshold on one original row and time. -/
def firstFollowerEvent (i : Fin (p.m - 1)) (row : CompleteRow p)
    (time : Fin p.T) (arm : Fin p.K) (xi : ℝ) : Prop :=
  slotDraw (row.2 time).1 = dataSlot ∧
    pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 time).1 = arm ∧
    (∀ player : Fin p.m,
      player ≠ followerPlayer p.two_le_m i →
        pilotDraw (K_pos p) player (row.2 time).1 ≠ arm) ∧
    ((row.2 time).1 Label.thin).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * xi) /
        CanonicalRecordingSlice.recordingZeta p.m p.K

private theorem logAt_contribution_eq_event
    (eta : ReferencePrelaunchFollower.LearningRate)
    (M : DownRecord (p := p) eta)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (time : Fin p.T)
    (activation : ReferencePrelaunchFollower.Activation p)
    (hactive : activation.val ≤ time.val + 1)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (arm : Fin p.K) (xi : ℝ)
    (hown : slotDraw (row.2 time).1 = dataSlot →
      own.1 = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
        (row.2 time).1)
    (hsource : recorderSourceDraw p.two_le_m p.m_lt_K (row.2 time).1 =
      followerPlayer p.two_le_m i)
    (hxi : xi = OrdinaryMessageCodec.dyadicRate M.val.h) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
      eta.val M.val.h arm (time.val + 1)
      (ReferencePrelaunchFollower.logAt i row activation time own) =
    if firstFollowerEvent i row time arm xi then
      Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0 := by
  classical
  let thinGate : Prop :=
    ((row.2 time).1 Label.thin).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * xi) /
        CanonicalRecordingSlice.recordingZeta p.m p.K
  let savedGate : Prop :=
    ((row.2 time).1 Label.thin).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
        (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  have hthreshold : thinGate ↔ savedGate := by
    dsimp [thinGate, savedGate]
    have hnum : (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * xi) /
        CanonicalRecordingSlice.recordingZeta p.m p.K =
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
        (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
      rw [hxi, OrdinaryMessageCodec.dyadicRate,
        CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    rw [hnum]
  have htestsEq :
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i row activation time own) ↔
        slotDraw (row.2 time).1 = dataSlot ∧
          (∀ player : Fin p.m, player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ own.1) := by
    rw [ActiveFollowerLogging.loggingTestsPass_iff_source_mask]
    constructor
    · rintro ⟨_, hd, _, hm⟩
      exact ⟨hd, by simpa [hown hd] using hm⟩
    · rintro ⟨hd, hm⟩
      exact ⟨hactive, hd, hsource, by simpa [hown hd] using hm⟩
  let event := firstFollowerEvent i row time arm xi
  by_cases htests : SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row activation time own)
  · have ⟨hdata, hmask⟩ := htestsEq.mp htests
    by_cases hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
        (row.2 time).1 = arm
    · have hownArm : own.1 = arm := (hown hdata).trans hpilot
      have hmaskArm : ∀ player : Fin p.m,
          player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ arm := by
        intro player hplayer
        intro hsame
        exact hmask player hplayer (by simpa [hownArm] using hsame)
      have hevent : event ↔ thinGate := by
        change (slotDraw (row.2 time).1 = dataSlot ∧
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 time).1 = arm ∧
          (∀ player : Fin p.m, player ≠ followerPlayer p.two_le_m i →
            pilotDraw (K_pos p) player (row.2 time).1 ≠ arm) ∧
          thinGate) ↔ thinGate
        constructor
        · intro he
          exact he.2.2.2
        · intro ht
          exact ⟨hdata, hpilot, hmaskArm, ht⟩
      rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation time own htests]
      change (if time.val + 1 = time.val + 1 ∧ own.1 = arm then
          SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p)
            eta.val M.val.h own.2.val
            ((row.2 time).1 Label.thin) else 0) =
        if event then Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
      have hkey : time.val + 1 = time.val + 1 ∧ own.1 = arm :=
        ⟨rfl, hownArm⟩
      rw [if_pos hkey]
      by_cases hthin : thinGate
      · have he : event := hevent.mpr hthin
        have hsaved : savedGate := hthreshold.mp hthin
        have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor
          (p := p) eta M own.2
        unfold ActiveFollowerQueueOperation.sourceArrivalFloor at hfloor
        rw [← hxi] at hfloor
        rw [SparseCalendarReplay.savedContribution_eq_floor_of_le
          p.K (p.m - 1) (D p) eta.val M.val.h own.2.val
          ((row.2 time).1 Label.thin) hsaved]
        change Nat.floor ((D p : ℝ) * eta.val * (2 : ℝ) ^ M.val.h *
          own.2.val.val) = if event then
            Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
        rw [if_pos he, hfloor.symm]
      · have hnotEvent : ¬ event := fun he => hthin (hevent.mp he)
        have hnotSaved : ¬ savedGate := fun hs => hthin (hthreshold.mpr hs)
        have hsavedNot : ¬ ((row.2 time).1 Label.thin).val ≤
            (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
              (((2 : ℝ) ^ M.val.h)⁻¹)) /
              SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
          simpa [savedGate] using hnotSaved
        change (if ((row.2 time).1 Label.thin).val ≤
            (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
              (((2 : ℝ) ^ M.val.h)⁻¹)) /
              SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) then
            Nat.floor ((D p : ℝ) * eta.val * (2 : ℝ) ^ M.val.h *
              own.2.val.val) else 0) =
          if event then Nat.floor ((D p : ℝ) * eta.val * own.2.val.val / xi) else 0
        rw [if_neg hsavedNot, if_neg hnotEvent]
    · have hownNe : own.1 ≠ arm := by
        intro heq
        exact hpilot ((hown hdata).symm.trans heq)
      have hnotEvent : ¬ event := by
        intro he
        exact hpilot he.2.1
      rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation time own htests]
      simp [SparseCalendarReplay.sparseBufferContribution,
        SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound,
        hownNe, hnotEvent, event]
  · have hnotEvent : ¬ event := by
      intro he
      exact htests (htestsEq.mpr ⟨he.1,
        by simpa [hown he.1, he.2.1] using he.2.2.1⟩)
    rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i row activation time own htests]
    simp [SparseCalendarReplay.sparseBufferContribution, hnotEvent, event]

/-- The exact numerical parameters inherited from the source learning rate. -/
def queueParameters (rate : RateInput p) : RecordedQueueRun.Parameters where
  D := D p
  n := rate.n
  eta := rate.eta.val
  D_pos := ConstructorDimensions.D_pos p
  n_pos := ActiveFollowerDownAcceptance.rate_n_pos p rate
  capacity_le_D := ActiveFollowerDownAcceptance.four_n_le_D p rate
  eta_pos := rate.eta.property
  n_eq_eta_mul_D := rate.n_scale

/-- The one-round analytical input retains the whole current reward row and
the first installed payload's complete rate vector. -/
noncomputable def firstCellInput
    (rate : RateInput p) (i : Fin (p.m - 1))
    (record : RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input))) :
    RecordedQueueRun.RoundInput p.K where
  enabled := true
  recordedArm :=
    if firstFollowerEvent i record.input.row record.input.time
        (installed.registers.payload.assignment.assigned i)
        (installed.registers.payload.rate
          (installed.registers.payload.assignment.assigned i)) then
      some (installed.registers.payload.assignment.assigned i)
    else none
  reward := fun a =>
    ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ)
  rate := installed.registers.payload.rate
  reward_nonneg := by
    intro a
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  reward_le_one := by
    intro a
    have hvalue : (record.input.rewards record.input.time a).val ≤ D p :=
      Nat.le_of_lt_succ (record.input.rewards record.input.time a).isLt
    apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
    exact_mod_cast hvalue
  rate_pos := by
    intro a
    exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
      (installed.registers.payload.beta_le_rate a)

/-- On the literal selected-follower event, physical preparation makes that
follower play the installed arm and actual DATA feedback returns the original
grid reward, including a zero reward. -/
theorem first_launch_selected_follower_feedback
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (i : Fin (p.m - 1))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          (firstPhysicalRecord rate source rewards C_star C_h hc hs).input)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      (firstPhysicalRecord rate source rewards C_star C_h hc hs).input.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (firstPhysicalRecord rate source rewards C_star C_h hc hs).input) =
      .chosen installed arm) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let assigned := installed.registers.payload.assignment.assigned i
    let xi := installed.registers.payload.rate assigned
    ∀ hEvent : firstFollowerEvent i record.input.row record.input.time assigned xi,
      (ReferenceActivePhysicalStep.prepare record.input).arms.actions
          (followerPlayer p.two_le_m i) = assigned ∧
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
            (followerPlayer p.two_le_m i) = record.input.rewards record.input.time assigned ∧
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (followerPlayer p.two_le_m i)).val.val =
          ((record.input.rewards record.input.time assigned).val : ℝ) / (D p : ℝ) := by
  intro record assigned xi hEvent
  have hcall := first_launch_call_frame rate source rewards C_star C_h hc hs
    installed arm hchosen
  dsimp only at hcall
  rcases hcall with ⟨hdispatch, htime, hlive, _, _⟩
  have htime' : installed.registers.time = record.input.time := by
    simpa only [record] using htime
  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    record.input installed.registers.payload installed.startRoundResult
    installed.registers.time installed.registers.complementWeights arm htime'
  have hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected := by
    change ReferenceActivePhysicalStep.DispatchCut.selection
      (ReferenceActivePhysicalStep.dispatch record.input) = some selected
    rw [hdispatch]
    dsimp [ReferenceActivePhysicalStep.DispatchCut.selection, selected]
    exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      record.input installed.registers.payload installed.startRoundResult
      installed.registers.time installed.registers.complementWeights arm htime'
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let initOutput := ReferenceInitializationRun.output init
  let states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun j => ReferenceInitializationRun.ordinary init initOutput
      (ActualReferenceInitializationBlock.refFollower j)
  let memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun _ => ActiveFollowerLifecycle.initialMemory p
  have hseed := actual_launch_seed rate source rewards C_star C_h hc
  rcases hseed with ⟨_, _, _, _, _, _, _, hfollowers⟩
  have hstatus (j : Fin (p.m - 1)) : (states j).status = .unoccupied := by
    rcases hfollowers j with ⟨_, _, _, _, _, _, hstatus, _, _, _, _⟩
    simpa [states, init, initOutput] using hstatus
  have hprepared : ∀ j,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
    intro j
    have hraw := firstPhysicalRecord_prepared_seed rate source rewards C_star C_h hc hs j
    have hraw' : (record.output.preparation.followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
      simpa [record, states, memories, init, initOutput] using hraw
    rw [record.output_eq] at hraw'
    simpa [ReferenceActivePhysicalStep.step] using hraw'
  have hfields : ∀ j, (states j).status ≠ .unoccupied →
      (states j).lastDown = some (selected.view.payload.downRecord j) := by
    intro j hoccupied
    exact False.elim (hoccupied (hstatus j))
  have hdata : slotDraw (record.input.row.2 record.input.time).1 = dataSlot := hEvent.1
  have hlocal : (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i)).configuration =
        .ordinary (states i) (memories i) := by
    simpa [ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActiveFeedbackCut.prepare,
      ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.RoundInput.row] using hprepared i
  have hlocalArm := ReferenceActiveDataOwnership.ordinary_data_arm
    installed.registers.payload i record.input.row (record.input.state.activations i)
    record.input.time (record.input.active i) (record.input.state.followers i)
    (states i) (memories i) hlocal
    (fun hocc => False.elim (hocc (hstatus i))) hdata
  have hlocalArmAssigned :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).arm = assigned := by
    rw [hlocalArm]
    simp [hstatus i, hEvent.2.1]
  have haction : (ReferenceActivePhysicalStep.prepare record.input).arms.actions
      (followerPlayer p.two_le_m i) = assigned := by
    simpa [ReferenceActivePhysicalStep.PreparedRound.arms,
      ReferenceActiveFeedbackCut.ActionInputs.actions_follower,
      ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActiveFeedbackCut.prepare,
      ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.RoundInput.row] using hlocalArmAssigned
  have hne := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot selected states))
      (followerPlayer p.two_le_m i) assigned := by
    simp only [SnapshotRecordingKernel.owns, dite_eq_right hne,
      ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hne]
    rfl
  have hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
      (followerPlayer p.two_le_m i) assigned (record.input.row.2 record.input.time).1 := by
    intro player hplayer
    exact hEvent.2.2.1 player hplayer
  have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback
    record.input selected hselected states memories hprepared hfields hlive hdata
    (followerPlayer p.two_le_m i) assigned haction howns hmask
  exact ⟨haction, hfeedback.1, hfeedback.2⟩

/-- C's actual unoccupied ordinary buffer admits the real checked append on
the first physical record. The append stores the full pre-thinning candidate
log, and its successful buffer remains locally valid. -/
theorem firstPhysicalRecord_checkedLog
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (i : Fin (p.m - 1)) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let initOutput := ReferenceInitializationRun.output init
    let state := ReferenceInitializationRun.ordinary init initOutput
      (ActualReferenceInitializationBlock.refFollower i)
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i)) state = .ok logged ∧
      record.output.ownEntries (followerPlayer p.two_le_m i) =
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) ∧
      logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
      ReferenceFollowerBufferProvenance.logEmission i record =
        ReferencePrelaunchFollower.logAt i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i)) ∧
      ActiveFollowerLifecycle.localBufferValid logged := by
  intro record init initOutput state
  rcases actual_launch_seed rate source rewards C_star C_h hc with
    ⟨_, _, _, _, _, _, _, hfollowers⟩
  rcases hfollowers i with
    ⟨_, _hlast, _haccepted, _hS, _hdelta, _hbacklog, hstatus,
      _hdomain, hbufferValid, _hpairwise, hstamps⟩
  obtain ⟨_, htime, _, _, _⟩ :=
    firstPhysicalRecord_source_inputs rate source rewards C_star C_h hc hs
  have hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary state (ActiveFollowerLifecycle.initialMemory p) := by
    simpa [record, init, initOutput, state] using
      firstPhysicalRecord_prepared_seed rate source rewards C_star C_h hc hs i
  have hbefore : ∀ saved ∈ state.buffer, saved.calendarRound < record.input.time.val + 1 := by
    intro saved hsaved
    have hle := hstamps saved hsaved
    have htime' : record.input.time.val =
        ReferenceInitializationRun.elapsed p initOutput.completed := by
      simpa only [record, initOutput] using htime
    rw [← htime'] at hle
    omega
  rcases ReferenceFollowerBufferProvenance.actualPreparedLogging_success i record state
      (ActiveFollowerLifecycle.initialMemory p) hprepared hbufferValid hbefore hstatus with
    ⟨logged, hlogging, hown, happend, hvalid⟩
  have hlogEmission : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i)) := by
    unfold ReferenceFollowerBufferProvenance.logEmission
    simp only [hprepared]
    split_ifs with hunoccupied
    · rfl
    · exact False.elim (hunoccupied hstatus)
  exact ⟨logged, hlogging, hown, happend, hlogEmission, hvalid⟩

/-- Before applying thinning, the actual unoccupied follower candidate arm on
DATA is its own pilot draw. -/
theorem firstPhysicalRecord_sourcePilot
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (i : Fin (p.m - 1))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          (firstPhysicalRecord rate source rewards C_star C_h hc hs).input))) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    ∀ hdata : slotDraw (record.input.row.2 record.input.time).1 = dataSlot,
      (record.output.ownEntries (followerPlayer p.two_le_m i)).1 =
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
  intro record hdata
  let init := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let initOutput := ReferenceInitializationRun.output init
  let state := ReferenceInitializationRun.ordinary init initOutput
    (ActualReferenceInitializationBlock.refFollower i)
  have hseed := actual_launch_seed rate source rewards C_star C_h hc
  rcases hseed with ⟨_, _, _, _, _, _, _, hfollowers⟩
  rcases hfollowers i with ⟨_, _, haccepted, hS, hdelta, hbacklog,
    hstatus, hdomain, _, _, _⟩
  have hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary state (ActiveFollowerLifecycle.initialMemory p) := by
    simpa [record, init, initOutput, state] using
      firstPhysicalRecord_prepared_seed rate source rewards C_star C_h hc hs i
  have hlocal : (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i)).configuration =
        .ordinary state (ActiveFollowerLifecycle.initialMemory p) := by
    rw [record.output_eq] at hprepared
    simpa [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActiveFeedbackCut.prepare,
      ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.RoundInput.row] using hprepared
  have hlocalArm := ReferenceActiveDataOwnership.ordinary_data_arm
    installed.registers.payload i record.input.row (record.input.state.activations i)
    record.input.time (record.input.active i) (record.input.state.followers i)
    state (ActiveFollowerLifecycle.initialMemory p) hlocal
    (fun hocc => False.elim (hocc (by simpa [state, init, initOutput] using hstatus))) hdata
  have hlocalArmData :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).arm =
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
    rw [hlocalArm]
    simp [hstatus, state, init, initOutput]
  have hpreparedArm :
      (record.output.preparation.followers.followers i).arm =
        (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i)).arm := by
    rw [record.output_eq]
    simp [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActiveFeedbackCut.prepare,
      ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.RoundInput.row]
  have hown := ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared i record
  calc
    (record.output.ownEntries (followerPlayer p.two_le_m i)).1 =
        (record.output.preparation.followers.followers i).arm := by
          exact congrArg Prod.fst hown
    _ = (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).arm := hpreparedArm
    _ = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
        (record.input.row.2 record.input.time).1 := hlocalArmData

/-- The same actual source-selected installation and original recorder-source
draw define the sparse physical emission and the existing one-round numerical
replay. The event remains the local computed branch selector. -/
theorem first_launch_sparse_numerical_cell
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (i : Fin (p.m - 1))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          (firstPhysicalRecord rate source rewards C_star C_h hc hs).input)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      (firstPhysicalRecord rate source rewards C_star C_h hc hs).input.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (firstPhysicalRecord rate source rewards C_star C_h hc hs).input) =
      .chosen installed arm)
    (hsource : recorderSourceDraw p.two_le_m p.m_lt_K
      ((firstPhysicalRecord rate source rewards C_star C_h hc hs).input.row.2
        (firstPhysicalRecord rate source rewards C_star C_h hc hs).input.time).1 =
        followerPlayer p.two_le_m i) :
    let record := firstPhysicalRecord rate source rewards C_star C_h hc hs
    let payload := installed.registers.payload
    let assigned := payload.assignment.assigned i
    let xi := payload.rate assigned
    let y := ((record.input.rewards record.input.time assigned).val : ℝ) / (D p : ℝ)
    let event := firstFollowerEvent i record.input.row record.input.time assigned xi
    let cell := firstCellInput rate i record installed
    cell.enabled = true ∧
      cell.recordedArm = (if event then some assigned else none) ∧
      (∀ other : Fin p.K, other ≠ assigned →
        RecordedQueueRun.quantizedArrival (queueParameters rate) cell other = 0) ∧
      ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (payload.downRecord i) i record =
          (if event then Nat.floor ((D p : ℝ) * rate.eta.val * y / xi) else 0) ∧
      RecordedQueueRun.quantizedArrival (queueParameters rate) cell assigned =
        ReferenceFollowerSparseEmissionRecovery.emissionContribution
          (payload.downRecord i) i record ∧
      (∀ hEvent : event,
        ((record.output.ownEntries (followerPlayer p.two_le_m i)).2).val.val = y) := by
  intro record payload assigned xi y event cell
  classical
  have hcellRecorded : cell.recordedArm = (if event then some assigned else none) := by
    rfl
  have hother : ∀ other : Fin p.K, other ≠ assigned →
      RecordedQueueRun.quantizedArrival (queueParameters rate) cell other = 0 := by
    intro other hne
    unfold RecordedQueueRun.quantizedArrival
    rw [hcellRecorded]
    by_cases hevent : event
    · have hneq : assigned ≠ other := fun heq => hne heq.symm
      simp [hevent, hneq]
    · simp [hevent]
  have harrival :
      RecordedQueueRun.quantizedArrival (queueParameters rate) cell assigned =
        if event then Nat.floor ((rate.n : ℝ) * y / xi) else 0 := by
    unfold RecordedQueueRun.quantizedArrival
    rw [hcellRecorded]
    by_cases hevent : event
    · simp [hevent, queueParameters, cell, firstCellInput, payload, assigned, xi, y]
    · simp [hevent]
  have hfacts := first_installation_payload_facts rate source rewards C_star C_h hc hs
    installed arm hchosen
  dsimp only at hfacts
  rcases hfacts with ⟨_, _, hpayload, _, _, _, _, _⟩
  have hxi : xi = OrdinaryMessageCodec.dyadicRate (payload.downRecord i).val.h := by
    simpa [payload, assigned, xi] using (hpayload i).2.2
  rcases firstPhysicalRecord_checkedLog rate source rewards C_star C_h hc hs i with
    ⟨logged, hlogging, hown, happend, hlogEmission, hvalid⟩
  have hsourcePilot := firstPhysicalRecord_sourcePilot
    rate source rewards C_star C_h hc hs i installed
  have hownData : slotDraw (record.input.row.2 record.input.time).1 = dataSlot →
      (record.output.ownEntries (followerPlayer p.two_le_m i)).1 =
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
    simpa [record] using hsourcePilot
  have hcandidate := logAt_contribution_eq_event rate.eta (payload.downRecord i)
    i record.input.row record.input.time (record.input.state.activations i)
    (record.input.active i) (record.output.ownEntries (followerPlayer p.two_le_m i))
    assigned xi hownData (by simpa [record] using hsource) hxi
  have hdownArm : PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i) = assigned :=
    ReferenceActiveDataOwnership.downRecord_arm payload i
  have hcontributionOwn :
      ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (payload.downRecord i) i record =
          if event then Nat.floor ((D p : ℝ) * rate.eta.val *
            ((record.output.ownEntries (followerPlayer p.two_le_m i)).2).val.val / xi)
          else 0 := by
    unfold ReferenceFollowerSparseEmissionRecovery.emissionContribution
    rw [hlogEmission, hdownArm]
    exact hcandidate
  have hgeometry := first_launch_selected_follower_feedback rate source rewards C_star C_h
    hc hs i installed arm hchosen
  have hpreparedObservation :
      record.output.preparation.feedback.observations (followerPlayer p.two_le_m i) =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (followerPlayer p.two_le_m i) := by
    rw [record.output_eq]
    rfl
  have hownObservation : ∀ hEvent : event,
      ((record.output.ownEntries (followerPlayer p.two_le_m i)).2).val.val = y := by
    intro hevent
    have hfeedback := hgeometry hevent
    calc
      ((record.output.ownEntries (followerPlayer p.two_le_m i)).2).val.val =
          ((record.output.preparation.feedback.observations
            (followerPlayer p.two_le_m i)).val.val) := by rw [hown]
      _ = ((record.input.rewards record.input.time assigned).val : ℝ) / (D p : ℝ) := by
        rw [hpreparedObservation]
        exact hfeedback.2.2
      _ = y := rfl
  have hcontribution :
      ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (payload.downRecord i) i record =
          if event then Nat.floor ((D p : ℝ) * rate.eta.val * y / xi) else 0 := by
    rw [hcontributionOwn]
    by_cases hevent : event
    · simp [hevent, hownObservation hevent, y]
    · simp [hevent]
  have hnum : (rate.n : ℝ) * y / xi = (D p : ℝ) * rate.eta.val * y / xi := by
    rw [rate.n_scale]
    ring
  have hsameArrival :
      RecordedQueueRun.quantizedArrival (queueParameters rate) cell assigned =
        ReferenceFollowerSparseEmissionRecovery.emissionContribution
          (payload.downRecord i) i record := by
    rw [harrival, hcontribution]
    by_cases hevent : event <;> simp [hevent, hnum]
  exact ⟨rfl, hcellRecorded, hother, hcontribution, hsameArrival,
    hownObservation⟩

/-- When the local event fails, the analytical round is still enabled and
accepts a zero record, whose service is zero at the actual zero registers.
The explicitly disabled copy instead records a disabled no-op and preserves
registers by the queue API. -/
theorem firstCell_enabledZero_vs_disabled
    (rate : RateInput p) (i : Fin (p.m - 1))
    (record : RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input)))
    (hnot : ¬ firstFollowerEvent i record.input.row record.input.time
      (installed.registers.payload.assignment.assigned i)
      (installed.registers.payload.rate
        (installed.registers.payload.assignment.assigned i))) :
    let q := queueParameters rate
    let cell := firstCellInput rate i record installed
    let initial := RecordedQueueRun.initialState p.K
    let disabled := { cell with enabled := false }
    cell.enabled = true ∧
      (∀ a : Fin p.K,
        RecordedQueueRun.quantizedArrival q cell a = 0 ∧
        RecordedQueueRun.acceptedRecord q initial cell a = (true, 0) ∧
        RecordedQueueRun.recordService (4 * q.n) (0, 0) (true, 0) = 0 ∧
        (RecordedQueueRun.step q initial cell).registers a = (0, 0)) ∧
      (∀ a : Fin p.K,
        (RecordedQueueRun.step q initial disabled).registers a = initial.registers a ∧
        RecordedQueueRun.acceptedRecord q initial disabled a = (false, 0)) := by
  intro q cell initial disabled
  have hrecorded : cell.recordedArm = none := by
    simp [cell, firstCellInput, hnot]
  have hzero : ∀ a : Fin p.K, RecordedQueueRun.quantizedArrival q cell a = 0 := by
    intro a
    simp [RecordedQueueRun.quantizedArrival, hrecorded]
  have henabled : cell.enabled = true := by
    rfl
  refine ⟨henabled, ?_, ?_⟩
  · intro a
    have haccepted : RecordedQueueRun.acceptedRecord q initial cell a = (true, 0) := by
      simp [RecordedQueueRun.acceptedRecord, initial,
        RecordedQueueRun.initialState, henabled, hzero a]
    refine ⟨hzero a, haccepted, ?_, ?_⟩
    · simp [RecordedQueueRun.recordService, CappedService.service]
    · simp [RecordedQueueRun.step, initial, RecordedQueueRun.initialState,
        RecordedQueueRun.acceptedRecord, henabled, hzero a, QueueReplay.transition]
  · intro a
    have hdisabled := RecordedQueueRun.step_disabled_preserves q initial disabled
      rfl a
    have hrecord : RecordedQueueRun.acceptedRecord q initial disabled a = (false, 0) := by
      simp [RecordedQueueRun.acceptedRecord, disabled, initial,
        RecordedQueueRun.initialState]
    exact ⟨hdisabled.1, hrecord⟩

end Bandits.Support.ReferenceFirstLaunchNumericalCell

end
