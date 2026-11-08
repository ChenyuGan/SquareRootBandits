/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffFollowerPreparation
public import Bandits.Support.ReferenceFirstCutoffFollowerObservation
public import Bandits.Support.ReferenceFirstCutoffReceiverDomain
public import Bandits.Support.ReferenceFirstCutoffFinishSafety
public import Bandits.Support.ReferenceFirstLaunchNumericalCell

import Lean.Elab.Tactic.Omega

/-!
# Generated first-cutoff survival and extraction

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,41-70,246-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module assembles actual launch and first-cutoff data on the original
source rows, selected private row, and full reward table. It claims no
manuscript theorem closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceInitializationControlRemainder
open Bandits.Support.ReferenceDownReception
open Bandits.Support.CoordinatorUpReception

namespace Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters}

/-- The actual launch remains in its all-active mode at the elapsed time
recorded by the same initialization output. -/
theorem generatedLaunchActive
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed) :
    allActiveAtStart (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc) s := by
  simpa [hsElapsed] using
    ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart rate z rewards C_star C_h hc

/-- The one original physical run on the whole source and reward table. -/
def generatedFirstCutoffRun
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T) :
    ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc) :=
  ReferenceActivePhysicalHorizon.run
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)

/-- The followers' seed is the ordinary state from the actual initialization
output, and their initial memory is the lifecycle's literal initial memory. -/
def generatedFirstCutoffSeed
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
  fun i => ReferenceInitializationRun.ordinary
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
    (ActualReferenceInitializationBlock.refFollower i)

def generatedFirstCutoffMemory : Fin (p.m - 1) → LocalMemory p :=
  fun _ => ActiveFollowerLifecycle.initialMemory p

/-- The fixed-control inverse fibre constructs the same corrected launch as
the numerical launch cell. -/
theorem generatedLaunchSeed_eq_launchState
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (hsT : s < p.T) :
    ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p
        (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩ z).1
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p
        (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩ z).2
      (by
        change PrivateSourceStreams.coordinatorIndex p
          ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p
            (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩ z).2.2).1.2 =
              ActualInitializationPhysicalStep.selectedRowIndex p z
        rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
        change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = _
        rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex])
      s (Nat.le_of_eq rfl)
      (by
        apply (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
          rate rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p z)
          ⟨s, hsT⟩
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p
            (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩ z).1
          z rfl s (Nat.le_of_eq rfl)).mpr
        exact ⟨hc, hsElapsed.symm⟩) =
      ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc := by
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let t : Fin p.T := ⟨s, hsT⟩
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z
  have hremainder : split.2 ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t := by
    change PrivateSourceStreams.coordinatorIndex p
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z).2.2).1.2 = J
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = J
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hstart : split.2 ∈ launchStartRemainderEvent rate rewards C_star C_h J t s split.1 := by
    exact (launchStartRemainderEvent_iff_source rate rewards C_star C_h J t split.1
      z rfl s (Nat.le_of_eq rfl)).mpr ⟨hc, hsElapsed.symm⟩
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h J t split.1 split.2 hremainder s (Nat.le_of_eq rfl) hstart
  let source := ReferenceGeneratedActivePrefixFactor.splitSource J t split.1 split.2
  have hsource : source = z := by
    dsimp [source, ReferenceGeneratedActivePrefixFactor.splitSource, J, t, split]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p
      (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨s, hsT⟩).symm_apply_apply z
  have hcorrected := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hc
  have hcorrected' : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h =
        some (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc) := by
    rw [hsource]
    exact hcorrected
  exact Option.some.inj (hspec.1.symm.trans (by simpa [source] using hcorrected'))

/-- The generated first-cutoff geometry, actual initialization state facts,
and first DOWN payload are all stated directly over the original physical run. -/
theorem run_generated_first_cutoff_survival
    (rate : RateInput p) (z : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (firstLiveWindow
      (generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let k := window.length
    let hprefixSpan : s + k ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) s) hspan
    let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan
      (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
    allActiveAtStart initial s ∧
    initial.coordinator = .first ∧
    initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
    ReferenceInitializationRun.coordinatorLearner
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)) =
      some (RecordedQueueRun.initialState p.K) ∧
    (∀ arm : Fin p.K,
      (RecordedQueueRun.initialState p.K).registers arm = (0, 0) ∧
      (RecordedQueueRun.initialState p.K).records arm = [] ∧
      (RecordedQueueRun.initialState p.K).overflow = false) ∧
    (∀ i : Fin (p.m - 1),
      initial.followers i = .ordinary (generatedFirstCutoffSeed rate z rewards C_star C_h i)
        (generatedFirstCutoffMemory (p := p) i) ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).lastDown = none ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).S = 0 ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).delta = 0 ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).backlog = 0 ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).status = .unoccupied ∧
      localStateDomainValid (generatedFirstCutoffSeed rate z rewards C_star C_h i) ∧
      localBufferValid (generatedFirstCutoffSeed rate z rewards C_star C_h i) ∧
      (generatedFirstCutoffSeed rate z rewards C_star C_h i).buffer.Pairwise
        (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ (generatedFirstCutoffSeed rate z rewards C_star C_h i).buffer,
        saved.calendarRound ≤ s) ∧
      downDecoderStateValid (generatedFirstCutoffSeed rate z rewards C_star C_h i)) ∧
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        have hk : k < count := by simpa [window, execution] using hshort
        have hlen : execution.records.length = count := by
          simpa [execution, generatedFirstCutoffRun] using
            ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
              (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
        omega) ∧
      cut.input.time.val = s + k ∧
      cut.input.state = prefixRun.finalState ∧
      cut.input.rows = z.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      cut.input.rewards = rewards ∧
      ∃ r q base,
        cut.input.state.coordinator = .live r q base ∧
        r.payload.sigma.val = s ∧
        (∀ i : Fin (p.m - 1),
          (r.payload.downRecord (ActualReferenceInitializationBlock.refFollower i)).val.q = 0) ∧
        ∃ dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected,
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          let u := cut.input.time.val + 1
          u = s + k + 1 ∧
          u ≤ p.T ∧
          u ≤ r.gridBoundary ∧
          ledger.sigma = r.payload.sigma.val + 1 ∧
          ledger.cutoff = u ∧
          (∀ i : Fin (p.m - 1),
            ∃ c μ logged d post,
              let prepared := cut.output.preparation.followers.followers i
              let own := cut.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let view := cut.output.preparation.coordinator.downView
              prepared.configuration = .ordinary c μ ∧
              ActiveFollowerLogging.checkedLogging i cut.input.row
                (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
              logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
                (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
              d = referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
              (recordFollower view i cut.input.row (cut.input.state.activations i)
                cut.input.time (cut.input.active i) prepared.arm own c).result = .ok post ∧
              (recordFollower view i cut.input.row (cut.input.state.activations i)
                cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
              (recordFollower view i cut.input.row (cut.input.state.activations i)
                cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
              DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
                own c μ post = .ok (post, μ) ∧
              (cut.output.followers i).configuration = .ordinary post μ ∧
              (cut.output.followers i).failure = none ∧
              post.status = .unoccupied ∧ localStateDomainValid post ∧
              post.S + post.backlog ≤ k * D p ∧
              post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
              (cut.output.followers i).downInput = some logged ∧
              (cut.output.followers i).down = some d) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
  let window := firstLiveWindow execution.records
  let k := window.length
  have hwindowShort : window.length < count := by
    simpa [window, execution, generatedFirstCutoffRun, initial] using hshort
  have hfirst : initial.coordinator = .first := by
    obtain ⟨_, _, _, hfirst, _, _, _, _⟩ :=
      ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc
    exact hfirst
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed) hfirst hwindowShort
  dsimp only [execution, window, k] at houtside
  rcases houtside with ⟨cut, suffix, hsplit, hindex, htime, hactual, hstateWitness⟩
  rcases hstateWitness with ⟨r, q, base, hcutState, hprefixLive, hcall⟩
  rcases hcall with ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock,
    hpending, hnoAssignment, selected, hbranchRest⟩
  rcases hbranchRest with
    ⟨hbranch, _, hsigma, _, hbirth, _, _, hcutoffRest⟩
  rcases hcutoffRest with ⟨huValue, _, huT, huGrid, _, hledgerSigma, hledgerCut, _⟩
  obtain ⟨birth, _, _, _, installed, birthSelection, hbirthPrep, hbirthPayload⟩ := hbirth
  have hdispatch : ReferenceActivePhysicalStep.dispatch birth.input =
      .first (.chosen installed birthSelection) :=
    birth.output.preparation.coordinator_eq.symm.trans hbirthPrep
  have hbirthFirst : birth.input.state.coordinator = .first := by
    cases hstate : birth.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch] at hdispatch
        cases hdispatch
    | collection payload ledger proposal =>
        simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
        split at hdispatch <;> cases hdispatch
    | dagger =>
        simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
        cases hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput birth.input) =
        .chosen installed birthSelection := by
    rw [ReferenceActivePhysicalStep.dispatch_first birth.input hbirthFirst] at hdispatch
    injection hdispatch with hchosen
  have hqzero : ∀ i : Fin (p.m - 1),
      (r.payload.downRecord (ActualReferenceInitializationBlock.refFollower i)).val.q = 0 := by
    intro i
    rw [← hbirthPayload]
    exact ReferenceAssignmentPayloadPersistence.firstChosen_down_queue_zero birth.input
      installed birthSelection hchosen (ActualReferenceInitializationBlock.refFollower i)
  have hA := ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc
  rcases hA with ⟨_, hactive, _, _, hbank, hlearner, hzero, hfollowers⟩
  have hactiveRoot : allActiveAtStart initial s := by
    simpa [initial, hsElapsed] using hactive
  have hprefixSpan : s + k ≤ p.T := by
    exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hwindowShort) s) hspan
  let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
  have hcutIndex : cut = execution.records[k]'(by
      have hk : k < count := by simpa [window, execution] using hwindowShort
      have hlen : execution.records.length = count := by
        simpa [execution, generatedFirstCutoffRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
            (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
      omega) := by
    simpa [execution, window, k] using hindex
  have hcutTime : cut.input.time.val = s + k := by
    simpa [window, k] using htime
  have hcutPrefix : cut.input.state = prefixRun.finalState := by
    simpa [prefixRun, hprefixSpan, k, execution, window] using hcutState
  have hcutRows : cut.input.rows = z.1.2 := by
    rw [hactual]
    rfl
  have hcutSelected : cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z := by
    rw [hactual]
    rfl
  have hcutRewards : cut.input.rewards = rewards := by
    rw [hactual]
    rfl
  let seed := generatedFirstCutoffSeed rate z rewards C_star C_h
  let memory := generatedFirstCutoffMemory (p := p)
  have hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    simpa [initial, seed, memory, generatedFirstCutoffSeed,
      generatedFirstCutoffMemory, ActualReferenceInitializationBlock.referenceInput] using
      (hfollowers i).1
  have hS : ∀ i, (seed i).S = 0 := by
    intro i
    rcases hfollowers i with ⟨_, _, _, hzero, _, _, _, _, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hzero
  have hdelta : ∀ i, (seed i).delta = 0 := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, hzero, _, _, _, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hzero
  have hbacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, _, hzero, _, _, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hzero
  have hnone : ∀ i, (seed i).lastDown = none := by
    intro i
    rcases hfollowers i with ⟨_, hzero, _, _, _, _, _, _, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hzero
  have hunoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, _, _, hstatus, _, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hstatus
  have hbufferValid : ∀ i, localBufferValid (seed i) := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, _, _, _, _, hvalid, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hvalid
  have hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, _, _, _, _, _, hpair, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hpair
  have htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s := by
    intro i saved hsaved
    rcases hfollowers i with ⟨_, _, _, _, _, _, _, _, _, _, htime⟩
    have hsaved' : saved ∈
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
          (ActualReferenceInitializationBlock.refFollower i)).buffer := by
      simpa [seed, generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hsaved
    simpa [hsElapsed] using htime saved hsaved'
  have hbatch : ∀ i, downDecoderStateValid (seed i) := by
    intro i
    rcases hfollowers i with ⟨_, _, _, _, _, _, _, hdomain, _, _, _⟩
    simpa [seed, generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hdomain.2.2
  have hprep := ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed) hfirst seed memory
    hseed hS hdelta hbacklog hnone hunoccupied hbufferValid hpair htime hbatch hwindowShort
  rcases hprep with
    ⟨preparedCut, preparedSuffix, _, hpreparedIndex, _, _, _, _, _, hpreparedFollowers, _, _⟩
  have hpreparedCutIndex : preparedCut = execution.records[k]'(by
      have hk : k < count := by simpa [window, execution] using hwindowShort
      have hlen : execution.records.length = count := by
        simpa [execution, generatedFirstCutoffRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
            (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
      omega) := by
    simpa [execution, window, k] using hpreparedIndex
  have hsameCut : cut = preparedCut := hcutIndex.trans hpreparedCutIndex.symm
  have hobs := ReferenceFirstCutoffFollowerObservation.run_first_cutoff_follower_observation
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed) hfirst seed memory
    hseed hS hdelta hbacklog hnone hunoccupied hbufferValid hpair htime hbatch hwindowShort
  have hfollowersObserved : ∀ i : Fin (p.m - 1),
      ∃ c μ logged d post,
        let prepared := cut.output.preparation.followers.followers i
        let own := cut.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        let view := cut.output.preparation.coordinator.downView
        prepared.configuration = .ordinary c μ ∧
        ActiveFollowerLogging.checkedLogging i cut.input.row
          (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
        logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
          (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
        d = referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
        (recordFollower view i cut.input.row (cut.input.state.activations i)
          cut.input.time (cut.input.active i) prepared.arm own c).result = .ok post ∧
        (recordFollower view i cut.input.row (cut.input.state.activations i)
          cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
        (recordFollower view i cut.input.row (cut.input.state.activations i)
          cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
        DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
          own c μ post = .ok (post, μ) ∧
        (cut.output.followers i).configuration = .ordinary post μ ∧
        (cut.output.followers i).failure = none ∧ post.status = .unoccupied ∧
        localStateDomainValid post ∧ post.S + post.backlog ≤ k * D p ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
        (cut.output.followers i).downInput = some logged ∧
        (cut.output.followers i).down = some d := by
    intro i
    rcases hpreparedFollowers i with
      ⟨state, mem, hstate, _, _, _, hprepared, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    have hpreparedCut :
        (cut.output.preparation.followers.followers i).configuration = .ordinary
          ({state with status := .unoccupied}) mem := by
      have hprepared' := hprepared
      rw [← hsameCut] at hprepared'
      exact hprepared'
    have hobsIndex := hobs i
    dsimp only at hobsIndex
    rw [← hcutIndex] at hobsIndex
    rw [hpreparedCut] at hobsIndex
    rcases hobsIndex with
      ⟨logged, d, post, hlogging, hloggedBuffer, hdownCut, hrecordResult,
        hrecordInput, hrecordDown, hrelease, hpostConfig, hfailure, hstatus,
        hdomainPost, hmass, hpairPost, hstamps, hdiagInput, hdiagDown⟩
    exact ⟨{state with status := .unoccupied}, mem, logged, d, post, hpreparedCut,
      hlogging, hloggedBuffer, hdownCut, hrecordResult, hrecordInput, hrecordDown,
      hrelease, hpostConfig, hfailure, hstatus, hdomainPost, hmass, hpairPost,
      hstamps, hdiagInput, hdiagDown⟩
  refine ⟨hactiveRoot, hfirst, hbank, hlearner, hzero, ?_, ?_⟩
  · intro i
    rcases hfollowers i with
      ⟨hconfiguration, hlast, _, hS, hdelta, hbacklog, hstatus,
        hdomain, hbuffer, hpair, htimeSeed⟩
    have hconfiguration' : initial.followers i =
        .ordinary (generatedFirstCutoffSeed rate z rewards C_star C_h i)
          (generatedFirstCutoffMemory (p := p) i) := by
      simpa [generatedFirstCutoffSeed, generatedFirstCutoffMemory,
        ActualReferenceInitializationBlock.referenceInput] using hconfiguration
    refine ⟨hconfiguration', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hlast
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hS
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hdelta
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hbacklog
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hstatus
    · simpa [generatedFirstCutoffSeed,
      ActualReferenceInitializationBlock.referenceInput] using hdomain
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hbuffer
    · simpa [generatedFirstCutoffSeed,
        ActualReferenceInitializationBlock.referenceInput] using hpair
    · intro saved hsaved
      have hsaved' : saved ∈
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i)).buffer := by
        simpa [generatedFirstCutoffSeed,
          ActualReferenceInitializationBlock.referenceInput] using hsaved
      simpa [hsElapsed] using htimeSeed saved hsaved'
    · have hdomain' : localStateDomainValid
          (generatedFirstCutoffSeed rate z rewards C_star C_h i) := by
        simpa [generatedFirstCutoffSeed,
          ActualReferenceInitializationBlock.referenceInput] using hdomain
      exact hdomain'.2.2
  · refine ⟨cut, suffix, hsplit, hcutIndex, hcutTime, hcutPrefix,
      hcutRows, hcutSelected, hcutRewards, r, q, base,
      (by rw [hcutPrefix]; exact hprefixLive), ?_, hqzero,
      dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
      hnoAssignment, selected, hbranch, ?_⟩
    · exact hsigma
    · refine ⟨?_, huT, huGrid, hledgerSigma, hledgerCut, hfollowersObserved⟩
      simpa [hcutTime, generatedFirstCutoffRun] using huValue

end Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

end
