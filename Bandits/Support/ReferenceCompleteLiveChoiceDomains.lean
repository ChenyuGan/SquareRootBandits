/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEpisodeScoreGrowth
public import Bandits.Support.ReferenceCompleteLiveDispatchDomains

import Lean.Elab.Tactic.Omega

/-!
# Complete-source live arm choice

For an actual incoming LIVE state in the original complete suffix, the stored
clock and retained episode envelope discharge the remaining pre-choice local
checks. The original dispatcher therefore produces its continuing or cutoff
choice on the same complete source row. This module ends at that selection.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-114,140-188,219-243`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,123-189,246-299,355-390`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.ReferenceCompletePhysicalHistory

namespace Bandits.Support.ReferenceCompleteLiveChoiceDomains

variable {p : ConstructorDimensions.Parameters}

/-- The clock invariant at an actual complete-suffix member, obtained from the
corrected launch's real seed and the public clock-preservation theorem. The
proof is local so callers never use the dispatch-domain module's private
complete-suffix clock helper. -/
private theorem complete_suffix_member_clockAt_local
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.state := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let launchState := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      let J : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
      let rows : CompletePublicTable.CompleteRows p := source.1.2
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      let initial := active
      have hactiveLaunch : initial = launchState := by
        have hboth := hlaunch.symm.trans hcanonical
        exact Option.some.inj hboth
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        have hfirst : initial.coordinator = .first := by
          rw [hactiveLaunch]
          exact seed.coordinatorFirst
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial rows J rewards start
        (p.T - start) hspan hmode
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start (p.T - start) hspan hmode hseed
      have hmember : (R[k.val]'k.isLt) ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      have hrecord := hclockRun.2.2.2 (R[k.val]'k.isLt) hmember
      rw [hrecord.2.2.1, hrecord.2.2.2.1]
      exact hrecord.1

/-- A successful LIVE `StartRound` on a valid stored live clock has precisely
the two source command forms: no interruption, preserving the live frame, or
an interruption at this same calendar coordinate, initializing collection. -/
private theorem live_startRound_command_shape
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hsigma : ∃ sigma, clock.sigma = some sigma)
    (hu : clock.u = none)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending =
      .ok started) :
    (started.ledgerCommand = none ∧ started.clock = clock ∧
      started.pending = pending ∧ started.assignmentStart = none) ∨
    (started.ledgerCommand = some (.initializeAt time) ∧
      started.clock = { clock with u := some time } ∧
      started.pending = Finset.univ ∧ started.assignmentStart = none) := by
  classical
  rcases hsigma with ⟨oldSigma, hsigma⟩
  have h := hstart
  unfold CoordinatorPhaseClock.startRound at h
  simp only [hparam, hclock, htime, ↓reduceIte] at h
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure =>
      simp [hdetect] at h
  | ok decision =>
      cases decision with
      | cutoff sigma hcutoff =>
          obtain ⟨actual, hactual, hframe, hpending, hcommand, hassignment⟩ :=
            CoordinatorPhaseClock.startRound_cutoff_effect p rate.eta.val time sigma
              clock pending hparam hclock htime hcutoff hdetect
          have hactual' : actual = started := Except.ok.inj (hactual.symm.trans hstart)
          subst started
          exact Or.inr ⟨hcommand, hframe, hpending, hassignment⟩
      | noCutoff =>
          have hsource :
              ¬ CoordinatorPhaseClock.sourceStartTest clock.sigma clock.u time pending := by
            simp [CoordinatorPhaseClock.sourceStartTest,
              CoordinatorPhaseClock.cutoffAtOrBefore, hu, hsigma]
          have hactual :
              CoordinatorPhaseClock.startRound p rate.eta.val time clock pending =
                .ok
                  { clock := clock
                    gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
                      p rate.eta.val clock hclock
                    pending := pending, ledgerCommand := none, assignmentStart := none } := by
            simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
              hdetect, hsource]
            rfl
          have heq : started =
              { clock := clock
                gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
                  p rate.eta.val clock hclock
                pending := pending, ledgerCommand := none, assignmentStart := none } :=
            Except.ok.inj (hstart.symm.trans hactual)
          subst started
          exact Or.inl ⟨rfl, rfl, rfl, rfl⟩

/-- At each actual complete-source suffix member whose coordinator is LIVE,
the original incoming dispatcher makes a nonempty arm choice. Its exact
`continuingChosen` or `cutoffChosen` result is retained in the physical
preparation, including the actual start result, source row, choice arrays, and
the physical selection carrying the same stored payload. The cutoff case keeps
the source cutoff at the current round; the continuation case keeps the
sentinel cutoff and unchanged live clock frame. No post-choice service is
asserted here. -/
theorem complete_live_dispatch_choice_exists
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live r q base) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let x := (R[k.val]'k.isLt).input
    let current := ReferenceActivePhysicalStep.liveInput x r q base
    let preparation := ReferenceActivePhysicalStep.prepare x
    let chosen := CoordinatorRoundDispatch.dispatchLive current
    preparation.coordinator = .live r q base chosen ∧
    (show Prop from match chosen with
    | .continuingChosen dispatched _ continuation selection =>
        CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          continuation.startRoundResult ∧
        dispatched.startResult.clock.u = none ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights ∧
        dispatched.startResult.clock.g ≤ p.T + 1 ∧
        CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
          dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
          x.row = some selection.arm ∧
        ∃ physical : ReferenceActivePhysicalStep.Selection x,
          preparation.coordinator.selection = some physical ∧
          physical.view.payload = r.payload ∧
          physical.view.pendingAtChoice = dispatched.startResult.pending ∧
          physical.view.cutoff =
            CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
              dispatched.startResult.clock.u ∧
          physical.started = dispatched.startResult ∧
          physical.arm = selection.arm ∧
          physical.view.pendingAtChoice = physical.started.pending ∧
          physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            physical.started.clock.u ∧
          CoordinatorLocalArmChoice.coordinatorArmChoice physical.view.payload
            physical.view.pendingAtChoice physical.view.cutoff x.time
            physical.view.complementWeights x.row = some physical.arm
    | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ selection =>
        dispatched.startResult.ledgerCommand = some (.initializeAt x.time) ∧
        dispatched.startResult.clock =
          { (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock with
              u := some x.time } ∧
        dispatched.startResult.pending = Finset.univ ∧
        dispatched.startResult.assignmentStart = none ∧
        dispatched.collectionInitialization = .success (some ledger) ∧
        ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights ∧
        dispatched.startResult.clock.g ≤ p.T + 1 ∧
        CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
          dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
          x.row = some selection.arm ∧
        ∃ physical : ReferenceActivePhysicalStep.Selection x,
          preparation.coordinator.selection = some physical ∧
          physical.view.payload = r.payload ∧
          physical.view.pendingAtChoice = dispatched.startResult.pending ∧
          physical.view.cutoff =
            CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
              dispatched.startResult.clock.u ∧
          physical.started = dispatched.startResult ∧
          physical.arm = selection.arm ∧
          physical.view.pendingAtChoice = physical.started.pending ∧
          physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            physical.started.clock.u ∧
          CoordinatorLocalArmChoice.coordinatorArmChoice physical.view.payload
            physical.view.pendingAtChoice physical.view.cutoff x.time
            physical.view.complementWeights x.row = some physical.arm
    | _ => False) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let x := record.input
  let currentRegisters := ReferenceActivePhysicalStep.liveRegistersAt r x.time
  let currentOwned := ReferenceActivePhysicalStep.liveOwnedAt r q x.time
  let current := ReferenceActivePhysicalStep.liveInput x r q base
  let preparation := ReferenceActivePhysicalStep.prepare x
  let chosen := CoordinatorRoundDispatch.dispatchLive current
  change preparation.coordinator = .live r q base chosen ∧ _
  have hstateX : x.state.coordinator = .live r q base := hstate

  have hnumeric := ReferenceCompleteLiveDispatchDomains.complete_live_numeric_domains_and_dispatch
    rate rewards C_star C_h source k r q base hstateX
  dsimp only at hnumeric
  rcases hnumeric with
      ⟨hscore, hqueue, hprevious, hbase, hinitializationDomain,
      ⟨startedFromRoot, hstartFromRoot, hdispatchFromRoot⟩, _hnumericSafe⟩

  have hclockAt := complete_suffix_member_clockAt_local rate rewards C_star C_h source k
  have hclockLive : ReferenceCoordinatorClockDomains.clockAt
      x.rows x.selected x.time.val x.state := by
    simpa [x, record, R] using hclockAt
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstateX] at hclockLive
  rcases hclockLive with
    ⟨_hstoredTime, hclockValid, hpayloadClock, hpriorNoCutoff, hgridFrame,
      hsourceStart, hbeforeGrid, _hproposal⟩

  obtain ⟨startedFromClock, hstartFromClock⟩ :=
    ReferenceCoordinatorClockDomains.live_dispatch_startRound_success
      r q base hstateX hclockAt
  have hstartCurrent : CoordinatorPhaseClock.startRound p rate.eta.val
      current.registers.time current.registers.priorClock current.registers.clockPending =
        .ok startedFromClock := by
    simpa [current, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hstartFromClock
  have hstartedEq : startedFromRoot = startedFromClock :=
    Except.ok.inj (hstartFromRoot.symm.trans hstartCurrent)
  subst startedFromRoot
  let started := startedFromClock
  have hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      current.registers.time current.registers.priorClock current.registers.clockPending =
        .ok started := hstartCurrent
  have hdispatch : CoordinatorStartRoundCutoffDispatch.dispatch
      current.registers current.ownedRegisters base =
        .ok ⟨started, .success
          (if started.ledgerCommand = some (.initializeAt x.time) then
            some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              current.registers current.ownedRegisters base x.time)
          else none)⟩ := by
    simpa [current] using hdispatchFromRoot
  have hdispatchCurrent := hdispatch
  change CoordinatorStartRoundCutoffDispatch.dispatch
      current.registers current.ownedRegisters current.followerBaseScore =
    .ok ⟨started, .success
      (if started.ledgerCommand = some (.initializeAt x.time) then
        some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          current.registers current.ownedRegisters current.followerBaseScore x.time)
      else none)⟩ at hdispatchCurrent

  have hclockGrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
    p rate.eta.val r.priorClock hclockValid
  have hpriorGrid : r.priorClock.g ≤ p.T + 1 := by
    cases hsigma : r.priorClock.sigma with
    | none =>
        simp only [CoordinatorPhaseClock.clockGridDomain, hsigma] at hclockGrid
        omega
    | some sigma =>
        simp only [CoordinatorPhaseClock.clockGridDomain, hsigma] at hclockGrid
        exact hclockGrid.2
  have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p x.time r.priorClock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, hpayloadClock,
      hpriorNoCutoff, FollowerCutoffScan.calendarRound]
    omega
  have hparameterValid :=
    ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hstartShape := live_startRound_command_shape rate x.time r.priorClock
    r.clockPending started hparameterValid hclockValid htimeValid
    ⟨r.payload.sigma, hpayloadClock⟩ hpriorNoCutoff hstart

  have henvelopeAtSource :=
    ReferenceCompleteEpisodeScoreGrowth.complete_retained_episode_weight_envelopes
      p rate rewards C_star C_h source k
  rw [hstateX] at henvelopeAtSource
  change r.complementEnvelopeValid at henvelopeAtSource
  have henvelope : currentRegisters.complementEnvelopeValid := by
    change r.complementEnvelopeValid
    exact henvelopeAtSource

  have hstartBound : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
      CoordinatorLocalArmChoice.sourceRound x.time := by
    simp only [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound]
    omega
  have hweights : ∀ j, 0 < currentRegisters.complementWeights j ∧
      r.payload.anchor j.1 ≤ currentRegisters.complementWeights j ∧
      currentRegisters.complementWeights j ≤ 2 * r.payload.anchor j.1 := by
    intro j
    have hj := henvelope j
    refine ⟨lt_of_lt_of_le (r.payload.anchor_pos j.1) hj.1, ?_, ?_⟩
    · exact hj.1
    · exact hj.2
  have hboundaryPrior : r.priorClock.g ≤ p.T + 1 := hpriorGrid
  rcases hstartShape with
    ⟨hcommandNone, hclockUnchanged, hpendingUnchanged, hassignmentNone⟩ |
    ⟨hcommandCutoff, hcutoffClock, hpendingReset, hassignmentNone⟩
  · have hcutoffStart : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
        CoordinatorLocalArmChoice.cutoffRound
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) := by
      simp [CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
        hclockUnchanged, hpriorNoCutoff,
        CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorLocalArmChoice.assignmentStart]
    have hchoice := CoordinatorLocalArmChoice.choiceInputsValid_mk
      r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      current.registers.time currentRegisters.complementWeights
      hstartBound hcutoffStart hweights
    have hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        current.registers.time := by
      have hchoiceTime := hchoice.time.assignment_started
      have hcurrentTime : current.registers.time = x.time := rfl
      simp [CoordinatorLocalArmChoice.assignmentIsLive,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
        hclockUnchanged, hpriorNoCutoff,
        CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.sourceRound,
        CoordinatorLocalArmChoice.cutoffRound, hcurrentTime]
      omega
    have hboundary : started.clock.g ≤ p.T + 1 := by
      rw [hclockUnchanged]
      exact hboundaryPrior
    have hselectedNe := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      current.registers.time currentRegisters.complementWeights x.row hchoice
    have hgood : (show Prop from match chosen with
        | .continuingChosen dispatched _ continuation selection =>
            CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              current.registers continuation.startRoundResult ∧
            dispatched.startResult.clock.u = none ∧
            CoordinatorLocalArmChoice.ChoiceInputsValid current.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) current.registers.time
              current.registers.complementWeights ∧
            dispatched.startResult.clock.g ≤ p.T + 1 ∧
            CoordinatorLocalArmChoice.coordinatorArmChoice current.registers.payload
              dispatched.startResult.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) current.registers.time
              current.registers.complementWeights current.row = some selection.arm ∧
            ∃ physical : ReferenceActivePhysicalStep.Selection x,
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live r q base chosen) = some physical ∧
              physical.view.payload = r.payload ∧
              physical.view.pendingAtChoice = dispatched.startResult.pending ∧
              physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u ∧
              physical.started = dispatched.startResult ∧ physical.arm = selection.arm ∧
              physical.view.pendingAtChoice = physical.started.pending ∧
              physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                physical.started.clock.u ∧
              CoordinatorLocalArmChoice.coordinatorArmChoice physical.view.payload
                physical.view.pendingAtChoice physical.view.cutoff x.time
                physical.view.complementWeights x.row = some physical.arm
        | .cutoffChosen .. => False
        | _ => False) := by
      dsimp only [current, ReferenceActivePhysicalStep.liveInput, currentRegisters,
        currentOwned, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
      have hresult : CoordinatorRoundDispatch.dispatchLive current = chosen := rfl
      unfold CoordinatorRoundDispatch.dispatchLive at hresult
      dsimp only [current, ReferenceActivePhysicalStep.liveInput,
        ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] at hresult
      split at hresult
      · rename_i failure hcall
        have hcontra := hcall.symm.trans hdispatchCurrent
        cases hcontra
      · rename_i actual hcall
        have hd : CoordinatorStartRoundCutoffDispatch.dispatch
            current.registers current.ownedRegisters current.followerBaseScore =
              .ok ⟨started, .success none⟩ := by
          simpa only [hcommandNone, reduceCtorEq, ↓reduceIte] using hdispatchCurrent
        have hactual : actual = ⟨started, .success none⟩ :=
          Except.ok.inj (hcall.symm.trans hd)
        subst actual
        dsimp only at hresult
        have hframe : unchangedLiveClockFrame current.registers started :=
          ⟨hclockUnchanged, hpendingUnchanged, hcommandNone, hassignmentNone⟩
        have hpayload : current.registers.priorClock.sigma =
            some current.registers.payload.sigma := hpayloadClock
        have hgrid : current.registers.gridBoundary = current.registers.priorClock.g :=
          hgridFrame
        have hscoreCurrent : current.registers.scoreDomainValid := hscore
        have hqueueCurrent : current.ownedRegisters.queueDomainValid := hqueue
        have hpreviousCurrent : current.ownedRegisters.previousServiceDomainValid := hprevious
        have hbaseCurrent : ∀ i, current.followerBaseScore i ≤ p.T * D p := hbase
        simp only [current, ReferenceActivePhysicalStep.liveInput] at hframe hpayload hgrid hscoreCurrent hqueueCurrent hpreviousCurrent hbaseCurrent
        have hliveCurrent : assignmentIsLive (liveRegistersAt r x.time).payload
            (cutoffFromClock p started.clock.u) (liveRegistersAt r x.time).time := hlive
        have hchoiceCurrent : ChoiceInputsValid (liveRegistersAt r x.time).payload
            (cutoffFromClock p started.clock.u) (liveRegistersAt r x.time).time
            (liveRegistersAt r x.time).complementWeights := hchoice
        have henvelopeCurrent : (liveRegistersAt r x.time).complementEnvelopeValid := henvelope
        simp only [hframe, hpayload, hgrid, hscoreCurrent, hqueueCurrent,
          hpreviousCurrent, hbaseCurrent, hliveCurrent, hchoiceCurrent, hboundary,
          henvelopeCurrent, implies_true, ↓reduceDIte] at hresult
        split at hresult
        · rename_i hnone
          exact (hselectedNe hnone).elim
        · rename_i actualArm hselected
          rw [← hresult]
          refine ⟨hframe, ?_, hchoice, hboundary, hselected, ?_⟩
          · rw [hclockUnchanged]
            exact hpriorNoCutoff
          · simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte]
            exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hselected⟩
    have hprep : preparation.coordinator = .live r q base chosen := by
      change ReferenceActivePhysicalStep.dispatch x = .live r q base chosen
      unfold ReferenceActivePhysicalStep.dispatch
      rw [hstateX]
      rfl
    refine ⟨hprep, ?_⟩
    rw [hprep]
    cases hc : chosen <;> simp only [hc] at hgood
    · simp only [chosen, current, x, record, R] at hc
      rw [hc]
      exact hgood
  · have hcutoffBound : CoordinatorLocalArmChoice.assignmentStart r.payload ≤
        CoordinatorLocalArmChoice.cutoffRound
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) := by
      simp [CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
        hcutoffClock, CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorLocalArmChoice.assignmentStart]
      omega
    have hchoice := CoordinatorLocalArmChoice.choiceInputsValid_mk
      r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      current.registers.time currentRegisters.complementWeights
      hstartBound hcutoffBound hweights
    have hboundary : started.clock.g ≤ p.T + 1 := by
      rw [hcutoffClock]
      exact hboundaryPrior
    have hselectedNe := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      current.registers.time currentRegisters.complementWeights x.row hchoice
    have hgood : (show Prop from match chosen with
        | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ selection =>
            dispatched.startResult.ledgerCommand = some (.initializeAt x.time) ∧
            dispatched.startResult.clock =
              { currentRegisters.priorClock with u := some x.time } ∧
            dispatched.startResult.pending = Finset.univ ∧
            dispatched.startResult.assignmentStart = none ∧
            dispatched.collectionInitialization = .success (some ledger) ∧
            ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              currentRegisters currentOwned base x.time ∧
            CoordinatorLocalArmChoice.ChoiceInputsValid current.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) current.registers.time
              current.registers.complementWeights ∧
            dispatched.startResult.clock.g ≤ p.T + 1 ∧
            CoordinatorLocalArmChoice.coordinatorArmChoice current.registers.payload
              dispatched.startResult.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u) current.registers.time
              current.registers.complementWeights current.row = some selection.arm ∧
            ∃ physical : ReferenceActivePhysicalStep.Selection x,
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live r q base chosen) = some physical ∧
              physical.view.payload = r.payload ∧
              physical.view.pendingAtChoice = dispatched.startResult.pending ∧
              physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u ∧
              physical.started = dispatched.startResult ∧ physical.arm = selection.arm ∧
              physical.view.pendingAtChoice = physical.started.pending ∧
              physical.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                physical.started.clock.u ∧
              CoordinatorLocalArmChoice.coordinatorArmChoice physical.view.payload
                physical.view.pendingAtChoice physical.view.cutoff x.time
                physical.view.complementWeights x.row = some physical.arm
        | _ => False) := by
      dsimp only [current, ReferenceActivePhysicalStep.liveInput, currentRegisters,
        currentOwned, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
      have hresult : CoordinatorRoundDispatch.dispatchLive current = chosen := rfl
      unfold CoordinatorRoundDispatch.dispatchLive at hresult
      dsimp only [current, ReferenceActivePhysicalStep.liveInput,
        ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] at hresult
      split at hresult
      · rename_i failure hcall
        have hcontra := hcall.symm.trans hdispatchCurrent
        cases hcontra
      · rename_i actual hcall
        have hd : CoordinatorStartRoundCutoffDispatch.dispatch
            current.registers current.ownedRegisters current.followerBaseScore =
              .ok ⟨started, .success (some
                (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                  current.registers current.ownedRegisters current.followerBaseScore x.time))⟩ := by
          simpa only [hcommandCutoff, ↓reduceIte] using hdispatchCurrent
        have hactual : actual = ⟨started, .success (some
            (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              current.registers current.ownedRegisters current.followerBaseScore x.time))⟩ :=
          Except.ok.inj (hcall.symm.trans hd)
        subst actual
        dsimp only at hresult
        have hchoiceCurrent : ChoiceInputsValid (liveRegistersAt r x.time).payload
            (cutoffFromClock p started.clock.u) (liveRegistersAt r x.time).time
            (liveRegistersAt r x.time).complementWeights := hchoice
        have henvelopeCurrent : (liveRegistersAt r x.time).complementEnvelopeValid := henvelope
        simp only [hchoiceCurrent, hboundary, henvelopeCurrent, ↓reduceDIte] at hresult
        split at hresult
        · rename_i hnone
          exact (hselectedNe hnone).elim
        · rename_i actualArm hselected
          rw [← hresult]
          refine ⟨hcommandCutoff, hcutoffClock, hpendingReset, hassignmentNone,
            rfl, rfl, hchoice, hboundary, hselected, ?_⟩
          simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt, ↓reduceDIte]
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hselected⟩
    have hprep : preparation.coordinator = .live r q base chosen := by
      change ReferenceActivePhysicalStep.dispatch x = .live r q base chosen
      unfold ReferenceActivePhysicalStep.dispatch
      rw [hstateX]
      rfl
    refine ⟨hprep, ?_⟩
    rw [hprep]
    cases hc : chosen <;> simp only [hc] at hgood
    · simp only [chosen, current, x, record, R] at hc
      rw [hc]
      exact hgood

end Bandits.Support.ReferenceCompleteLiveChoiceDomains

end
