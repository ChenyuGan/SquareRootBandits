/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInstalledClockPreservation
public import Bandits.Support.ReferenceLiveClockPreservation
public import Bandits.Support.ReferenceCollectionClockPreservation

import Lean.Elab.Tactic.Omega

/-!
# Clock preservation for the actual reference run

The clock predicate is the literal
`ReferenceCoordinatorClockDomains.clockAt`. The one-step result follows the
actual dispatcher and checked preparation branches, including their absorbing
failure outcomes; the finite-run results fold that transition over the actual
calendar without introducing a clock trace. Source ranges:
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-247,277-296`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-44,81-84`.

These are conditional internal clock results. They do not establish local
validity, no dagger, score or queue truth, sampler or recorder laws, or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CoordinatorRoundDispatch

namespace Bandits.Support.ReferenceRunClockPreservation

private theorem step_clockAt_of_no_selection
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none) :
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next := by
  have hconfiguration :
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger := by
    cases hcut : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome =>
        have hs : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none := by
          simpa only [hcut] using hselection
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          hcut, hs, ReferenceActivePhysicalStep.coordinatorFailure]
    | live r q base outcome =>
        have hs : (ReferenceActivePhysicalStep.DispatchCut.live r q base outcome).selection = none := by
          simpa only [hcut] using hselection
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          hcut, hs, ReferenceActivePhysicalStep.coordinatorFailure]
    | collection payload ledger clock cutoff outcome =>
        have hs : (ReferenceActivePhysicalStep.DispatchCut.collection
            payload ledger clock cutoff outcome).selection = none := by
          simpa only [hcut] using hselection
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          hcut, hs, ReferenceActivePhysicalStep.coordinatorFailure]
    | invalidCollectionCutoff =>
        have hs : (ReferenceActivePhysicalStep.DispatchCut.invalidCollectionCutoff
            (x := x)).selection = none := by
          simpa only [hcut] using hselection
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          hcut, hs, ReferenceActivePhysicalStep.coordinatorFailure]
    | dagger =>
        have hs : (ReferenceActivePhysicalStep.DispatchCut.dagger (x := x)).selection = none := by
          simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut, hs]
  have hnext : (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger :=
    (ReferenceActivePhysicalStep.step_next_fields x).1.trans hconfiguration
  simp [ReferenceCoordinatorClockDomains.clockAt, hnext]

/-- The literal coordinator clock is preserved by one actual physical step.
Every dispatcher and prepare constructor is eliminated from the same input;
start results, phase frames, and installation data come from those
constructors. Checked failures and malformed collection cutoffs enter the
actual absorbing coordinator state. -/
theorem step_clockAt
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hclock : ReferenceCoordinatorClockDomains.clockAt
      x.rows x.selected x.time.val x.state) :
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next := by
  classical
  cases hcoord : x.state.coordinator with
  | first =>
      cases hdispatch : CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput x) with
      | chosen installation selection =>
          rcases ReferenceInstalledClockPreservation.step_clockAt_firstChosen
              x installation selection hcoord hdispatch with
            ⟨_, _, _, _, _, hnext, _⟩
          exact hnext
      | choiceDomainFailure installation =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .first (.choiceDomainFailure installation) := by
            change ReferenceActivePhysicalStep.dispatch x = _
            rw [ReferenceActivePhysicalStep.dispatch_first x hcoord, hdispatch]
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
            rw [hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          exact step_clockAt_of_no_selection x hselection
      | recorderBoundaryFailure installation =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .first (.recorderBoundaryFailure installation) := by
            change ReferenceActivePhysicalStep.dispatch x = _
            rw [ReferenceActivePhysicalStep.dispatch_first x hcoord, hdispatch]
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
            rw [hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          exact step_clockAt_of_no_selection x hselection
      | choiceRejected installation =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .first (.choiceRejected installation) := by
            change ReferenceActivePhysicalStep.dispatch x = _
            rw [ReferenceActivePhysicalStep.dispatch_first x hcoord, hdispatch]
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
            rw [hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          exact step_clockAt_of_no_selection x hselection
  | live r q base =>
      cases hdispatch : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x r q base) with
      | clockFailure failure hfailure =>
          obtain ⟨started, hstarted⟩ :=
            ReferenceCoordinatorClockDomains.live_dispatch_startRound_success
              r q base hcoord hclock
          have hstartFailure :=
            (CoordinatorStartRoundCutoffDispatch.dispatch_clockError_iff
              (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base failure).mp hfailure
          rw [hstarted] at hstartFailure
          cases hstartFailure
      | initializerFailure dispatched hstart checked hchecked =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live r q base (.initializerFailure dispatched hstart checked hchecked) := by
            simp [ReferenceActivePhysicalStep.prepare,
              ReferenceActivePhysicalStep.dispatch, hcoord,
              CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection :
              (ReferenceActivePhysicalStep.DispatchCut.live r q base
                (.initializerFailure dispatched hstart checked hchecked)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          rcases ReferenceLiveClockPreservation.step_live_noChoice_dagger
              r q base (.initializerFailure dispatched hstart checked hchecked)
              hcut hselection with ⟨_, hnext⟩
          exact hnext
      | localFailure dispatched hstart reason =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live r q base (.localFailure dispatched hstart reason) := by
            simp [ReferenceActivePhysicalStep.prepare,
              ReferenceActivePhysicalStep.dispatch, hcoord,
              CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection :
              (ReferenceActivePhysicalStep.DispatchCut.live r q base
                (.localFailure dispatched hstart reason)).selection = none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          rcases ReferenceLiveClockPreservation.step_live_noChoice_dagger
              r q base (.localFailure dispatched hstart reason) hcut hselection with
            ⟨_, hnext⟩
          exact hnext
      | cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
          hcutoffClock hcutoffPending hnoAssignment selection =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live r q base (.cutoffChosen dispatched hstart ledger hinitialization
                hcandidate hdomains hcutoffClock hcutoffPending hnoAssignment selection) := by
            simp [ReferenceActivePhysicalStep.prepare,
              ReferenceActivePhysicalStep.dispatch, hcoord,
              CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          exact ReferenceCollectionClockPreservation.step_clockAt_live_cutoff
            r q base (.cutoffChosen dispatched hstart ledger hinitialization
              hcandidate hdomains hcutoffClock hcutoffPending hnoAssignment selection)
            hcoord hclock hcut
      | continuingChosen dispatched hstart continuation selection =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .live r q base (.continuingChosen dispatched hstart continuation selection) := by
            simp [ReferenceActivePhysicalStep.prepare,
              ReferenceActivePhysicalStep.dispatch, hcoord,
              CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          exact ReferenceLiveClockPreservation.step_clockAt_live_continuing
            r q base dispatched continuation selection hcoord hclock hstart hcut
  | collection payload ledger saved =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        have hcut_of (outcome : CoordinatorRoundDispatch.CollectionOutcome source)
            (hdispatch : CoordinatorRoundDispatch.dispatchCollection source = outcome) :
            (ReferenceActivePhysicalStep.prepare x).coordinator =
              .collection payload ledger clock cutoff outcome := by
          change ReferenceActivePhysicalStep.dispatch x = _
          simp [ReferenceActivePhysicalStep.dispatch, hcoord, hcutoff,
            cutoff, clock, source, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
        cases hdispatch : CoordinatorRoundDispatch.dispatchCollection source with
        | clockFailure failure hstart =>
            obtain ⟨started, hstarted⟩ :=
              ReferenceCoordinatorClockDomains.collection_dispatch_startRound_success
                payload ledger saved hcoord hclock
            have hstartFailure :
                CoordinatorPhaseClock.startRound p rate.eta.val x.time clock
                  ledger.pending = .error failure := by
              exact hstart
            rw [hstarted] at hstartFailure
            cases hstartFailure
        | localFailure started hstart hcore reason =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | coreFailure core started hstart reason =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | continuing core prepared boundary hscores =>
            have hcut := hcut_of _ hdispatch
            exact ReferenceCollectionClockPreservation.step_clockAt_collection_continuing
              payload ledger saved clock cutoff
              (.continuing core prepared boundary hscores) hcoord hclock hcut
        | laterReconstructionFailure core consistent started hstart instruction
            hinstruction failure hlater =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | laterPrefixFailure core consistent started hstart instruction
            hinstruction arm failure hlater =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | laterOrientationFailure core consistent started hstart instruction
            hinstruction set hlater =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | laterChoiceFailure core consistent started hstart instruction
            hinstruction output hlocal clockData installation reason =>
            have hcut := hcut_of _ hdispatch
            have hselection :
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            exact step_clockAt_of_no_selection x hselection
        | laterChosen core consistent started hstart instruction hinstruction output
            hlocal clockData installation selection =>
            have hcut := hcut_of _ hdispatch
            rcases ReferenceInstalledClockPreservation.step_clockAt_laterChosen
                x payload ledger clock cutoff core consistent started hstart
                instruction hinstruction output hlocal clockData installation
                selection hcut with
              ⟨_, _, _, _, _, hnext, _⟩
            exact hnext
      · have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .invalidCollectionCutoff := by
            exact (ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
              x payload ledger saved hcoord hcutoff).1
        have hselection :
            (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
          rw [hcut]
          simp [ReferenceActivePhysicalStep.DispatchCut.selection]
        exact step_clockAt_of_no_selection x hselection
  | dagger =>
      have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .dagger := by
        exact ReferenceActivePhysicalStep.dispatch_dagger x hcoord
      have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
        rw [hcut]
        simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      exact step_clockAt_of_no_selection x hselection

private theorem run_clockAt_final_and_records
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceCoordinatorClockDomains.clockAt rows selected start initial) :
    ReferenceCoordinatorClockDomains.clockAt rows selected (start + count)
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState ∧
      ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records,
        ReferenceCoordinatorClockDomains.clockAt rows selected record.input.time.val
            record.input.state ∧
          ReferenceCoordinatorClockDomains.clockAt rows selected (record.input.time.val + 1)
            record.output.next := by
  induction count with
  | zero =>
      constructor
      · rw [ReferenceActivePhysicalHorizon.run_zero_final initial rows selected rewards
          start hspan hmode]
        simpa using hseed
      · intro record hrecord
        rw [ReferenceActivePhysicalHorizon.run_zero_records initial rows selected rewards
          start hspan hmode] at hrecord
        simp at hrecord
  | succ count ih =>
      have hprevSpan : start + count ≤ p.T := by omega
      rcases ih hprevSpan with ⟨hprevClock, hprevRecords⟩
      let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hprevSpan hmode
      let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
        ⟨start + count, by omega, by omega⟩
      let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected
        rewards start hmode prefixRun entry
      have hinputClock : ReferenceCoordinatorClockDomains.clockAt rows selected
          input.time.val input.state := by
        simpa [input, ReferenceActivePhysicalHorizon.roundInputAt, prefixRun, entry] using
          hprevClock
      have hstep := step_clockAt input hinputClock
      have hrunEq := ReferenceActivePhysicalHorizon.run_successor_step initial rows
        selected rewards start count hspan hmode
      have hfold := ReferenceActivePhysicalHorizon.foldRound_equations initial rows
        selected rewards start hmode prefixRun entry
      have hfinalEq :
          (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
            hmode prefixRun entry).finalState = (ReferenceActivePhysicalStep.step input).next := by
        simpa [input] using hfold.1
      have hrecordsEq :
          (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start
            hmode prefixRun entry).records = prefixRun.records ++
              [⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] := by
        simpa [input] using hfold.2
      constructor
      · rw [hrunEq, hfinalEq]
        have htime : start + (count + 1) = start + count + 1 := by omega
        rw [htime]
        simpa [input, ReferenceActivePhysicalHorizon.roundInputAt, entry] using hstep
      · intro record hrecord
        rw [hrunEq, hrecordsEq] at hrecord
        rcases List.mem_append.mp hrecord with hprevious | hcurrent
        · exact hprevRecords record hprevious
        · have hrecordEq := List.mem_singleton.mp hcurrent
          subst record
          constructor
          · exact hinputClock
          · exact hstep

/-- A genuine seed of the literal coordinator invariant propagates through
the computed `H.run` fold. The result covers every shorter run prefix and every
member record of this same run, with its retained row, selected index, reward
table, and physical calendar coordinate. Prefix induction uses
`run_successor_step` and `foldRound_equations`; record membership is retained
through the fold and identities come from `run_record_inputs` and
`run_time_values`. -/
theorem run_clockAt
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hseed : ReferenceCoordinatorClockDomains.clockAt rows selected start initial) :
    ReferenceCoordinatorClockDomains.clockAt rows selected (start + count)
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState ∧
      (∀ prefixLength, ∀ hpref : prefixLength ≤ count,
        ReferenceCoordinatorClockDomains.clockAt rows selected (start + prefixLength)
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start prefixLength
            (by omega) hmode).finalState) ∧
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records.map
            (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar start count) ∧
      ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records,
        ReferenceCoordinatorClockDomains.clockAt rows selected record.input.time.val
            record.input.state ∧
          ReferenceCoordinatorClockDomains.clockAt rows selected (record.input.time.val + 1)
            record.output.next ∧
          record.input.rows = rows ∧ record.input.selected = selected ∧
          record.input.rewards = rewards ∧
          record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar start count := by
  have hmain := run_clockAt_final_and_records initial rows selected rewards start count
    hspan hmode hseed
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs initial rows selected
    rewards start count hspan hmode
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected
    rewards start count hspan hmode
  refine ⟨hmain.1, ?_, htimes, ?_⟩
  · intro prefixLength hpref
    have hprefixSpan : start + prefixLength ≤ p.T := by omega
    exact (run_clockAt_final_and_records initial rows selected rewards start prefixLength
      hprefixSpan hmode hseed).1
  · intro record hrecord
    have hrecordClock := hmain.2 record hrecord
    have hrecordInputs := hinputs record hrecord
    have hrecordTime : record.input.time.val ∈
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records.map
            (fun member => member.input.time.val) :=
      List.mem_map.mpr ⟨record, hrecord, rfl⟩
    rw [htimes] at hrecordTime
    exact ⟨hrecordClock.1, hrecordClock.2, hrecordInputs.1, hrecordInputs.2.1,
      hrecordInputs.2.2, hrecordTime⟩

/-- Conditional specialization at the actual launched boundary. It retains
the original source, rewards, shared constants, preceding block and carry,
chronological past, all exclusion/cleanliness/force premises, launch, learner
seed, and computed handoff equality. The converted state is the actual
postlaunch state; its coordinator is `.first`, so `clockAt` supplies the seed
without an added clock hypothesis. The run begins at the original clipped
`blockStop` and spans through `p.T`, including the zero length case. -/
theorem actualLaunchedBoundary_run_clockAt
    {p : ConstructorDimensions.Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i =
        false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched
    let block := ReferenceInitializationRun.nextBlock b h
    let start := BootstrapObservedFollower.blockStop p block
    let count := p.T - start
    ReferenceCoordinatorClockDomains.clockAt rows selected start initial ∧
      ∃ hspan : start + count ≤ p.T,
        ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start,
          let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count hspan hmode
          ReferenceActivePhysicalHorizon.allActiveAtStart execution.finalState (start + count) ∧
          ReferenceCoordinatorClockDomains.clockAt rows selected (start + count)
            execution.finalState ∧
      (∀ prefixLength, ∀ hpref : prefixLength ≤ count,
            ReferenceCoordinatorClockDomains.clockAt rows selected (start + prefixLength)
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards start prefixLength
                (by omega) hmode).finalState) ∧
          execution.records.map (fun record => record.input.time.val) =
            ReferenceActivePhysicalHorizon.calendar start count ∧
          (∀ record ∈ execution.records,
            ReferenceCoordinatorClockDomains.clockAt rows selected record.input.time.val
                record.input.state ∧
              ReferenceCoordinatorClockDomains.clockAt rows selected
                (record.input.time.val + 1) record.output.next ∧
              record.input.rows = rows ∧ record.input.selected = selected ∧
              record.input.rewards = rewards ∧
              record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar start count) := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  let block := ReferenceInitializationRun.nextBlock b h
  let start := BootstrapObservedFollower.blockStop p block
  let count := p.T - start
  have hstart : start ≤ p.T := by
    dsimp [start, block, BootstrapObservedFollower.blockStop]
    exact Nat.min_le_left _ _
  have hspan : start + count ≤ p.T := by
    dsimp [count]
    omega
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro i
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
  have hcoordinator := ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, initial, hcoordinator]
  have hruns := run_clockAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode hseed
  have hactiveEnd := ReferenceActivePhysicalHorizon.run_allActiveAtEnd initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
  refine ⟨hseed, hspan, hmode, hactiveEnd, ?_⟩
  simpa [initial, start, count] using hruns

/-- The clock invariant itself yields the finite physical source index for a
collection cutoff and its source-time, freeze, and clipped-boundary geometry.
The saved proposal token is not constrained by the collection branch of
`clockAt`. -/
theorem collection_clockAt_cutoff_geometry
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (k : ℕ) (state : ReferenceActivePhysicalHorizon.State p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : state.coordinator = .collection payload ledger saved)
    (hclock : ReferenceCoordinatorClockDomains.clockAt rows selected k state) :
    ∃ cutoff : Fin p.T,
      cutoff.val + 1 = ledger.cutoff ∧
      ledger.sigma = payload.sigma.val + 1 ∧
      payload.sigma.val + 1 < cutoff.val + 1 ∧
      cutoff.val + 1 ≤ k ∧
      cutoff.val + 1 ≤ ledger.freezeAt ∧
      ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      ledger.freezeAt ≤ p.T + 1 := by
  have hinvariant := hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hinvariant
  rcases hinvariant with ⟨hsigma, hsource, hpositive, hbound, htime, hfreeze,
    hfreezeCutoff, hfreezeBound⟩
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  refine ⟨cutoff, ?_, hsigma, ?_, ?_, ?_, hfreeze, hfreezeBound⟩
  · dsimp [cutoff]
    omega
  · dsimp [cutoff]
    omega
  · dsimp [cutoff]
    omega
  · dsimp [cutoff]
    omega

end Bandits.Support.ReferenceRunClockPreservation

end
