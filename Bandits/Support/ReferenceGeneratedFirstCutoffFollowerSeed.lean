/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

import Lean.Elab.Tactic.Omega

/-!
# Generated first-cutoff follower seed refinement

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,246-297`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module refines the actual cutoff output of
`ReferenceGeneratedFirstCutoffSurvival`. Its roots are the same generated
initialization, complete reward table, original private arrays, and physical
prefix; it retains C's actual cut, payload, dispatcher, and follower
observations. It proves no coordinator receive or finish result and no
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
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.CoordinatorUpReception

namespace Bandits.Support.ReferenceGeneratedFirstCutoffFollowerSeed

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters}

/-- The actual first-cutoff record initializes every follower's continuing
local state with whole retained DOWN fields and the same physical successor.
The first conjunct is C's full generated result, preserving its launch, cutoff,
dispatcher, and observation witnesses. The refinement adds the incoming
prefix follower states, the literal first cutoff and first-payload queues, and
the per-follower successor seed fields.
-/
theorem actual_first_cutoff_follower_seed
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
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let k := window.length
    let cut := execution.records[k]'(by
      have hk : k < count := by simpa [window, execution] using hshort
      have hlen : execution.records.length = count := by
        simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
            (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
              rate z rewards C_star C_h hc s hsElapsed)
      omega)
    let successorSpan : s + (k + 1) ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      omega
    let successorRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1)
      successorSpan
      (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
        rate z rewards C_star C_h hc s hsElapsed)
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
        FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = u ∧
        (∀ i : Fin (p.m - 1),
          ∃ old μ c logged d recordPost post,
            let prepared := cut.output.preparation.followers.followers i
            let own := cut.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            let view := cut.output.preparation.coordinator.downView
            cut.input.state.followers i = .ordinary old μ ∧
            (old.status = .unoccupied →
              old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
            (old.status ≠ .unoccupied →
              old.lastDown = some (r.payload.downRecord i)) ∧
            localStateDomainValid old ∧
            localBufferValid old ∧
            downDecoderStateValid old ∧
            old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ old.buffer, saved.calendarRound < s + k + 1) ∧
            startRound rate.eta cut.input.time old μ =
              .ok ({old with status := .unoccupied}, μ) ∧
            prepared.configuration = .ordinary c μ ∧
            c = {old with status := .unoccupied} ∧
            localStateDomainValid c ∧
            localBufferValid c ∧
            downDecoderStateValid c ∧
            c.S + c.backlog ≤ k * D p ∧
            c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ c.buffer, saved.calendarRound < cut.input.time.val + 1) ∧
            c.S = old.S ∧ c.delta = old.delta ∧ c.backlog = old.backlog ∧
            c.lastDown = old.lastDown ∧ c.buffer = old.buffer ∧
            c.downBatch = old.downBatch ∧
            c.initializationFailure = old.initializationFailure ∧
            ActiveFollowerLogging.checkedLogging i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
            logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
            d = referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).result = .ok recordPost ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
            DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
              own c μ recordPost = .ok (post, μ) ∧
            (cut.output.followers i).configuration = .ordinary post μ ∧
            cut.output.next.followers i = .ordinary post μ ∧
            (cut.output.followers i).failure = none ∧
            post.status = .unoccupied ∧
            localStateDomainValid post ∧ localBufferValid post ∧ downDecoderStateValid post ∧
            post.S + post.backlog ≤ k * D p ∧
            post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
            (cut.output.followers i).downInput = some logged ∧
            (cut.output.followers i).down = some d ∧
            ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
              post.lastDown = some (r.payload.downRecord i))) ∧
        s < p.T ∧
        successorRun.finalState = cut.output.next := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let k := window.length
  have hwindowShort : k < count := by
    simpa [window, execution] using hshort
  have hactive := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate z rewards C_star C_h hc s hsElapsed
  have hprefixSpan : s + k ≤ p.T :=
    le_trans (Nat.add_le_add_left (Nat.le_of_lt hwindowShort) s) hspan
  let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan hactive
  let seed := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffSeed
    rate z rewards C_star C_h
  let memory := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffMemory (p := p)
  have hcore := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate z rewards C_star C_h hc s hsElapsed count hspan hshort
  have hcoreParts := hcore
  rcases hcoreParts with ⟨_, hfirst, _, _, _, hseedFacts, hcutWitness⟩
  have hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    exact (hseedFacts i).1
  have hS : ∀ i, (seed i).S = 0 := by
    intro i
    rcases hseedFacts i with ⟨_, _, hS, _, _, _, _, _, _, _, _⟩
    exact hS
  have hdelta : ∀ i, (seed i).delta = 0 := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, hdelta, _, _, _, _, _, _, _⟩
    exact hdelta
  have hbacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, _, hbacklog, _, _, _, _, _, _⟩
    exact hbacklog
  have hnone : ∀ i, (seed i).lastDown = none := by
    intro i
    rcases hseedFacts i with ⟨_, hnone, _, _, _, _, _, _, _, _, _⟩
    exact hnone
  have hunoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, _, _, hunoccupied, _, _, _, _, _⟩
    exact hunoccupied
  have hvalid : ∀ i, localBufferValid (seed i) := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, _, _, _, _, hvalid, _, _, _⟩
    exact hvalid
  have hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, _, _, _, _, _, hpair, _, _⟩
    exact hpair
  have htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s := by
    intro i saved hsaved
    rcases hseedFacts i with ⟨_, _, _, _, _, _, _, _, _, htime, _⟩
    exact htime saved hsaved
  have hbatch : ∀ i, downDecoderStateValid (seed i) := by
    intro i
    rcases hseedFacts i with ⟨_, _, _, _, _, _, _, _, _, _, hbatch⟩
    exact hbatch
  have hinitialFollowers : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro i state mem hstate
    rcases hseedFacts i with ⟨hconfig, hnone, _, _, _, hunoccupied, _, _, _, _, _⟩
    rw [hconfig] at hstate
    injection hstate with hstate hmem
    subst state
    exact ⟨hunoccupied, hnone⟩
  have hfirstLive := ReferenceFirstLiveConfirmationHistory.run_firstLive_prefix_state
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    s count hspan hactive hfirst hinitialFollowers
  have hprefixLive : FirstLiveState prefixRun.finalState := by
    simpa [prefixRun, execution, window, k] using
      hfirstLive k (Nat.le_of_lt hwindowShort) (by rfl)
  have hprep := ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    s count hspan hactive hfirst seed memory hseed hS hdelta hbacklog hnone
    hunoccupied hvalid hpair htime hbatch hwindowShort
  have hprepParts := hprep
  rcases hprepParts with
    ⟨cutPrep, suffixPrep, _, hindexPrep, _, hprefixPrep, _, _, _, hprepFollowers, _, _⟩
  have hcutWitnessParts := hcutWitness
  rcases hcutWitnessParts with
    ⟨cutCore, suffixCore, _, hindexCore, htimeCoreOriginal, hprefixCore,
      _, _, _, hstateWitness⟩
  have hcutEq : cutPrep = cutCore := hindexPrep.trans hindexCore.symm
  let cut := execution.records[k]'(by
    have hlen : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
    omega)
  have hcutCoreEq : cutCore = cut := by simpa [cut] using hindexCore
  subst cutCore
  have hcutPrepEq : cutPrep = cut := hcutEq
  have hcutPrefix : cut.input.state = prefixRun.finalState := by
    exact hprefixCore
  have hcutLive : FirstLiveState cut.input.state := by
    rw [hcutPrefix]
    exact hprefixLive
  rcases hstateWitness with ⟨r, q, base, hcoordCore, hsigma, hqzero, hdispatchWitness⟩
  have hcoord : cut.input.state.coordinator = .live r q base := by
    exact hcoordCore
  have hcarry : ReferenceActiveDataOwnership.carriedOccupiedFields r.payload cut.input.state := by
    simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hcoord] at hcutLive
    exact hcutLive.1
  rcases hdispatchWitness with
    ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock,
      hpending, hnoAssignment, selected, hbranchRest⟩
  rcases hbranchRest with ⟨hcoordPrepCore, hcutoffRest⟩
  have hcoordPrep : cut.output.preparation.coordinator = .live r q base
      (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
        hnoAssignment selected) := by
    exact hcoordPrepCore
  rcases hcutoffRest with ⟨huCore, huT, _, _, _, hfollowersCore⟩
  have huCore' : cut.input.time.val + 1 = s + k + 1 := huCore
  have huT' : cut.input.time.val + 1 ≤ p.T := huT
  have hsuccessorSpan : s + (k + 1) ≤ p.T :=
    Nat.le_trans
      (Nat.add_le_add_left (Nat.succ_le_of_lt hwindowShort) s) hspan
  have hstartSpan : s + 1 ≤ p.T :=
    Nat.le_trans
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) s)
      hsuccessorSpan
  have hstartBeforeT : s < p.T :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hstartSpan
  have hfollowersCoreLocal : ∀ i : Fin (p.m - 1),
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
    exact hfollowersCore i
  have hprepInput : ∀ i, ∃ old μ,
      cut.input.state.followers i = .ordinary old μ ∧
        (old.status = .unoccupied → old.lastDown = none ∧ old.S = 0 ∧
          old.delta = 0 ∧ old.backlog = 0) ∧
        (old.status ≠ .unoccupied → old.lastDown = some (r.payload.downRecord i)) ∧
        localStateDomainValid old ∧ localBufferValid old ∧ downDecoderStateValid old ∧
        old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ old.buffer, saved.calendarRound < s + k + 1) ∧
        startRound rate.eta cut.input.time old μ =
          .ok ({old with status := .unoccupied}, μ) ∧
        (cut.output.preparation.followers.followers i).configuration =
          .ordinary ({old with status := .unoccupied}) μ ∧
        localStateDomainValid ({old with status := .unoccupied}) ∧
        ({old with status := .unoccupied}).S +
          ({old with status := .unoccupied}).backlog ≤ k * D p ∧
        ({old with status := .unoccupied}).buffer.Pairwise
          (fun (a b : SparseCalendarReplay.SparseCalendarRecord p.K) =>
            a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ ({old with status := .unoccupied}).buffer,
          saved.calendarRound < cut.input.time.val + 1) ∧
        ({old with status := .unoccupied}).S = old.S ∧
        ({old with status := .unoccupied}).delta = old.delta ∧
        ({old with status := .unoccupied}).backlog = old.backlog ∧
        ({old with status := .unoccupied}).lastDown = old.lastDown ∧
        ({old with status := .unoccupied}).buffer = old.buffer ∧
        ({old with status := .unoccupied}).downBatch = old.downBatch ∧
        ({old with status := .unoccupied}).initializationFailure = old.initializationFailure := by
    intro i
    rcases hprepFollowers i with
      ⟨old, μ, hstate, hunocc, hocc, hstart, hprepared, hdomain, hmass,
        _, _, _, hpair, hstamps, hSkeep, hdeltaKeep, hbacklogKeep, hlastKeep,
        hbufferKeep, hbatchKeep, hfailureKeep, _, _, _, _⟩
    have hstate' : cut.input.state.followers i = .ordinary old μ := by
      calc
        cut.input.state.followers i = prefixRun.finalState.followers i :=
          congrArg (fun state => state.followers i) hcutPrefix
        _ = .ordinary old μ := hstate
    have hcutPrepTime : cutPrep.input.time = cut.input.time :=
      congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord =>
        record.input.time) hcutPrepEq
    have hcarryi := hcarry i
    rw [hstate'] at hcarryi
    change (old.status ≠ .unoccupied →
      old.lastDown = some (r.payload.downRecord i)) at hcarryi
    have hprepared' :
        (cut.output.preparation.followers.followers i).configuration =
          .ordinary ({old with status := .unoccupied}) μ := by
      calc
        (cut.output.preparation.followers.followers i).configuration =
            (cutPrep.output.preparation.followers.followers i).configuration :=
          congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord =>
            (record.output.preparation.followers.followers i).configuration)
            hcutPrepEq.symm
        _ = .ordinary ({old with status := .unoccupied}) μ := hprepared
    have htimeCore : cut.input.time.val = s + k := by
      exact htimeCoreOriginal
    have htime' : ∀ saved ∈ old.buffer, saved.calendarRound < s + k + 1 := by
      intro saved hsaved
      have hlt := hstamps saved hsaved
      rw [hcutPrepTime] at hlt
      rw [htimeCore] at hlt
      omega
    have hstart' : startRound rate.eta cut.input.time old μ =
        .ok ({old with status := .unoccupied}, μ) := by
      simpa [hcutPrepTime] using hstart
    exact ⟨old, μ, hstate', hunocc, hcarryi, hdomain, hdomain.2.1,
      hdomain.2.2, hpair, htime', hstart', hprepared', hdomain, hmass,
      by simpa using hpair, by simpa [hcutPrepTime] using hstamps, hSkeep, hdeltaKeep,
      hbacklogKeep, hlastKeep, hbufferKeep, hbatchKeep, hfailureKeep⟩
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    s count hspan hactive hfirst hwindowShort
  dsimp only [execution, window, k] at houtside
  rcases houtside with
    ⟨cutOutside, suffixOutside, _, hindexOutside, _, hactualOutside, hstateOutside⟩
  rcases hstateOutside with
    ⟨rOutside, qOutside, baseOutside, hprefixOutside,
      hprefixLiveOutside, hcallOutside⟩
  rcases hcallOutside with
    ⟨_, _, _, _, _, _, _, _, _, _, hbranchOutside⟩
  rcases hbranchOutside with
    ⟨hbranchOutside, _, _, _, _, _, _, hcutoffOutside⟩
  rcases hcutoffOutside with
    ⟨_, _, _, _, _, _, _, _, hfirstCutoffOutside, _⟩
  have hcutOutsideEq : cutOutside = cut := by
    calc
      cutOutside = cutPrep := by
        calc
          cutOutside = execution.records[k]'(by
              have hk : k < count := hwindowShort
              have hlen : execution.records.length = count := by
                simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
                  ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
              omega) := by
                simpa [execution, window, k,
                  ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hindexOutside
          _ = cutPrep := by
            symm
            simpa [execution, window, k,
              ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hindexPrep
      _ = cut := hcutPrepEq
  have hactualCut :
      cut = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
        hsuccessorSpan hactive := by
    calc
      cut = cutOutside := hcutOutsideEq.symm
      _ = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
          hsuccessorSpan hactive := by
            simpa [execution, window, k,
              ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using hactualOutside
  have hcoordOutside : cutOutside.input.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live rOutside qOutside baseOutside := by
    rw [hprefixOutside]
    exact hprefixLiveOutside
  have hsameLive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      rOutside qOutside baseOutside =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base := by
    calc
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          rOutside qOutside baseOutside = cutOutside.input.state.coordinator :=
        hcoordOutside.symm
      _ = prefixRun.finalState.coordinator :=
        congrArg ReferenceActivePhysicalStep.State.coordinator hprefixOutside
      _ = cut.input.state.coordinator :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hcutPrefix).symm
      _ = .live r q base := hcoord
  injection hsameLive with hrOutside hqOutside hbaseOutside
  have hfirstCutoff : FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
        cut.input.time.val + 1 := by
    simpa [hrOutside, hcutOutsideEq] using
      hfirstCutoffOutside
  have hcutoffFacts :
      (∀ i : Fin (p.m - 1),
        ∃ old μ c logged d recordPost post,
          let prepared := cut.output.preparation.followers.followers i
          let own := cut.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let view := cut.output.preparation.coordinator.downView
          cut.input.state.followers i = .ordinary old μ ∧
          (old.status = .unoccupied → old.lastDown = none ∧ old.S = 0 ∧
            old.delta = 0 ∧ old.backlog = 0) ∧
          (old.status ≠ .unoccupied → old.lastDown = some (r.payload.downRecord i)) ∧
          localStateDomainValid old ∧ localBufferValid old ∧ downDecoderStateValid old ∧
          old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ old.buffer, saved.calendarRound < s + k + 1) ∧
          startRound rate.eta cut.input.time old μ =
            .ok ({old with status := .unoccupied}, μ) ∧
          prepared.configuration = .ordinary c μ ∧
          c = {old with status := .unoccupied} ∧
          localStateDomainValid c ∧ localBufferValid c ∧ downDecoderStateValid c ∧
          c.S + c.backlog ≤ k * D p ∧
          c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ c.buffer, saved.calendarRound < cut.input.time.val + 1) ∧
          c.S = old.S ∧ c.delta = old.delta ∧ c.backlog = old.backlog ∧
          c.lastDown = old.lastDown ∧ c.buffer = old.buffer ∧ c.downBatch = old.downBatch ∧
          c.initializationFailure = old.initializationFailure ∧
          ActiveFollowerLogging.checkedLogging i cut.input.row
            (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
          logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
            (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
          d = referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
          (recordFollower view i cut.input.row (cut.input.state.activations i)
            cut.input.time (cut.input.active i) prepared.arm own c).result = .ok recordPost ∧
          (recordFollower view i cut.input.row (cut.input.state.activations i)
            cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
          (recordFollower view i cut.input.row (cut.input.state.activations i)
            cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
            own c μ recordPost = .ok (post, μ) ∧
          (cut.output.followers i).configuration = .ordinary post μ ∧
          cut.output.next.followers i = .ordinary post μ ∧
          (cut.output.followers i).failure = none ∧ post.status = .unoccupied ∧
          localStateDomainValid post ∧ localBufferValid post ∧ downDecoderStateValid post ∧
          post.S + post.backlog ≤ k * D p ∧
          post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
          (cut.output.followers i).downInput = some logged ∧
          (cut.output.followers i).down = some d ∧
          ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
            post.lastDown = some (r.payload.downRecord i))) := by
    intro i
    let prepared := cut.output.preparation.followers.followers i
    let own := cut.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := cut.output.preparation.coordinator.downView
    rcases hprepInput i with
      ⟨old, μ, hstate, hunocc, hfields, hdomainOld, hbufferOld, hdecoderOld,
        hpairOld, htimeOld, hstartOld, hpreparedOld, hdomainC, hmassC,
        hpairC, htimeC, hSkeep, hdeltaKeep, hbacklogKeep, hlastKeep,
        hbufferKeep, hbatchKeep, hfailureKeep⟩
    rcases hfollowersCoreLocal i with
      ⟨cCore, μCore, logged, d, recordPost, hpreparedCore, hlogging, hloggedBuffer,
        hdown, hrecordResult, hrecordInput, hrecordDown, hrelease, hpostConfig,
        hfailure, hstatus, hdomainPost, hmassPost, hpairPost, hstampsPost,
        hdiagInput, hdiagDown⟩
    let post := recordPost
    have hpreparedOld' :
        (cut.output.preparation.followers.followers i).configuration =
          .ordinary ({old with status := .unoccupied}) μ := hpreparedOld
    have hpreparedEq := LocalConfiguration.ordinary.inj (hpreparedOld'.symm.trans hpreparedCore)
    have hcEq : {old with status := .unoccupied} = cCore := hpreparedEq.1
    have hμEq : μ = μCore := hpreparedEq.2
    subst cCore
    subst μCore
    have hcUnoccupied : ({old with status := .unoccupied}).status = .unoccupied := rfl
    have hobserved :
        ((ReferenceActivePhysicalStep.prepare cut.input).observeFollower i).configuration =
          .ordinary recordPost μ := by
      have h := hpostConfig
      rw [cut.output_eq] at h
      simpa [ReferenceActivePhysicalStep.step] using h
    have hnextFollower : cut.output.next.followers i = .ordinary recordPost μ := by
      calc
        cut.output.next.followers i =
            (ReferenceActivePhysicalStep.step cut.input).next.followers i := by
              rw [cut.output_eq]
        _ = ((ReferenceActivePhysicalStep.prepare cut.input).observeFollower i).configuration :=
          (ReferenceActivePhysicalStep.step_next_fields cut.input).2.2.2 i
        _ = .ordinary recordPost μ := hobserved
    have hlogFrame := ActiveFollowerLogging.checkedLogging_success_frame i cut.input.row
      (cut.input.state.activations i) cut.input.time (prepared.arm, own)
      ({old with status := .unoccupied}) logged hlogging
    let choiceView : ReferenceDownReception.ChoiceTimeView p rate.eta :=
      ⟨r.payload, dispatched.startResult.pending,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u,
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights⟩
    have hdownView : cut.output.preparation.coordinator.downView = some choiceView := by
      simpa [choiceView] using (by
        simp [ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, hcoordPrep])
    have hdownExact' : d = referenceDownCut p (some choiceView) i cut.input.row
        cut.input.time own rate logged := by
      rw [← hdownView]
      exact hdown
    have hconsume : consumeDownResult rate
        (referenceDownCut p (some choiceView) i cut.input.row cut.input.time own rate logged).outcome =
          .ok recordPost := by
      have h := hrecordResult
      unfold ReferenceActivePhysicalStep.recordFollower at h
      rw [dite_eq_left hcUnoccupied, hlogging] at h
      simpa [hdownView] using h
    have hdownInv := ReferenceFollowerReplyChronology.referenceDownCut_ordinary_inversion
      (some choiceView) i cut.input.row cut.input.time own logged recordPost hconsume
    have hreleaseFrame := ReferenceFollowerReplyChronology.releaseAndFinish_frame
      i cut.input.row cut.input.time own ({old with status := .unoccupied})
      recordPost post μ μ hrelease
    have hacceptedFields :
        ∀ raw M scan regs lastService,
          (referenceDownCut p (some choiceView) i cut.input.row cut.input.time own rate logged).outcome =
            .accepted logged recordPost raw M scan regs lastService →
          recordPost.lastDown = some (r.payload.downRecord i) := by
      intro raw M scan regs lastService haccepted
      have hfieldsAccepted := ReferenceActiveDataOwnership.referenceDown_accepted_fields
        choiceView i cut.input.row cut.input.time own logged logged recordPost raw M scan regs
        lastService haccepted
      exact hfieldsAccepted.2
    have hreplyLogged : ReferenceFollowerReplyChronology.reply logged =
        ReferenceFollowerReplyChronology.reply old := by
      simp only [ReferenceFollowerReplyChronology.reply, hlogFrame.1,
        hlogFrame.2.1, hlogFrame.2.2.1, hlogFrame.2.2.2.1]
    have hfinalFieldsOfFrame
        (hframe : ReferenceFollowerReplyChronology.reply recordPost =
          ReferenceFollowerReplyChronology.reply logged) :
        ReferenceFollowerReplyChronology.reply post =
          ReferenceFollowerReplyChronology.reply old := by
      exact hreleaseFrame.1.trans (hframe.trans hreplyLogged)
    have hfinalAlt :
        (post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
          post.lastDown = some (r.payload.downRecord i) := by
      rcases hdownInv with hframe | ⟨raw, M, scan, regs, lastService, haccepted, _, _⟩
      · by_cases hu : old.status = .unoccupied
        · rcases hunocc hu with ⟨hnoneOld, hSOld, hdeltaOld, hbacklogOld⟩
          have hreply := hfinalFieldsOfFrame hframe.1
          have hlast : post.lastDown = none := by
            have := congrArg Prod.fst hreply
            simpa [ReferenceFollowerReplyChronology.reply, hnoneOld] using this
          have hSfinal : post.S = 0 := by
            have := congrArg (fun x => x.2.1) hreply
            simpa [ReferenceFollowerReplyChronology.reply, hSOld] using this
          have hdeltaFinal : post.delta = 0 := by
            have := congrArg (fun x => x.2.2.1) hreply
            simpa [ReferenceFollowerReplyChronology.reply, hdeltaOld] using this
          have hbacklogFinal : post.backlog = 0 := by
            have := congrArg (fun x => x.2.2.2) hreply
            simpa [ReferenceFollowerReplyChronology.reply, hbacklogOld] using this
          exact Or.inl ⟨hlast, hSfinal, hdeltaFinal, hbacklogFinal⟩
        · have hlastOld := hfields hu
          have hreply := hfinalFieldsOfFrame hframe.1
          have hlast : post.lastDown = some (r.payload.downRecord i) := by
            have := congrArg Prod.fst hreply
            simpa [ReferenceFollowerReplyChronology.reply, hlastOld] using this
          exact Or.inr hlast
      · have haccepted := hacceptedFields raw M scan regs lastService haccepted
        have hlast : post.lastDown = some (r.payload.downRecord i) := by
          calc
            post.lastDown = recordPost.lastDown := congrArg Prod.fst hreleaseFrame.1
            _ = some (r.payload.downRecord i) := haccepted
        exact Or.inr hlast
    have hfinalBundle :
        (post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
          post.lastDown = some (r.payload.downRecord i) := hfinalAlt
    exact ⟨old, μ, {old with status := .unoccupied}, logged, d, recordPost, post,
      hstate, hunocc, hfields, hdomainOld, hbufferOld, hdecoderOld, hpairOld,
      htimeOld, hstartOld, hpreparedOld', rfl, hdomainC, hdomainC.2.1,
      hdomainC.2.2, hmassC, hpairC, htimeC, hSkeep, hdeltaKeep, hbacklogKeep,
      hlastKeep, hbufferKeep, hbatchKeep, hfailureKeep, hlogging, hloggedBuffer,
      hdown, hrecordResult, hrecordInput, hrecordDown, hrelease, hpostConfig,
      hnextFollower, hfailure, hstatus, hdomainPost, hdomainPost.2.1,
      hdomainPost.2.2, hmassPost,
      hpairPost, hstampsPost, hdiagInput, hdiagDown, hfinalBundle⟩
  have htimeCut : cut.input.time.val = s + k := htimeCoreOriginal
  let u := cut.input.time.val + 1
  have hnext : (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1)
      hsuccessorSpan hactive).finalState = cut.output.next := by
    have hsucc := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
      initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
      hsuccessorSpan hactive
    calc
      (ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1)
        hsuccessorSpan hactive).finalState =
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
            hsuccessorSpan hactive).output.next := hsucc
      _ = cut.output.next := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord => record.output.next)
        hactualCut.symm
  refine ⟨r, q, base, ?_, hsigma, hqzero, ?_⟩
  · exact hcoord
  · refine ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock,
      hpending, hnoAssignment, selected, hcoordPrep, ?_⟩
    refine ⟨?_, ?_, hfirstCutoff, hcutoffFacts, ?_, ?_⟩
    · exact huCore'
    · exact huT'
    · exact hstartBeforeT
    · simpa [hsuccessorSpan] using hnext

end Bandits.Support.ReferenceGeneratedFirstCutoffFollowerSeed

end
