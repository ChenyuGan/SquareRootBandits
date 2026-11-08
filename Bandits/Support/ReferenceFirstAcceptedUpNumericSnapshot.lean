/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAcceptedUpFollowerHistory
public import Bandits.Support.ReferenceFirstDownRecoveryBudget
public import Bandits.Support.ReferenceOccupiedFieldHistory

/-!
# First accepted UP sender-local numeric replay

Mathematical sources: `appendix_a_local_protocol.tex:54-60`,
`06_interruptions.tex:116-120,192-233,257-275,301-324,327-344`,
`05_binary_transport.tex:426-431`, and `04_slow_fast_learner.tex:157-165`.

This module records the literal reply-side queue projection and establishes
the selected-view interval from actual payload births in the original
physical run. It does not identify the local projection with a source marker
queue or assert a regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstAcceptedUpNumericSnapshot

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev Record {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord {p : Parameters} {rate : RateInput p} :=
  OrdinaryMessageCodec.DownRecord
    (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

/-- The literal enabled queue records for a first assignment's reply window.
Before and on the accepted DOWN record, arrivals are the actual saved
emissions; later arrivals are the actual own-row local recorder values. -/
def firstReplyQueueRecords
    (records : List (Record (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (j : ℕ) (message : DownRecord (p := p) (rate := rate))
    (m : ℕ) : List (Bool × ℕ) :=
  ((records.take m).zipIdx).map fun (record, n) =>
    (true, if n ≤ j then
      ReferenceFollowerSparseEmissionRecovery.emissionContribution message i record
    else
      ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row
        record.input.time message
        (record.output.ownEntries
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2)

/-- An actual accepted UP with first-assignment sigma has the exact retained
earlier DOWN and the current ordinary, unoccupied sender returned by the
existing connected-history inversion. This is branch selection only; it does
not identify the sender's numbers with a global queue. -/
theorem acceptedUp_first_assignment_prior_down
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory)
    (hnone : seed.lastDown = none)
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start count hspan hmode).records.length)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start count hspan hmode).records[k.val].input) i message)
    (hfirstSigma : message.val.sigma = start + 1) :
    ∃ j : Fin (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start count hspan hmode).records.length,
      j.val < k.val ∧ ∃ prior : DownRecord (p := p) (rate := rate),
        ReferenceAcceptedUpFollowerHistory.RetainedDown
          (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
            start count hspan hmode).records[j.val] i prior ∧
        prior.val.sigma = start + 1 ∧
        ∃ sender state senderMemory,
          sender = ReferenceFollowerFixedReply.actualChoice
            (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
              start count hspan hmode).records[k.val] i ∧
          sender.configuration = .ordinary state senderMemory ∧
          state.status = .unoccupied ∧ state.lastDown = some prior ∧
          message.val.S = state.S ∧ message.val.delta = state.delta ∧
          message.val.q = state.backlog := by
  obtain ⟨j, hjk, prior, hretained, _happlied, hpriorSigma, sender, state,
      senderMemory, hsender, hconfiguration, hunoccupied, _hoff, _hstart,
      hstarted, hscore, hdelta, hbacklog, hlastDown, _hstateSigma, _hpositive⟩ :=
    ReferenceAcceptedUpFollowerHistory.run_acceptedUp_prior_down
      initial rows selectedRow rewards start count hspan hmode i seed memory hseed hnone
      k message haccepted
  refine ⟨j, hjk, prior, hretained, hpriorSigma.trans hfirstSigma,
    sender, state, senderMemory, hsender, hconfiguration, hunoccupied, hlastDown,
    hscore, hdelta, hbacklog⟩

/-- Every selected view in a genuine run has a payload born no earlier than
the run's first physical coordinate. The birth theorem and contiguous calendar
are applied to the exact same run; later replacements are included. -/
theorem run_selectedViewInterval
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selectedRow : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ReferenceFollowerSparseEmissionRecovery.selectedViewInterval start
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start count
        hspan hmode).records := by
  intro record hrecord view hview
  have hselected : ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view = view := by
    cases hselection : record.output.preparation.coordinator.selection with
    | none =>
        simp only [ReferenceActivePhysicalStep.DispatchCut.downView,
          hselection, Option.map_none] at hview
        cases hview
    | some selected =>
        have hview' : some selected.view = some view := by
          simpa only [ReferenceActivePhysicalStep.DispatchCut.downView,
            hselection, Option.map_some] using hview
        exact ⟨selected, rfl, Option.some.inj hview'⟩
  obtain ⟨chosen, hselection, hviewEq⟩ := hselected
  subst view
  obtain ⟨birth, hbirth, hbirthPayload, hbirthTime, _⟩ :=
    ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
      initial rows selectedRow rewards start count hspan hmode hfirst record chosen
      hrecord hselection
  have hbirthMemTime : birth.input.time.val ∈
      (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards start count
        hspan hmode).records.map (fun record => record.input.time.val) :=
    List.mem_map.mpr ⟨birth, hbirth, rfl⟩
  rw [ReferenceActivePhysicalHorizon.run_time_values initial rows selectedRow rewards
    start count hspan hmode] at hbirthMemTime
  have hcalendar : birth.input.time.val ∈
      ReferenceActivePhysicalHorizon.calendar start count := by
    simpa only [ReferenceActivePhysicalHorizon.calendar] using hbirthMemTime
  have htimeLower :=
    (ReferenceActivePhysicalHorizon.calendar_bounds hspan hcalendar).1
  calc
    start ≤ birth.input.time.val := htimeLower
    _ = chosen.view.payload.sigma.val := hbirthTime

end Bandits.Support.ReferenceFirstAcceptedUpNumericSnapshot

namespace Bandits.Support.ReferenceFirstAcceptedUpNumericSnapshot

variable {p : Parameters} {rate : RateInput p}

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
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
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

/-- The real original-source launch producer supplies the local initial
invariants needed by the accepted-UP replay. All initialization, private-row,
reward, carry, and launch inputs remain explicit. -/
theorem actual_launched_follower_local_invariants (i : Fin (p.m - 1)) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    initial.coordinator = .first ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart initial
        (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) ∧
    ∃ seed memory,
      initial.followers i = .ordinary seed memory ∧
      seed.S = 0 ∧ seed.delta = 0 ∧ seed.backlog = 0 ∧
      seed.lastDown = none ∧ seed.status = .unoccupied ∧
      ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ seed.buffer,
        saved.calendarRound ≤ BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h) := by
  dsimp only
  have hcoordinator := ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) := by
    intro player
    have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched player
    omega
  obtain ⟨seed, memory, hseed, hS, hdelta, hbacklog, hunoccupied, hnone,
      hvalid, hpair, htime⟩ :=
    ReferenceFirstFollowerMassBudget.actual_launched_follower_seed
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
  exact ⟨hcoordinator, hactive, seed, memory, hseed, hS, hdelta, hbacklog,
    hnone, hunoccupied, hvalid, hpair, htime⟩

end ActualLaunch

end Bandits.Support.ReferenceFirstAcceptedUpNumericSnapshot

end
