/-
Copyright (c) 2026 Bandits Lean formalization contributors. All rights reserved.
-/
module

public import Bandits.Support.ReferenceRunClockPreservation
public import Bandits.Support.ReferenceFollowerOccupiedRecorderEvent
public import Bandits.Support.ReferenceFollowerSparseEmissionRecovery
public import Bandits.Support.ReferenceAssignmentPayloadChronology
public import Bandits.Support.ReferenceFirstLiveConfirmationHistory

/-!
# First actual assignment follower queue budgets

The source queue update and its first overflow check are specified in
`sources/zip4/manuscript/04_slow_fast_learner.tex:143-175` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-60`. Sparse logging,
actual DOWN reception, and replay follow
`sources/zip4/manuscript/06_interruptions.tex:192-209,246-275,295`; the saved
contribution is the literal floor in
`sources/zip4/manuscript/05_binary_transport.tex:426-431`.

This module works on the original actual launched initialization and the
canonical physical run. Initial follower registers and replay buffers remain
the converted boundary values. It does not assert later assignment-seed mass,
global queue truth, or any manuscript regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.QueueReplay

namespace Bandits.Support.ReferenceFirstFollowerMassBudget

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord {p : Parameters} {rate : RateInput p} :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

private theorem replay_mass_after_arrivals (capacity D : ℕ)
    (initial : ℕ × ℕ) (arrivals : List ℕ)
    (harrivals : ∀ a ∈ arrivals, a ≤ D) :
    (QueueReplay.replay capacity initial (arrivals.map fun a => (true, a))).1 +
        (QueueReplay.replay capacity initial (arrivals.map fun a => (true, a))).2 ≤
      initial.1 + initial.2 + arrivals.length * D := by
  induction arrivals generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons a rest ih =>
      have ha := harrivals a List.mem_cons_self
      have htail : ∀ x ∈ rest, x ≤ D := by
        intro x hx
        exact harrivals x (List.mem_cons_of_mem _ hx)
      have hstep :
          (QueueReplay.transition capacity initial (true, a)).1 +
              (QueueReplay.transition capacity initial (true, a)).2 =
            initial.1 + initial.2 + a := by
        simp [QueueReplay.transition]
        omega
      change
        (QueueReplay.replay capacity initial ((true, a) ::
          rest.map fun x => (true, x))).1 +
            (QueueReplay.replay capacity initial ((true, a) ::
              rest.map fun x => (true, x))).2 ≤
          initial.1 + initial.2 + (rest.length + 1) * D
      rw [QueueReplay.replay, List.foldl_cons]
      have hnext := ih (QueueReplay.transition capacity initial (true, a)) htail
      calc
        _ ≤ (QueueReplay.transition capacity initial (true, a)).1 +
              (QueueReplay.transition capacity initial (true, a)).2 + rest.length * D := by
          simpa only [QueueReplay.replay] using hnext
        _ = initial.1 + initial.2 + a + rest.length * D := by rw [hstep]
        _ ≤ initial.1 + initial.2 + (rest.length + 1) * D := by
          have hadd : (rest.length + 1) * D = rest.length * D + D := by
            rw [Nat.add_mul, one_mul]
          rw [hadd]
          omega

private theorem replay_zero_mass_after_arrivals (capacity D : ℕ)
    (arrivals : List ℕ) (harrivals : ∀ a ∈ arrivals, a ≤ D) :
    (QueueReplay.replay capacity (0, 0) (arrivals.map fun a => (true, a))).1 +
        (QueueReplay.replay capacity (0, 0) (arrivals.map fun a => (true, a))).2 ≤
      arrivals.length * D := by
  have h := replay_mass_after_arrivals capacity D (0, 0) arrivals harrivals
  simpa using h

private theorem checkedCalendarReplay_success_of_mass
    (D T capacity offset elapsed : ℕ)
    (current : ActiveFollowerDownAcceptance.ReplayRegisters)
    (arrivalAt : ℕ → ℕ) (rounds : List ℕ)
    (hscore : current.registers.1 ≤ elapsed * D)
    (hbacklog : current.registers.2 ≤ elapsed * D)
    (hlast : current.lastService ≤ D)
    (hmass : current.registers.1 + current.registers.2 ≤ elapsed * D)
    (hcapacity : capacity ≤ D)
    (harrival : ∀ r ∈ rounds, arrivalAt r ≤ D)
    (hspan : elapsed + rounds.length ≤ T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedCalendarReplay D (T * D) capacity offset
        current arrivalAt rounds = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (elapsed + rounds.length) * D ∧
      final.lastService ≤ D := by
  induction rounds generalizing current offset elapsed with
  | nil =>
      have htime : elapsed ≤ T := by omega
      have hqueue : current.registers.1 ≤ T * D := by
        exact hscore.trans (Nat.mul_le_mul_right D htime)
      have hbacklog' : current.registers.2 ≤ T * D := by
        exact hbacklog.trans (Nat.mul_le_mul_right D htime)
      have hdomain : ActiveFollowerDownAcceptance.replay_register_domain D (T * D) current :=
        ⟨hqueue, hlast, hbacklog'⟩
      refine ⟨current, ?_, ?_, hlast⟩
      · simp [ActiveFollowerDownAcceptance.checkedCalendarReplay, hdomain]
      · simpa using hmass
  | cons r rest ih =>
      have ha := harrival r List.mem_cons_self
      have htail : ∀ u ∈ rest, arrivalAt u ≤ D := by
        intro u hu
        exact harrival u (List.mem_cons_of_mem _ hu)
      let service := ActiveFollowerDownAcceptance.replayService capacity current (true, arrivalAt r)
      let next := QueueReplay.transition capacity current.registers (true, arrivalAt r)
      have hservice : service ≤ D := by
        dsimp [service, ActiveFollowerDownAcceptance.replayService]
        exact (Nat.min_le_left _ _).trans hcapacity
      have hmin : min capacity (current.registers.2 + arrivalAt r) ≤
          current.registers.2 + arrivalAt r := Nat.min_le_right _ _
      have hnextMass : next.1 + next.2 ≤ (elapsed + 1) * D := by
        have hconserve : next.1 + next.2 = current.registers.1 +
            current.registers.2 + arrivalAt r := by
          dsimp [next, QueueReplay.transition]
          omega
        have hmul : (elapsed + 1) * D = elapsed * D + D := by
          rw [Nat.add_mul, one_mul]
        rw [hconserve, hmul]
        omega
      have hnextScore : next.1 ≤ (elapsed + 1) * D :=
        (Nat.le_add_right _ _).trans hnextMass
      have hnextBacklog : next.2 ≤ (elapsed + 1) * D :=
        (Nat.le_add_left _ _).trans hnextMass
      have htime : elapsed + 1 ≤ T := by
        have : elapsed + (r :: rest).length ≤ T := hspan
        simp only [List.length_cons] at this
        omega
      have hnextBound : (elapsed + 1) * D ≤ T * D :=
        Nat.mul_le_mul_right D htime
      have hdomain : ActiveFollowerDownAcceptance.replay_register_domain D (T * D) current := by
        refine ⟨?_, hlast, ?_⟩
        · exact hscore.trans (Nat.mul_le_mul_right D (by omega))
        · exact hbacklog.trans (Nat.mul_le_mul_right D (by omega))
      have hscoreCheck : next.1 ≤ T * D := hnextScore.trans hnextBound
      have hbacklogCheck : next.2 ≤ T * D := hnextBacklog.trans hnextBound
      have hscoreGuard : current.registers.1 +
          min capacity (current.registers.2 + arrivalAt r) ≤ T * D := by
        simpa [next, QueueReplay.transition] using hscoreCheck
      have hqueuePlusArrival : current.registers.2 + arrivalAt r ≤ (elapsed + 1) * D := by
        have hmul : (elapsed + 1) * D = elapsed * D + D := by
          rw [Nat.add_mul, one_mul]
        rw [hmul]
        omega
      have hbacklogGuard : current.registers.2 + arrivalAt r ≤
          T * D + min capacity (current.registers.2 + arrivalAt r) := by
        exact (hqueuePlusArrival.trans hnextBound).trans (Nat.le_add_right _ _)
      have hupdate : ActiveFollowerDownAcceptance.checkedReplayUpdate D (T * D) capacity
          current (true, arrivalAt r) = .ok ⟨next, service⟩ := by
        simp [ActiveFollowerDownAcceptance.checkedReplayUpdate,
          ActiveFollowerDownAcceptance.replayService, next, service,
          QueueReplay.transition, ha, hcapacity, hscoreGuard, hbacklogGuard]
      have htailspan : elapsed + 1 + rest.length ≤ T := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hspan
      obtain ⟨final, hfinal, hfinalMass, hfinalLast⟩ := ih
        (offset + 1) (elapsed + 1) ⟨next, service⟩
        hnextScore hnextBacklog hservice hnextMass htail htailspan
      refine ⟨final, ?_, ?_, hfinalLast⟩
      · simpa [ActiveFollowerDownAcceptance.checkedCalendarReplay, hdomain, hupdate] using hfinal
      · calc
          final.registers.1 + final.registers.2 ≤ (elapsed + 1 + rest.length) * D :=
            hfinalMass
          _ = (elapsed + (rest.length + 1)) * D := by
            congr 1
            omega

private theorem sparseBufferContribution_zero_of_no_key
    (d : ℕ) (D : ℝ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead : ¬ (saved.calendarRound = r ∧ saved.pilot = arm) :=
        hno saved List.mem_cons_self
      have htail : ∀ item ∈ rest,
          ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
        intro item hi
        exact hno item (List.mem_cons_of_mem _ hi)
      change (if saved.calendarRound = r ∧ saved.pilot = arm then
          savedContribution p.K d D eta h saved.observation saved.thinScalar else 0) +
        sparseBufferContribution d D eta h arm r rest = 0
      rw [ite_eq_right hhead, zero_add]
      exact ih htail

private theorem sparseBufferContribution_le_of_unique_key
    (d D : ℕ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hkeys : (buffer.map fun saved => (saved.calendarRound, saved.pilot)).Nodup)
    (hcontribution : ∀ saved ∈ buffer,
      saved.calendarRound = r → saved.pilot = arm →
        savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar ≤ D) :
    sparseBufferContribution d (D : ℝ) eta h arm r buffer ≤ D := by
  classical
  induction buffer with
  | nil => simp [sparseBufferContribution]
  | cons saved rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      have htail : ∀ item ∈ rest,
          item.calendarRound = r → item.pilot = arm →
            savedContribution p.K d (D : ℝ) eta h item.observation item.thinScalar ≤ D := by
        intro item hitem hround hpilot
        exact hcontribution item (List.mem_cons_of_mem _ hitem) hround hpilot
      by_cases hkey : saved.calendarRound = r ∧ saved.pilot = arm
      · have hnotTail : ∀ item ∈ rest,
            ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
          intro item hitem hitemKey
          apply hkeys.1
          apply List.mem_map.mpr
          exact ⟨item, hitem,
            Prod.ext (hitemKey.1.trans hkey.1.symm) (hitemKey.2.trans hkey.2.symm)⟩
        have hone := sparseBufferContribution_zero_of_no_key d (D : ℝ) eta h arm r rest hnotTail
        change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_left hkey, hone]
        exact hcontribution saved List.mem_cons_self hkey.1 hkey.2
      · change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_right hkey, zero_add]
        exact ih hkeys.2 htail

private theorem bufferArrival_le_D
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (r : ℕ) :
    ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r ≤ D p := by
  change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r logged.buffer ≤ D p
  apply sparseBufferContribution_le_of_unique_key
    (d := p.m - 1) (D := D p) (eta := rate.eta.val) (h := M.val.h)
    (arm := PrelaunchBufferRecovery.downArm rate.eta M) (r := r)
    (buffer := logged.buffer)
    (ActiveFollowerLifecycle.localBufferValid_keys_nodup hvalid)
  intro saved hsaved hround harm
  by_cases hthin : saved.thinScalar.1 ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  · rw [SparseCalendarReplay.savedContribution_eq_floor_of_le
      p.K (p.m - 1) (D p : ℝ) rate.eta.val M.val.h saved.observation
      saved.thinScalar hthin]
    obtain ⟨own, hown⟩ := ActiveFollowerLifecycle.localBufferValid_observation_typed
      hvalid saved hsaved
    have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta M own
    have hsame := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor rate.eta M own
    rw [hown] at hsame
    rw [hsame] at hfloor
    exact hfloor
  · simp [SparseCalendarReplay.savedContribution, hthin]

private theorem checkedRecovery_budget_of_zero_queue_and_valid_buffer
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hell : M.val.q = 0)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (ell : ℕ) (hlen : ell - M.val.sigma ≤ p.T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (ell - M.val.sigma) * D p ∧
      ∀ j, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).take j) =
            .ok middle ∧
        middle.registers.1 + middle.registers.2 ≤ j * D p := by
  let arrivals := ActiveFollowerDownAcceptance.recoveryArrivals p rate M logged ell
  have harrivals : ∀ a ∈ arrivals, a ≤ D p := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact bufferArrival_le_D M logged hvalid r
  have hlength := ActiveFollowerDownAcceptance.recoveryRounds_length p rate M ell
  have hrounds : (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length ≤ p.T := by
    rw [ActiveFollowerDownAcceptance.recoveryRounds_length]
    exact hlen
  have hcapacity := ActiveFollowerDownAcceptance.four_n_le_D p rate
  let current : ActiveFollowerDownAcceptance.ReplayRegisters := ⟨(0, 0), 0⟩
  obtain ⟨final, hchecked, hmass, _⟩ := checkedCalendarReplay_success_of_mass
    (D p) p.T (4 * rate.n) 0 0 current
    (ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged)
    (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell)
    (by simp [current]) (by simp [current]) (by simp [current]) (by simp [current])
    hcapacity
    (by
      intro r hr
      exact bufferArrival_le_D M logged hvalid r)
    (by simpa only [Nat.zero_add] using hrounds)
  have hfinal : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final := by
    rw [ActiveFollowerDownAcceptance.checkedRecovery, hell]
    exact hchecked
  have hmass' : final.registers.1 + final.registers.2 ≤
      (ell - M.val.sigma) * D p := by
    simpa only [ActiveFollowerDownAcceptance.recoveryArrivals,
      ActiveFollowerDownAcceptance.recoveryRounds, List.length_map,
      SparseCalendarReplay.sparseCalendarRounds_length, Nat.zero_add] using hmass
  refine ⟨final, hfinal, hmass', ?_⟩
  intro j
  obtain ⟨middle, hprefix, _, hregisters⟩ :=
    ActiveFollowerDownAcceptance.checkedRecovery_success_prefix p rate M logged ell final hfinal j
  have hregisters' : middle.registers =
      QueueReplay.replay (4 * rate.n) (0, 0)
        ((arrivals.take j).map fun a => (true, a)) := by
    simpa [ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals, List.map_take, hell,
      arrivals] using hregisters
  have hprefixMass := replay_mass_after_arrivals (4 * rate.n) (D p) (0, 0)
    (arrivals.take j) (by
      intro a ha
      exact harrivals a (List.mem_of_mem_take ha))
  have htake : (arrivals.take j).length ≤ j := List.length_take_le _ _
  have hprefixMass' :
      (QueueReplay.replay (4 * rate.n) (0, 0)
        ((arrivals.take j).map fun a => (true, a))).1 +
        (QueueReplay.replay (4 * rate.n) (0, 0)
          ((arrivals.take j).map fun a => (true, a))).2 ≤
        (arrivals.take j).length * D p := by
    simpa using hprefixMass
  have hbound : middle.registers.1 + middle.registers.2 ≤ j * D p := by
    rw [hregisters']
    exact hprefixMass'.trans (Nat.mul_le_mul_right _ htake)
  refine ⟨middle, ?_, hbound⟩
  simpa [ActiveFollowerDownAcceptance.checkedRecovery,
    ActiveFollowerDownAcceptance.recoveryQueueRecords, hell] using hprefix

private theorem occupied_outputDomain_of_prefix_mass
    (steps : ℕ) (hsteps : steps + 1 ≤ p.T)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : DownRecord (p := p) (rate := rate))
    (observation : ReferencePrelaunchFollower.Observation p)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (hmass : s.S + s.backlog ≤ steps * D p) :
    ActiveFollowerQueueOperation.outputDomain rate.n s
      (ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation)
      (ActiveFollowerQueueOperation.localService rate.n s.backlog
        (ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation)) := by
  let arrival := ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation
  let service := ActiveFollowerQueueOperation.localService rate.n s.backlog arrival
  have harrival := ActiveFollowerQueueOperation.rawArrival_le_D rate.eta i row t M observation
  have hservice := ActiveFollowerQueueOperation.localService_le_D rate.eta rate.sourceCap
    rate.n rate.n_scale s.backlog arrival
  have hresidual := CappedService.residual_add_service
    (ActiveFollowerQueueOperation.serviceCapacity rate.n) s.backlog arrival
  have hresidual' :
      CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
          s.backlog arrival + service = s.backlog + arrival := by
    dsimp [service, ActiveFollowerQueueOperation.localService]
    exact hresidual
  have hconservation : s.S + service +
      CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
        s.backlog arrival = s.S + s.backlog + arrival := by
    calc
      _ = s.S + (CappedService.residual
          (ActiveFollowerQueueOperation.serviceCapacity rate.n) s.backlog arrival + service) := by
        omega
      _ = s.S + (s.backlog + arrival) := by rw [hresidual']
      _ = s.S + s.backlog + arrival := by omega
  have hprefix : s.S + s.backlog + arrival ≤ (steps + 1) * D p := by
    have hmul : (steps + 1) * D p = steps * D p + D p := by
      rw [Nat.add_mul, one_mul]
    rw [hmul]
    omega
  have htotal : s.S + service +
      CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
        s.backlog arrival ≤ p.T * D p := by
    calc
      _ = s.S + s.backlog + arrival := hconservation
      _ ≤ (steps + 1) * D p := hprefix
      _ ≤ p.T * D p := Nat.mul_le_mul_right _ hsteps
  have hscore : s.S + service ≤ p.T * D p := by omega
  have hbacklog : CappedService.residual
      (ActiveFollowerQueueOperation.serviceCapacity rate.n) s.backlog arrival ≤ p.T * D p := by
    omega
  exact ⟨harrival, hservice, hscore, hbacklog⟩

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

/-- The actual launch conversion supplies zero follower registers and its
real replay buffer, including buffer validity and strict chronology. -/
theorem actual_launched_follower_seed (i : Fin (p.m - 1)) :
    ∃ seed memory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h b h
        actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary seed memory ∧
      seed.S = 0 ∧ seed.delta = 0 ∧ seed.backlog = 0 ∧
      seed.status = .unoccupied ∧ seed.lastDown = none ∧
      ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ seed.buffer,
        saved.calendarRound ≤ BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h) := by
  obtain ⟨state, memory, hstate, hlast, _haccepted, hS, hdelta, hbacklog, hstatus, _⟩ :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_registers
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
  obtain ⟨seed, seedMemory, hseed, hvalid, hpair, htime⟩ :=
    ReferenceFollowerBufferProvenance.actualLaunchedBoundary_follower_buffer_seed
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
  rw [hstate] at hseed
  cases hseed
  refine ⟨state, memory, hstate, ?_, ?_, ?_, ?_, ?_, hvalid, hpair, htime⟩
  · exact hS
  · exact hdelta
  · exact hbacklog
  · exact hstatus
  · exact hlast

end ActualLaunch

end Bandits.Support.ReferenceFirstFollowerMassBudget

end
