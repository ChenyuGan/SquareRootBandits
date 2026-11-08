/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Clock domains along the computed reference coordinator execution

The source clock uses clipped grid boundaries and reads only the correctly
stamped previous proposal in a live assignment. During collection it does not
read saved proposal memory. These clock-domain facts follow the literal
`StartRound` and `FinishRound` operations in
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-247,277-294`;
the total local protocol and its absorbing error branch are specified in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,30-44,81-84`.

This module records only clock-register validity, phase timestamps, and the
proposal stamp. It makes no score, queue, decoder, sampler, success, or
probability claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceCoordinatorClockDomains

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State

variable {p : Parameters} {rate : RateInput p}

/-- The literal clock-domain and fresh-stamp invariant for the actual
coordinator state at the boundary after `k` calendar rounds. Collection keeps
the source cutoff and clipped freeze boundary, but its saved bit is deliberately
unconstrained because `StartRound` does not read it in that phase. -/
def clockAt (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (k : ℕ) (state : State p rate) : Prop :=
  match state.coordinator with
  | .first => True
  | .dagger => True
  | .live r _ _ =>
      r.time.val + 1 = k ∧
      CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock ∧
      r.priorClock.sigma = some r.payload.sigma ∧
      r.priorClock.u = none ∧
      r.gridBoundary = r.priorClock.g ∧
      r.payload.sigma.val < k ∧
      k < r.gridBoundary ∧
      r.priorClock.lastProposal = some (r.time,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected) r.time)
  | .collection payload ledger _ =>
      ledger.sigma = payload.sigma.val + 1 ∧
      payload.sigma.val + 1 < ledger.cutoff ∧
      1 ≤ ledger.cutoff ∧
      ledger.cutoff ≤ p.T ∧
      ledger.cutoff ≤ k ∧
      ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      ledger.cutoff ≤ ledger.freezeAt ∧
      ledger.freezeAt ≤ p.T + 1

/-- Every source-capped rate lies in the phase clock's proposal-parameter
domain. This uses the original source cap from `RateInput`; it does not replace
or weaken that rate input. -/
theorem proposalParameterValid_of_rate (rate : RateInput p) :
    CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_of_lt p.two_le_m)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    have htwo : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
    exact_mod_cast (Nat.le_trans (by decide) htwo)
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hdenCap := (le_div_iff₀ hden).mp rate.sourceCap
  have hsmall : 4 * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      4 * (p.m : ℝ) ≤ 1024 * (p.m : ℝ) := by nlinarith
      _ = (1024 * (p.m : ℝ)) * 1 := by ring
      _ ≤ (1024 * (p.m : ℝ)) * (p.K : ℝ) := by
        exact mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (1024 * (p.m : ℝ) * (p.K : ℝ)) * 1 := by ring
      _ ≤ (1024 * (p.m : ℝ) * (p.K : ℝ)) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by
        exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hhazard : 4 * (p.m : ℝ) * rate.eta.val ≤ 1 := by
    calc
      4 * (p.m : ℝ) * rate.eta.val ≤
          (1024 * (p.m : ℝ) * (p.K : ℝ) *
            (CanonicalRecordingRates.L_stab p : ℝ)) * rate.eta.val :=
        mul_le_mul_of_nonneg_right hsmall (le_of_lt rate.eta.property)
      _ = rate.eta.val * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by ring
      _ ≤ 1 := hdenCap
  refine ⟨rate.eta.property, ?_, ?_⟩
  · unfold FollowerCutoffScan.proposalHazard
    have hmpos : 0 < (p.m : ℝ) := by exact_mod_cast ConstructorDimensions.m_pos p
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hmpos)
      rate.eta.property
  · simpa only [FollowerCutoffScan.proposalHazard] using hhazard

private theorem live_detectCutoff_success
    (clock : CoordinatorPhaseClock.ClockRegisters p) (sigma stamp : Fin p.T)
    (bit : Bool) (t : Fin p.T)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hproposal : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 = t.val) :
    ∃ decision, CoordinatorPhaseClock.detectCutoff clock t = .ok decision := by
  classical
  by_cases hgrid : FollowerCutoffScan.calendarRound t = clock.g
  · rcases clock with ⟨s, v, g, token⟩
    change s = some sigma at hsigma
    change v = none at hu
    subst s
    subst v
    change FollowerCutoffScan.calendarRound t = g at hgrid
    refine ⟨.cutoff sigma rfl, ?_⟩
    simp [CoordinatorPhaseClock.detectCutoff, hgrid]
  · rcases clock with ⟨s, v, g, token⟩
    change s = some sigma at hsigma
    change v = none at hu
    subst s
    subst v
    change token = some (stamp, bit) at hproposal
    subst token
    change FollowerCutoffScan.calendarRound t ≠ g at hgrid
    have hread := CoordinatorPhaseClock.savedPriorProposal_correct
      (⟨some sigma, none, g, some (stamp, bit)⟩ :
        CoordinatorPhaseClock.ClockRegisters p) t stamp bit (by rfl) hstamp
    change ∃ decision,
      CoordinatorPhaseClock.detectCutoff
        (⟨some sigma, none, g, some (stamp, bit)⟩ :
          CoordinatorPhaseClock.ClockRegisters p) t = .ok decision
    by_cases hbit : bit = true
    · have hreadTrue : CoordinatorPhaseClock.savedPriorProposal
          (⟨some sigma, none, g, some (stamp, bit)⟩ :
            CoordinatorPhaseClock.ClockRegisters p) t = .ok true := by
        simpa [hbit] using hread
      have hreadTrue' : CoordinatorPhaseClock.savedPriorProposal
          (⟨some sigma, none, g, some (stamp, true)⟩ :
            CoordinatorPhaseClock.ClockRegisters p) t = .ok true := by
        simpa [hbit] using hreadTrue
      refine ⟨.cutoff sigma rfl, ?_⟩
      simp [CoordinatorPhaseClock.detectCutoff, hgrid,
        hreadTrue', hbit, Bind.bind, Except.bind]
    · have hbitFalse : bit = false := by cases bit <;> simp_all
      have hreadFalse : CoordinatorPhaseClock.savedPriorProposal
          (⟨some sigma, none, g, some (stamp, bit)⟩ :
            CoordinatorPhaseClock.ClockRegisters p) t = .ok false := by
        simpa [hbitFalse] using hread
      have hreadFalse' : CoordinatorPhaseClock.savedPriorProposal
          (⟨some sigma, none, g, some (stamp, false)⟩ :
            CoordinatorPhaseClock.ClockRegisters p) t = .ok false := by
        simpa [hbitFalse] using hreadFalse
      refine ⟨.noCutoff, ?_⟩
      simp [CoordinatorPhaseClock.detectCutoff, hgrid,
        hreadFalse', hbitFalse, Bind.bind, Except.bind]

/-- A live state satisfying `clockAt` makes the exact clock call performed by
`dispatchLive` succeed at its actual input time. In particular the checked
previous proposal has stamp `t.val - 1`, and a non-grid continuation has not
passed the old boundary. -/
theorem live_startRound_success
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (k : ℕ) (state : State p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : state.coordinator = .live r q base)
    (hclock : clockAt rows selected k state)
    (t : Fin p.T) (ht : t.val = k) :
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val t
      r.priorClock r.clockPending = .ok started := by
  have hclock' := hclock
  simp only [clockAt, hstate] at hclock'
  rcases hclock' with ⟨hstamp, hvalid, hsigma, hu, hgrid, hsigmaTime,
    hbeforeGrid, hproposal⟩
  have hparam := proposalParameterValid_of_rate (p := p) rate
  have htime : CoordinatorPhaseClock.startRoundTimeValid p t r.priorClock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
      FollowerCutoffScan.calendarRound]
    omega
  have hstampTime : r.time.val + 1 = t.val := by omega
  let bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (rows selected) r.time
  have hdetect := live_detectCutoff_success r.priorClock r.payload.sigma
    r.time bit t hsigma hu hproposal hstampTime
  have hsuccess : ∃ started,
      CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock
        r.clockPending = .ok started := by
    classical
    rcases hdetect with ⟨decision, hdecision⟩
    cases decision with
    | cutoff sigma hsigma' =>
        rcases CoordinatorPhaseClock.startRound_cutoff_effect
            p rate.eta.val t sigma r.priorClock r.clockPending hparam
            hvalid htime hsigma' hdecision with ⟨started, hstarted, _, _, _, _⟩
        exact ⟨started, hstarted⟩
    | noCutoff =>
        let started : CoordinatorPhaseClock.StartRoundResult p := {
          clock := r.priorClock
          gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
            p rate.eta.val r.priorClock hvalid
          pending := r.clockPending
          ledgerCommand := none
          assignmentStart := none }
        refine ⟨started, ?_⟩
        simp [CoordinatorPhaseClock.startRound, hparam, hvalid, htime,
          hdecision, CoordinatorPhaseClock.sourceStartTest, hsigma, hu,
          CoordinatorPhaseClock.cutoffAtOrBefore, started]
        rfl
  exact hsuccess

/-- The preceding theorem is exactly the live dispatcher's call: its only
time-field change is `liveRegistersAt r x.time`. -/
theorem live_dispatch_startRound_success
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live r q base)
    (hclock : clockAt x.rows x.selected x.time.val x.state) :
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
        .ok started := by
  obtain ⟨started, hstarted⟩ := live_startRound_success
    x.rows x.selected x.time.val x.state r q base hstate hclock x.time rfl
  have hpending : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
      r.clockPending := CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq _
  refine ⟨started, ?_⟩
  rw [hpending]
  simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hstarted

/-- The exact live consumer `CoordinatorStartRoundCutoffDispatch.dispatch`
cannot return a clock failure on a state satisfying the literal invariant. -/
theorem live_dispatch_no_clockFailure
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live r q base)
    (hclock : clockAt x.rows x.selected x.time.val x.state) :
    ∀ failure, CoordinatorStartRoundCutoffDispatch.dispatch
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base ≠ .error failure := by
  intro failure hfailure
  obtain ⟨started, hstarted⟩ := live_dispatch_startRound_success r q base hstate hclock
  have hstartFailure :=
    (CoordinatorStartRoundCutoffDispatch.dispatch_clockError_iff
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base failure).mp hfailure
  rw [hstarted] at hstartFailure
  cases hstartFailure

/-- A collection state's actual clock call succeeds at every in-horizon
round at or beyond its finite cutoff. The saved proposal token is unrestricted
because collection cutoff detection does not read it. -/
theorem collection_startRound_success
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (k : ℕ) (state : State p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : state.coordinator = .collection payload ledger saved)
    (hclock : clockAt rows selected k state)
    (t u : Fin p.T) (ht : t.val = k)
    (hu' : u.val = ledger.cutoff - 1) :
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val t
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved u)
      ledger.pending = .ok started := by
  have hclock' := hclock
  simp only [clockAt, hstate] at hclock'
  rcases hclock' with ⟨hsigmaLedger, horder, hcutPos, hcutBound,
    hcutTime, hfreeze, hcutFreeze, hfreezeBound⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
  have hsigma : clock.sigma = some payload.sigma := rfl
  have hu : clock.u = some u := rfl
  have hparam := proposalParameterValid_of_rate (p := p) rate
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    change ledger.freezeAt =
        FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      payload.sigma.val + 1 < ledger.freezeAt ∧
      ledger.freezeAt ≤ p.T + 1 ∧ payload.sigma.val < u.val ∧
      u.val + 1 ≤ ledger.freezeAt
    refine ⟨hfreeze, ?_, hfreezeBound, ?_, ?_⟩ <;> omega
  have htime : CoordinatorPhaseClock.startRoundTimeValid p t clock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, clock,
      ReferenceActivePhysicalStep.collectionClock]
    omega
  have hut : u.val ≤ t.val := by
    rw [hu']
    omega
  have hgrid : CoordinatorPhaseClock.newGridBoundaryValid p t
      (FollowerCutoffScan.gridBoundary p rate.eta.val t) := by
    have hbounds := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
      rate.eta.property rate.sourceCap t
    simpa [CoordinatorPhaseClock.newGridBoundaryValid,
      FollowerCutoffScan.calendarRound] using hbounds
  by_cases hpending : ledger.pending = ∅
  · have hstart := CoordinatorPhaseClock.startRound_collection_empty
      p rate.eta.val t payload.sigma u clock hparam hclockValid hsigma hu
      hut hgrid
    let started : CoordinatorPhaseClock.StartRoundResult p := {
      clock := {
        sigma := some t
        u := none
        g := FollowerCutoffScan.gridBoundary p rate.eta.val t
        lastProposal := saved }
      gridDomain := hgrid
      pending := Finset.univ
      ledgerCommand := none
      assignmentStart := some ⟨t,
        CoordinatorPhaseClock.classifyAssignmentStart (some payload.sigma) t
          ledger.freezeAt⟩ }
    refine ⟨started, ?_⟩
    change CoordinatorPhaseClock.startRound p rate.eta.val t clock
      ledger.pending = .ok started
    rw [hpending]
    rw [hstart]
    simp [started, clock, ReferenceActivePhysicalStep.collectionClock,
      CoordinatorPhaseClock.classifyAssignmentStart]
  · have hstart := CoordinatorPhaseClock.startRound_collection_pending
      p rate.eta.val t payload.sigma u clock ledger.pending hparam
      hclockValid hsigma hu hut hpending
    let started : CoordinatorPhaseClock.StartRoundResult p := {
      clock := clock
      gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
        p rate.eta.val clock hclockValid
      pending := ledger.pending
      ledgerCommand := none
      assignmentStart := none }
    exact ⟨started, by simpa [started, clock,
      ReferenceActivePhysicalStep.collectionClock] using hstart⟩

/-- The preceding theorem is exactly the computed collection dispatch call.
Its finite cutoff coordinate is made from the source ledger's integer cutoff. -/
theorem collection_dispatch_startRound_success
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hclock : clockAt x.rows x.selected x.time.val x.state) :
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by
      have hclock' := hclock
      simp only [clockAt, hstate] at hclock'
      omega⟩
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
      ledger.pending = .ok started := by
  have hclock' := hclock
  simp only [clockAt, hstate] at hclock'
  rcases hclock' with ⟨_, _, _, _, _, _, _, _⟩
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hcutoff : cutoff.val = ledger.cutoff - 1 := rfl
  exact collection_startRound_success x.rows x.selected x.time.val x.state
    payload ledger saved hstate hclock x.time cutoff rfl hcutoff

/-- The literal post-choice tail either enters its actual absorbing failure
state or stores the current complete-row proposal stamp. Its successful branch
uses the same checked finish operation as `livePostChoice`; the previous
proposal stamp is an explicit input to the preceding dispatch proof. -/
private theorem livePostChoice_clockAt
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock)
    (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hu : r.priorClock.u = none)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hstrict : r.payload.sigma.val < r.time.val + 1)
    (hboundary : r.time.val + 1 < r.gridBoundary)
    (hstarted : started.clock = r.priorClock)
    (htime : r.time = x.time) :
    clockAt x.rows x.selected (x.time.val + 1)
      { x.state with coordinator :=
        (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration } := by
  classical
  have hfinishTime :
      CoordinatorPhaseClock.finishRoundTimeValid x.time r.priorClock := by
    simp [CoordinatorPhaseClock.finishRoundTimeValid, hsigma, hu,
      FollowerCutoffScan.calendarRound]
    omega
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [ReferenceActivePhysicalStep.livePostChoice, hrecord,
      ReferenceActivePhysicalStep.coordinatorFailure, clockAt]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
    | error reason =>
        simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
          ReferenceActivePhysicalStep.coordinatorFailure, clockAt]
    | ok serviced =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
          started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none =>
          simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice, hconfirmation,
            ReferenceActivePhysicalStep.coordinatorFailure, clockAt]
      | some pending =>
        cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock pending x.row with
        | error reason =>
            simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice, hconfirmation, hfinish,
              ReferenceActivePhysicalStep.coordinatorFailure, clockAt]
        | ok finished =>
          rw [ReferenceActivePhysicalStep.livePostChoice_success prepared r q base
            started recording serviced pending finished hrecord hservice hconfirmation hfinish]
          have hstartedEq : started.clock = r.priorClock := hstarted
          rw [hstartedEq] at hfinish
          have hfinishSaved := CoordinatorPhaseClock.finishRound_live_savedProposal
            p rate.eta.val x.time r.priorClock pending x.row hclock hfinishTime
            (by rw [hsigma]; exact Option.some_ne_none _) hu hparam
          rcases hfinishSaved with ⟨saved, hsaved, hsavedClock, _, _⟩
          have hfinishedEq : finished = saved :=
            (Except.ok.inj (hsaved.symm.trans hfinish)).symm
          subst finished
          let currentProposal : Option (Fin p.T × Bool) :=
            some (x.time, FollowerCutoffScan.completeRowProposalBit
              p rate.eta.val x.row x.time)
          have hclockUpdate : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
              ({ r.priorClock with lastProposal := currentProposal } :
                CoordinatorPhaseClock.ClockRegisters p) := by
            simpa [CoordinatorPhaseClock.clockRegistersValid,
              CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hclock
          have hproposalUpdate : saved.clock.lastProposal = some (x.time,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (x.rows x.selected) x.time) := by
            rw [hsavedClock]
            rfl
          change x.time.val + 1 = x.time.val + 1 ∧
            CoordinatorPhaseClock.clockRegistersValid p rate.eta.val saved.clock ∧
            saved.clock.sigma = some r.payload.sigma ∧
            saved.clock.u = none ∧ saved.clock.g = saved.clock.g ∧
            r.payload.sigma.val < x.time.val + 1 ∧
            x.time.val + 1 < saved.clock.g ∧
            saved.clock.lastProposal = some (x.time,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (x.rows x.selected) x.time)
          have hsigmaSaved : saved.clock.sigma = some r.payload.sigma := by
            rw [hsavedClock]
            exact hsigma
          have huSaved : saved.clock.u = none := by
            rw [hsavedClock]
            exact hu
          have hproposalSaved : saved.clock.lastProposal = some (x.time,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (x.rows x.selected) x.time) := by
            simpa [ReferenceActivePhysicalStep.RoundInput.row] using hproposalUpdate
          refine ⟨rfl, ?_, hsigmaSaved, huSaved, rfl, ?_, ?_, hproposalSaved⟩
          · simpa [hsavedClock] using hclockUpdate
          · simpa [htime] using hstrict
          · simpa [hgrid, htime, hsavedClock] using hboundary

/-- The actual continuing-live choice branch stores the same checked clock
and the current complete-row proposal stamp after the literal post-choice
tail. `hcut` is the observation equation for this outcome of `dispatchLive`. -/
theorem step_clockAt_live_continuing
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload
      dispatched.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hstate : x.state.coordinator = .live r q base)
    (hclock : clockAt x.rows x.selected x.time.val x.state)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
        .ok dispatched.startResult)
    (hcontinuation : continuation.startRoundResult = dispatched.startResult)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation selection)) :
    clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next := by
  classical
  have hinv := hclock
  simp only [clockAt, hstate] at hinv
  rcases hinv with ⟨_, hvalid, hsigma, hu, hgrid, hsigmaTime, hbeforeGrid, _⟩
  let live := ReferenceActivePhysicalStep.liveRegistersAt r x.time
  let owned := ReferenceActivePhysicalStep.liveOwnedAt r q x.time
  have hparam := proposalParameterValid_of_rate (p := p) rate
  have hstrict : live.payload.sigma.val < live.time.val + 1 := by
    simp [live, ReferenceActivePhysicalStep.liveRegistersAt]
    omega
  have hstarted : dispatched.startResult.clock = r.priorClock := by
    rw [← hcontinuation]
    exact continuation.clockFrame.1
  have hstartTime : CoordinatorPhaseClock.startRoundTimeValid p x.time r.priorClock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
      FollowerCutoffScan.calendarRound]
    omega
  have hpending : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
      r.clockPending := CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq _
  have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      r.clockPending = .ok dispatched.startResult := by
    have hstart'' := hstart
    rw [hpending] at hstart''
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hstart''
  have hnotgrid : FollowerCutoffScan.calendarRound x.time ≠ r.priorClock.g := by
    intro heq
    obtain ⟨expected, hcutoff, hcutClock, _, _, _⟩ :=
      CoordinatorPhaseClock.startRound_grid_cutoff p rate.eta.val x.time
        r.payload.sigma r.priorClock r.clockPending hparam hvalid hstartTime
        hsigma hu heq
    have hresult : expected = dispatched.startResult :=
      Except.ok.inj (hcutoff.symm.trans hstart')
    have hclockEq : expected.clock = r.priorClock :=
      (congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult).trans hstarted
    have huEq := congrArg CoordinatorPhaseClock.ClockRegisters.u hclockEq
    rw [hcutClock, hu] at huEq
    cases huEq
  have hboundary : live.time.val + 1 < live.gridBoundary := by
    simp [live, ReferenceActivePhysicalStep.liveRegistersAt, hgrid]
    have hcalendar_le : FollowerCutoffScan.calendarRound x.time ≤ r.priorClock.g := by
      have hparts : r.payload.sigma.val < x.time.val ∧
          FollowerCutoffScan.calendarRound x.time ≤ r.priorClock.g := by
        simpa [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu] using hstartTime
      exact hparts.2
    have hnotgrid' : x.time.val + 1 ≠ r.priorClock.g := by
      simpa [FollowerCutoffScan.calendarRound] using hnotgrid
    have hcalendar_le' : x.time.val + 1 ≤ r.priorClock.g := by
      simpa [FollowerCutoffScan.calendarRound] using hcalendar_le
    omega
  have htail := livePostChoice_clockAt (ReferenceActivePhysicalStep.prepare x)
    live owned base dispatched.startResult hparam hvalid hsigma hu hgrid
    hstrict hboundary hstarted rfl
  have hselection : (ReferenceActivePhysicalStep.DispatchCut.live r q base
      (.continuingChosen dispatched hstart continuation selection)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
    (ReferenceActivePhysicalStep.prepare x) r q base
    (.continuingChosen dispatched hstart continuation selection) hcut
  have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare x) live owned base dispatched.startResult := by
    simpa [hselection] using hobserve
  simpa [ReferenceActivePhysicalStep.step, hobs, clockAt] using htail

end Bandits.Support.ReferenceCoordinatorClockDomains

end
