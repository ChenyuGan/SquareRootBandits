/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety

import Lean.Elab.Tactic.Omega

/-!
# One actual occupied follower transition

This local induction component follows the occupied-at-choice branch of
`appendix_a_local_protocol.tex:28-64` and `06_interruptions.tex:246-299`.
It runs on the canonical preparation and physical step. The local mass and
domain premises belong to the later induction; no physical-history invariant
is asserted here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceOccupiedServiceDomain

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem stateInputDomain_of_localStateDomainValid
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid s) :
    ActiveFollowerQueueOperation.stateInputDomain s := by
  refine ⟨hvalid.1.1, hvalid.1.2.1, hvalid.1.2.2, ?_, hvalid.2.1.2.1⟩
  intro record hrecord
  exact hvalid.2.1.1 record hrecord

/-- The actual prepared occupied follower services once, then runs the
pre-choice pending-only release test and reads the proposal bit from the same
current row. The check succeeds from local domains and calendar mass; no
output-domain or successful-operation premise is supplied. -/
theorem occupied_tail_preserves_local_domain
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1))
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary s memory)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid s)
    (hmass : s.S + s.backlog ≤ x.time.val * D p)
    (hoccupied : s.status ≠ .unoccupied)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hM : s.lastDown = some M)
    (htime : M.val.sigma ≤ x.time.val) :
    let prepared := ReferenceActivePhysicalStep.prepare x
    let f := prepared.followers.followers i
    let own := prepared.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let arrival := ActiveFollowerQueueOperation.rawArrival
      rate.eta i x.row x.time M own
    let service := min (4 * rate.n) (s.backlog + arrival)
    f.follower = i ∧ f.row = x.row ∧ f.time = x.time ∧
      f.activation = x.state.activations i ∧
      ∃ serviced next nextMemory,
        ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
          rate.n rate.n_scale f.follower f.row f.activation f.time own s =
            .success serviced ∧
        serviced.arrival = arrival ∧ serviced.service = service ∧
        serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival ∧
        arrival ≤ D p ∧ service ≤ D p ∧
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
          f.follower f.row f.activation f.time f.active f.arm own s).result =
            .ok serviced.output ∧
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
          f.follower f.row f.activation f.time f.active f.arm own s).downInput = none ∧
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
          f.follower f.row f.activation f.time f.active f.arm own s).down = none ∧
        DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time
          own s memory serviced.output = .ok (next, nextMemory) ∧
        ((ReferenceActivePhysicalStep.step x).followers i).configuration =
          .ordinary next nextMemory ∧
        ((ReferenceActivePhysicalStep.step x).followers i).failure = none ∧
        ((ReferenceActivePhysicalStep.step x).followers i).downInput = none ∧
        ((ReferenceActivePhysicalStep.step x).followers i).down = none ∧
        next.S = s.S + service ∧ next.delta = service ∧
        next.backlog = s.backlog + arrival - service ∧
        ((next.S, next.backlog) = Bandits.Support.QueueReplay.transition
          (ActiveFollowerQueueOperation.serviceCapacity rate.n)
          (s.S, s.backlog) (true, arrival)) ∧
        next.S + next.backlog = s.S + s.backlog + arrival ∧
        next.S + next.backlog ≤ (x.time.val + 1) * D p ∧
        ActiveFollowerLifecycle.localStateDomainValid next ∧
        next.lastDown = s.lastDown ∧ next.buffer = s.buffer ∧
        next.downBatch = s.downBatch ∧
        next.initializationFailure = s.initializationFailure ∧
        (next.status = .released ↔
          s.status = .released ∨
            (s.status = .pending ∧
              ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
                own M)) ∧
        (next.status = .pending ↔
          s.status = .pending ∧
            ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
              (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
              own M) ∧
        next.status ≠ .unoccupied ∧
        nextMemory.lastProposalRead = some ⟨x.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row x.time⟩ := by
  classical
  let prepared := ReferenceActivePhysicalStep.prepare x
  let f := prepared.followers.followers i
  let own := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let arrival := ActiveFollowerQueueOperation.rawArrival
    rate.eta i x.row x.time M own
  let service := min (4 * rate.n) (s.backlog + arrival)
  have halign := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    prepared i
  have hfollower : f.follower = i := halign.2.1
  have hrow : f.row = x.row := halign.1
  have htimeField : f.time = x.time := halign.2.2.1
  have hactivation : f.activation = x.state.activations i := halign.2.2.2
  have hactive : f.activation.val ≤ f.time.val + 1 := f.active
  have hdomain := stateInputDomain_of_localStateDomainValid s hvalid
  have harrival : arrival ≤ D p :=
    ActiveFollowerQueueOperation.rawArrival_le_D rate.eta i x.row x.time M own
  have hserviceEq : ActiveFollowerQueueOperation.localService rate.n s.backlog arrival =
      service := by
    simp [service, ActiveFollowerQueueOperation.localService,
      ActiveFollowerQueueOperation.serviceCapacity, Bandits.Support.CappedService.service]
  have hserviceBound : service ≤ D p := by
    rw [← hserviceEq]
    exact ActiveFollowerQueueOperation.localService_le_D rate.eta rate.sourceCap
      rate.n rate.n_scale s.backlog arrival
  have hoccupiedFlag : s.status.occupied := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => simp [ActiveRoundActions.FollowerStatus.occupied]
    | released => simp [ActiveRoundActions.FollowerStatus.occupied]
  have houtputEq : ActiveFollowerQueueOperation.serviceOutput rate.n s arrival =
      ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival := by
    simp [ActiveFollowerQueueOperation.serviceOutput, hoccupiedFlag]
  rcases ActiveFollowerQueueOperation.serviceUpdate_register_equations
      rate.n s arrival with ⟨hscore, hdelta, hresidual⟩
  have hconservation :
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
        (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog =
          s.S + s.backlog + arrival := by
    rw [hscore, hserviceEq]
    omega
  have hmassNext :
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
        (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤
          (x.time.val + 1) * D p := by
    rw [hconservation]
    calc
      s.S + s.backlog + arrival ≤ s.S + s.backlog + D p := by omega
      _ ≤ x.time.val * D p + D p := Nat.add_le_add_right hmass (D p)
      _ = (x.time.val + 1) * D p := by
        rw [Nat.add_mul, Nat.one_mul]
  have htimeNext : x.time.val + 1 ≤ p.T := by omega
  have hmassHorizon :
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
        (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤
          p.T * D p :=
    hmassNext.trans (Nat.mul_le_mul_right (D p) htimeNext)
  have hscoreBound :
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S ≤ p.T * D p := by
    omega
  have hbacklogBound :
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤ p.T * D p := by
    omega
  have houtputScoreDomain : s.S +
      ActiveFollowerQueueOperation.localService rate.n s.backlog arrival ≤ p.T * D p := by
    rw [← hscore]
    exact hscoreBound
  have houtputDomain : ActiveFollowerQueueOperation.outputDomain rate.n s arrival
      (ActiveFollowerQueueOperation.localService rate.n s.backlog arrival) := by
    refine ⟨harrival, ?_, houtputScoreDomain, ?_⟩
    · exact hserviceBound
    · exact hbacklogBound
  have hthin := ActiveFollowerQueueOperation.thinningProbability_domain rate.eta M
  have hraw : ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row
      f.time M own = arrival := by
    rw [hfollower, hrow, htimeField]
  have houtputDomainActual : ActiveFollowerQueueOperation.outputDomain rate.n s
      (ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own)
      (ActiveFollowerQueueOperation.localService rate.n s.backlog
        (ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own)) := by
    simpa only [hraw] using houtputDomain
  have houtputEqActual : ActiveFollowerQueueOperation.serviceOutput rate.n s
      (ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own) =
        ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival := by
    rw [hraw]
    exact houtputEq
  let serviced : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n
      f.follower f.row f.activation f.time own s := {
    output := ActiveFollowerQueueOperation.serviceOutput rate.n s
      (ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own)
    arrival := ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own
    service := ActiveFollowerQueueOperation.localService rate.n s.backlog
      (ActiveFollowerQueueOperation.rawArrival rate.eta f.follower f.row f.time M own)
    inputDomain := hdomain
    sourceRateCap := rate.sourceCap
    naturalScale := rate.n_scale
    arrival_le_D := houtputDomainActual.1
    service_le_D := houtputDomainActual.2.1
    score_le_TD := by rw [houtputEqActual]; exact hscoreBound
    backlog_le_TD := by rw [houtputEqActual]; exact hbacklogBound
    queueUpdate := rfl
    action := by
      cases hstatus : s.status with
      | unoccupied => exact False.elim (hoccupied hstatus)
      | pending =>
          simp only [ActiveFollowerQueueOperation.serviceAction, hstatus]
          exact ⟨hactive, M, hM, hthin, rfl, trivial⟩
      | released =>
          simp only [ActiveFollowerQueueOperation.serviceAction, hstatus]
          exact ⟨hactive, M, hM, hthin, rfl, trivial⟩ }
  have hservicedArrival : serviced.arrival = arrival := hraw
  have hservicedService : serviced.service = service := by
    calc
      serviced.service = ActiveFollowerQueueOperation.localService rate.n s.backlog
          serviced.arrival := rfl
      _ = ActiveFollowerQueueOperation.localService rate.n s.backlog arrival := by
        rw [hservicedArrival]
      _ = service := hserviceEq
  have hchecked : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale f.follower f.row f.activation f.time own s = .success serviced := by
    unfold ActiveFollowerQueueOperation.checkedService
    rw [dite_eq_left hdomain]
    split
    · rename_i hstatus
      exact False.elim (hoccupied hstatus)
    · rw [dite_eq_left hactive]
      split
      · rename_i hmissing
        rw [hM] at hmissing
        cases hmissing
      · rename_i M' hlast
        have hM' : M' = M := Option.some.inj (hlast.symm.trans hM)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left houtputDomainActual]
    · rw [dite_eq_left hactive]
      split
      · rename_i hmissing
        rw [hM] at hmissing
        cases hmissing
      · rename_i M' hlast
        have hM' : M' = M := Option.some.inj (hlast.symm.trans hM)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left houtputDomainActual]
  have hservicedOutput : serviced.output =
      ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival := by
    exact houtputEqActual
  have hpostValid : ActiveFollowerLifecycle.localStateDomainValid serviced.output := by
    rw [hservicedOutput]
    refine ⟨⟨hscoreBound, ?_, hbacklogBound⟩, hvalid.2.1, hvalid.2.2⟩
    rw [hdelta, hserviceEq]
    exact hserviceBound
  have hpostMass : serviced.output.S + serviced.output.backlog ≤
      (x.time.val + 1) * D p := by
    rw [hservicedOutput]
    exact hmassNext
  have hpostLast : serviced.output.lastDown = s.lastDown := by
    rw [hservicedOutput]
    exact (ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
      rate.n s arrival).1
  have hpostBuffer : serviced.output.buffer = s.buffer := by
    rw [hservicedOutput]
    exact (ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
      rate.n s arrival).2.2.1
  have hpostBatch : serviced.output.downBatch = s.downBatch := by
    rw [hservicedOutput]
    exact (ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
      rate.n s arrival).2.1
  have hpostStatus : serviced.output.status = s.status := by
    rw [hservicedOutput]
    exact (ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
      rate.n s arrival).2.2.2.1
  have hpostOccupied : serviced.output.status ≠ .unoccupied := by
    rw [hpostStatus]
    exact hoccupied
  have hpostFailure : serviced.output.initializationFailure = s.initializationFailure := by
    rw [hservicedOutput]
    exact (ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
      rate.n s arrival).2.2.2.2
  have hpostRecord : serviced.output.lastDown = some M := hpostLast.trans hM
  let releaseTest := ActiveFollowerLifecycle.releaseCondition rate.eta i
    (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own M
  let next : ReferencePrelaunchFollower.State p rate.eta :=
    match s.status with
    | .unoccupied => serviced.output
    | .pending => if releaseTest then {serviced.output with status := .released}
        else serviced.output
    | .released => serviced.output
  let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
    ⟨some ⟨x.time,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row x.time⟩⟩
  have hrecordTimeNext : M.val.sigma ≤ x.time.val + 1 := by omega
  have hfinishCanonical : DeclaredFollowerLocalRound.releaseAndFinish rate i x.row x.time
      own s memory serviced.output = .ok (next, nextMemory) := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending =>
        have hrecordForRelease :
            (¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own M ∧
              serviced.output.status = .unoccupied) ∨
            ∃ M', serviced.output.lastDown = some M' ∧ M'.val.sigma ≤ x.time.val + 1 :=
          Or.inr ⟨M, hpostRecord, hrecordTimeNext⟩
        have hrelease := ActiveFollowerLifecycle.releaseAfterService_pending_branch
          rate.eta i x.time (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
          own s serviced.output hstatus hvalid M hM htime hpostValid hrecordForRelease
        by_cases htest : releaseTest
        · have hreleaseEq : ActiveFollowerLifecycle.releaseAfterService rate.eta i x.time
              (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own s
              serviced.output = .ok {serviced.output with status := .released} := by
            simpa [releaseTest, htest] using hrelease
          have hreleasedValid : ActiveFollowerLifecycle.localStateDomainValid
              {serviced.output with status := .released} := by
            simpa [ActiveFollowerLifecycle.localStateDomainValid,
              ActiveFollowerLifecycle.serviceRegistersValid,
              ActiveFollowerLifecycle.localBufferValid,
              ActiveFollowerLifecycle.downDecoderStateValid] using hpostValid
          have hfinishRound := ActiveFollowerLifecycle.finishRound_occupied_read rate.eta
            x.time x.row {serviced.output with status := .released} memory (by simp)
            hreleasedValid M (by simp only [hpostLast, hM]) hrecordTimeNext
          simp [DeclaredFollowerLocalRound.releaseAndFinish, hreleaseEq, hfinishRound,
            next, hstatus, releaseTest, htest, nextMemory]
        · have hreleaseEq : ActiveFollowerLifecycle.releaseAfterService rate.eta i x.time
              (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own s
              serviced.output = .ok serviced.output := by
            simpa [releaseTest, htest] using hrelease
          have hfinishRound := ActiveFollowerLifecycle.finishRound_occupied_read rate.eta
            x.time x.row serviced.output memory hpostOccupied hpostValid M hpostRecord hrecordTimeNext
          simp [DeclaredFollowerLocalRound.releaseAndFinish, hreleaseEq, hfinishRound,
            next, hstatus, releaseTest, htest, nextMemory]
    | released =>
        have hnotPending : s.status ≠ .pending := by simp [hstatus]
        have hrelease := ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta
          i x.time (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time) own s
          serviced.output hnotPending
        have hfinishRound := ActiveFollowerLifecycle.finishRound_occupied_read rate.eta
          x.time x.row serviced.output memory hpostOccupied hpostValid M hpostRecord hrecordTimeNext
        simp [DeclaredFollowerLocalRound.releaseAndFinish, hrelease, hfinishRound,
          next, hstatus, nextMemory]
  have hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time
      own s memory serviced.output = .ok (next, nextMemory) := by
    simpa only [hfollower, hrow, htimeField] using hfinishCanonical
  have hnextFrame : next.S = serviced.output.S ∧
      next.delta = serviced.output.delta ∧ next.backlog = serviced.output.backlog ∧
      next.lastDown = serviced.output.lastDown ∧ next.buffer = serviced.output.buffer ∧
      next.downBatch = serviced.output.downBatch ∧
      next.initializationFailure = serviced.output.initializationFailure := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => by_cases htest : releaseTest <;>
        simp [next, hstatus, releaseTest, htest]
    | released => simp [next, hstatus]
  have hnextValid : ActiveFollowerLifecycle.localStateDomainValid next := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => by_cases htest : releaseTest <;>
        simpa [next, hstatus, releaseTest, htest,
          ActiveFollowerLifecycle.localStateDomainValid,
          ActiveFollowerLifecycle.serviceRegistersValid,
          ActiveFollowerLifecycle.localBufferValid,
          ActiveFollowerLifecycle.downDecoderStateValid] using hpostValid
    | released => simpa [next, hstatus,
        ActiveFollowerLifecycle.localStateDomainValid,
        ActiveFollowerLifecycle.serviceRegistersValid,
        ActiveFollowerLifecycle.localBufferValid,
        ActiveFollowerLifecycle.downDecoderStateValid] using hpostValid
  have hnextScore : next.S = s.S + service := by
    rw [hnextFrame.1, hservicedOutput, hscore, hserviceEq]
  have hnextDelta : next.delta = service := by
    rw [hnextFrame.2.1, hservicedOutput, hdelta, hserviceEq]
  have hnextBacklog : next.backlog = s.backlog + arrival - service := by
    rw [hnextFrame.2.2.1, hservicedOutput]
    omega
  have hnextQueue : (next.S, next.backlog) = Bandits.Support.QueueReplay.transition
      (ActiveFollowerQueueOperation.serviceCapacity rate.n) (s.S, s.backlog)
        (true, arrival) := by
    rw [hnextFrame.1, hnextFrame.2.2.1, hservicedOutput]
    exact ActiveFollowerQueueOperation.serviceUpdate_eq_queueTransition rate.n s arrival
  have hnextConservation : next.S + next.backlog = s.S + s.backlog + arrival := by
    rw [hnextFrame.1, hnextFrame.2.2.1, hservicedOutput]
    exact hconservation
  have hnextMass : next.S + next.backlog ≤ (x.time.val + 1) * D p := by
    rw [hnextFrame.1, hnextFrame.2.2.1]
    exact hpostMass
  have hnextRecord : next.lastDown = s.lastDown :=
    hnextFrame.2.2.2.1.trans hpostLast
  have hnextBuffer : next.buffer = s.buffer := hnextFrame.2.2.2.2.1.trans hpostBuffer
  have hnextBatch : next.downBatch = s.downBatch := hnextFrame.2.2.2.2.2.1.trans hpostBatch
  have hnextFailure : next.initializationFailure = s.initializationFailure :=
    hnextFrame.2.2.2.2.2.2.trans hpostFailure
  have hnextStatus : next.status = .released ↔
      s.status = .released ∨ (s.status = .pending ∧ releaseTest) := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => by_cases htest : releaseTest <;>
        simp [next, hstatus, releaseTest, htest, hpostStatus]
    | released => simp [next, hstatus, hpostStatus]
  have hnextPending : next.status = .pending ↔
      s.status = .pending ∧ ¬ releaseTest := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => by_cases htest : releaseTest <;>
        simp [next, hstatus, releaseTest, htest, hpostStatus]
    | released => simp [next, hstatus, hpostStatus]
  have hnextOccupied : next.status ≠ .unoccupied := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => by_cases htest : releaseTest <;>
        simp [next, hstatus, releaseTest, htest, hpostStatus]
    | released => simp [next, hstatus, hpostStatus]
  have hactualOutput :
      (ReferenceActivePhysicalStep.step x).followers i =
        ReferenceActivePhysicalStep.PreparedRound.observeFollower prepared i := rfl
  have hfchoice : f.configuration = .ordinary s memory := by
    change f.configuration = .ordinary s memory at hchoice
    exact hchoice
  have hfchoiceRaw : (prepared.followers.followers i).configuration =
      .ordinary s memory := by
    simpa only [f] using hfchoice
  have hrecordResult :
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm own s).result =
          .ok serviced.output := by
    simp [ReferenceActivePhysicalStep.recordFollower, hoccupied,
      DeclaredFollowerLocalRound.recordOrServiceThenDown, hchecked]
  have hrecordNoDown :
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm own s).downInput = none ∧
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm own s).down = none := by
    simp [ReferenceActivePhysicalStep.recordFollower, hoccupied]
  have hrecordResultRaw :
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        (prepared.followers.followers i).follower (prepared.followers.followers i).row
        (prepared.followers.followers i).activation (prepared.followers.followers i).time
        (prepared.followers.followers i).active (prepared.followers.followers i).arm
        (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).result =
          .ok serviced.output := by
    simpa only [f, own] using hrecordResult
  have hrecordNoDownRaw :
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        (prepared.followers.followers i).follower (prepared.followers.followers i).row
        (prepared.followers.followers i).activation (prepared.followers.followers i).time
        (prepared.followers.followers i).active (prepared.followers.followers i).arm
        (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).downInput = none ∧
      (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        (prepared.followers.followers i).follower (prepared.followers.followers i).row
        (prepared.followers.followers i).activation (prepared.followers.followers i).time
        (prepared.followers.followers i).active (prepared.followers.followers i).arm
        (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).down = none := by
    simpa only [f, own] using hrecordNoDown
  have hfinishRaw : DeclaredFollowerLocalRound.releaseAndFinish rate
      (prepared.followers.followers i).follower (prepared.followers.followers i).row
      (prepared.followers.followers i).time
      (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      s memory serviced.output = .ok (next, nextMemory) := by
    simpa only [f, own] using hfinish
  have hfinishFollower := ReferenceActivePhysicalStep.finishFollower_success
    prepared.coordinator.downView f own s serviced.output next memory nextMemory hfchoice
    hrecordResult hfinish
  have hstepConfig : ((ReferenceActivePhysicalStep.step x).followers i).configuration =
      .ordinary next nextMemory := by
    calc
      ((ReferenceActivePhysicalStep.step x).followers i).configuration =
          (ReferenceActivePhysicalStep.PreparedRound.observeFollower prepared i).configuration :=
        congrArg ReferenceActivePhysicalStep.FollowerObservation.configuration hactualOutput
      _ = .ordinary next nextMemory := hfinishFollower.1
  have hstepFailure : ((ReferenceActivePhysicalStep.step x).followers i).failure = none := by
    calc
      ((ReferenceActivePhysicalStep.step x).followers i).failure =
          (ReferenceActivePhysicalStep.PreparedRound.observeFollower prepared i).failure :=
        congrArg ReferenceActivePhysicalStep.FollowerObservation.failure hactualOutput
      _ = none := hfinishFollower.2
  have hstepNoDown :
      ((ReferenceActivePhysicalStep.step x).followers i).downInput = none ∧
      ((ReferenceActivePhysicalStep.step x).followers i).down = none := by
    rw [hactualOutput]
    change (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
      (prepared.followers.followers i)
      (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))).downInput = none ∧
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        (prepared.followers.followers i)
        (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))).down = none
    simp only [ReferenceActivePhysicalStep.finishFollower, hfchoiceRaw,
      hrecordResultRaw, hfinishRaw]
    exact ⟨hrecordNoDownRaw.1, hrecordNoDownRaw.2⟩
  refine ⟨hfollower, hrow, htimeField, hactivation, serviced, next, nextMemory,
    hchecked, hservicedArrival, hservicedService, hservicedOutput,
    harrival, hserviceBound, hrecordResult, hrecordNoDown.1, hrecordNoDown.2,
    hfinish, hstepConfig, hstepFailure, hstepNoDown.1, hstepNoDown.2,
    hnextScore, hnextDelta, hnextBacklog, hnextQueue, hnextConservation,
    hnextMass, hnextValid, hnextRecord, hnextBuffer, hnextBatch, hnextFailure,
    hnextStatus, hnextPending, hnextOccupied, rfl⟩

end Bandits.Support.ReferenceOccupiedServiceDomain

end
