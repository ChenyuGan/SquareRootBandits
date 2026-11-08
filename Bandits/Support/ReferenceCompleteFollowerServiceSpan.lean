/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorMass

import Lean.Elab.Tactic.Omega

/-!
# Assignment-relative service and queue conservation on the complete suffix

This module keeps the installed follower queue as the initial queue in the
literal checked DOWN recovery, then records the arithmetic needed to extend
that replay through actual occupied service rounds.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerServiceSpan

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem acceptedTotal_le_of_record_cap
    (records : List (Bool × ℕ)) (cap : ℕ)
    (hcap : ∀ record ∈ records, record.2 ≤ cap) :
    Bandits.Support.RecordedQueueRun.acceptedTotal records ≤ records.length * cap := by
  induction records with
  | nil => simp [Bandits.Support.RecordedQueueRun.acceptedTotal]
  | cons record records ih =>
      have hrecord := hcap record List.mem_cons_self
      have htail : ∀ item ∈ records, item.2 ≤ cap := by
        intro item hitem
        exact hcap item (List.mem_cons_of_mem _ hitem)
      have hrest := ih htail
      cases record with
      | mk enabled arrival =>
          cases enabled
          · simp [Bandits.Support.RecordedQueueRun.acceptedTotal,
              Bandits.Support.RecordedQueueRun.acceptedArrival]
            exact Nat.le_trans hrest
              (Nat.mul_le_mul_right cap (Nat.le_succ records.length))
          · simp [Bandits.Support.RecordedQueueRun.acceptedTotal,
              Bandits.Support.RecordedQueueRun.acceptedArrival]
            calc
              arrival + Bandits.Support.RecordedQueueRun.acceptedTotal records ≤
                  cap + records.length * cap := Nat.add_le_add hrecord hrest
              _ = (records.length + 1) * cap := by
                rw [Nat.add_mul, Nat.one_mul]
                exact Nat.add_comm _ _

/-- Quantitative bounds for the literal successful checked recovery. The
initial queue is the actual DOWN payload queue, and each recorded arrival is
counted at its real scanned timestamp. -/
theorem checked_recovery_service_conservation
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (hinterval : M.val.sigma < ell)
    (final : ActiveFollowerDownAcceptance.ReplayRegisters)
    (hchecked : ActiveFollowerDownAcceptance.checkedRecovery p rate M state ell = .ok final) :
    final.registers.1 ≤ (4 * rate.n) * (ell - M.val.sigma) ∧
      final.registers.1 + final.registers.2 ≤
        M.val.q + (ell - M.val.sigma) * D p ∧
      final.lastService ≤ final.registers.1 ∧ final.lastService ≤ 4 * rate.n := by
  obtain ⟨_hdomain, hregisters, harrivals⟩ :=
    ActiveFollowerDownAcceptance.checkedRecovery_success p rate M state ell final hchecked
  let records := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state ell
  have hReplay : final.registers =
      Bandits.Support.QueueReplay.replay (4 * rate.n) (0, M.val.q) records := by
    simpa only [records, ActiveFollowerDownAcceptance.recoveredRegisters] using hregisters
  have hrecordsLength : records.length = ell - M.val.sigma := by
    dsimp only [records, ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals]
    rw [List.length_map, List.length_map,
      ActiveFollowerDownAcceptance.recoveryRounds_length]
  have harrivalCap : ∀ record ∈ records, record.2 ≤ D p := by
    intro record hrecord
    obtain ⟨arrival, ha, rfl⟩ := List.mem_map.mp hrecord
    exact harrivals arrival ha
  have henvelope := Bandits.Support.ReplayWeightStability.replay_score_envelope
    (4 * rate.n) 0 M.val.q records
  rw [← hReplay] at henvelope
  have htotal := Bandits.Support.RecordedQueueRun.replay_total
    (4 * rate.n) (0, M.val.q) records
  have hconserve : final.registers.1 + final.registers.2 =
      M.val.q + Bandits.Support.RecordedQueueRun.acceptedTotal records := by
    rw [hReplay]
    simpa only [Nat.zero_add] using htotal
  have harrivalTotal := acceptedTotal_le_of_record_cap records (D p) harrivalCap
  have hlast := ActiveFollowerDownAcceptance.checkedRecovery_success_last_service
    p rate M state ell hinterval final hchecked
  rw [ActiveFollowerDownAcceptance.recoveredLastService_eq_min] at hlast
  have hfinalScore : final.registers.1 =
      (ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast
        p rate M state ell hinterval).1 +
        min (4 * rate.n)
          ((ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast
            p rate M state ell hinterval).2 +
            ActiveFollowerDownAcceptance.bufferArrivalAt p rate M state (ell - 1)) := by
    calc
      final.registers.1 =
          (ActiveFollowerDownAcceptance.recoveredRegisters p rate M state ell).1 := by
            simpa only [ActiveFollowerDownAcceptance.recoveredRegisters] using
              congrArg Prod.fst hReplay
      _ = (ActiveFollowerDownAcceptance.recoveredLastTransition
          p rate M state ell hinterval).1 := by
            rw [ActiveFollowerDownAcceptance.recoveredRegisters_eq_lastTransition]
      _ = _ := by
        simp [ActiveFollowerDownAcceptance.recoveredLastTransition,
          Bandits.Support.QueueReplay.transition]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hrecordsLength] using henvelope.2
  · calc
      final.registers.1 + final.registers.2 =
          M.val.q + Bandits.Support.RecordedQueueRun.acceptedTotal records := hconserve
      _ ≤ M.val.q + records.length * D p := by omega
      _ = M.val.q + (ell - M.val.sigma) * D p := by rw [hrecordsLength]
  · rw [hlast, hfinalScore]
    omega
  · rw [hlast]
    exact Nat.min_le_left _ _

/-- One actual ordinary follower round advances the assignment-relative
service bounds. The cutoff status and token come from the same complete
source record; an occupied choice contributes its checked arrival and service,
while an unoccupied choice preserves the reply fields. -/
theorem actual_follower_service_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i =
        .ordinary state memory)
    (hdown : state.lastDown = some M)
    (hrow : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.row = row)
    (hnext : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.next.followers i =
        .ordinary next nextMemory)
    (hnextStart : ReferencePrelaunchFollower.acceptedStart next = M.val.sigma)
    (Q sigma : ℕ)
    (hspan : state.S ≤ (4 * rate.n) *
      (min (FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val + 1) - sigma))
    (hmass : state.S + state.backlog ≤ Q +
      (min (FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val + 1) - sigma) * D p)
    (hdelta : state.delta ≤ state.S ∧ state.delta ≤ 4 * rate.n)
    (hsigma : sigma ≤ min
      (FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val + 1))
    (hpositive : 1 ≤ sigma)
    (hqueueStart : Q ≤ (sigma - 1) * D p) :
    next.lastDown = some M ∧
      next.S ≤ (4 * rate.n) *
        (min (FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val + 2) - sigma) ∧
      next.S + next.backlog ≤ Q +
        (min (FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val + 2) - sigma) * D p ∧
      next.delta ≤ next.S ∧ next.delta ≤ 4 * rate.n := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let r := R[k.val]
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate M)
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
  have hinput' : r.input.state.followers i = .ordinary state memory := by
    simpa only [r, R] using hinput
  have hnext' : r.output.next.followers i = .ordinary next nextMemory := by
    simpa only [r, R] using hnext
  obtain ⟨choice, choiceMemory, hactualChoice, _hstartBound, hfreeze, _haccepted⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology r i next nextMemory hnext'
  have hpreparedActual :
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
    have h := hactualChoice
    rw [ReferenceFollowerFixedReply.actualChoice] at h
    rw [r.output_eq] at h
    exact h
  have hprepared :
      (DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (r.input.state.followers i)).configuration = .ordinary choice choiceMemory := by
    have h := hpreparedActual
    rw [(ReferenceActivePhysicalStep.prepare r.input).followers.followers_eq i] at h
    change (DeclaredFollowerLocalRound.prepare rate i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i)).configuration = .ordinary choice choiceMemory at h
    exact h
  obtain ⟨before, beforeMemory, hbefore, hstart, hreply, _hbeforeUnoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i r.input.row (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i) choice choiceMemory hprepared
  have hbeforeEq : before = state ∧ beforeMemory = memory := by
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hbefore.symm.trans hinput')
    exact ⟨heq.1, heq.2⟩
  have hbeforeState : before = state := hbeforeEq.1
  have hbeforeMemory : beforeMemory = memory := hbeforeEq.2
  subst before
  subst beforeMemory
  have hvalidState : ActiveFollowerLifecycle.localStateDomainValid state := by
    by_contra hnot
    have hbad := ActiveFollowerLifecycle.interruptionDecision_invalid_domain
      rate.eta r.input.time state memory hnot
    unfold ActiveFollowerLifecycle.startRound at hstart
    rw [hbad] at hstart
    cases hstart
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta r.input.time
    state choice memory choiceMemory hstart
  have hvalidChoice : ActiveFollowerLifecycle.localStateDomainValid choice := by
    unfold ActiveFollowerLifecycle.localStateDomainValid at hvalidState ⊢
    rcases hvalidState with ⟨hregisters, hbuffer, hdecoder⟩
    rcases hstartFrame with ⟨_hdown, hS, hdelta, hbacklog, hbatch, hbufferEq,
      _hmarker, _hmemory⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ActiveFollowerLifecycle.serviceRegistersValid, hS, hdelta, hbacklog]
        using hregisters
    · simpa only [ActiveFollowerLifecycle.localBufferValid, hbufferEq] using hbuffer
    · simpa only [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hdecoder
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h source k i state memory hinput M hdown
  have htoken : state.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = r.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row stamp⟩ := by
    intro hbusy
    obtain ⟨stamp, hstamp, hread⟩ :=
      ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
        rate rewards C_star C_h source k i state memory hinput hbusy
    exact ⟨stamp, by simpa [r, R] using hstamp, by simpa [r, R] using hread⟩
  have hchoiceCut := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    r.input.time r.input.row state choice memory choiceMemory M hdown hphase htoken hstart
  have hchoiceStatus : choice.status = .unoccupied ↔ u ≤ r.input.time.val + 1 := by
    simpa [u, r, R, hrow] using hchoiceCut
  have hchoiceReply : ReferenceFollowerReplyChronology.reply choice =
      ReferenceFollowerReplyChronology.reply state := hreply
  have hchoiceDown : choice.lastDown = some M := by
    have h := congrArg Prod.fst hchoiceReply
    change choice.lastDown = state.lastDown at h
    exact h.trans hdown
  have hchoiceStart : ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma := by
    calc
      ReferencePrelaunchFollower.acceptedStart choice =
          ReferencePrelaunchFollower.acceptedStart state :=
            ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hchoiceReply
      _ = M.val.sigma := by simp [ReferencePrelaunchFollower.acceptedStart, hdown]
  have hchoiceStartNext : ReferencePrelaunchFollower.acceptedStart choice =
      ReferencePrelaunchFollower.acceptedStart next := by
    rw [hchoiceStart, hnextStart]
  by_cases hunoccupied : choice.status = .unoccupied
  · have hcut : u ≤ r.input.time.val + 1 := hchoiceStatus.mp hunoccupied
    obtain ⟨hnextUnoccupied, hnextReply⟩ := hfreeze hunoccupied hchoiceStartNext
    have hfields : next.lastDown = state.lastDown ∧ next.S = state.S ∧
        next.delta = state.delta ∧ next.backlog = state.backlog := by
      simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using
        hnextReply.trans hchoiceReply
    have hnextDown : next.lastDown = some M := hfields.1.trans hdown
    have hmin₁ : min u (r.input.time.val + 1) = u := Nat.min_eq_left hcut
    have hmin₂ : min u (r.input.time.val + 2) = u :=
      Nat.min_eq_left (by omega)
    have hspan' : state.S ≤
        (4 * rate.n) * (min u (r.input.time.val + 1) - sigma) := by
      simpa [u, r, R, hrow] using hspan
    have hmass' : state.S + state.backlog ≤
        Q + (min u (r.input.time.val + 1) - sigma) * D p := by
      simpa [u, r, R, hrow] using hmass
    refine ⟨hnextDown, ?_, ?_, ?_, ?_⟩
    · calc
        next.S ≤ (4 * rate.n) * (min u (r.input.time.val + 1) - sigma) := by
          rw [hfields.2.1]
          exact hspan'
        _ = (4 * rate.n) * (min u (r.input.time.val + 2) - sigma) := by
          rw [hmin₁, hmin₂]
    · calc
        next.S + next.backlog ≤ Q + (min u (r.input.time.val + 1) - sigma) * D p := by
          rw [hfields.2.1, hfields.2.2.2]
          exact hmass'
        _ = Q + (min u (r.input.time.val + 2) - sigma) * D p := by
          rw [hmin₁, hmin₂]
    · rw [hfields.2.2.1, hfields.2.1]
      exact hdelta.1
    · rw [hfields.2.2.1]
      exact hdelta.2
  · have htimeCut : r.input.time.val + 1 < u := by
      have hnot : ¬ u ≤ r.input.time.val + 1 := by
        intro h
        exact hunoccupied (hchoiceStatus.mpr h)
      omega
    have hstateBusy : state.status ≠ .unoccupied := by
      intro hstateUnoccupied
      have hstarted := ActiveFollowerLifecycle.startRound_unoccupied
        rate.eta r.input.time state memory hvalidState hstateUnoccupied
      rw [hstart] at hstarted
      have heq := Prod.mk.inj (Except.ok.inj hstarted)
      exact hunoccupied (by simpa [heq.1] using hstateUnoccupied)
    have htime : M.val.sigma ≤ r.input.time.val := by
      by_contra hnot
      have hbad := ActiveFollowerLifecycle.interruptionDecision_incompatible_start
        rate.eta r.input.time state memory hstateBusy hvalidState M hdown
        (Nat.lt_of_not_ge hnot)
      unfold ActiveFollowerLifecycle.startRound at hstart
      rw [hbad] at hstart
      cases hstart
    have hmassState : state.S + state.backlog ≤ r.input.time.val * D p := by
      have helapsed := Nat.sub_le_sub_right
        (Nat.min_le_right u (r.input.time.val + 1)) sigma
      have htimeBound : sigma ≤ r.input.time.val + 1 :=
        hsigma.trans (Nat.min_le_right _ _)
      calc
        state.S + state.backlog ≤ Q +
            (min u (r.input.time.val + 1) - sigma) * D p := by simpa [u, r, R] using hmass
        _ ≤ (sigma - 1) * D p + (r.input.time.val + 1 - sigma) * D p :=
          Nat.add_le_add hqueueStart (Nat.mul_le_mul_right (D p) helapsed)
        _ = r.input.time.val * D p := by
          rw [← Nat.add_mul]
          congr 1
          omega
    have hchoiceMass : choice.S + choice.backlog ≤ r.input.time.val * D p := by
      have hS := congrArg (fun reply => reply.2.1) hchoiceReply
      have hbacklog := congrArg (fun reply => reply.2.2.2) hchoiceReply
      change choice.S = state.S at hS
      change choice.backlog = state.backlog at hbacklog
      rw [hS, hbacklog]
      exact hmassState
    -- The accepted actual follower output retains a successful checked
    -- service result on this very physical row.
    let prepared := ReferenceActivePhysicalStep.prepare r.input
    let f := prepared.followers.followers i
    let own := prepared.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    have hfinishConfig :
        (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView f own).configuration =
          .ordinary next nextMemory := by
      have h := hnext'
      rw [r.output_eq] at h
      change (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView f own).configuration =
        .ordinary next nextMemory at h
      exact h
    obtain ⟨choiceActual, memoryActual, post, hactual, hrecord, hfinish, _hrecordedInput,
      _hrecordedDown⟩ :=
      ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
        prepared.coordinator.downView f own next nextMemory hfinishConfig
    have hactualEq : choiceActual = choice ∧ memoryActual = choiceMemory := by
      have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hactual.symm.trans hpreparedActual)
      exact ⟨heq.1, heq.2⟩
    have hrecord' := hrecord
    have hchoiceActualEq : choiceActual = choice := hactualEq.1
    have hmemoryActualEq : memoryActual = choiceMemory := hactualEq.2
    subst choiceActual
    subst memoryActual
    have hrecordService :
        DeclaredFollowerLocalRound.recordOrServiceThenDown rate f.follower f.row
          f.activation f.time f.active f.arm own choice = .ok post := by
      rw [ReferenceActivePhysicalStep.recordFollower_result] at hrecord'
      unfold ReferenceDownReception.loggingThenReferenceDown at hrecord'
      simp only [dite_eq_right hunoccupied] at hrecord'
      exact hrecord'
    have hserviceStatus : choice.status.occupied := by
      cases hstatus : choice.status <;> simp_all [ActiveRoundActions.FollowerStatus.occupied]
    let checked := ActiveFollowerQueueOperation.checkedService
      rate.eta rate.sourceCap rate.n rate.n_scale f.follower f.row f.activation f.time own choice
    have hserviceData : ∃ result,
        checked = .success result ∧ result.output = post ∧
          result.arrival ≤ D p ∧ result.service ≤ D p ∧
          result.service = min (4 * rate.n) (choice.backlog + result.arrival) := by
      cases hstatus : checked with
      | failure =>
          simp [checked, DeclaredFollowerLocalRound.recordOrServiceThenDown,
            hunoccupied, hstatus] at hrecordService
      | success result =>
          have hpost : result.output = post := by
            have h := hrecordService
            simp [DeclaredFollowerLocalRound.recordOrServiceThenDown,
              hunoccupied, checked, hstatus] at h
            exact h
          have hformula : result.service =
              min (4 * rate.n) (choice.backlog + result.arrival) := by
            cases hchoiceStatus' : choice.status with
            | unoccupied => exact (hunoccupied hchoiceStatus').elim
            | pending =>
                have ha := result.action
                simp only [ActiveFollowerQueueOperation.serviceAction, hchoiceStatus'] at ha
                rcases ha with ⟨_, M', _, _, _, hlocal⟩
                simpa [ActiveFollowerQueueOperation.localService,
                  ActiveFollowerQueueOperation.serviceCapacity,
                  Bandits.Support.CappedService.service] using hlocal
            | released =>
                have ha := result.action
                simp only [ActiveFollowerQueueOperation.serviceAction, hchoiceStatus'] at ha
                rcases ha with ⟨_, M', _, _, _, hlocal⟩
                simpa [ActiveFollowerQueueOperation.localService,
                  ActiveFollowerQueueOperation.serviceCapacity,
                  Bandits.Support.CappedService.service] using hlocal
          exact ⟨result, rfl, hpost, result.arrival_le_D, result.service_le_D, hformula⟩
    obtain ⟨serviced, hserviceCase, hpost, harrivalBound, hserviceBound, hserviceEq⟩ :=
      hserviceData
    let arrival := serviced.arrival
    let service := min (4 * rate.n) (choice.backlog + arrival)
    have hserviceLocal :
        ActiveFollowerQueueOperation.localService rate.n choice.backlog arrival = service := by
      simp [service, ActiveFollowerQueueOperation.localService,
        ActiveFollowerQueueOperation.serviceCapacity, Bandits.Support.CappedService.service]
    have hserviceOutput : serviced.output =
        ActiveFollowerQueueOperation.serviceUpdate rate.n choice serviced.arrival := by
      rw [serviced.queueUpdate]
      simp [ActiveFollowerQueueOperation.serviceOutput, hserviceStatus]
    have hregs := ActiveFollowerQueueOperation.serviceUpdate_register_equations
      rate.n choice serviced.arrival
    have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
      f.follower f.row f.time own choice post next choiceMemory nextMemory hfinish
    have hscore : next.S = choice.S + service := by
      have hS := congrArg (fun fields => fields.2.1) hframe.1
      change next.S = post.S at hS
      rw [← hpost, hserviceOutput] at hS
      rw [hregs.1, hserviceLocal] at hS
      exact hS
    have hdeltaNext : next.delta = service := by
      have hδ := congrArg (fun fields => fields.2.2.1) hframe.1
      change next.delta = post.delta at hδ
      rw [← hpost, hserviceOutput] at hδ
      rw [hregs.2.1, hserviceLocal] at hδ
      exact hδ
    have hbacklogNext : next.backlog + service = choice.backlog + arrival := by
      have hB := congrArg (fun fields => fields.2.2.2) hframe.1
      change next.backlog = post.backlog at hB
      rw [← hpost, hserviceOutput] at hB
      calc
        next.backlog + service =
            (ActiveFollowerQueueOperation.serviceUpdate rate.n choice serviced.arrival).backlog +
              ActiveFollowerQueueOperation.localService rate.n choice.backlog arrival := by
          rw [hB, hserviceLocal]
        _ = choice.backlog + arrival := hregs.2.2
    have harrivalBound' : arrival ≤ D p := by simpa [arrival] using harrivalBound
    have hserviceBound' : service ≤ 4 * rate.n := Nat.min_le_left _ _
    have hconservation : next.S + next.backlog =
        choice.S + choice.backlog + arrival := by
      omega
    have hdownNext : next.lastDown = some M := by
      have hlast := congrArg Prod.fst hframe.1
      change next.lastDown = post.lastDown at hlast
      rw [← hpost, hserviceOutput] at hlast
      have hpreserve := ActiveFollowerQueueOperation.serviceUpdate_preserves_other_registers
        rate.n choice serviced.arrival
      exact hlast.trans (hpreserve.1.trans hchoiceDown)
    have hmin₁ : min u (r.input.time.val + 1) = r.input.time.val + 1 :=
      Nat.min_eq_right (Nat.le_of_lt htimeCut)
    have hmin₂ : min u (r.input.time.val + 2) = r.input.time.val + 2 :=
      Nat.min_eq_right (by omega)
    have hcount : (r.input.time.val + 2) - sigma =
        (r.input.time.val + 1 - sigma) + 1 := by
      have htimeBound : sigma ≤ r.input.time.val + 1 :=
        hsigma.trans (Nat.min_le_right _ _)
      calc
        r.input.time.val + 2 - sigma =
            1 + (r.input.time.val + 1) - sigma := by omega
        _ = 1 + (r.input.time.val + 1 - sigma) := Nat.add_sub_assoc htimeBound 1
        _ = (r.input.time.val + 1 - sigma) + 1 := Nat.add_comm _ _
    have hmin₂Target :
        min (FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val + 2) =
          r.input.time.val + 2 := by
      simpa [u, r, R, hrow] using hmin₂
    have hstartLe := hsigma
    have hcurrLen : min u (r.input.time.val + 1) - sigma =
        r.input.time.val + 1 - sigma := by rw [hmin₁]
    have hspanCurrent : state.S ≤
        (4 * rate.n) * (r.input.time.val + 1 - sigma) := by
      simpa [u, r, R, hrow, hmin₁] using hspan
    have hchoiceScoreEq := congrArg (fun fields => fields.2.1) hchoiceReply
    have hchoiceSpan : choice.S ≤
        (4 * rate.n) * (r.input.time.val + 1 - sigma) := by
      change choice.S = state.S at hchoiceScoreEq
      rw [hchoiceScoreEq]
      exact hspanCurrent
    have hnextDown : next.lastDown = some M := hdownNext
    refine ⟨hnextDown, ?_, ?_, ?_, ?_⟩
    · calc
        next.S = choice.S + service := hscore
        _ ≤ (4 * rate.n) * (r.input.time.val + 1 - sigma) + 4 * rate.n :=
          Nat.add_le_add hchoiceSpan hserviceBound'
        _ = (4 * rate.n) * ((r.input.time.val + 1 - sigma) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = (4 * rate.n) * (r.input.time.val + 2 - sigma) := by rw [← hcount]
        _ = (4 * rate.n) *
            (min (FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val].input.time.val + 2) - sigma) := by
          rw [hmin₂Target]
    · have hmassRelative : state.S + state.backlog ≤
          Q + (r.input.time.val + 1 - sigma) * D p := by
        simpa [u, r, R, hrow, hmin₁] using hmass
      have hchoiceRelative : choice.S + choice.backlog ≤
          Q + (r.input.time.val + 1 - sigma) * D p := by
        have hS := congrArg (fun fields => fields.2.1) hchoiceReply
        have hB := congrArg (fun fields => fields.2.2.2) hchoiceReply
        change choice.S = state.S at hS
        change choice.backlog = state.backlog at hB
        rw [hS, hB]
        exact hmassRelative
      calc
        next.S + next.backlog = choice.S + choice.backlog + arrival := hconservation
        _ ≤ (Q + (r.input.time.val + 1 - sigma) * D p) + D p :=
          Nat.add_le_add hchoiceRelative harrivalBound'
        _ = Q + (r.input.time.val + 2 - sigma) * D p := by
          rw [hcount, Nat.add_mul, Nat.one_mul]
          omega
        _ = Q +
            (min (FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val].input.time.val + 2) - sigma) * D p := by
          rw [hmin₂Target]
    · rw [hdeltaNext, hscore]
      omega
    · rw [hdeltaNext]
      exact hserviceBound'

/-! The following propagation theorem is the source-level fold interface. Its
seed bounds and calendar row/time facts are explicit so the caller must
produce them from the same accepted DOWN and original connected suffix. -/

/-- Propagate an actual checked-recovery seed through the complete connected
physical suffix up to an ordinary input carrying the same DOWN message. Each
intermediate state is obtained from the actual record output; the only step
premises are the bounds already established at that record's input. -/
theorem propagate_actual_follower_service_span
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) final)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (target : ReferencePrelaunchFollower.State p rate.eta)
    (targetMemory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (htarget : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary target targetMemory)
    (hdownTarget : target.lastDown = some M)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hjk : j.val < k.val)
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.next.followers i =
        .ordinary seed seedMemory)
    (hseedDown : seed.lastDown = some M)
    (Q sigma cutoff : ℕ)
    (row : CompletePublicTable.CompleteRow p) (start : ℕ)
    (hcutoff : cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
    (hseedSpan : seed.S ≤ (4 * rate.n) *
      (min cutoff
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val].input.time.val + 2) - sigma))
    (hseedMass : seed.S + seed.backlog ≤ Q +
      (min cutoff
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val].input.time.val + 2) - sigma) * D p)
    (hseedDelta : seed.delta ≤ seed.S ∧ seed.delta ≤ 4 * rate.n)
    (hseedSigma : sigma ≤ min cutoff
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j.val].input.time.val + 2))
    (hpositive : 1 ≤ sigma)
    (hqueueStart : Q ≤ (sigma - 1) * D p)
    (hrow : ∀ n (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[n].input.row = row)
    (htime : ∀ n (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[n].input.time.val = start + n) :
    target.S ≤ (4 * rate.n) *
        (min cutoff
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val + 1) - sigma) ∧
      target.S + target.backlog ≤ Q +
        (min cutoff
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val + 1) - sigma) * D p ∧
      target.delta ≤ target.S ∧ target.delta ≤ 4 * rate.n := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  have hprefix : ReferenceActivePhysicalHorizon.Connected initial (R.take k.val)
      R[k.val].input.state := by
    exact ReferenceFollowerReplyChronology.connected_take_to_input hchain k.val k.isLt
  have hjle : j.val + 1 ≤ k.val := by omega
  have hjnext : j.val + 1 < R.length := lt_of_le_of_lt hjle k.isLt
  have hseedAdjacent : R[j.val + 1].input.state.followers i = .ordinary seed seedMemory := by
    have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output
      hchain j.val j.isLt
    rw [List.drop_eq_getElem_cons hjnext] at hdrop
    have h := congrArg (fun state => state.followers i) hdrop.1
    rw [hseed] at h
    simpa [R] using h
  have hstates : ∀ n, (hlow : j.val + 1 ≤ n) → (hhigh : n ≤ k.val) →
      (hn : n < R.length) →
      ∃ F memory,
        (R[n]'hn).input.state.followers i = .ordinary F memory ∧ F.lastDown = some M ∧
        F.S ≤ (4 * rate.n) * (min cutoff ((R[n]'hn).input.time.val + 1) - sigma) ∧
        F.S + F.backlog ≤ Q +
          (min cutoff ((R[n]'hn).input.time.val + 1) - sigma) * D p ∧
        F.delta ≤ F.S ∧ F.delta ≤ 4 * rate.n ∧
        sigma ≤ min cutoff ((R[n]'hn).input.time.val + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hlow hhigh hn
      by_cases hbase : n = j.val + 1
      · subst n
        have hjtime : R[j.val].input.time.val + 2 = R[j.val + 1].input.time.val + 1 := by
          have h₁ := htime j.val j.isLt
          have h₂ := htime (j.val + 1) hjnext
          change R[j.val].input.time.val = start + j.val at h₁
          change R[j.val + 1].input.time.val = start + (j.val + 1) at h₂
          rw [h₁, h₂]
          simp [Nat.add_assoc]
        refine ⟨seed, seedMemory, hseedAdjacent, hseedDown, ?_, ?_, hseedDelta.1,
          hseedDelta.2, ?_⟩
        · simpa [R, hjtime] using hseedSpan
        · simpa [R, hjtime] using hseedMass
        · simpa [R, hjtime] using hseedSigma
      · have hprev : j.val + 1 ≤ n - 1 := by omega
        have hprevHigh : n - 1 ≤ k.val := by omega
        obtain ⟨before, beforeMemory, hbefore, hbeforeDown, hbeforeSpan, hbeforeMass,
          hbeforeDelta, hbeforeCap, hbeforeSigma⟩ := ih (n - 1) (by omega) hprev hprevHigh
            (by omega)
        have hrecordLt : n - 1 < k.val := by omega
        have hrecordLen : n - 1 < R.length := by omega
        let currentIndex : Fin R.length := ⟨n - 1, hrecordLen⟩
        have htakeIndex : n - 1 < (R.take k.val).length := by
          simp only [List.length_take]
          omega
        obtain ⟨next, nextMemory, hnextTake, hnextBound⟩ :=
          ReferenceFollowerReplyChronology.connected_output_chronology
            hprefix i target targetMemory htarget (n - 1) htakeIndex
        have hnext : R[n - 1].output.next.followers i = .ordinary next nextMemory := by
          rw [← List.getElem_take' (hj := hrecordLt)] at hnextTake
          exact hnextTake
        obtain ⟨actualBefore, actualMemory, hactualBefore, hmono, _hfreeze, _happlied⟩ :=
          ReferenceFollowerReplyChronology.record_ordinary_chronology
            R[n - 1] i next nextMemory hnext
        have hbeforeEq : actualBefore = before ∧ actualMemory = beforeMemory := by
          have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hactualBefore.symm.trans hbefore)
          exact ⟨heq.1, heq.2⟩
        have hmono' : ReferencePrelaunchFollower.acceptedStart before ≤
            ReferencePrelaunchFollower.acceptedStart next := by
          rw [← hbeforeEq.1]
          exact hmono
        have hbeforeStart : ReferencePrelaunchFollower.acceptedStart before = M.val.sigma := by
          simp [ReferencePrelaunchFollower.acceptedStart, hbeforeDown]
        have htargetStart : ReferencePrelaunchFollower.acceptedStart target = M.val.sigma := by
          simp [ReferencePrelaunchFollower.acceptedStart, hdownTarget]
        have hnextStart : ReferencePrelaunchFollower.acceptedStart next = M.val.sigma := by
          omega
        have hrow' : R[n - 1].input.row = row := hrow (n - 1) hrecordLen
        have htimeNext : R[n].input.time.val = R[n - 1].input.time.val + 1 := by
          have h₁ := htime (n - 1) hrecordLen
          have h₂ := htime n hn
          change R[n - 1].input.time.val = start + (n - 1) at h₁
          change R[n].input.time.val = start + n at h₂
          omega
        have hstep := actual_follower_service_step rewards C_star C_h source
          currentIndex i row before beforeMemory M next nextMemory hbefore hbeforeDown
          hrow' hnext hnextStart Q sigma
          (by simpa [R, currentIndex, hcutoff, hrow'] using hbeforeSpan)
          (by simpa [R, currentIndex, hcutoff, hrow'] using hbeforeMass)
          ⟨hbeforeDelta, hbeforeCap⟩
          (by simpa [R, hcutoff, hrow'] using hbeforeSigma) hpositive hqueueStart
        have hnextDown := hstep.1
        have hnextSpan : next.S ≤ (4 * rate.n) *
            (min cutoff (R[n].input.time.val + 1) - sigma) := by
          have h := hstep.2.1
          simpa [R, currentIndex, hcutoff, hrow', htimeNext] using h
        have hnextMass : next.S + next.backlog ≤ Q +
            (min cutoff (R[n].input.time.val + 1) - sigma) * D p := by
          have h := hstep.2.2.1
          simpa [R, currentIndex, hcutoff, hrow', htimeNext] using h
        have hnextDelta : next.delta ≤ next.S ∧ next.delta ≤ 4 * rate.n := by
          exact ⟨hstep.2.2.2.1, hstep.2.2.2.2⟩
        have hnextSigma : sigma ≤ min cutoff (R[n].input.time.val + 1) := by
          have hmin : min cutoff (R[n - 1].input.time.val + 1) ≤
              min cutoff (R[n - 1].input.time.val + 2) := by
            exact min_le_min le_rfl (Nat.le_succ _)
          have hmin' : min cutoff (R[n - 1].input.time.val + 1) ≤
              min cutoff (R[n].input.time.val + 1) := by
            rw [htimeNext]
            exact hmin
          exact hbeforeSigma.trans hmin'
        have hadj : R[n].input.state = R[n - 1].output.next := by
          have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output
            hchain (n - 1) hrecordLen
          rw [show n - 1 + 1 = n by omega] at hdrop
          rw [List.drop_eq_getElem_cons (show n < R.length by omega)] at hdrop
          exact hdrop.1
        have hinputNext : R[n].input.state.followers i = .ordinary next nextMemory := by
          rw [hadj]
          exact hnext
        exact ⟨next, nextMemory, hinputNext, hnextDown, hnextSpan, hnextMass,
          hnextDelta.1, hnextDelta.2, hnextSigma⟩
  obtain ⟨last, lastMemory, hlast, _hlastDown, hspan, hmass, hdelta, hcap, _hsigma⟩ :=
    hstates k.val (by omega) le_rfl k.isLt
  have hlastEq : last = target ∧ lastMemory = targetMemory := by
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hlast.symm.trans (by simpa [R] using htarget))
    exact ⟨heq.1, heq.2⟩
  rcases hlastEq with ⟨rfl, rfl⟩
  exact ⟨hspan, hmass, hdelta, hcap⟩


/-- A retained accepted DOWN and an actual ordinary output expose the same
checked recovery registers after the release and proposal-read frame. -/
private theorem retained_down_service_seed
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i M)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary next nextMemory) :
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row)
    next.lastDown = some M ∧
      next.S ≤ (4 * rate.n) * (min u (record.input.time.val + 2) - M.val.sigma) ∧
      next.S + next.backlog ≤
        M.val.q + (min u (record.input.time.val + 2) - M.val.sigma) * D p ∧
      next.delta ≤ next.S ∧ next.delta ≤ 4 * rate.n ∧
      M.val.sigma ≤ min u (record.input.time.val + 2) := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hlogged, hcut, haccepted⟩ := hretained
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    record i logged cut after raw M scan registers lastService hlogged hcut haccepted
  have halign := record.output.preparation.follower_alignment i
  rw [halign.1, halign.2.1, halign.2.2.1] at htransition
  have hend := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint
    i record.input.row record.input.time _ logged after raw M scan registers lastService htransition
  obtain ⟨_hparsed, hchecked, hinterval, _htime, _hhorizon, _hraw, hafter⟩ :=
    ActiveFollowerDownAcceptance.downTransition_accepted_checked p i record.input.row
      record.input.time _ rate logged after raw M scan registers lastService htransition
  have hbounds := checked_recovery_service_conservation M logged scan.endpoint hinterval
    ⟨registers, lastService⟩ hchecked
  obtain ⟨choice, choiceMemory, logged', hconfiguration, hunoccupied, hlogging,
    hlogged', hcutEq⟩ := ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      record i cut hcut
  have hsameLogged : logged' = logged := Option.some.inj (hlogged'.symm.trans hlogged)
  subst logged'
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record
  let prepared := record.output.preparation.followers.followers i
  let view := record.output.preparation.coordinator.downView
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    rw [← hfinish]
    have h := hnext
    rw [record.output_eq] at h ⊢
    exact h
  obtain ⟨choice', memory', post, hchoice', hrecord, hrelease, _hdi, _hd⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory hout
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hconfiguration.symm.trans hchoice')
  rcases heq with ⟨rfl, rfl⟩
  have hpost : post = after := by
    have hlogging' : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
        prepared.activation prepared.time (prepared.arm, observation) choice = .ok logged := hlogging
    have hcutEq' : cut = ReferenceDownReception.referenceDownCut p view prepared.follower
        prepared.row prepared.time observation rate logged := hcutEq
    have hr := hrecord
    simp only [ReferenceActivePhysicalStep.recordFollower, hunoccupied, dite_true,
      hlogging'] at hr
    rw [← hcutEq', haccepted] at hr
    exact (Except.ok.inj hr).symm
  subst post
  have hframe := (ReferenceFollowerReplyChronology.releaseAndFinish_frame
    prepared.follower prepared.row prepared.time observation choice after next
    choiceMemory nextMemory hrelease).1
  have hdown : next.lastDown = after.lastDown := congrArg Prod.fst hframe
  have hS : next.S = after.S := congrArg (fun r => r.2.1) hframe
  have hdelta : next.delta = after.delta := congrArg (fun r => r.2.2.1) hframe
  have hq : next.backlog = after.backlog := congrArg (fun r => r.2.2.2) hframe
  rw [hafter] at hdown hS hdelta hq
  dsimp only at hdown hS hdelta hq hbounds ⊢
  rw [hdown, hS, hdelta, hq, ← hend]
  exact ⟨rfl, hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2, hinterval.le⟩

/-- Assignment-relative service and conservation at an actual ordinary INPUT.
The installation, base vector and retained accepted DOWN are all produced on
the original complete suffix. No survival or supplied recovery seed is used. -/
theorem complete_ordinary_follower_input_service_span
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary state memory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (b j : Fin R.length) (P : ReferenceActivePhysicalStep.Payload rate)
      (beta : Fin (p.m - 1) → ℕ),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
      let sigma := P.sigma.val + 1
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[k.val].input.row)
      let L := min u (R[k.val].input.time.val + 1)
      0 < sigma ∧ ReferencePrelaunchFollower.acceptedStart state = sigma ∧
      P.queues (P.assignment.assigned i) ≤ (sigma - 1) * D p ∧
      beta i + P.queues (P.assignment.assigned i) ≤ (sigma - 1) * D p ∧
      state.S ≤ (4 * rate.n) * (L - sigma) ∧
      state.S + state.backlog ≤ P.queues (P.assignment.assigned i) + (L - sigma) * D p ∧
      state.delta ≤ state.S ∧ state.delta ≤ 4 * rate.n := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, _hmass, _hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_input_mass
      rewards C_star C_h source k i state memory hinput M hdown
  have hready := (ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source b).1
  obtain ⟨beta', hbase', hqueues, hassigned⟩ :=
    ReferenceAssignmentCollectionMassSteps.record_birth_mass_of_ready_credit R[b.val]
      (by
        intro old l saved hcollection a cut current hc hq
        unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hready
        rw [hcollection] at hready
        exact (hready a cut current hc hq).1) P hbirth
  have hbeta : beta' = beta := Option.some.inj (hbase'.symm.trans hbase)
  subst beta'
  have hstart : M.val.sigma = P.sigma.val + 1 := by
    rw [hmessage, P.downRecord_fields i]
  have hqueue : M.val.q = P.queues (P.assignment.assigned i) := by
    rw [hmessage, P.downRecord_initialQueue i]
  have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = P.sigma := by
    apply Fin.ext
    have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    rw [hstart] at h
    omega
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
  | some active =>
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
        dsimp only [start]
        omega
      let mode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let execution := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan mode
      have hrun : R = execution.records :=
        ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch
      have hchain : ReferenceActivePhysicalHorizon.Connected active R execution.finalState := by
        rw [hrun]
        exact execution.connected
      let row := source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      have hrow : ∀ n (hn : n < R.length), R[n].input.row = row := by
        intro n hn
        have hmem : R[n] ∈ execution.records := by rw [← hrun]; exact List.getElem_mem hn
        obtain ⟨hr, hs, _⟩ := ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (p.T - start) hspan mode R[n] hmem
        change R[n].input.rows R[n].input.selected = row
        rw [hr, hs]
      have htime : ∀ n (hn : n < R.length), R[n].input.time.val = start + n := by
        intro n hn
        exact ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨n, hn⟩
      have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hchain k.val k.isLt
      have hjtake : j.val < (R.take k.val).length := by
        rw [List.length_take]
        exact lt_min hjk j.isLt
      obtain ⟨seed, seedMemory, hseedTake, _hseedStart⟩ :=
        ReferenceFollowerReplyChronology.connected_output_chronology
          hprefix i state memory hinput j.val hjtake
      have hseed : R[j.val].output.next.followers i = .ordinary seed seedMemory := by
        rw [← List.getElem_take' (hj := hjk)] at hseedTake
        exact hseedTake
      have hb := retained_down_service_seed R[j.val] i M hretained seed seedMemory hseed
      dsimp only at hb
      obtain ⟨hseedDown, hseedS, hseedQ, hseedDelta, hseedCap, hseedSigma⟩ := hb
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
      have hcutoff : u = FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) := by rw [hstartP]
      rw [hstartP, hrow j.val j.isLt, hstart] at hseedS hseedQ hseedSigma
      rw [hqueue] at hseedQ
      have hresult := propagate_actual_follower_service_span rewards C_star C_h source
        active execution.finalState hchain k i state memory M hinput hdown j hjk seed seedMemory
        hseed hseedDown (P.queues (P.assignment.assigned i)) (P.sigma.val + 1) u row start
        hcutoff hseedS hseedQ ⟨hseedDelta, hseedCap⟩ hseedSigma (by omega)
        (by simpa only [Nat.add_sub_cancel] using hqueues (P.assignment.assigned i)) hrow htime
      refine ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, ?_⟩
      dsimp only
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · simp only [ReferencePrelaunchFollower.acceptedStart, hdown, hstart]
      · simpa only [Nat.add_sub_cancel] using hqueues (P.assignment.assigned i)
      · simpa only [Nat.add_sub_cancel] using hassigned i
      · have hrowK : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row = row := hrow k.val k.isLt
        simpa only [u, hrowK] using hresult


/-- PREPARE preserves the same assignment-relative INPUT fields at actual
CHOICE, with the same installation, base scores and retained DOWN witnesses. -/
theorem complete_ordinary_follower_choice_service_span
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] i).configuration = .ordinary choice memory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : choice.lastDown = some M) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (b j : Fin R.length) (P : ReferenceActivePhysicalStep.Payload rate)
      (beta : Fin (p.m - 1) → ℕ),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
      let sigma := P.sigma.val + 1
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[k.val].input.row)
      let L := min u (R[k.val].input.time.val + 1)
      0 < sigma ∧ ReferencePrelaunchFollower.acceptedStart choice = sigma ∧
      P.queues (P.assignment.assigned i) ≤ (sigma - 1) * D p ∧
      beta i + P.queues (P.assignment.assigned i) ≤ (sigma - 1) * D p ∧
      choice.S ≤ (4 * rate.n) * (L - sigma) ∧
      choice.S + choice.backlog ≤ P.queues (P.assignment.assigned i) + (L - sigma) * D p ∧
      choice.delta ≤ choice.S ∧ choice.delta ≤ 4 * rate.n := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨before, beforeMemory, hinput, hreply, _hstatus⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R[k.val] i choice memory hchoice
  have hbeforeDown : before.lastDown = some M := (congrArg Prod.fst hreply).symm.trans hdown
  obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, hdata⟩ :=
    complete_ordinary_follower_input_service_span rewards C_star C_h source k i before
      beforeMemory hinput M hbeforeDown
  have hlast : choice.lastDown = before.lastDown := congrArg Prod.fst hreply
  have hS : choice.S = before.S := congrArg (fun r => r.2.1) hreply
  have hdelta : choice.delta = before.delta := congrArg (fun r => r.2.2.1) hreply
  have hq : choice.backlog = before.backlog := congrArg (fun r => r.2.2.2) hreply
  refine ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, ?_⟩
  dsimp only at hdata ⊢
  simpa only [ReferencePrelaunchFollower.acceptedStart, hlast, hS, hdelta, hq] using hdata

/-- The actually accepted current UP inherits the assignment-relative bounds
of its actual sender input. Its birth is the same current collection payload,
and its full nonzero installed queue and retained base vector remain visible.
No condition is imposed on the sender's final output on this round. -/
theorem complete_accepted_up_service_span
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let sigma := c.payload.sigma.val + 1
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[k.val].input.row)
    ∃ (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      R[k.val].input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      0 < sigma ∧ ReferencePrelaunchFollower.acceptedStart F = sigma ∧
      U.val.sigma = sigma ∧ c.preLedger.sigma = sigma ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.payload.queues (c.payload.assignment.assigned i) ≤ (sigma - 1) * D p ∧
      c.preLedger.baseScore i + c.payload.queues (c.payload.assignment.assigned i) ≤
        (sigma - 1) * D p ∧
      U.val.S ≤ (4 * rate.n) * (u - sigma) ∧
      U.val.S + U.val.q ≤ c.payload.queues (c.payload.assignment.assigned i) +
        (u - sigma) * D p ∧
      U.val.delta ≤ U.val.S ∧ U.val.delta ≤ 4 * rate.n := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨bJoin, _jJoin, F, mu, _hJoinOrder, _hJoinBefore, hbirthJoin, hbaseJoin,
    _hretainedJoin, hinput, hlast, hUsigma, hledgerSigma, hUS, hUdelta, hUq,
    _hmass, _hdelta, _hreplyMass, _hreplyDelta⟩ :=
    ReferenceCompleteAcceptedUpBaseCredit.complete_accepted_up_base_credit
      rewards C_star C_h source k c hchoice i U haccepted
  obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, hdata⟩ :=
    complete_ordinary_follower_input_service_span rewards C_star C_h source k i F mu
      hinput (c.payload.downRecord i) hlast
  have hpayloadSigma : P.sigma.val = c.payload.sigma.val := by
    have heq := congrArg
      (fun M : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta) => M.val.sigma) hmessage
    rw [P.downRecord_fields i, c.payload.downRecord_fields i] at heq
    change c.payload.sigma.val + 1 = P.sigma.val + 1 at heq
    omega
  have htime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] P hbirth
  have htimeJoin := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[bJoin.val] c.payload hbirthJoin
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b] at htime
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source bJoin] at htimeJoin
  have hindex : bJoin = b := by apply Fin.ext; omega
  subst bJoin
  have hpayload : P = c.payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      R[b.val] P c.payload hbirth hbirthJoin
  subst P
  have hbeta : beta = c.preLedger.baseScore := Option.some.inj (hbase.symm.trans hbaseJoin)
  subst beta
  dsimp only at hdata ⊢
  obtain ⟨hpositive, hcurrentStart, hQ, hbaseQ, hS, hmass, hdeltaS, hdeltaC⟩ := hdata
  refine ⟨b, j, F, mu, hbj, hjk, hbirth, hbase, hretained, hinput, hlast,
    hpositive, hcurrentStart, hUsigma.trans hledgerSigma, hledgerSigma,
    hUS, hUdelta, hUq, hQ, hbaseQ, ?_, ?_, ?_, ?_⟩
  · rw [hUS]
    exact hS.trans (Nat.mul_le_mul_left (4 * rate.n)
      (Nat.sub_le_sub_right (Nat.min_le_left _ _) _))
  · rw [hUS, hUq]
    exact hmass.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (D p)
      (Nat.sub_le_sub_right (Nat.min_le_left _ _) _)) _)
  · rw [hUdelta, hUS]
    exact hdeltaS
  · rw [hUdelta]
    exact hdeltaC

end Bandits.Support.ReferenceCompleteFollowerServiceSpan

end
