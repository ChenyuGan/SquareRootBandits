/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOrdinaryFollowerMass
public import Bandits.Support.ReferenceCarriedDownForwardTransition
public import Bandits.Support.ReferenceOccupiedServiceDomain

import Lean.Elab.Tactic.Omega

/-!
# Actual complete-suffix occupied service

From an ordinary actual CHOICE on the complete physical suffix, this module
produces the retained assignment mass and the successful occupied service,
record, release, and finish on that same physical round.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteOccupiedServiceForward

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceActivePhysicalStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual complete-suffix CHOICE with occupied status has a retained
DOWN from a successful actual StartRound. The same historical birth, base
vector, and retained event bound its input mass; that credit discharges the
actual occupied service leaf on this very record. -/
theorem complete_ordinary_occupied_service_forward
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] i).configuration =
          .ordinary choice choiceMemory)
    (hoccupied : choice.status ≠ .unoccupied) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := R[k.val]
    ∃ (Mdown : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)),
      choice.lastDown = some Mdown ∧
      Mdown.val.sigma ≤ r.input.time.val ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ∃ (b j : Fin R.length) (P : ReferenceActivePhysicalStep.Payload rate)
        (beta : Fin (p.m - 1) → ℕ),
        b.val ≤ j.val ∧ j.val < k.val ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] = some beta ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i Mdown ∧
        Mdown = P.downRecord i ∧
        beta i + choice.S + choice.backlog ≤
          min r.input.time.val
            (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) - 1) *
              D p ∧
        choice.delta ≤ D p ∧
        choice.S + choice.backlog ≤ r.input.time.val * D p ∧
        (let prepared := ReferenceActivePhysicalStep.prepare r.input
         let f := prepared.followers.followers i
         let own := prepared.feedback.observations
           (PublicDiscreteDraws.followerPlayer p.two_le_m i)
         let arrival := ActiveFollowerQueueOperation.rawArrival
           rate.eta i r.input.row r.input.time Mdown own
         let service := min (4 * rate.n) (choice.backlog + arrival)
         f.follower = i ∧ f.row = r.input.row ∧ f.time = r.input.time ∧
          f.activation = r.input.state.activations i ∧
          ∃ serviced next nextMemory,
            ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
              rate.n rate.n_scale f.follower f.row f.activation f.time own choice =
                .success serviced ∧
            serviced.arrival = arrival ∧ serviced.service = service ∧
            serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n choice arrival ∧
            arrival ≤ D p ∧ service ≤ D p ∧
            (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
              f.follower f.row f.activation f.time f.active f.arm own choice).result =
                .ok serviced.output ∧
            (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
              f.follower f.row f.activation f.time f.active f.arm own choice).downInput = none ∧
            (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
              f.follower f.row f.activation f.time f.active f.arm own choice).down = none ∧
            DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time
              own choice choiceMemory serviced.output = .ok (next, nextMemory) ∧
            ((ReferenceActivePhysicalStep.step r.input).followers i).configuration =
              .ordinary next nextMemory ∧
            ((ReferenceActivePhysicalStep.step r.input).followers i).failure = none ∧
            ((ReferenceActivePhysicalStep.step r.input).followers i).downInput = none ∧
            ((ReferenceActivePhysicalStep.step r.input).followers i).down = none ∧
            next.S = choice.S + service ∧ next.delta = service ∧
            next.backlog = choice.backlog + arrival - service ∧
            ((next.S, next.backlog) = Bandits.Support.QueueReplay.transition
              (ActiveFollowerQueueOperation.serviceCapacity rate.n)
              (choice.S, choice.backlog) (true, arrival)) ∧
            next.S + next.backlog = choice.S + choice.backlog + arrival ∧
            next.S + next.backlog ≤ (r.input.time.val + 1) * D p ∧
            ActiveFollowerLifecycle.localStateDomainValid next ∧
            next.lastDown = choice.lastDown ∧ next.buffer = choice.buffer ∧
            next.downBatch = choice.downBatch ∧
            next.initializationFailure = choice.initializationFailure ∧
            (next.status = .released ↔
              choice.status = .released ∨
                (choice.status = .pending ∧
                  ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                    own Mdown)) ∧
            (next.status = .pending ↔
              choice.status = .pending ∧
                ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                  own Mdown) ∧
            next.status ≠ .unoccupied ∧
            nextMemory.lastProposalRead = some ⟨r.input.time,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                r.input.row r.input.time⟩ ∧
        (r.output.followers i).configuration = .ordinary next nextMemory ∧
        (r.output.followers i).failure = none ∧
        (r.output.followers i).downInput = none ∧
        (r.output.followers i).down = none ∧
        r.output.next.followers i = .ordinary next nextMemory) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]
  have hprepared :
      (r.output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory := by
    simpa only [ReferenceFollowerFixedReply.actualChoice] using hchoice
  have hprepare :
      (DeclaredFollowerLocalRound.prepare rate i r.input.row
        (r.input.state.activations i) r.input.time (r.input.active i)
        (r.input.state.followers i)).configuration = .ordinary choice choiceMemory := by
    have h := hprepared
    rw [r.output_eq] at h
    change (DeclaredFollowerLocalRound.prepare rate i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i)).configuration = .ordinary choice choiceMemory at h
    exact h
  obtain ⟨before, beforeMemory, hinput, hstart, hprepareFrame, hbeforeUnoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i) choice choiceMemory hprepare
  have hbeforeOccupied : before.status ≠ .unoccupied := by
    intro hstatus
    exact hoccupied (hbeforeUnoccupied hstatus)
  have hpreparedDomains :=
    Bandits.Support.ReferenceCarriedDownForwardTransition.actual_prepare_local_domains
      rate r i choice choiceMemory hprepared
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta r.input.time
    before choice beforeMemory choiceMemory hstart
  have hbeforeDomain : ActiveFollowerLifecycle.localStateDomainValid before := by
    unfold ActiveFollowerLifecycle.localStateDomainValid at hpreparedDomains ⊢
    rcases hpreparedDomains.1 with ⟨hregisters, hbuffer, hdecoder⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ActiveFollowerLifecycle.serviceRegistersValid,
        hstartFrame.2.1, hstartFrame.2.2.1, hstartFrame.2.2.2.1] using hregisters
    · simpa only [ActiveFollowerLifecycle.localBufferValid,
        hstartFrame.2.2.2.2.2.1] using hbuffer
    · simpa only [ActiveFollowerLifecycle.downDecoderStateValid,
        hstartFrame.2.2.2.2.1] using hdecoder
  obtain ⟨Mdown, hdown, htime⟩ :
      ∃ (Mdown : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
        choice.lastDown = some Mdown ∧ Mdown.val.sigma ≤ r.input.time.val := by
    cases hrecord : before.lastDown with
    | none =>
        have hbad : ActiveFollowerLifecycle.startRound rate.eta r.input.time
            before beforeMemory = .error .missingAcceptedDown := by
          simp [ActiveFollowerLifecycle.startRound,
            ActiveFollowerLifecycle.interruptionDecision, hbeforeDomain,
            hbeforeOccupied, hrecord]
        rw [hbad] at hstart
        cases hstart
    | some M =>
        refine ⟨M, ?_, ?_⟩
        · rw [hstartFrame.1, hrecord]
        · by_contra hnot
          have hbad : ActiveFollowerLifecycle.startRound rate.eta r.input.time
              before beforeMemory = .error .incompatibleAcceptedDown := by
            simp [ActiveFollowerLifecycle.startRound,
              ActiveFollowerLifecycle.interruptionDecision, hbeforeDomain,
              hbeforeOccupied, hrecord, hnot]
          rw [hbad] at hstart
          cases hstart
  obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage,
    hchoiceMass, hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
      rewards C_star C_h source k i choice choiceMemory hchoice Mdown hdown
  have hmass : choice.S + choice.backlog ≤ r.input.time.val * D p := by
    calc
      choice.S + choice.backlog ≤ beta i + choice.S + choice.backlog := by omega
      _ ≤ min r.input.time.val
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) - 1) * D p :=
        hchoiceMass
      _ ≤ r.input.time.val * D p :=
        Nat.mul_le_mul_right (D p) (Nat.min_le_left _ _)
  have hpreparedStep :
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
    have h := hprepared
    rw [r.output_eq] at h
    change ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
      .ordinary choice choiceMemory at h
    exact h
  have htail := ReferenceOccupiedServiceDomain.occupied_tail_preserves_local_domain
    r.input i choice choiceMemory hpreparedStep hpreparedDomains.1 hmass hoccupied
    Mdown hdown htime
  rcases htail with
    ⟨hfollower, hrow, htimeField, hactivation, serviced, next, nextMemory,
      hchecked, harrival, hservice, hserviceOutput, harrivalBound, hserviceBound,
      hrecordResult, hrecordDownInput, hrecordDown, hreleaseFinish,
      hstepConfiguration, hstepFailure, hstepDownInput, hstepDown,
      hscore, hdeltaNext, hbacklogNext, hqueueTransition, hconservation, hmassNext,
      hnextDomain, hnextDown, hbufferNext, hbatchNext, hinitializationFailure,
      hreleased, hpending, hnextOccupied, hproposalRead⟩
  have houtputConfiguration :
      (r.output.followers i).configuration = .ordinary next nextMemory := by
    simpa only [r.output_eq] using hstepConfiguration
  have houtputFailure : (r.output.followers i).failure = none := by
    simpa only [r.output_eq] using hstepFailure
  have houtputDownInput : (r.output.followers i).downInput = none := by
    simpa only [r.output_eq] using hstepDownInput
  have houtputDown : (r.output.followers i).down = none := by
    simpa only [r.output_eq] using hstepDown
  have hnextOutput : r.output.next.followers i = .ordinary next nextMemory := by
    rw [r.output_eq]
    calc
      (ReferenceActivePhysicalStep.step r.input).next.followers i =
          ((ReferenceActivePhysicalStep.step r.input).followers i).configuration :=
        (ReferenceActivePhysicalStep.step_next_fields r.input).2.2.2 i
      _ = .ordinary next nextMemory := hstepConfiguration
  refine ⟨Mdown, ?_⟩
  refine ⟨hdown, ?_⟩
  refine ⟨htime, ?_⟩
  refine ⟨hpreparedDomains.1, ?_⟩
  refine ⟨b, ?_⟩
  refine ⟨j, ?_⟩
  refine ⟨P, ?_⟩
  refine ⟨beta, ?_⟩
  refine ⟨hbj, ?_⟩
  refine ⟨hjk, ?_⟩
  refine ⟨hbirth, ?_⟩
  refine ⟨hbase, ?_⟩
  refine ⟨hretained, ?_⟩
  refine ⟨hmessage, ?_⟩
  refine ⟨hchoiceMass, ?_⟩
  refine ⟨hdelta, ?_⟩
  refine ⟨hmass, ?_⟩
  exact ⟨hfollower, hrow, htimeField, hactivation, serviced, next, nextMemory,
      hchecked, harrival, hservice, hserviceOutput, harrivalBound, hserviceBound,
      hrecordResult, hrecordDownInput, hrecordDown, hreleaseFinish,
      hstepConfiguration, hstepFailure, hstepDownInput, hstepDown,
      hscore, hdeltaNext, hbacklogNext, hqueueTransition, hconservation, hmassNext,
      hnextDomain, hnextDown, hbufferNext, hbatchNext, hinitializationFailure,
      hreleased, hpending, hnextOccupied, hproposalRead, houtputConfiguration,
      houtputFailure, houtputDownInput, houtputDown, hnextOutput⟩

end Bandits.Support.ReferenceCompleteOccupiedServiceForward

end
