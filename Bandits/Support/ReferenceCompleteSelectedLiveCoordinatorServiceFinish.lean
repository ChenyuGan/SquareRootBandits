/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorDataArrival
public import Bandits.Support.ReferenceCompleteCollectionDispatchCore

/-!
# Selected live coordinator service, confirmation, and finish

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

This result is pointwise at one selected live call in the original complete
physical suffix. It constructs the actual recorder result, the checked
complement service, the literal confirmation update, and the source clock
finish from the selected dispatch and its actual numerical mass inputs.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem servicePass_of_joint_mass
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (recording : CoordinatorRecordingOperation.Output p)
    (round : ℕ)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm registers.payload.slowSet,
      registers.complementScores j + owned.queue j ≤ round * D p)
    (hprevious : owned.previousServiceDomainValid)
    (hround : round + 1 ≤ p.T) :
    ∃ serviced : CoordinatorLiveServiceFinish.ServicedRegisters registers owned,
      CoordinatorLiveServiceFinish.servicePass registers owned recording = .ok serviced ∧
      serviced.recording = recording ∧
      (∀ j, serviced.arrival j =
        CoordinatorLiveServiceFinish.complementArrival registers.payload recording j) ∧
      (∀ j, serviced.service j = CappedService.service (4 * registers.payload.n)
        (owned.queue j) (serviced.arrival j)) ∧
      (∀ j, serviced.queue j = CappedService.residual (4 * registers.payload.n)
        (owned.queue j) (serviced.arrival j)) ∧
      (∀ j, serviced.score j = registers.complementScores j + serviced.service j) ∧
      (∀ j, serviced.previousService j = serviced.service j) ∧
      (∀ j, serviced.score j + serviced.queue j ≤ (round + 1) * D p) := by
  classical
  let arrival : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ :=
    fun j => CoordinatorLiveServiceFinish.complementArrival registers.payload recording j
  let service : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ :=
    fun j => CappedService.service (4 * registers.payload.n) (owned.queue j) (arrival j)
  let residual : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ :=
    fun j => CappedService.residual (4 * registers.payload.n) (owned.queue j) (arrival j)
  let score : CanonicalFastSampling.FastArm registers.payload.slowSet → ℕ :=
    fun j => registers.complementScores j + service j
  have hroundT : round ≤ p.T := by omega
  have hmassT : round * D p ≤ p.T * D p := Nat.mul_le_mul_right _ hroundT
  have hqueueInput : owned.queueDomainValid := by
    intro j
    exact (Nat.le_add_left (owned.queue j) (registers.complementScores j)).trans
      ((hcredit j).trans hmassT)
  have harrival : ∀ j, arrival j ≤ D p := by
    intro j
    change (if recording.gateArm = some j.1 then recording.rawArrival else 0) ≤ D p
    by_cases hgate : recording.gateArm = some j.1
    · simp [hgate, recording.rawArrival_le_D]
    · simp [hgate]
  have hcapacity : 4 * registers.payload.n ≤ D p := by
    rw [ReferenceActivePhysicalStep.payload_n_eq registers.payload]
    exact ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hservice : ∀ j, service j ≤ D p := by
    intro j
    exact (CappedService.service_le_capacity (4 * registers.payload.n)
      (owned.queue j) (arrival j)).trans hcapacity
  have hadvance : round * D p + D p = (round + 1) * D p := by
    rw [Nat.add_mul, one_mul]
  have htotal : ∀ j,
      score j + residual j ≤ (round + 1) * D p := by
    intro j
    have hconservation :
        score j + residual j =
          registers.complementScores j + owned.queue j + arrival j := by
      dsimp [score, service, residual]
      calc
        registers.complementScores j +
            CappedService.service (4 * registers.payload.n) (owned.queue j) (arrival j) +
            CappedService.residual (4 * registers.payload.n) (owned.queue j) (arrival j) =
          registers.complementScores j +
            (CappedService.residual (4 * registers.payload.n) (owned.queue j) (arrival j) +
              CappedService.service (4 * registers.payload.n) (owned.queue j) (arrival j)) := by omega
        _ = registers.complementScores j + (owned.queue j + arrival j) := by
          rw [CappedService.residual_add_service]
        _ = registers.complementScores j + owned.queue j + arrival j := by omega
    calc
      score j + residual j =
          registers.complementScores j + owned.queue j + arrival j := hconservation
      _ ≤ round * D p + D p := Nat.add_le_add (hcredit j) (harrival j)
      _ = (round + 1) * D p := hadvance
  have hscoreOut : ∀ j, score j ≤ p.T * D p := by
    intro j
    have h := htotal j
    have hbound : (round + 1) * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right _ hround
    dsimp [score, residual] at h ⊢
    omega
  have hqueueOut : ∀ j, residual j ≤ p.T * D p := by
    intro j
    exact (Nat.le_add_left (residual j) (score j)).trans
      ((htotal j).trans (Nat.mul_le_mul_right _ hround))
  let serviced : CoordinatorLiveServiceFinish.ServicedRegisters registers owned := {
    recording := recording
    arrival := arrival
    service := service
    queue := residual
    score := score
    previousService := service
    arrivalDomain := harrival
    serviceDomain := hservice
    queueDomain := hqueueOut
    scoreDomain := hscoreOut
    previousServiceDomain := hservice
    arrival_eq := fun _ => rfl
    service_eq := fun _ => rfl
    queue_eq := fun _ => rfl
    score_eq := fun _ => rfl
    previousService_eq := fun _ => rfl }
  have hpass : CoordinatorLiveServiceFinish.servicePass registers owned recording =
      .ok serviced := by
    unfold CoordinatorLiveServiceFinish.servicePass
    rw [dite_eq_left hqueueInput, dite_eq_left hprevious]
    rw [dite_eq_left harrival, dite_eq_left hservice]
    rw [dite_eq_left hscoreOut, dite_eq_left hqueueOut]
  refine ⟨serviced, hpass, ?_, ?_, ?_, ?_, ?_, ?_, htotal⟩
  · rfl
  · simpa only [serviced] using serviced.arrival_eq
  · simpa only [serviced] using serviced.service_eq
  · simpa only [serviced] using serviced.queue_eq
  · simpa only [serviced] using serviced.score_eq
  · simpa only [serviced] using serviced.previousService_eq

private theorem selected_live_tail
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (choiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time registers.complementWeights)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) =
        some recording)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm registers.payload.slowSet,
      registers.complementScores j + owned.queue j ≤ x.time.val * D p)
    (hprevious : owned.previousServiceDomainValid)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val started.clock)
    (htime : CoordinatorPhaseClock.finishRoundTimeValid x.time started.clock)
    (hsigma : started.clock.sigma ≠ none)
    (hu : started.clock.u = none)
    (hparameter : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val) :
    ∃ (serviced : CoordinatorLiveServiceFinish.ServicedRegisters registers owned)
      (pending : Finset (Fin (p.m - 1)))
      (finished : CoordinatorPhaseClock.FinishRoundResult p),
      CoordinatorLiveServiceFinish.servicePass registers owned recording = .ok serviced ∧
      owned.queueDomainValid ∧ owned.previousServiceDomainValid ∧
      serviced.recording = recording ∧
      (∀ j, serviced.arrival j =
        CoordinatorLiveServiceFinish.complementArrival registers.payload recording j) ∧
      (∀ j, serviced.service j = CappedService.service (4 * registers.payload.n)
        (owned.queue j) (serviced.arrival j)) ∧
      (∀ j, serviced.queue j = CappedService.residual (4 * registers.payload.n)
        (owned.queue j) (serviced.arrival j)) ∧
      (∀ j, serviced.score j = registers.complementScores j + serviced.service j) ∧
      (∀ j, serviced.previousService j = serviced.service j) ∧
      CoordinatorLocalArmChoice.confirmationUpdate registers.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some pending ∧
      pending =
        (if CoordinatorLocalArmChoice.downConfirmationEvent registers.payload started.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            x.time (x.row.2 x.time) prepared.coordinatorObservation then
          started.pending.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
            p.m_lt_K (x.row.2 x.time).1)
        else started.pending) ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
        .ok finished ∧
      ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started =
        ⟨.live {
            payload := registers.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := x.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          { queue := serviced.queue, previousService := serviced.previousService } base,
          x.state.upDecoderBank, none, some recording, none⟩ := by
  have hround : x.time.val + 1 ≤ p.T := by omega
  obtain ⟨serviced, hservice, hrecording, harrival, hserviceEq, hqueueEq,
    hscoreEq, hpreviousEq, _hmassAfter⟩ :=
    servicePass_of_joint_mass registers owned recording x.time.val hcredit hprevious hround
  have hqueue : owned.queueDomainValid := by
    intro j
    exact (Nat.le_add_left (owned.queue j) (registers.complementScores j)).trans
      ((hcredit j).trans (Nat.mul_le_mul_right _ (by omega)))
  have hconfirmationInputs := CoordinatorLocalArmChoice.confirmationInputsValid_mk
    registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    x.time choiceValid.time.assignment_started choiceValid.time.cutoff_after_start
  let pending : Finset (Fin (p.m - 1)) :=
    if CoordinatorLocalArmChoice.downConfirmationEvent registers.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time (x.row.2 x.time) prepared.coordinatorObservation then
      started.pending.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
        p.m_lt_K (x.row.2 x.time).1)
    else started.pending
  have hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation = some pending := by
    change CoordinatorLocalArmChoice.confirmationUpdateCore registers.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) prepared.coordinatorObservation = some pending
    simp only [CoordinatorLocalArmChoice.confirmationUpdateCore,
      dite_eq_left hconfirmationInputs, pending]
    rfl
  obtain ⟨finished, hfinish, _, _, _⟩ :=
    CoordinatorPhaseClock.finishRound_live_savedProposal p rate.eta.val x.time
      started.clock pending x.row hclock htime hsigma hu hparameter
  have hpost := ReferenceActivePhysicalStep.livePostChoice_success prepared registers owned base
    started recording serviced pending finished hrecord hservice hconfirmation hfinish
  exact ⟨serviced, pending, finished, hservice, hqueue, hprevious, hrecording,
    harrival, hserviceEq, hqueueEq, hscoreEq, hpreviousEq, hconfirmation, rfl,
    hfinish, hpost⟩

private def liveContinuationResultPair {x : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome x) :
    Option (CoordinatorPhaseClock.StartRoundResult p ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  match outcome with
  | .continuingChosen dispatched _ continuation _ =>
      some (dispatched.startResult, continuation.startRoundResult)
  | _ => none

private theorem live_dispatch_continuation_result
    {x : CoordinatorRoundDispatch.LiveInput p}
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation x.registers x.row)
    (selection : CoordinatorRoundDispatch.ArmSelection x.registers.payload
      dispatched.startResult x.registers.time x.registers.complementWeights x.row)
    (hstart : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (hactual : CoordinatorRoundDispatch.dispatchLive x =
      .continuingChosen dispatched hstart continuation selection) :
    continuation.startRoundResult = dispatched.startResult := by
  unfold CoordinatorRoundDispatch.dispatchLive at hactual
  dsimp only at hactual
  repeat' (first | split at hactual <;> try cases hactual)
  case h_3 =>
    rename_i actualDispatched hdispatch hinitialization
    by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        x.registers actualDispatched.startResult
    · simp only [dite_eq_left hframe] at hactual
      by_cases hpayload : x.registers.priorClock.sigma = some x.registers.payload.sigma
      · simp only [dite_eq_left hpayload] at hactual
        by_cases hgrid : x.registers.gridBoundary = x.registers.priorClock.g
        · simp only [dite_eq_left hgrid] at hactual
          by_cases hscore : x.registers.scoreDomainValid
          · simp only [dite_eq_left hscore] at hactual
            by_cases hqueue : x.ownedRegisters.queueDomainValid
            · simp only [dite_eq_left hqueue] at hactual
              by_cases hprevious : x.ownedRegisters.previousServiceDomainValid
              · simp only [dite_eq_left hprevious] at hactual
                by_cases hbase : ∀ i, x.followerBaseScore i ≤ p.T * D p
                · simp only [dite_eq_left hbase] at hactual
                  by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                      x.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        actualDispatched.startResult.clock.u) x.registers.time
                  · simp only [dite_eq_left hlive] at hactual
                    by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                        x.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          actualDispatched.startResult.clock.u)
                        x.registers.time x.registers.complementWeights
                    · simp only [dite_eq_left hchoice] at hactual
                      by_cases hboundary : actualDispatched.startResult.clock.g ≤ p.T + 1
                      · simp only [dite_eq_left hboundary] at hactual
                        by_cases henvelope : x.registers.complementEnvelopeValid
                        · simp only [dite_eq_left henvelope] at hactual
                          have hnonempty :=
                            CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                              x.registers.payload actualDispatched.startResult.pending
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                actualDispatched.startResult.clock.u)
                              x.registers.time x.registers.complementWeights x.row hchoice
                          split at hactual
                          · rename_i hselected
                            exact False.elim (hnonempty hselected)
                          · have hp := congrArg liveContinuationResultPair hactual
                            have hp' := by
                              simpa only [liveContinuationResultPair] using hp
                            have hpair := Option.some.inj hp'
                            have hfirst := congrArg Prod.fst hpair
                            have hsecond := congrArg Prod.snd hpair
                            exact hsecond.symm.trans hfirst
                        · simp only [dite_eq_right henvelope] at hactual
                          cases hactual
                      · simp only [dite_eq_right hboundary] at hactual
                        cases hactual
                    · simp only [dite_eq_right hchoice] at hactual
                      cases hactual
                  · simp only [dite_eq_right hlive] at hactual
                    cases hactual
                · simp only [dite_eq_right hbase] at hactual
                  cases hactual
              · simp only [dite_eq_right hprevious] at hactual
                cases hactual
            · simp only [dite_eq_right hqueue] at hactual
              cases hactual
          · simp only [dite_eq_right hscore] at hactual
            cases hactual
        · simp only [dite_eq_right hgrid] at hactual
          cases hactual
      · simp only [dite_eq_right hpayload] at hactual
        cases hactual
    · simp only [dite_eq_right hframe] at hactual
      cases hactual
  case h_1 =>
    rename_i actualDispatched hdispatch ledger hinitialization hchoice hboundary
      henvelope hselected
    have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      x.registers.payload actualDispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        actualDispatched.startResult.clock.u)
      x.registers.time x.registers.complementWeights x.row hchoice
    exact False.elim (hnonempty hselected)

private theorem actual_record_live_output
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (prepared : ReferenceActivePhysicalStep.PreparedRound record.input)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters registers owned)
    (recording : CoordinatorRecordingOperation.Output p)
    (hprepared : record.output.preparation = prepared)
    (hobserve : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started)
    (hpost : ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started =
      ⟨.live {
          payload := registers.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩) :
    record.output.coordinator =
      ⟨.live {
          payload := registers.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩ ∧
    record.output.next.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ∧
    record.output.next.upDecoderBank =
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).upDecoderBank := by
  have hpreparedStep : prepared = ReferenceActivePhysicalStep.prepare record.input := by
    calc
      prepared = record.output.preparation := hprepared.symm
      _ = (ReferenceActivePhysicalStep.step record.input).preparation := by
        rw [record.output_eq]
      _ = ReferenceActivePhysicalStep.prepare record.input := rfl
  have hcoordinator : record.output.coordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started := by
    calc
      record.output.coordinator = (ReferenceActivePhysicalStep.step record.input).coordinator := by
        rw [record.output_eq]
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := rfl
      _ = prepared.observeCoordinator := by rw [← hpreparedStep]
      _ = ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started := hobserve
  have hstepNext := ReferenceActivePhysicalStep.step_next_fields record.input
  have hnextCoordinator : record.output.next.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration := by
    calc
      record.output.next.coordinator = (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
        rw [record.output_eq]
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration := hstepNext.1
      _ = (prepared.observeCoordinator).configuration := by rw [← hpreparedStep]
      _ = (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration :=
        congrArg CoordinatorObservation.configuration hobserve
  have hnextBank : record.output.next.upDecoderBank =
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).upDecoderBank := by
    calc
      record.output.next.upDecoderBank = (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank := by
        rw [record.output_eq]
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.upDecoderBank := hstepNext.2.1
      _ = (prepared.observeCoordinator).upDecoderBank := by rw [← hpreparedStep]
      _ = (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).upDecoderBank :=
        congrArg CoordinatorObservation.upDecoderBank hobserve
  exact ⟨hcoordinator.trans hpost, hnextCoordinator, hnextBank⟩

theorem complete_selected_live_coordinator_service_finish
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      let x := r.input
      ∀ (v : ReferenceActivePhysicalStep.Selection x),
        r.output.preparation.coordinator.selection = some v →
        CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
          x.time →
        ∃ (a : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters a)
          (base : Fin (p.m - 1) → ℕ)
          (started : CoordinatorPhaseClock.StartRoundResult p),
          (match r.output.preparation.coordinator with
            | .first (.chosen installed _) =>
                a = installed.registers ∧ HEq q installed.ownedRegisters ∧
                  base = installed.followerBaseScore ∧
                  started = installed.startRoundResult
            | .live registers owned oldBase (.continuingChosen dispatched _ _ _) =>
                a = ReferenceActivePhysicalStep.liveRegistersAt registers x.time ∧
                  HEq q (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) ∧
                  base = oldBase ∧ started = dispatched.startResult
            | .collection _ _ _ _
                (.laterChosen _ _ roundStart _ _ _ _ _ _ installation _) =>
                a = installation.registers ∧ HEq q installation.ownedRegisters ∧
                  base = installation.retainedBaseScore ∧ started = roundStart
            | _ => False) ∧
          ∃ (valid : CoordinatorRecordingOperation.InputsValid
              (ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)) )
            (o : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters a q)
            (pending : Finset (Fin (p.m - 1)))
            (finished : CoordinatorPhaseClock.FinishRoundResult p),
            let call := ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)
            let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
              (((rewards x.time v.arm).val : ℝ) / (D p : ℝ)) /
              CanonicalRecordingRates.xi p rate.eta.val v.view.payload.anchor v.arm)
            let G0 : Prop :=
              CoordinatorRecordingOperation.selectedSlot call = PublicDiscreteDraws.dataSlot ∧
              CoordinatorRecordingOperation.selectedRecorder call =
                ActiveRoundActions.coordinator p.two_le_m ∧
              ¬ CoordinatorRecordingOperation.isFrozen call ∧
              CoordinatorRecordingOperation.ownsArm call.mode call.ownArm ∧
              CoordinatorRecordingOperation.ownMaskPasses call ∧
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                ((x.row.2 x.time).1)).val ≤
                CoordinatorRecordingOperation.coordinatorThreshold call valid
            CoordinatorRecordingOperation.run call = some o ∧
            r.output.coordinator.recording = some o ∧
            o.gateArm = (if G0 then some v.arm else none) ∧
            o.rawArrival = (if G0 then F0 else 0) ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) v.arm =
                some (if G0 then F0 else 0) ∧
            ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) =
                CoordinatorRecorderComplementBridge.recorderInput
                  (ReferenceActivePhysicalStep.liveRecordingInput
                    r.output.preparation a started) ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput
                r.output.preparation a started) = some o ∧
            q.queueDomainValid ∧ q.previousServiceDomainValid ∧
            serviced.recording = o ∧
            (∀ j, serviced.arrival j =
              CoordinatorLiveServiceFinish.complementArrival a.payload o j) ∧
            (∀ j, serviced.service j =
              CappedService.service (4 * a.payload.n) (q.queue j)
                (serviced.arrival j)) ∧
            (∀ j, serviced.queue j =
              CappedService.residual (4 * a.payload.n) (q.queue j)
                (serviced.arrival j)) ∧
            (∀ j, serviced.score j = a.complementScores j + serviced.service j) ∧
            (∀ j, serviced.previousService j = serviced.service j) ∧
            CoordinatorLocalArmChoice.confirmationUpdate a.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (r.output.preparation.coordinatorObservation) =
                some pending ∧
            pending =
              (if CoordinatorLocalArmChoice.downConfirmationEvent a.payload started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.time (x.row.2 x.time)
                  r.output.preparation.coordinatorObservation then
                started.pending.erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                  p.m_lt_K (x.row.2 x.time).1)
              else started.pending) ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              pending x.row = .ok finished ∧
            ReferenceActivePhysicalStep.livePostChoice r.output.preparation a q base
              started =
                ⟨.live {
                    payload := a.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := x.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  { queue := serviced.queue
                    previousService := serviced.previousService } base,
                  x.state.upDecoderBank, none, some o, none⟩ ∧
            r.output.coordinator =
              ⟨.live {
                  payload := a.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := x.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
                { queue := serviced.queue
                  previousService := serviced.previousService } base,
                x.state.upDecoderBank, none, some o, none⟩ ∧
            r.output.next.coordinator =
              (ReferenceActivePhysicalStep.livePostChoice
                r.output.preparation a q base started).configuration ∧
            r.output.next.upDecoderBank =
              (ReferenceActivePhysicalStep.livePostChoice
                r.output.preparation a q base started).upDecoderBank
  := by
  classical
  dsimp only
  intro k
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let x := record.input
  intro v hselected hlive
  -- The proof follows the selected constructor of the actual round output.
  have hprepare : record.output.preparation = ReferenceActivePhysicalStep.prepare x := by
    rw [record.output_eq]
    rfl
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      record.output.preparation.coordinator := by
    have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprepare
    simpa [ReferenceActivePhysicalStep.prepare] using h.symm
  have hselection : (ReferenceActivePhysicalStep.dispatch x).selection = some v := by
    rw [hdispatch]
    exact hselected
  have hcompleteMass :=
    (ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
      rate rewards C_star C_h source k).1
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  have hphase := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits
    record v hselection
  generalize hcut : record.output.preparation.coordinator = cut at hframes hphase ⊢
  cases cut with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          simp only [hcut] at hframes hphase
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights arm hframes.1
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              installed.registers.payload installed.startRoundResult installed.registers.time
              installed.registers.complementWeights arm hframes.1
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          have hliveCall : CoordinatorLocalArmChoice.assignmentIsLive
              installed.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                installed.startRoundResult.clock.u) record.input.time := by
            simpa [selectedCall, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using
              hframes.2.1
          obtain ⟨valid, o, hrun, hrecording, hgate, hraw, hdiagnostic⟩ :=
            ReferenceCompleteCoordinatorDataArrival.complete_selected_live_coordinator_arrival
              rewards C_star C_h source k selectedCall hshape hliveCall
          have hinput := ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
            record installed.registers installed.startRoundResult installed.registers.time arm
            hframes.1 hshape hliveCall
          have hbridge : CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                installed.registers installed.startRoundResult) = some o := by
            rw [CoordinatorRecorderComplementBridge.run_eq_accepted, ← hinput]
            exact hrun
          have hdispatchCut := hdispatch.trans hcut
          have hchosen : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput x) = .chosen installed arm := by
            cases hstate : x.state.coordinator with
            | first =>
                rw [ReferenceActivePhysicalStep.dispatch_first x hstate] at hdispatchCut
                exact DispatchCut.first.inj hdispatchCut
            | live r q b =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate,
                  CoordinatorRoundDispatch.dispatch] at hdispatchCut
                change DispatchCut.live r q b _ =
                  DispatchCut.first (.chosen installed arm) at hdispatchCut
                cases hdispatchCut
            | collection payload ledger saved =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatchCut
                by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
                · simp only [dif_pos hvalid, CoordinatorRoundDispatch.dispatch] at hdispatchCut
                  change DispatchCut.collection payload ledger _ _ _ =
                    DispatchCut.first (.chosen installed arm) at hdispatchCut
                  cases hdispatchCut
                · simp only [dif_neg hvalid] at hdispatchCut
                  cases hdispatchCut
            | dagger =>
                simp [ReferenceActivePhysicalStep.dispatch,
                  CoordinatorRoundDispatch.dispatch, hstate] at hdispatchCut
          have hinvested := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
            x installed arm hchosen
          let launch := CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput x)
          have hzero := ReferenceActivePhysicalStep.dispatchFirst_zero_seed x installed arm hchosen
          obtain ⟨hscoreZero, hqueueZero, hpreviousZero, _hbaseZero⟩ := hzero
          have hcredit : ∀ j : CanonicalFastSampling.FastArm
              installed.registers.payload.slowSet,
              installed.registers.complementScores j + installed.ownedRegisters.queue j ≤
                x.time.val * D p := by
            intro j
            rw [hscoreZero j, hqueueZero j]
            exact Nat.zero_le _
          have hprevious : installed.ownedRegisters.previousServiceDomainValid := by
            intro j
            rw [hpreviousZero j]
            exact Nat.zero_le _
          have hstartedSigma : installed.startRoundResult.clock.sigma =
              some installed.registers.payload.sigma := by
            rw [hinvested]
            rfl
          have hstartedU : installed.startRoundResult.clock.u = none := by
            rw [hinvested]
            rfl
          have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
              installed.startRoundResult.clock := by
            have hgrid := installed.startRoundResult.gridDomain
            unfold CoordinatorPhaseClock.clockRegistersValid
            constructor
            · rw [hstartedSigma]
              rw [hinvested]
              rfl
            · rw [hstartedSigma, hstartedU]
              have hbounds : installed.registers.payload.sigma.val + 1 <
                  installed.startRoundResult.clock.g ∧
                  installed.startRoundResult.clock.g ≤ p.T + 1 := by
                simpa only [CoordinatorPhaseClock.clockGridDomain, hstartedSigma] using hgrid
              exact ⟨hbounds.1, hbounds.2, trivial⟩
          have hpayloadTime : installed.registers.payload.sigma = x.time := by
            rw [hinvested]
            rfl
          have htimeEq : installed.registers.time = x.time :=
            ReferenceActivePhysicalStep.dispatchFirst_chosen_time x installed arm hchosen
          have hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid x.time
              installed.startRoundResult.clock := by
            unfold CoordinatorPhaseClock.finishRoundTimeValid
            rw [hstartedSigma, hstartedU]
            refine ⟨?_, ?_⟩
            · exact le_of_eq (congrArg Fin.val hpayloadTime)
            · exact le_of_lt hframes.2.2
          have hparameter : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
            exact CoordinatorAssignmentRegisterInstall.first_proposal_parameter_valid launch
          have hchoiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid
              installed.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                installed.startRoundResult.clock.u)
              x.time installed.registers.complementWeights := by
            rw [← hframes.1]
            exact arm.choiceInputsValid
          obtain ⟨serviced, pending, finished, hservice, hqueueDomain,
            hpreviousDomain, hservicedRecording, harrivalEq, hserviceEq, hqueueEq,
            hscoreEq, hpreviousEq, hconfirmation, hpendingFormula, hfinish, hpost⟩ :=
            selected_live_tail record.output.preparation installed.registers
              installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
              o hchoiceValid hbridge hcredit hprevious hclock hfinishTime
              (by rw [hstartedSigma]; simp) hstartedU hparameter
          have hnotNone :
              (DispatchCut.first (.chosen installed arm)).selection ≠ none := by
            rw [← hcut, hshape]
            simp
          have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            record.output.preparation (.chosen installed arm) hcut
          rw [if_neg hnotNone] at hobserve
          have houtputs := actual_record_live_output record.output.preparation
            installed.registers installed.ownedRegisters installed.followerBaseScore
            installed.startRoundResult finished serviced o rfl hobserve hpost
          simp only [hcut] at ⊢
          refine ⟨installed.registers, installed.ownedRegisters,
            installed.followerBaseScore, installed.startRoundResult, ?_⟩
          constructor
          · exact ⟨rfl, HEq.rfl, rfl, rfl⟩
          · refine ⟨valid, ?_⟩
            refine ⟨o, ?_⟩
            exact ⟨serviced, pending, finished, hrun, hrecording, hgate, hraw,
              hdiagnostic, hinput, hbridge,
              hqueueDomain, hpreviousDomain, hservicedRecording, harrivalEq,
              hserviceEq, hqueueEq, hscoreEq, hpreviousEq, hconfirmation,
              hpendingFormula, hfinish, hpost, houtputs.1, houtputs.2.1,
              houtputs.2.2⟩
      | _ => simp only [hcut] at hphase
  | live registers owned oldBase outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          simp only [hcut] at hframes hphase
          let localRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input registers.payload dispatched.startResult record.input.time
            localRegisters.complementWeights arm rfl
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              registers.payload dispatched.startResult record.input.time
              localRegisters.complementWeights arm rfl
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          have hliveCall : CoordinatorLocalArmChoice.assignmentIsLive registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
              record.input.time := by
            simpa [selectedCall, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using
              hframes.1
          obtain ⟨valid, o, hrun, hrecording, hgate, hraw, hdiagnostic⟩ :=
            ReferenceCompleteCoordinatorDataArrival.complete_selected_live_coordinator_arrival
              rewards C_star C_h source k selectedCall hshape hliveCall
          have hinput := ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
            record registers dispatched.startResult record.input.time arm rfl hshape hliveCall
          have hbridge : CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                registers dispatched.startResult) = some o := by
            rw [CoordinatorRecorderComplementBridge.run_eq_accepted, ← hinput]
            exact hrun
          have hdispatchCut := hdispatch.trans hcut
          have hinputState : x.state.coordinator = .live registers owned oldBase := by
            cases hstate : x.state.coordinator with
            | first =>
                rw [ReferenceActivePhysicalStep.dispatch_first x hstate] at hdispatchCut
                cases hdispatchCut
            | live sourceRegisters sourceOwned sourceBase =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate,
                  CoordinatorRoundDispatch.dispatch] at hdispatchCut
                change DispatchCut.live sourceRegisters sourceOwned sourceBase
                    (CoordinatorRoundDispatch.dispatchLive
                      (ReferenceActivePhysicalStep.liveInput x sourceRegisters sourceOwned sourceBase)) =
                  DispatchCut.live registers owned oldBase
                    (.continuingChosen dispatched hstart continuation arm) at hdispatchCut
                rcases DispatchCut.live.inj hdispatchCut with ⟨hregisters, howned, hbase, _⟩
                clear hdispatchCut
                subst sourceRegisters
                have hownedEq : sourceOwned = owned := eq_of_heq howned
                subst sourceOwned
                subst sourceBase
                rfl
            | collection payload sourceLedger saved =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatchCut
                by_cases hvalid : 1 ≤ sourceLedger.cutoff ∧ sourceLedger.cutoff ≤ p.T
                · simp only [dif_pos hvalid, CoordinatorRoundDispatch.dispatch] at hdispatchCut
                  change DispatchCut.collection payload sourceLedger _ _ _ =
                    DispatchCut.live registers owned oldBase
                      (.continuingChosen dispatched hstart continuation arm) at hdispatchCut
                  cases hdispatchCut
                · simp only [dif_neg hvalid] at hdispatchCut
                  cases hdispatchCut
            | dagger =>
                simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatchCut
          have hactualLive : CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput x registers owned oldBase) =
                .continuingChosen dispatched hstart continuation arm := by
            rw [ReferenceActivePhysicalStep.dispatch, hinputState,
              CoordinatorRoundDispatch.dispatch] at hdispatchCut
            change DispatchCut.live registers owned oldBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput x registers owned oldBase)) =
              DispatchCut.live registers owned oldBase
                (.continuingChosen dispatched hstart continuation arm) at hdispatchCut
            rcases DispatchCut.live.inj hdispatchCut with ⟨_, _, _, houtcome⟩
            exact eq_of_heq houtcome
          have hcontinuationStart := live_dispatch_continuation_result
            dispatched continuation arm hstart hactualLive
          have hmassInput := hcompleteMass
          unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hmassInput
          rw [hinputState] at hmassInput
          have hcredit : ∀ j : CanonicalFastSampling.FastArm
              localRegisters.payload.slowSet,
              localRegisters.complementScores j +
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time).queue j ≤
                  record.input.time.val * D p := by
            simpa [localRegisters, ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt] using hmassInput.1
          have hprevious :
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time).previousServiceDomainValid := by
            change ∀ j : CanonicalFastSampling.FastArm localRegisters.payload.slowSet,
              owned.previousService j ≤ D p
            intro j
            simpa [localRegisters, ReferenceActivePhysicalStep.liveRegistersAt] using
              hmassInput.2 j
          have hstartSource : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
              registers.priorClock registers.clockPending = .ok dispatched.startResult := by
            simpa [ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt,
              CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hstart
          have hstartFacts :
              CoordinatorPhaseClock.proposalParameterValid p rate.eta.val ∧
              CoordinatorPhaseClock.clockRegistersValid p rate.eta.val registers.priorClock ∧
              CoordinatorPhaseClock.startRoundTimeValid p record.input.time registers.priorClock := by
            unfold CoordinatorPhaseClock.startRound at hstartSource
            by_cases hparameter : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val
            · by_cases hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
                  registers.priorClock
              · by_cases htime : CoordinatorPhaseClock.startRoundTimeValid p
                    record.input.time registers.priorClock
                · exact ⟨hparameter, hclock, htime⟩
                · simp [hparameter, hclock, htime] at hstartSource
              · simp [hparameter, hclock] at hstartSource
            · simp [hparameter] at hstartSource
          have hframe : dispatched.startResult.clock = registers.priorClock ∧
              dispatched.startResult.pending = registers.clockPending ∧
              dispatched.startResult.ledgerCommand = none ∧
              dispatched.startResult.assignmentStart = none := by
            simpa [ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt,
              CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
              CoordinatorLiveChoiceRecorderStep.Registers.clockPending,
              hcontinuationStart] using continuation.clockFrame
          have hpayloadClock : registers.priorClock.sigma = some registers.payload.sigma := by
            simpa [ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt] using continuation.payloadClockStart
          have hliveAtPrior : CoordinatorLocalArmChoice.assignmentIsLive registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p registers.priorClock.u)
              record.input.time := by
            simpa [hframe.1] using hframes.1
          have huPrior : registers.priorClock.u = none := by
            cases hu : registers.priorClock.u with
            | none => rfl
            | some cutoff =>
                have htime := hstartFacts.2.2
                simp only [CoordinatorPhaseClock.startRoundTimeValid,
                  hpayloadClock, hu] at htime
                have hcutoffRound :
                    CoordinatorLocalArmChoice.cutoffRound
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p registers.priorClock.u) =
                    cutoff.val + 1 := by
                  rw [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hu]
                  rfl
                have hliveUpper := hliveAtPrior.2
                change CoordinatorLocalArmChoice.sourceRound record.input.time <
                  CoordinatorLocalArmChoice.cutoffRound
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p registers.priorClock.u) at hliveUpper
                rw [hcutoffRound, CoordinatorLocalArmChoice.sourceRound] at hliveUpper
                omega
          have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
              dispatched.startResult.clock := by
            simpa [hframe.1] using hstartFacts.2.1
          have hstartedSigma : dispatched.startResult.clock.sigma =
              some registers.payload.sigma := by simpa [hframe.1] using hpayloadClock
          have hstartedU : dispatched.startResult.clock.u = none := by
            simpa [hframe.1] using huPrior
          have hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid record.input.time
              dispatched.startResult.clock := by
            have hpriorTime := hstartFacts.2.2
            simp only [CoordinatorPhaseClock.startRoundTimeValid,
              hpayloadClock, huPrior] at hpriorTime
            have hfinishPrior : CoordinatorPhaseClock.finishRoundTimeValid
                record.input.time registers.priorClock := by
              simp only [CoordinatorPhaseClock.finishRoundTimeValid,
                hpayloadClock, huPrior]
              exact ⟨le_of_lt hpriorTime.1, hpriorTime.2⟩
            simpa [hframe.1] using hfinishPrior
          have hchoiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid
              localRegisters.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
              record.input.time localRegisters.complementWeights := by
            simpa [localRegisters, ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt] using arm.choiceInputsValid
          obtain ⟨serviced, pending, finished, hservice, hqueueDomain,
            hpreviousDomain, hservicedRecording, harrivalEq, hserviceEq, hqueueEq,
            hscoreEq, hpreviousEq, hconfirmation, hpendingFormula, hfinish, hpost⟩ :=
            selected_live_tail record.output.preparation localRegisters
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
              oldBase dispatched.startResult o hchoiceValid hbridge hcredit hprevious
              hclock hfinishTime (by rw [hstartedSigma]; simp) hstartedU
              hstartFacts.1
          have hnotNone : (DispatchCut.live registers owned oldBase
              (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
            rw [← hcut, hshape]
            simp
          have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            record.output.preparation registers owned oldBase
            (.continuingChosen dispatched hstart continuation arm) hcut
          rw [if_neg hnotNone] at hobserve
          have hobserve' : record.output.preparation.observeCoordinator =
              ReferenceActivePhysicalStep.livePostChoice record.output.preparation
                localRegisters (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                oldBase dispatched.startResult := by
            simpa [localRegisters, ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt] using hobserve
          have houtputs := actual_record_live_output record.output.preparation
            localRegisters (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
            oldBase dispatched.startResult finished serviced o rfl hobserve' hpost
          simp only [hcut] at ⊢
          refine ⟨localRegisters,
            ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time,
            oldBase, dispatched.startResult, ?_⟩
          constructor
          · exact ⟨rfl, HEq.rfl, rfl, rfl⟩
          · refine ⟨valid, ?_⟩
            refine ⟨o, ?_⟩
            exact ⟨serviced, pending, finished, hrun, hrecording, hgate, hraw,
              hdiagnostic, hinput, hbridge,
              hqueueDomain, hpreviousDomain, hservicedRecording, harrivalEq,
              hserviceEq, hqueueEq, hscoreEq, hpreviousEq, hconfirmation,
              hpendingFormula, hfinish, hpost, houtputs.1, houtputs.2.1,
              houtputs.2.2⟩
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending
          hno arm =>
          change ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record)
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) = false ∧ _ at hphase
          have hbit := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
            (ReferenceActiveHorizonMeasurability.roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) record.input.time rfl
          rcases hphase with ⟨hphaseLive, _⟩
          rw [hphaseLive] at hbit
          have hnotLive := of_decide_eq_false hbit.symm
          have hnotLive' : ¬ CoordinatorLocalArmChoice.assignmentIsLive
              v.view.payload v.view.cutoff record.input.time := by
            simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hnotLive
          exact False.elim (hnotLive' hlive)
      | _ =>
          exact False.elim hphase
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent roundStart hstart instruction hinstruction
          output hlocal clockData installation arm =>
          simp only [hcut] at hframes hphase
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input installation.registers.payload roundStart instruction.time
            installation.registers.complementWeights arm hframes.1
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              installation.registers.payload roundStart instruction.time
              installation.registers.complementWeights arm hframes.1
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          have hliveCall : CoordinatorLocalArmChoice.assignmentIsLive
              installation.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p roundStart.clock.u)
              record.input.time := by
            simpa [selectedCall, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using
              hframes.2.1
          obtain ⟨valid, o, hrun, hrecording, hgate, hraw, hdiagnostic⟩ :=
            ReferenceCompleteCoordinatorDataArrival.complete_selected_live_coordinator_arrival
              rewards C_star C_h source k selectedCall hshape hliveCall
          have hinput := ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
            record installation.registers roundStart instruction.time arm hframes.1
            hshape hliveCall
          have hbridge : CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                installation.registers roundStart) = some o := by
            rw [CoordinatorRecorderComplementBridge.run_eq_accepted, ← hinput]
            exact hrun
          have hdispatchCut := hdispatch.trans hcut
          have hcollectionState : ∃ saved,
              x.state.coordinator = .collection payload ledger saved := by
            cases hstate : x.state.coordinator with
            | first =>
                rw [ReferenceActivePhysicalStep.dispatch_first x hstate] at hdispatchCut
                cases hdispatchCut
            | live sourceRegisters sourceOwned sourceBase =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate,
                  CoordinatorRoundDispatch.dispatch] at hdispatchCut
                change DispatchCut.live sourceRegisters sourceOwned sourceBase _ =
                  DispatchCut.collection payload ledger clock cutoff
                    (.laterChosen core consistent roundStart hstart instruction hinstruction
                      output hlocal clockData installation arm) at hdispatchCut
                cases hdispatchCut
            | collection sourcePayload sourceLedger saved =>
                simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatchCut
                by_cases hvalid : 1 ≤ sourceLedger.cutoff ∧ sourceLedger.cutoff ≤ p.T
                · simp only [dif_pos hvalid, CoordinatorRoundDispatch.dispatch] at hdispatchCut
                  let sourceCutoff : Fin p.T := ⟨sourceLedger.cutoff - 1, by omega⟩
                  let sourceClock := ReferenceActivePhysicalStep.collectionClock
                    sourcePayload sourceLedger saved sourceCutoff
                  change DispatchCut.collection sourcePayload sourceLedger sourceClock sourceCutoff
                      (CoordinatorRoundDispatch.dispatchCollection
                        (ReferenceActivePhysicalStep.collectionInput x sourcePayload sourceLedger
                          sourceClock sourceCutoff)) =
                    DispatchCut.collection payload ledger clock cutoff
                      (.laterChosen core consistent roundStart hstart instruction hinstruction
                        output hlocal clockData installation arm) at hdispatchCut
                  have hpayloadEq : sourcePayload = payload := by
                    have heq := congrArg (fun c : DispatchCut x =>
                      match c with
                      | .collection payload _ _ _ _ => payload
                      | _ => payload) hdispatchCut
                    simpa using heq
                  have hledgerEq : sourceLedger = ledger := by
                    have heq := congrArg (fun c : DispatchCut x =>
                      match c with
                      | .collection _ ledger _ _ _ => ledger
                      | _ => ledger) hdispatchCut
                    simpa using heq
                  cases hpayloadEq
                  cases hledgerEq
                  exact ⟨saved, rfl⟩
                · simp only [dif_neg hvalid] at hdispatchCut
                  cases hdispatchCut
            | dagger =>
                simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatchCut
          obtain ⟨saved, hstate⟩ := hcollectionState
          have hmassInput := hcompleteMass
          unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hmassInput
          rw [hstate] at hmassInput
          have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
          rw [hdispatchCut] at hprovenance
          obtain ⟨hinstallation, hpayload, _hsigma, _hdown⟩ := hprovenance
          have hfields := CoordinatorRoundDispatch.collectionOperationLedger_fields
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
            core.payload_n_eq
          obtain ⟨_hassignment, _hsigma, _hcutoff, _hfreeze, _hbase, _hpending,
            hcutoffRegisters, hcurrentRegisters, hincrement, _hgamma, _hraw,
            _henabled, _hcursor, _hphase⟩ := hfields
          have hinstructionTime := ReferenceActivePhysicalStep.later_instruction_time x
            payload ledger clock cutoff core roundStart instruction hstart hinstruction
          have hoperation : ∀ (a : Fin p.K)
              (c : CoordinatorCollectionLedger.CutoffRegister)
              (q : CoordinatorCollectionLedger.CurrentRegister),
              (CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                core.payload_n_eq).cutoffRegisters a = some c →
              (CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                core.payload_n_eq).currentRegisters a = some q →
              c.score + (CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                core.payload_n_eq).increment a + q.queue ≤ instruction.time.val * D p := by
            intro a c q hc hq
            rw [hcutoffRegisters] at hc
            rw [hcurrentRegisters] at hq
            rw [hincrement, hinstructionTime]
            exact (hmassInput a c q hc hq).1
          obtain ⟨_queueMass, hjointMass, _followerMass, _downMass⟩ :=
            ReferenceAssignmentCollectionMassSteps.later_installation_mass
              output clockData hoperation
          have hdomains := CoordinatorAssignmentRegisterInstall.later_register_domains
            output clockData
          subst installation
          have hinstructionSigma :
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.sigma.val =
                x.time.val := by
            change output.payload.sigma.val = x.time.val
            rw [output.payload_start, hinstructionTime]
          have hcredit : ∀ j : CanonicalFastSampling.FastArm
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload.slowSet,
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementScores j +
                (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters.queue j ≤
                  x.time.val * D p := by
            intro j
            have hmass := hjointMass j
            exact hmass.trans (le_of_eq (congrArg (fun n : ℕ => n * D p)
              hinstructionSigma))
          have hprevious := hdomains.2.2
          have heffect := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
            x.time clock ledger.pending roundStart instruction core.clock_parameter_valid
            core.clock_registers_valid core.clock_start_time_valid hstart hinstruction
          obtain ⟨hinstructionTime', _hkind, hsigma, hu, _hgrid, _hlast, _hpending, _hcommand⟩ :=
            heffect
          have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
              roundStart.clock := by
            unfold CoordinatorPhaseClock.clockRegistersValid
            rw [hsigma, hu]
            constructor
            · simpa [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using _hgrid
            · have hgrid := roundStart.gridDomain
              simpa [CoordinatorPhaseClock.clockGridDomain, hsigma] using hgrid
          have hfinishTime : CoordinatorPhaseClock.finishRoundTimeValid x.time
              roundStart.clock := by
            unfold CoordinatorPhaseClock.finishRoundTimeValid
            rw [hsigma, hu]
            refine ⟨le_rfl, ?_⟩
            simp only [FollowerCutoffScan.calendarRound]
            exact le_of_lt hframes.2.2
          have hchoiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p roundStart.clock.u)
              x.time (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights := by
            simpa [hinstructionTime'] using arm.choiceInputsValid
          obtain ⟨serviced, pending, finished, hservice, hqueueDomain,
            hpreviousDomain, hservicedRecording, harrivalEq, hserviceEq, hqueueEq,
            hscoreEq, hpreviousEq, hconfirmation, hpendingFormula, hfinish, hpost⟩ :=
            selected_live_tail record.output.preparation
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore
              roundStart o hchoiceValid hbridge hcredit hprevious hclock hfinishTime
              (by rw [hsigma]; simp) hu core.clock_parameter_valid
          have hnotNone : (DispatchCut.collection payload ledger clock cutoff
              (.laterChosen core consistent roundStart hstart instruction hinstruction output
                hlocal clockData (CoordinatorAssignmentRegisterInstall.installLater output clockData) arm)).selection ≠ none := by
            rw [← hcut, hshape]
            simp
          have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            record.output.preparation payload ledger clock cutoff
            (.laterChosen core consistent roundStart hstart instruction hinstruction output
              hlocal clockData (CoordinatorAssignmentRegisterInstall.installLater output clockData) arm)
            hcut
          rw [ite_eq_right hnotNone] at hobserve
          have houtputs := actual_record_live_output record.output.preparation
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore
            roundStart finished serviced o rfl hobserve hpost
          simp only [hcut] at ⊢
          refine ⟨(CoordinatorAssignmentRegisterInstall.installLater output clockData).registers,
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters,
            (CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore,
            roundStart, ?_⟩
          constructor
          · exact ⟨rfl, HEq.rfl, rfl, rfl⟩
          · refine ⟨valid, ?_⟩
            refine ⟨o, ?_⟩
            exact ⟨serviced, pending, finished, hrun, hrecording, hgate, hraw,
              hdiagnostic, hinput, hbridge, hqueueDomain, hpreviousDomain,
              hservicedRecording, harrivalEq, hserviceEq, hqueueEq, hscoreEq,
              hpreviousEq, hconfirmation, hpendingFormula, hfinish, hpost,
              houtputs.1, houtputs.2.1, houtputs.2.2⟩
      | _ =>
          first
          | rcases hphase with ⟨hphaseLive, _⟩
            have hbit := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
              (ReferenceActiveHorizonMeasurability.roundRecordCode record)
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) record.input.time rfl
            rw [hphaseLive] at hbit
            have hnotLive := of_decide_eq_false hbit.symm
            have hnotLive' : ¬ CoordinatorLocalArmChoice.assignmentIsLive
                v.view.payload v.view.cutoff record.input.time := by
              simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hnotLive
            exact False.elim (hnotLive' hlive)
          | exact False.elim hphase
  | invalidCollectionCutoff => exact False.elim hphase
  | dagger => exact False.elim hphase

end Bandits.Support.ReferenceCompleteSelectedLiveCoordinatorServiceFinish

end
