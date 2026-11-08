/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorClockDomains

/-!
# Actual continuing-live clock preservation

The continuing-live branch retains the exact `StartRound` result produced by
the coordinator dispatcher. The clock invariant itself is the literal
`ReferenceCoordinatorClockDomains.clockAt` predicate. Source ranges:
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-247,277-294`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,30-44,81-84`.

This module handles only the continuing-live and live no-choice outcomes. It
does not establish a general step or run invariant, nor any non-clock property.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CoordinatorRoundDispatch

namespace Bandits.Support.ReferenceLiveClockPreservation

open Bandits.Support.ReferenceCoordinatorClockDomains

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private def continuingResultPair {x : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome x) :
    Option (CoordinatorPhaseClock.StartRoundResult p ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  match outcome with
  | .continuingChosen dispatched _ continuation _ =>
      some (dispatched.startResult, continuation.startRoundResult)
  | _ => none

private theorem dispatchLive_continuation_projection
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
                          · have hp := congrArg continuingResultPair hactual
                            have hp' := by
                              simpa only [continuingResultPair] using hp
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

private theorem actual_live_continuation_projection
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
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
        .ok dispatched.startResult)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation selection)) :
    continuation.startRoundResult = dispatched.startResult := by
  have hbranch := hcut
  simp only [ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch, hstate,
    CoordinatorRoundDispatch.dispatch] at hbranch
  injection hbranch with _ _ _ hactual
  exact dispatchLive_continuation_projection
    (x := ReferenceActivePhysicalStep.liveInput x r q base)
    dispatched continuation selection hstart hactual

/-- The actual continuing-live result of `prepare` preserves `clockAt` through
the full checked post-choice tail. The continuation equality is projected from
the dispatcher construction, not supplied as a separate premise. -/
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
    (hclock : ReferenceCoordinatorClockDomains.clockAt
      x.rows x.selected x.time.val x.state)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending =
        .ok dispatched.startResult)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation selection)) :
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next := by
  have hcontinuation := actual_live_continuation_projection r q base dispatched
    continuation selection hstate hstart hcut
  exact ReferenceCoordinatorClockDomains.step_clockAt_live_continuing
    r q base dispatched continuation selection hstate hclock hstart
    hcontinuation hcut

/-- A live actual outcome with no arm selection takes the coordinator's
literal absorbing `dagger` branch. This covers the clock, initializer, and
local rejection outcomes without claiming success for those operations. -/
theorem step_live_noChoice_dagger
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base))
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base outcome)
    (hselection : (ReferenceActivePhysicalStep.DispatchCut.live r q base outcome).selection =
      none) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∧
      ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
        (ReferenceActivePhysicalStep.step x).next := by
  have hconfiguration :
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger := by
    rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
      (ReferenceActivePhysicalStep.prepare x) r q base outcome hcut]
    simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure]
  have hnext : (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger :=
    (ReferenceActivePhysicalStep.step_next_fields x).1.trans hconfiguration
  constructor
  · exact hnext
  · simp [ReferenceCoordinatorClockDomains.clockAt, hnext]

end Bandits.Support.ReferenceLiveClockPreservation

end
