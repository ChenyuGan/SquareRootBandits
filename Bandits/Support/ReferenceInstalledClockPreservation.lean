/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorClockDomains

import Lean.Elab.Tactic.Lets
import Lean.Elab.Tactic.Omega

/-!
# Clock preservation at actual assignment installations

For the actual first and later chosen-assignment branches, the installed
registers retain the clock produced by that same checked start operation. The
post-choice tail either enters the actual absorbing failure state or finishes
with the current complete-row proposal stamp. The clock predicate is the
literal `ReferenceCoordinatorClockDomains.clockAt` from
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-247,277-294`;
absorbing failures follow
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,30-44,81-84`.

These are conditional internal one-step results. They do not establish a
general step invariant or a horizon/run theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorAssignmentRegisterInstall

namespace Bandits.Support.ReferenceInstalledClockPreservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal post-choice tail preserves the imported clock predicate from
primitive clock-register and call-frame facts. Each actual installation branch
below derives these facts from its dispatcher and installer equations. -/
theorem livePostChoice_clockAt_of_primitive_fields
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
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
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
  | none =>
      simp [ReferenceActivePhysicalStep.livePostChoice, hrecord,
        ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceCoordinatorClockDomains.clockAt]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
    | error reason =>
        simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
          ReferenceActivePhysicalStep.coordinatorFailure,
          ReferenceCoordinatorClockDomains.clockAt]
    | ok serviced =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
          started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none =>
          simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
            hconfirmation, ReferenceActivePhysicalStep.coordinatorFailure,
            ReferenceCoordinatorClockDomains.clockAt]
      | some pending =>
        cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock pending x.row with
        | error reason =>
            simp [ReferenceActivePhysicalStep.livePostChoice, hrecord, hservice,
              hconfirmation, hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
              ReferenceCoordinatorClockDomains.clockAt]
        | ok finished =>
          rw [ReferenceActivePhysicalStep.livePostChoice_success prepared r q
            base started recording serviced pending finished hrecord hservice
            hconfirmation hfinish]
          rw [hstarted] at hfinish
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

/-- The first chosen dispatcher branch installs the actual first start's
clipped clock, zero pending set, and payload timestamp at the current input
time. The final conjunct is the actual one-step `clockAt` result. -/
theorem step_clockAt_firstChosen
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
      installation.startRoundResult installation.registers.time
      installation.registers.complementWeights x.row)
    (hstate : x.state.coordinator = .first)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installation selection) :
    installation.registers.payload.sigma = x.time ∧
    installation.registers.time = x.time ∧
    installation.registers.priorClock.sigma =
      some installation.registers.payload.sigma ∧
    installation.registers.priorClock.u = none ∧
    installation.registers.priorClock.g = installation.registers.gridBoundary ∧
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next ∧
    installation.startRoundResult.clock = installation.registers.priorClock ∧
    installation.startRoundResult.pending = Finset.univ ∧
    installation.registers.pendingAtChoice = Finset.univ ∧
    installation.registers.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val x.time ∧
    installation.registers.priorClock.lastProposal = none ∧
    CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      installation.registers.priorClock ∧
    installation.registers.payload.sigma.val + 1 < installation.registers.gridBoundary ∧
    installation.registers.gridBoundary ≤ p.T + 1 := by
  let launch := CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput x)
  have hininstallation := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    x installation selection hchosen
  have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    x installation selection hchosen
  have hpayloadTime : installation.registers.payload.sigma = installation.registers.time := by
    rw [hininstallation]
    simp [CoordinatorAssignmentRegisterInstall.installFirst,
      CoordinatorAssignmentRegisterInstall.firstRegisters,
      AssignmentStartPayload.Input.ofFirstAssignment,
      FirstAssignmentLaunch.Input.start]
  have hpayloadSigma : installation.registers.payload.sigma = x.time :=
    hpayloadTime.trans htime
  have hstartedClock : installation.startRoundResult.clock =
      installation.registers.priorClock := by
    rw [hininstallation]
    rfl
  have hpendingStarted : installation.startRoundResult.pending = Finset.univ := by
    rw [hininstallation]
    rfl
  have hpendingRegisters : installation.registers.pendingAtChoice = Finset.univ := by
    rw [hininstallation]
    rfl
  have hgridBoundary : installation.registers.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val x.time := by
    rw [hininstallation]
    rfl
  have hclockSigma : installation.registers.priorClock.sigma =
      some installation.registers.payload.sigma := by
    rw [hininstallation]
    rfl
  have hclockU : installation.registers.priorClock.u = none := by
    rw [hininstallation]
    rfl
  have hclockG : installation.registers.priorClock.g =
      FollowerCutoffScan.gridBoundary p rate.eta.val x.time := by
    rw [hininstallation]
    rfl
  have hclockProposal : installation.registers.priorClock.lastProposal = none := by
    rw [hininstallation]
    rfl
  have hdomain : CoordinatorPhaseClock.clockGridDomain p
      installation.registers.priorClock := by
    rw [hininstallation]
    simpa [CoordinatorAssignmentRegisterInstall.installFirst,
      CoordinatorAssignmentRegisterInstall.firstRegisters] using
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).gridDomain
  have hdomain' : installation.registers.payload.sigma.val + 1 <
      installation.registers.priorClock.g ∧
      installation.registers.priorClock.g ≤ p.T + 1 := by
    simpa [CoordinatorPhaseClock.clockGridDomain, hclockSigma] using hdomain
  have hclockG' := hclockG
  rw [← hpayloadSigma] at hclockG'
  have hdomainGrid : installation.registers.payload.sigma.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma ∧
      FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma ≤
        p.T + 1 := by
    rw [← hclockG']
    exact hdomain'
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      installation.registers.priorClock := by
    simp [CoordinatorPhaseClock.clockRegistersValid,
      CoordinatorPhaseClock.boundaryFromSigma, hclockSigma, hclockU,
      hclockG', hdomainGrid]
  have hgridAgreement : installation.registers.priorClock.g =
      installation.registers.gridBoundary := hclockG.trans hgridBoundary.symm
  have hboundary : installation.registers.gridBoundary ≤ p.T + 1 := by
    rw [← hgridAgreement]
    exact hdomain'.2
  have hstrict : installation.registers.payload.sigma.val + 1 <
      installation.registers.gridBoundary := by
    rw [← hgridAgreement]
    exact hdomain'.1
  have hstrictTime : installation.registers.payload.sigma.val <
      installation.registers.time.val + 1 := by
    rw [hpayloadSigma, htime]
    omega
  have hboundaryTime : installation.registers.time.val + 1 <
      installation.registers.gridBoundary := by
    calc
      installation.registers.time.val + 1 =
          installation.registers.payload.sigma.val + 1 := by
        rw [htime, hpayloadSigma]
      _ < installation.registers.priorClock.g := hdomain'.1
      _ = installation.registers.gridBoundary := hgridAgreement
  have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .first (.chosen installation selection) := by
    change ReferenceActivePhysicalStep.dispatch x = _
    rw [ReferenceActivePhysicalStep.dispatch_first x hstate]
    simp only [hchosen]
  have hselection :
      (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installation selection)).selection
        ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, htime]
  have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare x) installation.registers
        installation.ownedRegisters installation.followerBaseScore
        installation.startRoundResult := by
    rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
      (ReferenceActivePhysicalStep.prepare x) (.chosen installation selection) hcut]
    simp [hselection]
  have htail := livePostChoice_clockAt_of_primitive_fields
    (ReferenceActivePhysicalStep.prepare x) installation.registers
    installation.ownedRegisters installation.followerBaseScore
    installation.startRoundResult hparam hclockValid hclockSigma hclockU
    hgridAgreement.symm hstrictTime hboundaryTime hstartedClock htime
  have hstep : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected
      (x.time.val + 1) (ReferenceActivePhysicalStep.step x).next := by
    simpa [ReferenceActivePhysicalStep.step, hobs,
      ReferenceCoordinatorClockDomains.clockAt] using htail
  exact ⟨hpayloadSigma, htime, hclockSigma, hclockU, hgridAgreement, hstep,
    hstartedClock, hpendingStarted, hpendingRegisters, hgridBoundary,
    hclockProposal, hclockValid, hstrict, hboundary⟩

private theorem dispatchCollection_later_installation_fields
    (x : CoordinatorRoundDispatch.CollectionInput p) :
    match CoordinatorRoundDispatch.dispatchCollection x with
    | .laterChosen _ _ started _ _ _ output _ clockData installation _ =>
        installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          clockData.result = started
    | .laterChoiceFailure _ _ _ _ _ _ output _ clockData installation _ =>
        installation = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | _ => True := by
  classical
  generalize hcomputed : CoordinatorRoundDispatch.dispatchCollection x = outcome
  unfold CoordinatorRoundDispatch.dispatchCollection at hcomputed
  repeat' first
    | (split at hcomputed)
    | (extract_lets at hcomputed)
    | (subst outcome; trivial)
  · rename_i started hstart core operationLedger weights cutoff selected consistent
      hpending hscores hchoice hframe hcutoff hchoiceActual hnonempty hboundary hinputs
    dsimp only [selected] at hcomputed
    split at hcomputed
    · contradiction
    · subst outcome
      trivial
  · rename_i hclockEquations hfreeze
    rcases hclockEquations with
      ⟨htime, hkind, hsigma, hcutoff, hgrid, hproposal, hpending, hcommand⟩
    dsimp only at hcomputed
    repeat' first
      | (split at hcomputed)
      | (extract_lets at hcomputed)
      | (subst outcome; trivial)

private theorem dispatch_later_installation_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .collection _ _ _ _
        (.laterChosen _ _ started _ _ _ output _ clockData installation _) =>
          installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
            clockData.result = started
    | .collection _ _ _ _
        (.laterChoiceFailure _ _ _ _ _ _ output _ clockData installation _) =>
          installation = CoordinatorAssignmentRegisterInstall.installLater output clockData
    | _ => True := by
  classical
  unfold ReferenceActivePhysicalStep.dispatch
  cases x.state.coordinator with
  | first => trivial
  | live registers owned base => trivial
  | collection payload ledger savedProposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        have hsource := dispatchCollection_later_installation_fields
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff)
          cutoff)
        generalize hresult : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff)
            cutoff) = outcome at *
        cases outcome <;> exact hsource
      · simp only [dite_eq_right hcutoff]
  | dagger => trivial

/-- The actual later chosen outcome installs the clock returned by its one
checked `StartRound` result. The original instruction time, clipped boundary,
clock-validity bounds, pending initialization, and payload stamp are all
derived from the dispatcher and installation equations. -/
theorem step_clockAt_laterChosen
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (consistent : LaterAssignmentStartOperation.LocalConsistency payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        core.payload_n_eq))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending =
      .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hinstruction : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        core.payload_n_eq) instruction x.row)
    (hlocal : output.localConsistency = consistent)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload started
      instruction.time installation.registers.complementWeights x.row)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff
        (.laterChosen core consistent started hstart instruction hinstruction
          output hlocal clockData installation selection)) :
    installation.registers.payload.sigma = x.time ∧
    installation.registers.time = x.time ∧
    installation.registers.priorClock.sigma =
      some installation.registers.payload.sigma ∧
    installation.registers.priorClock.u = none ∧
    installation.registers.priorClock.g = installation.registers.gridBoundary ∧
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      (ReferenceActivePhysicalStep.step x).next ∧
    installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
    clockData.result = started ∧
    installation.registers.pendingAtChoice = Finset.univ ∧
    started.pending = Finset.univ ∧
    installation.registers.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val x.time ∧
    installation.registers.priorClock.lastProposal = clockData.priorClock.lastProposal ∧
    CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      installation.registers.priorClock ∧
    installation.registers.payload.sigma.val + 1 < installation.registers.gridBoundary ∧
    installation.registers.gridBoundary ≤ p.T + 1 := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .collection payload ledger clock cutoff
        (.laterChosen core consistent started hstart instruction hinstruction
          output hlocal clockData installation selection) := by
    change ReferenceActivePhysicalStep.dispatch x = _ at hcut
    exact hcut
  have hactual := dispatch_later_installation_fields x
  rw [hdispatch] at hactual
  rcases hactual with ⟨hinstallation, hresult⟩
  have hcompat := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
    output clockData
  rcases hcompat with ⟨_, hclockSigma, hclockU, hclockGrid, hclockProposal,
    hpending, _, _, _⟩
  have hinstructionTime := ReferenceActivePhysicalStep.later_instruction_time
    x payload ledger clock cutoff core started instruction hstart hinstruction
  have hpayloadEq : installation.registers.payload = output.payload := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.later_registers_payload output clockData
  have hpayloadTime : installation.registers.payload.sigma = instruction.time := by
    rw [hpayloadEq]
    exact output.payload_start
  have hregisterTime : installation.registers.time = instruction.time := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.later_registers_time output clockData
  have hpayloadSigma : installation.registers.payload.sigma = x.time :=
    hpayloadTime.trans hinstructionTime
  have hregisterTime' : installation.registers.time = x.time :=
    hregisterTime.trans hinstructionTime
  have hregisterClock : installation.registers.priorClock = clockData.result.clock := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.later_registers_clock output clockData
  have hstartedClock : started.clock = installation.registers.priorClock := by
    calc
      started.clock = clockData.result.clock :=
        (congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult).symm
      _ = installation.registers.priorClock := hregisterClock.symm
  have hregisterGrid : installation.registers.gridBoundary = clockData.result.clock.g := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.later_registers_grid_boundary output clockData
  have hclockGridAgreement : installation.registers.priorClock.g =
      installation.registers.gridBoundary := by
    calc
      installation.registers.priorClock.g = clockData.result.clock.g :=
        congrArg CoordinatorPhaseClock.ClockRegisters.g hregisterClock
      _ = installation.registers.gridBoundary := hregisterGrid.symm
  have hgridBoundary : installation.registers.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val x.time := by
    calc
      installation.registers.gridBoundary = clockData.result.clock.g := hregisterGrid
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val instruction.time := hclockGrid
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val x.time := by
        simp only [hinstructionTime]
  have hclockSigmaRegisters : installation.registers.priorClock.sigma =
      some installation.registers.payload.sigma := by
    calc
      installation.registers.priorClock.sigma = clockData.result.clock.sigma :=
        congrArg CoordinatorPhaseClock.ClockRegisters.sigma hregisterClock
      _ = some instruction.time := hclockSigma
      _ = some installation.registers.payload.sigma := by rw [← hpayloadTime]
  have hclockURegisters : installation.registers.priorClock.u = none := by
    calc
      installation.registers.priorClock.u = clockData.result.clock.u :=
        congrArg CoordinatorPhaseClock.ClockRegisters.u hregisterClock
      _ = none := hclockU
  have hclockGRegisters : installation.registers.priorClock.g =
      FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma := by
    calc
      installation.registers.priorClock.g = installation.registers.gridBoundary :=
        hclockGridAgreement
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val x.time := hgridBoundary
      _ = FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma := by
        rw [← hpayloadSigma]
  have hdomain : instruction.time.val + 1 < clockData.result.clock.g ∧
      clockData.result.clock.g ≤ p.T + 1 := by
    simpa [CoordinatorPhaseClock.clockGridDomain, hclockSigma] using
      clockData.result.gridDomain
  have hdomain' : installation.registers.payload.sigma.val + 1 <
      installation.registers.priorClock.g ∧
      installation.registers.priorClock.g ≤ p.T + 1 := by
    constructor
    · have hstrict' : instruction.time.val + 1 < installation.registers.priorClock.g := by
        simpa [hregisterClock] using hdomain.1
      simpa [hpayloadTime] using hstrict'
    · simpa [hregisterClock] using hdomain.2
  have hdomainGrid : installation.registers.payload.sigma.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma ∧
      FollowerCutoffScan.gridBoundary p rate.eta.val installation.registers.payload.sigma ≤
        p.T + 1 := by
    rw [← hclockGRegisters]
    exact hdomain'
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      installation.registers.priorClock := by
    simp [CoordinatorPhaseClock.clockRegistersValid,
      CoordinatorPhaseClock.boundaryFromSigma, hclockSigmaRegisters,
      hclockURegisters, hclockGRegisters, hdomainGrid]
  have hstrict : installation.registers.payload.sigma.val + 1 <
      installation.registers.gridBoundary := by
    calc
      installation.registers.payload.sigma.val + 1 <
          installation.registers.priorClock.g := hdomain'.1
      _ = installation.registers.gridBoundary := hclockGridAgreement
  have hboundary : installation.registers.gridBoundary ≤ p.T + 1 := by
    rw [← hclockGridAgreement]
    exact hdomain'.2
  have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hstrictTime : installation.registers.payload.sigma.val <
      installation.registers.time.val + 1 := by
    rw [hpayloadSigma, hregisterTime']
    omega
  have hboundaryTime : installation.registers.time.val + 1 <
      installation.registers.gridBoundary := by
    calc
      installation.registers.time.val + 1 =
          installation.registers.payload.sigma.val + 1 := by
        rw [hregisterTime', hpayloadSigma]
      _ < installation.registers.priorClock.g := hdomain'.1
      _ = installation.registers.gridBoundary := hclockGridAgreement
  have hselection :
      (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
        (.laterChosen core consistent started hstart instruction hinstruction output hlocal
          clockData installation selection)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, hinstructionTime]
  have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare x) installation.registers
        installation.ownedRegisters installation.retainedBaseScore started := by
    rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
      (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
      (.laterChosen core consistent started hstart instruction hinstruction
        output hlocal clockData installation selection) hcut]
    simp [hselection]
  have htail := livePostChoice_clockAt_of_primitive_fields
    (ReferenceActivePhysicalStep.prepare x) installation.registers
    installation.ownedRegisters installation.retainedBaseScore started hparam hclockValid
    hclockSigmaRegisters hclockURegisters hclockGridAgreement.symm hstrictTime hboundaryTime
    hstartedClock hregisterTime'
  have hstep : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected
      (x.time.val + 1) (ReferenceActivePhysicalStep.step x).next := by
    simpa [ReferenceActivePhysicalStep.step, hobs,
      ReferenceCoordinatorClockDomains.clockAt] using htail
  have hpendingRegisters : installation.registers.pendingAtChoice = Finset.univ := by
    rw [hinstallation]
    exact CoordinatorAssignmentRegisterInstall.later_registers_pending_full output clockData
  have hstartedPending : started.pending = Finset.univ := by
    rw [← hresult]
    exact hpending
  have hlastProposal : installation.registers.priorClock.lastProposal =
      clockData.priorClock.lastProposal := by
    calc
      installation.registers.priorClock.lastProposal = clockData.result.clock.lastProposal :=
        congrArg CoordinatorPhaseClock.ClockRegisters.lastProposal hregisterClock
      _ = clockData.priorClock.lastProposal := hclockProposal
  exact ⟨hpayloadSigma, hregisterTime', hclockSigmaRegisters, hclockURegisters,
    hclockGridAgreement, hstep, hinstallation, hresult, hpendingRegisters,
    hstartedPending, hgridBoundary, hlastProposal, hclockValid, hstrict, hboundary⟩

end Bandits.Support.ReferenceInstalledClockPreservation

end
