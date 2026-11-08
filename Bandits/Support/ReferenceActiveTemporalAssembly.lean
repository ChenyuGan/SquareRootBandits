/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveDispatchTemporal
public import Bandits.Support.ReferenceActiveCoordinatorTemporal
public import Bandits.Support.ReferenceActiveTemporalCausality

/-!
# Temporal assembly for the canonical active physical execution

This module assembles the admitted dispatch, coordinator-tail, and follower
locality results on the existing `ReferenceActivePhysicalHorizon.run`.
The selected complete row, actual continuous controls, all current rewards,
saved follower buffers, exceptional paths, and every physical action are kept
literal. The exports are deterministic internal comparisons only; they do not
establish a Borel map, a probability law, or the main regret theorem.

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:197-209,
235-297,376-423`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveTemporalAssembly

open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon

variable {p : Bandits.Support.ReferenceActivePhysicalHorizon.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem firstOutcome_is_chosen (input : CoordinatorRoundDispatch.FirstInput p) :
    ∃ selected,
      CoordinatorRoundDispatch.dispatchFirst input =
        .chosen (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput input)) selected := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · exact False.elim (hnonempty ‹CoordinatorLocalArmChoice.coordinatorArmChoice
      payload started.pending cutoff installed.registers.time weights input.row = none›)
  · rename_i arm hselected
    exact ⟨{
      arm := arm
      choiceInputsValid := hchoice
      recorderBoundaryValid := hboundary
      armChoice_eq := hselected }, rfl⟩

private def firstTailArgs
    (launch : FirstAssignmentLaunch.Input p rate.eta) :
    Bandits.Support.ReferenceActiveDispatchTemporal.LiveArgs p rate :=
  ⟨(CoordinatorAssignmentRegisterInstall.installFirst launch).registers,
    (CoordinatorAssignmentRegisterInstall.installFirst launch).ownedRegisters,
    ((CoordinatorAssignmentRegisterInstall.installFirst launch).followerBaseScore,
      (CoordinatorAssignmentRegisterInstall.installFirst launch).startRoundResult)⟩

private theorem first_dispatch_tailArgs
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
        (ReferenceActivePhysicalStep.dispatch x) =
      .inr (.inr (.inl (firstTailArgs
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x)))) ) := by
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  obtain ⟨selection, hchosen⟩ := firstOutcome_is_chosen
    (ReferenceActivePhysicalStep.firstInput x)
  rw [hchosen]
  have htime :
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))).registers.time = x.time := rfl
  simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
    ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, htime, dite_true,
    Option.some_ne_none]
  rfl

private theorem firstState_of_firstCut
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput x)}
    (hcut : ReferenceActivePhysicalStep.DispatchCut.first outcome =
      ReferenceActivePhysicalStep.dispatch x) :
    x.state.coordinator = .first := by
  have hd : ReferenceActivePhysicalStep.dispatch x = .first outcome := hcut.symm
  cases hphase : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hphase,
        CoordinatorRoundDispatch.dispatch] at hd
      contradiction
  | collection payload ledger proposal =>
      simp only [ReferenceActivePhysicalStep.dispatch, hphase,
        CoordinatorRoundDispatch.dispatch] at hd
      split at hd <;> contradiction
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hphase] at hd
      contradiction

private theorem firstInstallation_eq_of_firstCut
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    {installation : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput x))}
    {selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
      installation.startRoundResult installation.registers.time installation.registers.complementWeights
      (ReferenceActivePhysicalStep.firstInput x).row}
    (hcut : ReferenceActivePhysicalStep.DispatchCut.first (.chosen installation selection) =
      ReferenceActivePhysicalStep.dispatch x) :
    installation = CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput x)) := by
  have hfirst := firstState_of_firstCut hcut
  have hd : ReferenceActivePhysicalStep.dispatch x = .first (.chosen installation selection) := hcut.symm
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst] at hd
  have hchosen := ReferenceActivePhysicalStep.DispatchCut.first.inj hd
  exact ReferenceActivePhysicalStep.dispatchFirst_chosen_installation x installation selection hchosen

/-- The actual first-launch input is fixed by the whole current control slice.
This includes the complete assignment vector used during installation. -/
theorem firstLaunchInput_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time) :
    CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          ⟨state, rows, selected, time, active, rewards⟩) =
      CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput
          ⟨state, otherRows, selected, time, active, otherRewards⟩) := by
  unfold CoordinatorRoundDispatch.firstLaunchInput
    ReferenceActivePhysicalStep.firstInput ReferenceActivePhysicalStep.RoundInput.row
  congr 1
  unfold LaterAssignmentStartOperation.ownAssignmentVector
  rw [hcurrent]

private theorem dispatchData_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, otherRows, selected, time, active, otherRewards⟩
    Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData x =
      Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData y := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, otherRewards⟩
  cases hphase : state.coordinator with
  | first =>
      have hlaunch := firstLaunchInput_eq_of_current state rows otherRows selected
        time active rewards otherRewards hcurrent
      have hpair := Bandits.Support.ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current state rows otherRows
        selected active rewards otherRewards hphase hcurrent
      have htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
            (ReferenceActivePhysicalStep.dispatch x) =
          Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
            (ReferenceActivePhysicalStep.dispatch y) := by
        rw [first_dispatch_tailArgs x hphase, first_dispatch_tailArgs y hphase]
        exact congrArg (fun args => Sum.inr (Sum.inr (Sum.inl args)))
          (congrArg firstTailArgs hlaunch)
      unfold Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData
        Bandits.Support.ReferenceActiveDispatchTemporal.cutData
      exact congrArg₂ (fun head tail => (head.1, head.2, tail)) hpair htail
  | live registers owned base =>
      exact Bandits.Support.ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current state rows otherRows selected time active
        rewards otherRewards registers owned base hphase hcurrent
  | collection payload ledger proposal =>
      exact Bandits.Support.ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current state rows otherRows selected time
        active rewards otherRewards payload ledger proposal hphase hcurrent
  | dagger =>
      change Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData x =
        Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData y
      unfold Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData
        Bandits.Support.ReferenceActiveDispatchTemporal.cutData
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hphase,
        ReferenceActivePhysicalStep.dispatch_dagger y hphase]
      rfl

private theorem observeCoordinator_eq_live_of_tailArgs
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
      prepared.coordinator = .inr (.inr (.inl ⟨r, q, base, started⟩))) :
    prepared.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
  classical
  cases prepared with
  | mk cut hcut followers =>
      cases cut with
      | first outcome =>
          cases outcome with
          | chosen installation selection =>
              have hinstall := firstInstallation_eq_of_firstCut hcut
              have htime : installation.registers.time = x.time := by
                rw [hinstall]
                rfl
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]; cases htail; rfl
          | choiceDomainFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | recorderBoundaryFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | choiceRejected installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | live registers owned base' outcome =>
          cases outcome with
          | continuingChosen dispatched hstart continuation selection =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]; rcases htail with
                  ⟨hregisters, hargs⟩; cases hregisters; cases hargs; rfl
          | cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomain
              hclock hpending hnoAssignment selection =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
          | clockFailure failure hdispatch =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | initializerFailure dispatched hstart checked hchecked =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | localFailure dispatched hstart reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | collection payload ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installation selection =>
              have htime : instruction.time = x.time := by
                by_contra htime
                simp [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                  ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, htime] at htail
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]; cases htail; rfl
          | clockFailure failure hstart =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | localFailure started hstart invalid reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | coreFailure core started hstart reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | continuing core snapshot boundary scores =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterChoiceFailure core consistent started hstart instruction hinstruction output hlocal
              clockData installation reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | invalidCollectionCutoff =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]
      | dagger =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem observeCoordinator_eq_collection_of_tailArgs
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
      prepared.coordinator = .inr (.inr (.inr ⟨payload, ledger, started, weights⟩))) :
    prepared.observeCoordinator =
      ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights := by
  classical
  cases prepared with
  | mk cut hcut followers =>
      cases cut with
      | first outcome =>
          cases outcome with
          | chosen installation selection =>
              have hinstall := firstInstallation_eq_of_firstCut hcut
              have htime : installation.registers.time = x.time := by
                rw [hinstall]
                rfl
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.chosen installation selection)).selection ≠ none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, htime]
              simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                dite_eq_right hselection] at htail
              simp at htail
          | choiceDomainFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | recorderBoundaryFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | choiceRejected installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | live registers owned base outcome =>
          cases outcome with
          | cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomain
              hclock hpending hnoAssignment selection =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]; rcases htail with
                  ⟨hpayload, hargs⟩; cases hpayload; cases hargs; rfl
          | continuingChosen dispatched hstart continuation selection =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
          | clockFailure failure hdispatch =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | initializerFailure dispatched hstart checked hchecked =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | localFailure dispatched hstart reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | collection sourcePayload sourceLedger clock cutoff outcome =>
          cases outcome with
          | continuing core snapshot boundary scores =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]; rcases htail with
                  ⟨hpayload, hargs⟩; cases hpayload; cases hargs; rfl
          | clockFailure failure hstart =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | localFailure started hstart invalid reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | coreFailure core started hstart reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterChoiceFailure core consistent started hstart instruction hinstruction output hlocal
              clockData installation reason =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installation selection =>
              by_cases htime : instruction.time = x.time
              · simp [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt,
                htime] at htail
              · simp [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt,
                htime] at htail
      | invalidCollectionCutoff =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]
      | dagger =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem observeCoordinator_eq_failure_of_tailArgs
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
      prepared.coordinator = .inr (.inl ())) :
    prepared.observeCoordinator = ReferenceActivePhysicalStep.coordinatorFailure
      x.state.upDecoderBank .dispatchRejected none none := by
  classical
  cases prepared with
  | mk cut hcut followers =>
      cases cut with
      | first outcome =>
          cases outcome with
          | chosen installation selection =>
              have hinstall := firstInstallation_eq_of_firstCut hcut
              have htime : installation.registers.time = x.time := by
                rw [hinstall]
                rfl
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.chosen installation selection)).selection ≠ none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, htime]
              simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                dite_eq_right hselection] at htail
              simp at htail
          | choiceDomainFailure installation =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | recorderBoundaryFailure installation =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | choiceRejected installation =>
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | live registers owned base outcome =>
          cases outcome <;>
            simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> try simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
          case laterChosen core consistent started startRoundEq instruction assignmentStartEq
              output localConsistencyEq clockData installation selection =>
            have htime : instruction.time ≠ x.time := by
              intro heq
              simp [heq] at htail
            simp_all []
      | invalidCollectionCutoff =>
          simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]
      | dagger =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem observeCoordinator_eq_dagger_of_tailArgs
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
      prepared.coordinator = .inl ()) :
    prepared.observeCoordinator =
      ⟨.dagger, x.state.upDecoderBank, none, none, none⟩ := by
  classical
  cases prepared with
  | mk cut hcut followers =>
      cases cut with
      | first outcome =>
          cases outcome with
          | chosen installation selection =>
              have hinstall := firstInstallation_eq_of_firstCut hcut
              have htime : installation.registers.time = x.time := by
                rw [hinstall]
                rfl
              simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
          | choiceDomainFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | recorderBoundaryFailure installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
          | choiceRejected installation =>
              simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                ReferenceActivePhysicalStep.DispatchCut.selection]
      | live registers owned base outcome =>
          cases outcome <;>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
      | collection payload ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installation selection =>
            by_cases htime : instruction.time = x.time
            · have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output hlocal
                      clockData installation selection)).selection ≠ none := by
                  simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                    ReferenceActivePhysicalStep.selectionAt, htime]
              simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                dite_eq_right hselection] at htail
              simp at htail
            · have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output hlocal
                      clockData installation selection)).selection = none := by
                  simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                    ReferenceActivePhysicalStep.selectionAt, htime]
              simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
                dite_eq_left hselection] at htail
              simp at htail
          | clockFailure _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | localFailure _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | coreFailure _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | continuing _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterReconstructionFailure _ _ _ _ _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterPrefixFailure _ _ _ _ _ _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterOrientationFailure _ _ _ _ _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
          | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
            simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
              ReferenceActivePhysicalStep.DispatchCut.selection]
      | invalidCollectionCutoff =>
          simp_all [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]
      | dagger =>
          simp_all [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
            ReferenceActivePhysicalStep.DispatchCut.selection]

/-- One actual accepted physical round depends on precisely its complete
current selected control, all current rewards, and the selected row's past
proposal scalars. All computed diagnostics and the literal successor agree. -/
theorem computedEvidence_eq_of_temporal_reads
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time)
    (hpast : ∀ s : Fin p.T, s.val < time.val →
      ((rows selected).2 s).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 s).1 ContinuousControlSlice.Label.prop)
    (hrewards : rewards time = otherRewards time) :
    ReferenceActivePhysicalHorizon.computedEvidence
        ⟨state, rows, selected, time, active, rewards⟩ =
      ReferenceActivePhysicalHorizon.computedEvidence
        ⟨state, otherRows, selected, time, active, otherRewards⟩ := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, otherRewards⟩
  let P : ReferenceActivePhysicalStep.PreparedRound x :=
    ReferenceActivePhysicalStep.prepare x
  let Q : ReferenceActivePhysicalStep.PreparedRound y :=
    ReferenceActivePhysicalStep.prepare y
  have hrewardsCurrent : x.rewards x.time = y.rewards y.time := by
    simpa only [x, y] using hrewards
  have hdata : Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData x =
      Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData y :=
    dispatchData_eq_of_current state rows otherRows selected time active
      rewards otherRewards hcurrent
  have hpair : ((ReferenceActivePhysicalStep.dispatch x).arm,
      (ReferenceActivePhysicalStep.dispatch x).downView) =
      ((ReferenceActivePhysicalStep.dispatch y).arm,
        (ReferenceActivePhysicalStep.dispatch y).downView) := by
    simpa only [Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData,
      Bandits.Support.ReferenceActiveDispatchTemporal.cutData] using
        congrArg (fun data => (data.1, data.2.1)) hdata
  have htail :
      Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch x) =
        Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch y) := by
    simpa only [Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData,
      Bandits.Support.ReferenceActiveDispatchTemporal.cutData] using
        congrArg (fun data => data.2.2) hdata
  have harm : P.coordinator.arm = Q.coordinator.arm := congrArg Prod.fst hpair
  have hview : P.coordinator.downView = Q.coordinator.downView :=
    congrArg Prod.snd hpair
  have hactions : P.arms.actions = Q.arms.actions := by
    funext player
    rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨i, hplayer⟩
    · subst player
      calc
        P.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
            P.coordinator.arm := P.arms.actions_coordinator
        _ = Q.coordinator.arm := harm
        _ = Q.arms.actions (ActiveRoundActions.coordinator p.two_le_m) :=
          Q.arms.actions_coordinator.symm
    · subst player
      rw [ReferenceActivePhysicalStep.PreparedRound.action_follower P i,
        ReferenceActivePhysicalStep.PreparedRound.action_follower Q i]
      exact congrArg Prod.fst
        (Bandits.Support.ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
          i (state.activations i) (active i) (state.followers i) hcurrent)
  have hfeedback : P.feedback.feedback = Q.feedback.feedback := by
    funext player
    rw [P.feedback_rule, Q.feedback_rule, hactions, hrewardsCurrent]
  have hown : (ReferenceActivePhysicalStep.step x).ownEntries =
      (ReferenceActivePhysicalStep.step y).ownEntries := by
    funext player
    calc
      (ReferenceActivePhysicalStep.step x).ownEntries player =
          (P.arms.actions player,
            ActualInitializationPhysicalStep.observationOfGrid p
              (P.feedback.feedback player)) :=
        ReferenceActivePhysicalStep.step_own_entry x player
      _ = (Q.arms.actions player,
            ActualInitializationPhysicalStep.observationOfGrid p
              (Q.feedback.feedback player)) := by rw [hactions, hfeedback]
      _ = (ReferenceActivePhysicalStep.step y).ownEntries player :=
        (ReferenceActivePhysicalStep.step_own_entry y player).symm
  have hcoordinator : P.observeCoordinator = Q.observeCoordinator := by
    have htailPQ :
        Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs P.coordinator =
          Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs Q.coordinator := by
      change Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch x) =
        Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch y)
      exact htail
    have hobservation : P.coordinatorObservation = Q.coordinatorObservation := by
      change P.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m) =
        Q.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)
      exact congrFun hfeedback (ActiveRoundActions.coordinator p.two_le_m)
    cases htag : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs P.coordinator with
    | inl _ =>
        have htagRight := htailPQ.symm.trans htag
        exact (observeCoordinator_eq_dagger_of_tailArgs P htag).trans
          (observeCoordinator_eq_dagger_of_tailArgs Q htagRight).symm
    | inr remaining =>
        cases remaining with
        | inl _ =>
            have htagRight := htailPQ.symm.trans htag
            exact (observeCoordinator_eq_failure_of_tailArgs P htag).trans
              (observeCoordinator_eq_failure_of_tailArgs Q htagRight).symm
        | inr data =>
            cases data with
            | inl args =>
                rcases args with ⟨registers, owned, base, started⟩
                have htagRight := htailPQ.symm.trans htag
                have hleft := observeCoordinator_eq_live_of_tailArgs P
                  registers owned base started htag
                have hright := observeCoordinator_eq_live_of_tailArgs Q
                  registers owned base started htagRight
                have htailObs :=
                  Bandits.Support.ReferenceActiveCoordinatorTemporal.livePostChoice_eq_of_current
                    state rows otherRows selected time active rewards otherRewards
                    registers owned base started hcurrent harm hobservation
                exact hleft.trans (htailObs.trans hright.symm)
            | inr args =>
                rcases args with ⟨payload, ledger, started, weights⟩
                have htagRight := htailPQ.symm.trans htag
                have hleft := observeCoordinator_eq_collection_of_tailArgs P
                  payload ledger started weights htag
                have hright := observeCoordinator_eq_collection_of_tailArgs Q
                  payload ledger started weights htagRight
                have hsenderConfiguration :
                    (P.followers.followers
                        (ReferenceActivePhysicalStep.upSenderIndex x)).configuration =
                      (Q.followers.followers
                        (ReferenceActivePhysicalStep.upSenderIndex x)).configuration := by
                  rw [P.followers.followers_eq (ReferenceActivePhysicalStep.upSenderIndex x),
                    ReferenceActiveFeedbackCut.prepareFollowers_apply,
                    Q.followers.followers_eq (ReferenceActivePhysicalStep.upSenderIndex x),
                    ReferenceActiveFeedbackCut.prepareFollowers_apply]
                  exact congrArg Prod.snd
                    (Bandits.Support.ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
                      (ReferenceActivePhysicalStep.upSenderIndex x)
                      (state.activations (ReferenceActivePhysicalStep.upSenderIndex x))
                      (active (ReferenceActivePhysicalStep.upSenderIndex x))
                      (state.followers (ReferenceActivePhysicalStep.upSenderIndex x)) hcurrent)
                have htailObs :=
                  Bandits.Support.ReferenceActiveCoordinatorTemporal.collectionPostChoice_eq_of_current
                    state rows otherRows selected time active rewards otherRewards
                    payload ledger started weights hcurrent harm hobservation hsenderConfiguration
                exact hleft.trans (htailObs.trans hright.symm)
  have hfollower : (fun i => P.observeFollower i) = fun i => Q.observeFollower i := by
    funext i
    have hobs :
        P.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          Q.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      change ActualInitializationPhysicalStep.observationOfGrid p
          (P.feedback.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        ActualInitializationPhysicalStep.observationOfGrid p
          (Q.feedback.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      exact congrArg (ActualInitializationPhysicalStep.observationOfGrid p)
        (congrFun hfeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    change ReferenceActivePhysicalStep.finishFollower P.coordinator.downView
        (P.followers.followers i)
        (P.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      ReferenceActivePhysicalStep.finishFollower Q.coordinator.downView
        (Q.followers.followers i)
        (Q.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    rw [← hview, P.followers.followers_eq i,
      ReferenceActiveFeedbackCut.prepareFollowers_apply, ← hobs,
      Q.followers.followers_eq i,
      ReferenceActiveFeedbackCut.prepareFollowers_apply]
    exact Bandits.Support.ReferenceActiveTemporalCausality.preparedFollower_eq_of_temporal_reads
      (P.coordinator.downView) i
      (state.activations i) (active i) (state.followers i)
      (ActualInitializationPhysicalStep.observationOfGrid p
        (P.feedback.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
      hcurrent (by
        intro s hs
        exact hpast s hs)
  have hnext : (ReferenceActivePhysicalStep.step x).next =
      (ReferenceActivePhysicalStep.step y).next := by
    change ReferenceActivePhysicalStep.State.mk
        P.observeCoordinator.configuration P.observeCoordinator.upDecoderBank
        state.activations (fun i => (P.observeFollower i).configuration) =
      ReferenceActivePhysicalStep.State.mk
        Q.observeCoordinator.configuration Q.observeCoordinator.upDecoderBank
        state.activations (fun i => (Q.observeFollower i).configuration)
    simp only [ReferenceActivePhysicalStep.State.mk.injEq]
    exact ⟨congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration
        hcoordinator,
      congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank hcoordinator,
      trivial,
      funext fun i => congrArg
        ReferenceActivePhysicalStep.FollowerObservation.configuration (congrFun hfollower i)⟩
  change ReferenceActivePhysicalHorizon.RoundEvidence.mk state time
      P.arms.actions P.feedback.feedback (ReferenceActivePhysicalStep.step x).ownEntries
      P.observeCoordinator (fun i => P.observeFollower i)
      (ReferenceActivePhysicalStep.step x).next =
    ReferenceActivePhysicalHorizon.RoundEvidence.mk state time
      Q.arms.actions Q.feedback.feedback (ReferenceActivePhysicalStep.step y).ownEntries
      Q.observeCoordinator (fun i => Q.observeFollower i)
      (ReferenceActivePhysicalStep.step y).next
  rw [hactions, hfeedback, hown, hcoordinator, hfollower, hnext]

/-- The existing physical calendar fold agrees when the selected complete row
has the same whole current controls and rewards on the interval, and the same
proposal scalars before its start. The compared record view is the evidence
projection, so retained row-indexed inputs are not equated. Source ranges:
`06_interruptions.tex:197-209,235-297,376-423`,
`appendix_a_local_protocol.tex:6-14`,
`appendix_b_communication.tex:25-55`, and `08_main_theorem.tex:29-42` in
`sources/zip4/manuscript/`. -/
theorem run_eq_of_temporal_reads
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hrewards : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      rewards j = otherRewards j)
    (hbefore : 0 < count → ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial otherRows selected otherRewards start count hspan hmode).finalState ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        (ReferenceActivePhysicalHorizon.run initial otherRows selected otherRewards start count hspan hmode).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  by_cases hzero : count = 0
  · subst count
    exact ReferenceActiveTemporalCausality.run_zero_eq initial rows otherRows selected
      rewards otherRewards start hspan hmode
  · unfold ReferenceActivePhysicalHorizon.run ReferenceActivePhysicalHorizon.foldCalendar
    refine List.foldl_rel
      (r := fun (left right : ReferenceActivePhysicalHorizon.Run initial) =>
        left.finalState = right.finalState ∧
          left.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
            right.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
      ⟨rfl, rfl⟩ ?_
    intro entry hentry left right hacc
    let x := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
      start hmode left entry
    let y := ReferenceActivePhysicalHorizon.roundInputAt initial otherRows selected otherRewards
      start hmode right entry
    let time : Fin p.T := ⟨entry.val, entry.property.2⟩
    have hbounds := ReferenceActiveTemporalCausality.calendarEntries_interval_bounds
      start count hspan entry hentry
    have hcontrol := hcontrols time hbounds.1 hbounds.2
    have hrewardsAt := hrewards time hbounds.1 hbounds.2
    have hpast := ReferenceActiveTemporalCausality.past_prop_eq_of_interval_reads
      start count time hbounds hcontrols hbefore
    have hlocal : ReferenceActivePhysicalHorizon.computedEvidence x =
        ReferenceActivePhysicalHorizon.computedEvidence
          ⟨x.state, otherRows, selected, x.time, x.active, otherRewards⟩ := by
      change ReferenceActivePhysicalHorizon.computedEvidence
          ⟨x.state, rows, selected, x.time, x.active, rewards⟩ =
        ReferenceActivePhysicalHorizon.computedEvidence
          ⟨x.state, otherRows, selected, x.time, x.active, otherRewards⟩
      exact computedEvidence_eq_of_temporal_reads x.state rows otherRows selected x.time
        x.active rewards otherRewards hcontrol hpast hrewardsAt
    have hcarry : ReferenceActivePhysicalHorizon.computedEvidence
          ⟨x.state, otherRows, selected, x.time, x.active, otherRewards⟩ =
        ReferenceActivePhysicalHorizon.computedEvidence y :=
      ReferenceActivePhysicalHorizon.computedEvidence_congr
        ⟨x.state, otherRows, selected, x.time, x.active, otherRewards⟩ y
        hacc.1 rfl rfl rfl rfl
    have hi : ReferenceActivePhysicalHorizon.computedEvidence x =
        ReferenceActivePhysicalHorizon.computedEvidence y := hlocal.trans hcarry
    constructor
    · change (ReferenceActivePhysicalStep.step x).next =
        (ReferenceActivePhysicalStep.step y).next
      exact congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hi
    · change (left.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk x
          (ReferenceActivePhysicalStep.step x) rfl]).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        (right.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk y
          (ReferenceActivePhysicalStep.step y) rfl]).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence
      simp only [List.map_append, List.map_singleton]
      exact congrArg₂
        (fun a b : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) => a ++ b)
        hacc.2 (congrArg (fun evidence => [evidence]) hi)

end Bandits.Support.ReferenceActiveTemporalAssembly

end
