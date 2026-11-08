/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterDispatchFibre
public import Bandits.Support.ReferenceAssignmentEffectCongruence

/-!
# Later assignment fibres through the actual physical round

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,235-296,376-423`,
`sources/zip4/manuscript/05_binary_transport.tex:62-80`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

This module assembles the admitted deterministic pre-choice and post-choice
comparisons for the existing physical step. It compares the complete checked
assignment vector through its successful slow-set fibre. No physical law,
truthful score reconstruction, or manuscript closure is assumed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLaterPhysicalFibreAssembly

open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceLaterDispatchFibre
open Bandits.Support.ReferenceAssignmentEffectCongruence
open Bandits.Support.AssignmentParameterFibreKernel
open MeasureTheory

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem withAssignment_state (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : (withAssignment x v).state = x.state := rfl

private theorem withAssignment_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : (withAssignment x v).time = x.time := rfl

private theorem rejected_coordinator
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hs : (ReferenceActivePhysicalStep.dispatch x).selection = none) :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
        .dispatchRejected none none := by
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
  change (if (ReferenceActivePhysicalStep.dispatch x).selection = none then _ else _) = _
  rw [ite_eq_left hs]
  dsimp only [ReferenceActivePhysicalStep.prepare]
  unfold ReferenceActivePhysicalStep.dispatch
  rw [hphase]
  dsimp only [CoordinatorRoundDispatch.dispatch]
  split_ifs <;> rfl

private theorem rejected_observation_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hv : (ReferenceActivePhysicalStep.dispatch (withAssignment x v)).selection = none)
    (hw : (ReferenceActivePhysicalStep.dispatch (withAssignment x w)).selection = none) :
    (ReferenceActivePhysicalStep.prepare (withAssignment x v)).observeCoordinator =
      (ReferenceActivePhysicalStep.prepare (withAssignment x w)).observeCoordinator := by
  have hstateV : (withAssignment x v).state.coordinator = .collection payload ledger proposal := by
    rw [withAssignment_state, hphase]
  have hstateW : (withAssignment x w).state.coordinator = .collection payload ledger proposal := by
    rw [withAssignment_state, hphase]
  rw [rejected_coordinator _ payload ledger proposal hstateV hv,
    rejected_coordinator _ payload ledger proposal hstateW hw]
  rfl

private theorem livePostChoice_pair_congr
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (left right : Σ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      CoordinatorLiveServiceFinish.OwnedRegisters r)
    (hp : left = right)
    (baseL baseR : Fin (p.m - 1) → ℕ) (hb : baseL = baseR)
    (startedL startedR : CoordinatorPhaseClock.StartRoundResult p) (hs : startedL = startedR) :
    ReferenceActivePhysicalStep.livePostChoice prepared left.1 left.2 baseL startedL =
      ReferenceActivePhysicalStep.livePostChoice prepared right.1 right.2 baseR startedR := by
  cases hp
  cases hb
  cases hs
  rfl

private theorem coordinator_observation_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    (ReferenceActivePhysicalStep.prepare (withAssignment x v)).observeCoordinator =
      (ReferenceActivePhysicalStep.prepare (withAssignment x w)).observeCoordinator := by
  classical
  have hcontinuations := ReferenceLaterDispatchFibre.dispatch_collection_continuations_fibre
    x payload ledger proposal hphase v w hf
  have harmDown := ReferenceLaterDispatchFibre.dispatch_collection_arm_downView_fibre
    x payload ledger proposal hphase v w hf
  have harm := harmDown.1
  have hstateV : (withAssignment x v).state.coordinator = .collection payload ledger proposal := by
    rw [withAssignment_state, hphase]
  have hstateW : (withAssignment x w).state.coordinator = .collection payload ledger proposal := by
    rw [withAssignment_state, hphase]
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
    let inputV := ReferenceActivePhysicalStep.collectionInput (withAssignment x v)
      payload ledger clock cutoff
    let inputW := ReferenceActivePhysicalStep.collectionInput (withAssignment x w)
      payload ledger clock cutoff
    have hcutV : ReferenceActivePhysicalStep.dispatch (withAssignment x v) =
        .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection inputV) := by
      simp only [ReferenceActivePhysicalStep.dispatch, hstateV, hcutoff,
        CoordinatorRoundDispatch.dispatch]
      rfl
    have hcutW : ReferenceActivePhysicalStep.dispatch (withAssignment x w) =
        .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection inputW) := by
      simp only [ReferenceActivePhysicalStep.dispatch, hstateW, hcutoff,
        CoordinatorRoundDispatch.dispatch]
      rfl
    have hp := hcontinuations
    rw [hcutV, hcutW] at hp
    cases hleft : CoordinatorRoundDispatch.dispatchCollection inputV
    case continuing coreL snapshotL boundaryL currentL =>
      cases hright : CoordinatorRoundDispatch.dispatchCollection inputW
      case continuing coreR snapshotR boundaryR currentR =>
        rw [hleft, hright] at hp
        rcases hp with ⟨_, _, _, _, hstarted, _, hweights⟩
        have hweightsEq := eq_of_heq hweights
        have hpost := ReferenceAssignmentEffectCongruence.collection_post_choice_fibre
          x v w harm payload ledger snapshotL.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput (withAssignment x v)
              payload ledger clock cutoff)
            snapshotL.inputsValid.ledger_valid snapshotL.inputsValid.assignment_eq)
        have hcutV' := hcutV
        have hcutW' := hcutW
        rw [hleft] at hcutV'
        rw [hright] at hcutW'
        have hcoordinatorV : (ReferenceActivePhysicalStep.prepare (withAssignment x v)).coordinator =
            .collection payload ledger clock cutoff
              (.continuing coreL snapshotL boundaryL currentL) := by
          simpa [ReferenceActivePhysicalStep.prepare] using hcutV'
        have hcoordinatorW : (ReferenceActivePhysicalStep.prepare (withAssignment x w)).coordinator =
            .collection payload ledger clock cutoff
              (.continuing coreR snapshotR boundaryR currentR) := by
          simpa [ReferenceActivePhysicalStep.prepare] using hcutW'
        have hobsV := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          (ReferenceActivePhysicalStep.prepare (withAssignment x v)) payload ledger clock cutoff
          (.continuing coreL snapshotL boundaryL currentL) hcoordinatorV
        have hobsW := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          (ReferenceActivePhysicalStep.prepare (withAssignment x w)) payload ledger clock cutoff
          (.continuing coreR snapshotR boundaryR currentR) hcoordinatorW
        rw [hobsV, hobsW]
        simpa [ReferenceActivePhysicalStep.DispatchCut.selection, hstarted, hweightsEq] using hpost
      all_goals
        rw [hleft, hright] at hp
        have hselV : (ReferenceActivePhysicalStep.dispatch (withAssignment x v)).selection = none := by
          rw [hcutV, hleft]
          exact hp.1
        have hselW : (ReferenceActivePhysicalStep.dispatch (withAssignment x w)).selection = none := by
          rw [hcutW, hright]
          exact hp.2
        exact rejected_observation_eq x payload ledger proposal hphase v w hselV hselW
    case laterChosen coreL consistentL startedL startEqL instructionL instructionEqL
        outputL localEqL clockDataL installationL selectionL =>
      cases hright : CoordinatorRoundDispatch.dispatchCollection inputW
      case laterChosen coreR consistentR startedR startEqR instructionR instructionEqR
          outputR localEqR clockDataR installationR selectionR =>
        rw [hleft, hright] at hp
        rcases hp with ⟨htimeL, htimeR, _, _, hstarted, _, hregisters,
          howned, hbase, _, _, _hsuccessL, _hsuccessR, _hinstallL, _hinstallR⟩
        have hinstalledPair :
            (⟨installationL.registers, installationL.ownedRegisters⟩ :
              Σ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
                CoordinatorLiveServiceFinish.OwnedRegisters r) =
            ⟨installationR.registers, installationR.ownedRegisters⟩ := by
          apply Sigma.ext hregisters
          exact howned
        have hpostTransport := livePostChoice_pair_congr
          (ReferenceActivePhysicalStep.prepare (withAssignment x w))
          (⟨installationR.registers, installationR.ownedRegisters⟩)
          (⟨installationL.registers, installationL.ownedRegisters⟩)
          hinstalledPair.symm
          installationR.retainedBaseScore installationL.retainedBaseScore
          hbase.symm startedR startedL hstarted.symm
        have hpost := ReferenceAssignmentEffectCongruence.live_post_choice_fibre
          x v w harm
          installationL.registers installationL.ownedRegisters
          installationL.retainedBaseScore
          startedL
        have hcutV' := hcutV
        have hcutW' := hcutW
        rw [hleft] at hcutV'
        rw [hright] at hcutW'
        have hcoordinatorV : (ReferenceActivePhysicalStep.prepare (withAssignment x v)).coordinator =
            .collection payload ledger clock cutoff
              (.laterChosen coreL consistentL startedL startEqL instructionL instructionEqL
                outputL localEqL clockDataL installationL selectionL) := by
          simpa [ReferenceActivePhysicalStep.prepare] using hcutV'
        have hcoordinatorW : (ReferenceActivePhysicalStep.prepare (withAssignment x w)).coordinator =
            .collection payload ledger clock cutoff
              (.laterChosen coreR consistentR startedR startEqR instructionR instructionEqR
                outputR localEqR clockDataR installationR selectionR) := by
          simpa [ReferenceActivePhysicalStep.prepare] using hcutW'
        have hobsV := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          (ReferenceActivePhysicalStep.prepare (withAssignment x v)) payload ledger clock cutoff
          (.laterChosen coreL consistentL startedL startEqL instructionL instructionEqL
            outputL localEqL clockDataL installationL selectionL) hcoordinatorV
        have hobsW := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          (ReferenceActivePhysicalStep.prepare (withAssignment x w)) payload ledger clock cutoff
          (.laterChosen coreR consistentR startedR startEqR instructionR instructionEqR
            outputR localEqR clockDataR installationR selectionR) hcoordinatorW
        rw [hobsV, hobsW]
        simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, withAssignment_time,
          htimeL, htimeR] using
          hpost.trans hpostTransport.symm
      all_goals
        rw [hleft, hright] at hp
        have hselV : (ReferenceActivePhysicalStep.dispatch (withAssignment x v)).selection = none := by
          rw [hcutV, hleft]
          exact hp.1
        have hselW : (ReferenceActivePhysicalStep.dispatch (withAssignment x w)).selection = none := by
          rw [hcutW, hright]
          exact hp.2
        exact rejected_observation_eq x payload ledger proposal hphase v w hselV hselW
    all_goals
      cases hright : CoordinatorRoundDispatch.dispatchCollection inputW
      all_goals
        rw [hleft, hright] at hp
        have hselV : (ReferenceActivePhysicalStep.dispatch (withAssignment x v)).selection = none := by
          rw [hcutV, hleft]
          exact hp.1
        have hselW : (ReferenceActivePhysicalStep.dispatch (withAssignment x w)).selection = none := by
          rw [hcutW, hright]
          exact hp.2
        exact rejected_observation_eq x payload ledger proposal hphase v w hselV hselW
  · have hbadV := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
      (withAssignment x v) payload ledger proposal hstateV hcutoff
    have hbadW := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
      (withAssignment x w) payload ledger proposal hstateW hcutoff
    have hselV : (ReferenceActivePhysicalStep.dispatch (withAssignment x v)).selection = none := by
      rw [hbadV.1]
      rfl
    have hselW : (ReferenceActivePhysicalStep.dispatch (withAssignment x w)).selection = none := by
      rw [hbadW.1]
      rfl
    exact rejected_observation_eq x payload ledger proposal hphase v w hselV hselW

/-- Whole deterministic physical evidence is constant on the actual later
assignment-sampler fibre. The only hypotheses are the incoming collection
phase selector and the successful slow-set equality at the original optional
parameters. All rejected dispatcher paths remain present, including different
sampler failure tags; only the evidence projection erases those raw tags.
-/
theorem computedEvidence_later_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    ReferenceActivePhysicalHorizon.computedEvidence (withAssignment x v) =
      ReferenceActivePhysicalHorizon.computedEvidence (withAssignment x w) := by
  have harmDown := ReferenceLaterDispatchFibre.dispatch_collection_arm_downView_fibre
    x payload ledger proposal hphase v w hf
  have hcoordinator := coordinator_observation_fibre x payload ledger proposal hphase v w hf
  exact ReferenceAssignmentEffectCongruence.computed_evidence_fibre x v w
    harmDown.1 harmDown.2 hcoordinator

/-- The actual `S.step` output projections inherit the evidence equality:
full action profile, grid feedback, own entries, coordinator and follower
observations, and the complete successor configuration are retained. -/
theorem step_projections_later_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    let left := ReferenceActivePhysicalStep.step (withAssignment x v)
    let right := ReferenceActivePhysicalStep.step (withAssignment x w)
    left.next = right.next ∧
      left.preparation.arms.actions = right.preparation.arms.actions ∧
      left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
      left.ownEntries = right.ownEntries ∧
      left.coordinator = right.coordinator ∧
      left.followers = right.followers := by
  let left := ReferenceActivePhysicalStep.step (withAssignment x v)
  let right := ReferenceActivePhysicalStep.step (withAssignment x w)
  have he := computedEvidence_later_fibre x payload ledger proposal hphase v w hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after he
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.actions, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.actions he
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback he
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.ownEntries, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.ownEntries he
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.coordinator he
  · simpa [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.followerDiagnostics, left, right] using
      congrArg ReferenceActivePhysicalHorizon.RoundEvidence.followers he

/-- The literal input at the next coordinate of `H.run`, starting from the
actual prefix accumulator and using its actual fixed table, index, and rewards.
This is a named projection of the existing run, not a parallel trace. -/
def runSuccessorInput
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode)
    ⟨start + count, by omega, by omega⟩

/-- Specialize the same physical fibre theorem to the real next record of the
existing `H.run`. `run_successor_step` and `run_record_inputs` supply its
membership and unchanged public input fields; no trace or alternate run is an
additional premise. The result remains conditional on this actual record's
phase and successful-slow-set fibre. -/
theorem run_successor_record_later_fibre
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : (runSuccessorInput initial rows selected rewards start count hspan hmode).state.coordinator =
      .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match ReferenceLaterAssignmentFibreStep.parameters?
        (runSuccessorInput initial rows selected rewards start count hspan hmode) with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    ∃ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (count + 1) hspan hmode).records,
      record.input = runSuccessorInput initial rows selected rewards start count hspan hmode ∧
      record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards ∧
      ReferenceActivePhysicalHorizon.computedEvidence (withAssignment record.input v) =
        ReferenceActivePhysicalHorizon.computedEvidence (withAssignment record.input w) := by
  let runPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    (by omega) hmode
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start + count, by omega, by omega⟩
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    runPrefix entry
  have hinput : input = runSuccessorInput initial rows selected rewards start count hspan hmode := rfl
  let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
  have hrecord : record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (count + 1) hspan hmode).records := by
    rw [ReferenceActivePhysicalHorizon.run_successor_step initial rows selected rewards
      start count hspan hmode]
    have hfold := (ReferenceActivePhysicalHorizon.foldRound_equations initial rows selected
      rewards start hmode runPrefix entry).2
    change record ∈
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
        runPrefix entry).records
    rw [hfold]
    apply List.mem_append.mpr
    right
    simp only [List.mem_singleton]
    rfl
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs initial rows selected rewards
    start (count + 1) hspan hmode record hrecord
  refine ⟨record, hrecord, hinput, hinputs.1, hinputs.2.1, hinputs.2.2, ?_⟩
  have hphase' : input.state.coordinator = .collection payload ledger proposal := by
    rw [hinput]
    exact hphase
  have hf' : match ReferenceLaterAssignmentFibreStep.parameters? input with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w := by
    rw [hinput]
    exact hf
  simpa [record] using computedEvidence_later_fibre input payload ledger proposal hphase' v w hf'

/-- At the actual later-sampler parameter, each positive-mass conditional
fibre gives almost-sure physical-evidence equality. This is only a conditional
fibre statement; it does not establish a feasible corrected law or a bridge to
the recorded run. -/
theorem ae_computedEvidence_later_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (hpos : 0 < AssignmentParameterFibreKernel.fibreMass p theta a)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (hv : AssignmentParameterFibreKernel.successfulSlowSet p theta v = a) :
    ∀ᵐ w ∂AssignmentParameterFibreKernel.fibreMeasure p theta a,
      ReferenceActivePhysicalHorizon.computedEvidence (withAssignment x v) =
        ReferenceActivePhysicalHorizon.computedEvidence (withAssignment x w) := by
  filter_upwards [AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos
    p theta a hpos] with w hw
  have hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta' => AssignmentParameterFibreKernel.successfulSlowSet p theta' v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta' w := by
    rw [hparameters]
    exact hv.trans hw.symm
  exact computedEvidence_later_fibre x payload ledger proposal hphase v w hf

/-- The admitted joint-measure identity instantiated at the actual optional
parameter of a physical input. It reconstructs the original full-vector law
through finite fibres; by itself it proves neither a feasible corrected law
nor a `RecordedRunBridge`. -/
local instance actualOutcomeMeasurableSpace :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

theorem actualParameter_jointMeasure_eq_map
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta) :
    ReferenceLaterAssignmentFibreStep.parameters? x = some theta ∧
      AssignmentParameterFibreKernel.jointMeasure p (Measure.dirac theta) =
        ((Measure.dirac theta).prod (ContinuousControlSlice.assignmentLaw p.K)).map
          (fun z : AssignmentParameterFibreKernel.Theta p × CheckedAssignmentSample.AssignmentVector p =>
            ((z.1, AssignmentParameterFibreKernel.successfulSlowSet p z.1 z.2), z.2)) := by
  exact ⟨hparameters, AssignmentParameterFibreKernel.jointMeasure_eq_map p (Measure.dirac theta)⟩

end Bandits.Support.ReferenceLaterPhysicalFibreAssembly

end
