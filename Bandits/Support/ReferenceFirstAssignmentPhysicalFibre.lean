/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstAssignmentFibreStep
public import Bandits.Support.ReferenceAssignmentEffectCongruence

/-!
# First-assignment physical-fibre congruence

For one actual first-coordinator round, changing only the complete selected
assignment vector within a common first-launch sampler fibre preserves the
whole computed physical evidence. The accepted inverse control-coordinate
split retains every non-assignment scalar and affine channel. The proof follows
the actual first installation, dispatch, follower tails, and live
post-choice operation, including their checked failure outputs.

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,195-233,376-423`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

These are internal pointwise results. They do not establish a conditional
physical law, a launched-state reachability claim, manuscript closure, or the
main regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceFirstAssignmentPhysicalFibre

abbrev Parameters := ReferenceActivePhysicalHorizon.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev AssignmentVector := LaunchAssignmentCoordinateSplit.AssignmentVector

variable {p : Parameters} {rate : RateInput p}

private def zeroOwnedRegisters
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) :
    CoordinatorLiveServiceFinish.OwnedRegisters registers := {
  queue := fun _ => 0
  previousService := fun _ => 0
}

private theorem ownedRegisters_ext
    {registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta}
    (left right : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (hqueue : left.queue = right.queue)
    (hservice : left.previousService = right.previousService) : left = right := by
  cases left with
  | mk leftQueue leftService =>
    cases right with
    | mk rightQueue rightService =>
      cases hqueue
      cases hservice
      rfl

private theorem choiceTimeView_registers_eq
    (registersV registersW : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (startedV startedW : CoordinatorPhaseClock.StartRoundResult p)
    (hregisters : registersV = registersW) (hstarted : startedV = startedW) :
    (ReferenceDownReception.ChoiceTimeView.mk registersV.payload startedV.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p startedV.clock.u)
      registersV.complementWeights) =
    (ReferenceDownReception.ChoiceTimeView.mk registersW.payload startedW.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p startedW.clock.u)
      registersW.complementWeights) := by
  cases hregisters
  cases hstarted
  rfl

/-- The first-step coordinate update is the accepted later-fibre update on the
same inverse control-assignment split and the same retained remainder. -/
theorem assignmentCoordinateUpdate_eq_controlWithAssignment
    (x : RoundInput p rate) (v : AssignmentVector p) :
    ReferenceFirstAssignmentFibreStep.assignmentCoordinateUpdate x v =
      ReferenceLaterAssignmentFibreStep.controlWithAssignment x v := rfl

/-- The first-step row replacement is the accepted later-fibre row
replacement, with its forward arrays and every other calendar slice intact. -/
theorem assignmentFibreRow_eq_rowWithAssignment
    (x : RoundInput p rate) (v : AssignmentVector p) :
    ReferenceFirstAssignmentFibreStep.assignmentFibreRow x v =
      ReferenceLaterAssignmentFibreStep.rowWithAssignment x v := rfl

/-- The first-step input replacement is the same selected-row update as the
accepted later-fibre input replacement. -/
theorem assignmentFibreInput_eq_withAssignment
    (x : RoundInput p rate) (v : AssignmentVector p) :
    ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v =
      ReferenceLaterAssignmentFibreStep.withAssignment x v := rfl

private theorem first_installed_data
    (x : RoundInput p rate) (v w : AssignmentVector p)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    let xv := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v
    let xw := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w
    ∃ installedV selectedV installedW selectedW,
      CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput xv) = .chosen installedV selectedV ∧
      CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput xw) = .chosen installedW selectedW ∧
      installedV.registers = installedW.registers ∧
      installedV.followerBaseScore = installedW.followerBaseScore ∧
      installedV.startRoundResult = installedW.startRoundResult := by
  let xv := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v
  let xw := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w
  obtain ⟨installedV, selectedV, hdispatchV⟩ :=
    ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
      (ReferenceActivePhysicalStep.firstInput xv)
  obtain ⟨installedW, selectedW, hdispatchW⟩ :=
    ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
      (ReferenceActivePhysicalStep.firstInput xw)
  refine ⟨installedV, selectedV, installedW, selectedW, hdispatchV, hdispatchW, ?_, ?_, ?_⟩
  · rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xv installedV selectedV hdispatchV,
      ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xw installedW selectedW hdispatchW]
    exact ReferenceFirstAssignmentFibreStep.firstRegisters_assignmentFibre_eq x v w hsampler
  · rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xv installedV selectedV hdispatchV,
      ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xw installedW selectedW hdispatchW]
    funext i
    rfl
  · rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xv installedV selectedV hdispatchV,
      ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xw installedW selectedW hdispatchW]
    simp [CoordinatorAssignmentRegisterInstall.installFirst,
      CoordinatorAssignmentRegisterInstall.firstStartRoundResult,
      CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, xv, xw,
      ReferenceFirstAssignmentFibreStep.assignmentFibreInput]

private theorem chosen_first_down_view
    (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput x)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      x.row)
    (htime : installed.registers.time = x.time) :
    (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed selected)).downView =
      some {
        payload := installed.registers.payload
        pendingAtChoice := installed.startRoundResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
          installed.startRoundResult.clock.u
        complementWeights := installed.registers.complementWeights } := by
  simp [ReferenceActivePhysicalStep.DispatchCut.downView,
    ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, htime]

private theorem first_down_view_eq
    (x : RoundInput p rate) (v w : AssignmentVector p)
    (hfirst : x.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    (ReferenceActivePhysicalStep.dispatch
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v)).downView =
    (ReferenceActivePhysicalStep.dispatch
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w)).downView := by
  let xv := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v
  let xw := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w
  obtain ⟨installedV, selectedV, installedW, selectedW, hdispatchV, hdispatchW,
      hregs, _, hstarted⟩ := first_installed_data x v w hsampler
  have htimeV := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    xv installedV selectedV hdispatchV
  have htimeW := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    xw installedW selectedW hdispatchW
  have hfirstV : xv.state.coordinator = .first := by
    simpa [xv, ReferenceFirstAssignmentFibreStep.assignmentFibreInput] using hfirst
  have hfirstW : xw.state.coordinator = .first := by
    simpa [xw, ReferenceFirstAssignmentFibreStep.assignmentFibreInput] using hfirst
  have hchosenViews :
      (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedV selectedV)).downView =
      (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedW selectedW)).downView := by
    rw [chosen_first_down_view xv installedV selectedV htimeV,
      chosen_first_down_view xw installedW selectedW htimeW]
    apply congrArg some
    exact choiceTimeView_registers_eq installedV.registers installedW.registers
      installedV.startRoundResult installedW.startRoundResult hregs hstarted
  calc
    _ = (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedV selectedV)).downView := by
      rw [ReferenceActivePhysicalStep.dispatch_first xv hfirstV, hdispatchV]
    _ = (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedW selectedW)).downView := hchosenViews
    _ = _ := by
      rw [ReferenceActivePhysicalStep.dispatch_first xw hfirstW, hdispatchW]

private theorem first_coordinator_observation_eq
    (x : RoundInput p rate) (v w : AssignmentVector p)
    (hfirst : x.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    (ReferenceActivePhysicalStep.prepare
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v)).observeCoordinator =
    (ReferenceActivePhysicalStep.prepare
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w)).observeCoordinator := by
  let xv := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v
  let xw := ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w
  obtain ⟨installedV, selectedV, installedW, selectedW, hdispatchV, hdispatchW,
      hregs, hbase, hstarted⟩ := first_installed_data x v w hsampler
  have hfirstV : xv.state.coordinator = .first := by
    simpa [xv, ReferenceFirstAssignmentFibreStep.assignmentFibreInput] using hfirst
  have hfirstW : xw.state.coordinator = .first := by
    simpa [xw, ReferenceFirstAssignmentFibreStep.assignmentFibreInput] using hfirst
  have hcutV : (ReferenceActivePhysicalStep.prepare xv).coordinator =
      .first (.chosen installedV selectedV) := by
    simp [ReferenceActivePhysicalStep.prepare, xv,
      ReferenceActivePhysicalStep.dispatch_first xv hfirstV, hdispatchV]
  have hcutW : (ReferenceActivePhysicalStep.prepare xw).coordinator =
      .first (.chosen installedW selectedW) := by
    simp [ReferenceActivePhysicalStep.prepare, xw,
      ReferenceActivePhysicalStep.dispatch_first xw hfirstW, hdispatchW]
  have htimeV := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    xv installedV selectedV hdispatchV
  have htimeW := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    xw installedW selectedW hdispatchW
  have hselectedV :
      (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedV selectedV)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, htimeV, xv]
  have hselectedW :
      (ReferenceActivePhysicalStep.DispatchCut.first
        (.chosen installedW selectedW)).selection ≠ none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, htimeW, xw]
  have harm := ReferenceFirstAssignmentFibreStep.dispatchFirst_arm_assignmentFibre_eq
    x v w hfirst hsampler
  have hownedV : installedV.ownedRegisters = zeroOwnedRegisters installedV.registers := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xv installedV selectedV hdispatchV]
    apply ownedRegisters_ext
    · funext j
      rfl
    · funext j
      rfl
  have hownedW : installedW.ownedRegisters = zeroOwnedRegisters installedW.registers := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      xw installedW selectedW hdispatchW]
    apply ownedRegisters_ext
    · funext j
      rfl
    · funext j
      rfl
  have hobs :
      ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare
            (ReferenceLaterAssignmentFibreStep.withAssignment x v))
          installedV.registers installedV.ownedRegisters installedV.followerBaseScore
          installedV.startRoundResult =
        ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare
            (ReferenceLaterAssignmentFibreStep.withAssignment x w))
          installedW.registers installedW.ownedRegisters installedW.followerBaseScore
          installedW.startRoundResult := by
    have hcommon := ReferenceAssignmentEffectCongruence.live_post_choice_fibre x v w harm
      installedV.registers (zeroOwnedRegisters installedV.registers)
      installedV.followerBaseScore installedV.startRoundResult
    have hregTail := congrArg
      (fun registers => ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare
          (ReferenceLaterAssignmentFibreStep.withAssignment x w))
        registers (zeroOwnedRegisters registers) installedV.followerBaseScore
        installedV.startRoundResult) hregs
    have hbaseTail := congrArg
      (fun base => ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare
          (ReferenceLaterAssignmentFibreStep.withAssignment x w))
        installedW.registers (zeroOwnedRegisters installedW.registers) base
        installedV.startRoundResult) hbase
    have hstartedTail := congrArg
      (fun started => ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare
          (ReferenceLaterAssignmentFibreStep.withAssignment x w))
        installedW.registers (zeroOwnedRegisters installedW.registers)
        installedW.followerBaseScore started) hstarted
    calc
      _ = ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare
            (ReferenceLaterAssignmentFibreStep.withAssignment x v))
          installedV.registers (zeroOwnedRegisters installedV.registers)
          installedV.followerBaseScore installedV.startRoundResult := by
        rw [hownedV]
      _ = ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare
            (ReferenceLaterAssignmentFibreStep.withAssignment x w))
          installedV.registers (zeroOwnedRegisters installedV.registers)
          installedV.followerBaseScore installedV.startRoundResult := hcommon
      _ = ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare
            (ReferenceLaterAssignmentFibreStep.withAssignment x w))
          installedW.registers (zeroOwnedRegisters installedW.registers)
          installedW.followerBaseScore installedW.startRoundResult :=
        hregTail.trans (hbaseTail.trans hstartedTail)
      _ = _ := by rw [hownedW]
  change ReferenceActivePhysicalStep.livePostChoice
      (ReferenceActivePhysicalStep.prepare xv) installedV.registers installedV.ownedRegisters
      installedV.followerBaseScore installedV.startRoundResult =
    ReferenceActivePhysicalStep.livePostChoice
      (ReferenceActivePhysicalStep.prepare xw) installedW.registers installedW.ownedRegisters
      installedW.followerBaseScore installedW.startRoundResult at hobs
  rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
      (ReferenceActivePhysicalStep.prepare xv) (.chosen installedV selectedV) hcutV,
    ReferenceActivePhysicalStep.observeCoordinator_first_equation
      (ReferenceActivePhysicalStep.prepare xw) (.chosen installedW selectedW) hcutW]
  simpa [hselectedV, hselectedW] using hobs

/-- The actual first-assignment sampler fibre preserves the entire computed
physical evidence: before state, simultaneous actions, grid feedback, own
entries, coordinator diagnostics, every follower diagnostic, and successor
state. Only the current complete assignment vector is replaced. -/
theorem computedEvidence_assignmentFibre_eq
    (x : RoundInput p rate) (v w : AssignmentVector p)
    (hfirst : x.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x v) =
      ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput x w) := by
  apply ReferenceAssignmentEffectCongruence.computed_evidence_fibre
  · exact ReferenceFirstAssignmentFibreStep.dispatchFirst_arm_assignmentFibre_eq
      x v w hfirst hsampler
  · exact first_down_view_eq x v w hfirst hsampler
  · exact first_coordinator_observation_eq x v w hfirst hsampler

/-- The actual RoundRecord specialization retains its input's complete table,
rewards, selected row index, private state, activation proof, and shared rate. -/
theorem roundRecord_computedEvidence_assignmentFibre_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v w : AssignmentVector p)
    (hfirst : record.input.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput record.input v) =
      ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput record.input w) :=
  computedEvidence_assignmentFibre_eq record.input v w hfirst hsampler

/-- Projection form of the actual-record result, including every diagnostic
and the full successor consequence. -/
theorem roundRecord_physical_projections_assignmentFibre_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v w : AssignmentVector p)
    (hfirst : record.input.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    let evidenceV := ReferenceActivePhysicalHorizon.computedEvidence
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput record.input v)
    let evidenceW := ReferenceActivePhysicalHorizon.computedEvidence
      (ReferenceFirstAssignmentFibreStep.assignmentFibreInput record.input w)
    evidenceV.actions = evidenceW.actions ∧
      evidenceV.gridFeedback = evidenceW.gridFeedback ∧
      evidenceV.ownEntries = evidenceW.ownEntries ∧
      evidenceV.coordinator = evidenceW.coordinator ∧
      evidenceV.followers = evidenceW.followers ∧
      evidenceV.after = evidenceW.after := by
  dsimp only
  have h := roundRecord_computedEvidence_assignmentFibre_eq record v w hfirst hsampler
  exact ⟨congrArg ReferenceActivePhysicalHorizon.RoundEvidence.actions h,
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback h,
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.ownEntries h,
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.coordinator h,
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.followers h,
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after h⟩

/-- Specialize the pointwise result to the accepted actual launched boundary.
The original source retains its published complete rows and private index
coordinate, while the original rewards, shared constants/rate, boundary,
past replay, launch, learner seed, and every constructor input remain bound.
The only round-domain premise is the explicit active-time typing condition
derived from the actual block endpoint. -/
theorem actualLaunchedBoundary_computedEvidence_assignmentFibre_eq
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
      (ActualReferenceInitializationBlock.referenceInput source rewards
        C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards
            C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards
            C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards
        C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (time : Fin p.T)
    (hafter : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) ≤ time.val)
    (v w : AssignmentVector p)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    let boundary := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce
      launch learnerSeed hlaunched
    let input : RoundInput p rate := {
      state := boundary
      rows := source.1.2
      selected := ActualInitializationPhysicalStep.selectedRowIndex p source
      time := time
      active := ActualInitializationLaunchState.ofActualLaunchedBoundary_activeAtTime
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce
        launch learnerSeed hlaunched time hafter
      rewards := rewards }
    ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput input v) =
      ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceFirstAssignmentFibreStep.assignmentFibreInput input w) := by
  dsimp only
  apply computedEvidence_assignmentFibre_eq
  · exact ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce
      launch learnerSeed hlaunched
  · exact hsampler

end Bandits.Support.ReferenceFirstAssignmentPhysicalFibre
