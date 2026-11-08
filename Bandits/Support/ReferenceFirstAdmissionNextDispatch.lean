/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAllKnownCollectionSampleInstall
public import Bandits.Support.ReferenceFirstAdmissionEmptyPendingInput

import Lean.Elab.Tactic.Omega

/-!
# Original-source next dispatch after first admission

Starting from the original-source first-admission constructor, retain its
exhausted rejected-prefix and nonempty-pending paths. At an accepted empty-
pending FINISH, carry the admitted physical boundary output and construct the
actual next round input only below the calendar horizon. Apply the admitted
all-known collection dispatcher to that constructed input, preserving its
underflow, prefix-failure, and successful-install branches.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
240-299`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-82`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37,97-174,219-243`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstAdmissionNextDispatch

/-- Original-source first admission, followed by the actual next dispatch at
an empty-pending boundary. The public telescope is exactly the original
first-admission input: one rate, source, whole reward table, shared unrestricted
constants, crossing, elapsed time, truncated execution length, and the
first-window condition. The terminal branch exposes the FINISH cursor and
final-state equations without making an action at `T`. -/
theorem first_admission_next_dispatch_cases
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : ReferenceGeneratedFirstCollectionAdmission.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s hsElapsed count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let b := w + 1
    let Q := (execution.records.drop b).takeWhile
      (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
    let hcount : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
            rate source rewards C_star C_h hcross s hsElapsed)
    let htail : b + Q.length ≤ count := by
      have hw : w < count := by simpa [execution, firstWindow, w] using hshort
      have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
      have hlen := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      omega
    let k := b + Q.length
    let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
      ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
        (by omega)
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∃ cut payload saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, firstWindow, w] using hshort
        simpa [execution, firstWindow, w] using Nat.lt_of_lt_of_eq hw hcount.symm) ∧
      (∃ ledger,
        (prefixAt Q.length (by omega)).finalState.coordinator =
          .collection payload ledger saved ∧
        ledger.pending = Finset.univ ∧ ledger.sigma = s + 1 ∧ ledger.cutoff = s + b ∧
        ((k = count ∧
          (prefixAt Q.length (by omega)).finalState = execution.finalState ∧
          (∀ htime : s + k < p.T,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
                  rate source rewards C_star C_h hcross s hsElapsed)
                (prefixAt Q.length (by omega)) ⟨s + k, by omega, htime⟩)
              payload ledger saved) ∧
          (s + k = p.T →
            ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
              (prefixAt Q.length (by omega)).finalState payload ledger saved)) ∨
         (∃ hendpoint : k < count,
          ∃ output : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
            source rewards C_star C_h hcross s hsElapsed count hspan execution B payload ledger
            saved w Q.length k,
            output.k_before_end = hendpoint ∧
            ∃ boundary : ReferenceGeneratedFirstCollectionAdmissionBoundary.AcceptedBoundaryOutput
              output,
              ((boundary.finished.pending = ∅ ∧
                ∃ empty : ReferenceFirstAdmissionEmptyPendingInput.EmptyPendingBoundaryOutput
                  output boundary,
                ((s + k + 1 = p.T ∧
                    boundary.finished.cursor = p.T + 1 ∧
                    empty.prefixState = execution.finalState) ∨
                 (∃ hbefore : s + k + 1 < p.T,
                  ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
                    next = ReferenceActivePhysicalHorizon.roundInputAt
                      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
                        rate source rewards C_star C_h hcross)
                      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                      rewards
                      (ReferenceInitializationRun.elapsed p
                        (ReferenceInitializationRun.output
                          (ActualReferenceInitializationBlock.referenceInput
                            source rewards C_star C_h rate)).completed)
                      output.actualMode output.actualPrefixNext
                      ⟨s + k + 1, by omega, hbefore⟩ ∧
                    next.state = output.actualPrefixNext.finalState ∧
                    next.state = output.record.output.next ∧
                    next.rows = source.1.2 ∧
                    next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                    next.rewards = rewards ∧
                    next.time.val = s + k + 1 ∧
                    boundary.finished.cursor = next.time.val + 1 ∧
                    CoordinatorUpReception.decoderBankCheck p next.state.upDecoderBank = true ∧
                    (∀ (hnext : k + 1 < count),
                      next = (output.actualRun.records[k + 1]'(by
                        rw [ReferenceGeneratedFirstCollectionAdmissionBoundary.admission_actual_run_record_count
                          output]
                        exact hnext)).input) ∧
                    (∃ cutoff : Fin p.T, cutoff.val + 1 = boundary.finished.cutoff ∧
                      let clock := ReferenceActivePhysicalStep.collectionClock payload
                        boundary.finished saved cutoff
                      let input := ReferenceActivePhysicalStep.collectionInput next payload
                        boundary.finished clock cutoff
                      ∃ core : CoordinatorRoundDispatch.CollectionCoreValid input,
                      ∃ started : CoordinatorPhaseClock.StartRoundResult p,
                      ∃ hstart : CoordinatorPhaseClock.startRound p rate.eta.val next.time
                        clock boundary.finished.pending = .ok started,
                      ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
                      ∃ hassignment : started.assignmentStart = some instruction,
                      let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
                        input core.payload_n_eq
                      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency
                        input.payload operationLedger,
                      instruction.time = next.time ∧
                      instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
                        operationLedger.freezeAt instruction.time ∧
                      (ReferenceActivePhysicalStep.prepare next).coordinator =
                        .collection payload boundary.finished clock cutoff
                          (CoordinatorRoundDispatch.dispatchCollection input) ∧
                      (AssignmentScoreReconstruction.reconstructLaterStart operationLedger
                          instruction = .failure .previousOutputDomain ↔
                        instruction.time.val + 1 < boundary.finished.freezeAt ∧
                          ∃ a c, boundary.finished.cutoffRegisters a = some c ∧
                            c.score < c.lastService) ∧
                      ((∃ a c, boundary.finished.cutoffRegisters a = some c ∧
                          c.score < c.lastService ∧
                          ∃ hrec : AssignmentScoreReconstruction.reconstructLaterStart
                            operationLedger instruction = .failure .previousOutputDomain,
                          instruction.kind = .corrected ∧
                          CoordinatorRoundDispatch.dispatchCollection input =
                            .laterReconstructionFailure core consistent started hstart
                              instruction hassignment .previousOutputDomain
                              (LaterAssignmentStartOperation.laterAssignmentStart_reconstructionFailure
                                input.payload operationLedger instruction input.row consistent
                                .previousOutputDomain hrec)) ∨
                       ∃ out : AssignmentScoreReconstruction.ReconstructedStart operationLedger
                          instruction,
                       AssignmentScoreReconstruction.reconstructLaterStart operationLedger
                          instruction = .success operationLedger instruction out ∧
                       ((∃ hcutoffReached : operationLedger.cutoff ≤ instruction.time.val + 1,
                          ∃ hcurrentPos : ∀ i,
                            0 < AssignmentScoreReconstruction.currentWeight out i,
                          ∃ law : LaterAssignmentStartOperation.SelectedLaw input.payload
                            operationLedger instruction out,
                          ∃ arm : Fin p.K,
                          ∃ reason : CheckedPrefixSampler.FailureReason,
                          instruction.kind = .corrected ∧
                          LaterAssignmentStartOperation.selectLaw? input.payload operationLedger
                            instruction out hcutoffReached hcurrentPos = some law ∧
                          ∃ previous,
                            AssignmentScoreReconstruction.previousWeight out = some previous ∧
                            (∀ i, 0 < previous i) ∧ law.anchor = input.payload.anchor ∧
                            (∀ S, law.mass S = LaterAssignmentStartOperation.correctedRawMass
                              input.payload operationLedger instruction out previous
                                hcutoffReached S) ∧
                          ∃ hlater : LaterAssignmentStartOperation.laterAssignmentStart
                            input.payload operationLedger instruction input.row consistent =
                              .prefixFailure (some arm) reason,
                          CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
                            (LaterAssignmentStartOperation.ownAssignmentVector input.row
                              instruction.time) = .prefixFailure (some arm) reason ∧
                          ∃ state : PrefixSetSampler.PrefixState p.K p.m,
                            CheckedPrefixSampler.runCheckedPrefix law.mass
                              (PrefixSamplerLaw.prefixValues
                                (LaterAssignmentStartOperation.ownAssignmentVector input.row
                                  instruction.time)) arm.val (Nat.le_of_lt arm.isLt) =
                                .ready state ∧
                            CheckedPrefixSampler.checkedStep law.mass
                              ((PrefixSamplerLaw.prefixValues
                                (LaterAssignmentStartOperation.ownAssignmentVector input.row
                                  instruction.time)) arm)
                              state arm = .failed arm reason ∧
                            0 < CheckedPrefixSampler.rawStateMass law.mass state ∧
                            ((reason = .probabilityBelowZero ∧
                                CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                                  CheckedPrefixSampler.rawStateMass law.mass state < 0) ∨
                             (reason = .probabilityAboveOne ∧
                                1 < CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                                  CheckedPrefixSampler.rawStateMass law.mass state)) ∧
                          CoordinatorRoundDispatch.dispatchCollection input =
                            .laterPrefixFailure core consistent started hstart instruction
                              hassignment (some arm) reason hlater) ∨
                        ∃ result : LaterAssignmentStartOperation.SuccessfulStart input.payload
                          operationLedger instruction input.row,
                        ∃ hlocal : result.localConsistency = consistent,
                        ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                          result,
                        ∃ installation : CoordinatorAssignmentRegisterInstall.LaterInstallation
                          result clockData,
                        ∃ selection : CoordinatorRoundDispatch.ArmSelection
                          installation.registers.payload started instruction.time
                          installation.registers.complementWeights input.row,
                          installation =
                            CoordinatorAssignmentRegisterInstall.installLater result clockData ∧
                          CoordinatorLocalArmChoice.coordinatorArmChoice
                            installation.registers.payload started.pending
                            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                            instruction.time installation.registers.complementWeights input.row =
                              some selection.arm ∧
                          result.reconstruction = out ∧
                          LaterAssignmentStartOperation.laterAssignmentStart input.payload
                            operationLedger instruction input.row consistent =
                              .success result hlocal ∧
                          CoordinatorRoundDispatch.dispatchCollection input =
                            .laterChosen core consistent started hstart instruction hassignment
                              result hlocal clockData installation selection ∧
                          LaterAssignmentStartOperation.selectLaw? input.payload operationLedger
                            instruction result.reconstruction result.cutoffReached
                            result.currentWeight_pos = some result.law ∧
                          result.assignmentVector =
                            LaterAssignmentStartOperation.ownAssignmentVector input.row
                              instruction.time ∧
                          CheckedAssignmentSample.checkedAssignmentSample p result.law.mass
                            result.law.anchor result.assignmentVector = .sampled result.outcome ∧
                          result.slowSet.1 = result.outcome.1.1.1.erase result.outcome.1.2 ∧
                          Finset.univ.image result.payload.assignment.assigned =
                            result.slowSet.1 ∧
                          StrictMono result.payload.assignment.assigned ∧
                          (result.payload.assignment.auxiliary ∈
                            CanonicalFastSampling.fastArmFinset result.slowSet ∧
                            (∀ j, j ∈ CanonicalFastSampling.fastArmFinset result.slowSet →
                              result.payload.anchor result.payload.assignment.auxiliary ≤
                                result.payload.anchor j) ∧
                            ∀ j, j ∈ CanonicalFastSampling.fastArmFinset result.slowSet →
                              result.payload.anchor result.payload.assignment.auxiliary =
                                result.payload.anchor j →
                                  result.payload.assignment.auxiliary ≤ j) ∧
                          (∀ a, result.payload.queues a =
                            AssignmentScoreReconstruction.initialQueue result.reconstruction a) ∧
                          (∀ i, result.baseScore i =
                            AssignmentScoreReconstruction.sourceScore result.reconstruction
                              (result.payload.assignment.assigned i)) ∧
                          (∀ i : ActiveRoundActions.Follower p.m,
                            installation.retainedBaseScore i =
                              AssignmentScoreReconstruction.sourceScore result.reconstruction
                                (result.payload.assignment.assigned i)) ∧
                          (instruction.kind = .corrected →
                            instruction.time.val + 1 < result.localConsistency.oldFreezeAt ∧
                            ∃ previous,
                              AssignmentScoreReconstruction.previousWeight
                                result.reconstruction = some previous ∧
                              (∀ i, 0 < previous i) ∧
                              result.payload.anchor = input.payload.anchor ∧
                              ∀ S, result.law.mass S =
                                LaterAssignmentStartOperation.correctedRawMass input.payload
                                  operationLedger instruction result.reconstruction previous
                                  result.cutoffReached S) ∧
                          (instruction.kind = .renewal →
                            AssignmentScoreReconstruction.previousScore result.reconstruction =
                              none ∧
                            AssignmentScoreReconstruction.previousWeight result.reconstruction =
                              none ∧
                            result.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
                            result.payload.anchor =
                              AssignmentScoreReconstruction.currentWeight
                                result.reconstruction ∧
                            (∀ S, result.law.mass S =
                              LaterAssignmentStartOperation.renewalRawMass
                                result.reconstruction S) ∧
                            ∀ vector : CheckedAssignmentSample.AssignmentVector p,
                              ∃ outcome,
                                CheckedAssignmentSample.checkedAssignmentSample p
                                  result.law.mass result.law.anchor vector = .sampled outcome) ∧
                          (∀ i : ActiveRoundActions.Follower p.m,
                            (result.payload.downRecord i).val =
                              ⟨instruction.time.val + 1,
                                (result.payload.assignment.assigned i).val + 1,
                                result.payload.assignment.auxiliary.val + 1,
                                result.payload.exponent
                                  (result.payload.assignment.assigned i),
                                AssignmentScoreReconstruction.initialQueue
                                  result.reconstruction
                                  (result.payload.assignment.assigned i)⟩) ∧
                          (∀ i : ActiveRoundActions.Follower p.m,
                            OrdinaryMessageCodec.dyadicRate
                              (result.payload.downRecord i).val.h =
                              CanonicalRecordingRates.xi p rate.eta.val result.payload.anchor
                                (result.payload.assignment.assigned i)))))))) ∨
                boundary.finished.pending.Nonempty)))) := by
  classical
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross s hsElapsed count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let b := w + 1
  let Q := (execution.records.drop b).takeWhile
    (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
  let k := b + Q.length
  have hFirst := ReferenceFirstAdmissionEmptyPendingInput.first_admission_empty_pending_input
    rate source rewards C_star C_h hcross s hsElapsed count hspan hshort
  dsimp only at hFirst
  rcases hFirst with ⟨cut, payload, saved, hcut, ledger, hcoordinator, hpending,
    hsigma, hcutoff, hbranch⟩
  refine ⟨cut, payload, saved, hcut, ledger, hcoordinator, hpending, hsigma,
    hcutoff, ?_⟩
  rcases hbranch with hexhausted | haccepted
  · exact Or.inl hexhausted
  · rcases haccepted with ⟨hendpoint, output, hendpointEq, boundary, hresult⟩
    refine Or.inr ⟨hendpoint, output, hendpointEq, ?_⟩
    refine ⟨boundary, ?_⟩
    rcases hresult with hempty | hnonempty
    · rcases hempty with ⟨hpendingEmpty, hconstructed⟩
      rcases hconstructed with ⟨empty⟩
      refine Or.inl ⟨hpendingEmpty, empty, ?_⟩
      have hnextIndex : k + 1 ≤ count := Nat.succ_le_of_lt hendpoint
      have hnextTimeLe : s + k + 1 ≤ p.T := by omega
      by_cases hterminal : s + k + 1 = p.T
      · left
        refine ⟨hterminal, empty.terminal_cursor hterminal, ?_⟩
        have hlast : k + 1 = count := by omega
        exact empty.prefix_next_is_execution_final_when_last hlast
      · right
        have hbefore : s + k + 1 < p.T := by omega
        refine ⟨hbefore, ?_⟩
        obtain ⟨next, hround, hnextActual, hnextRecord, hrows, hselected, hrewards,
          htime, hcursor, hbank, hnextRecordInput⟩ := empty.next_input hbefore
        refine ⟨next, hround, hnextActual, hnextRecord, hrows, hselected, hrewards,
          htime, hcursor, hbank, hnextRecordInput, ?_⟩
        have hnextState : next.state = empty.prefixState := by
          calc
            next.state = output.actualPrefixNext.finalState := hnextActual
            _ = empty.prefixState := empty.prefixState_is_actual_next.symm
        have hstate : next.state.coordinator = .collection payload boundary.finished saved := by
          rw [hnextState]
          exact empty.finished_coordinator
        have hN := ReferenceAllKnownCollectionSampleInstall.all_known_collection_next_dispatch_cases
          next payload boundary.finished saved hstate empty.finished_valid empty.finished_ready
          empty.finished_sigma empty.finished_sigma_lt_cutoff empty.finished_cutoff_lt_cursor
          hcursor empty.finished_freezeAt empty.finished_assignment empty.pending_empty
          empty.finished_anchor empty.finished_joint_mass empty.finished_joint_service hbank
        exact hN
    · exact Or.inr hnonempty

end Bandits.Support.ReferenceFirstAdmissionNextDispatch

end
