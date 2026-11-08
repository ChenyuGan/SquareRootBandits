/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorLiveServiceFinish
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Live coordinator PREPARE / own-feedback OBSERVE cut

The operation follows `StartRound`, the coordinator's pre-observation arm
choice, its one local recorder call, service of every owned complement queue,
confirmation from the original pending set, and the actual `FinishRound`.
PREPARE returns the accepted continuation itself; OBSERVE consumes that same
continuation and the coordinator's typed own observation.

Sources: `sources/zip4/manuscript/06_interruptions.tex:37-70,235-296`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

This is the accepted unchanged-live-clock branch only. It does not install a
new assignment or perform collection transitions, and it proves no physical
history, adaptive law, or manuscript theorem closure.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.CoordinatorLiveServiceFinish

namespace Bandits.Support.CoordinatorLiveInteractive

abbrev Parameters := CoordinatorLiveServiceFinish.Parameters
abbrev LearningRate := CoordinatorLiveChoiceRecorderStep.LearningRate

variable {p : Parameters} {eta : LearningRate}

instance exactOutputCodeMeasurableSpace
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    MeasurableSpace (CoordinatorLiveServiceFinish.ExactOutputCode r q) := ⊤

instance outputCodeMeasurableSpace
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    MeasurableSpace (Except CoordinatorLiveServiceFinish.Failure
      (CoordinatorLiveServiceFinish.ExactOutputCode r q)) := ⊤

/-- PREPARE exposes the accepted continuation without adding stored state.
Only the already accepted failure-code map is applied to preparation errors. -/
noncomputable def prepareCut
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (row : CompleteRow p) :
    Except CoordinatorLiveServiceFinish.Failure
      (CoordinatorLiveChoiceRecorderStep.Continuation r row) := by
  classical
  exact match CoordinatorLiveChoiceRecorderStep.prepare r row with
  | .error failure => .error (CoordinatorLiveServiceFinish.prepareFailureCode failure)
  | .ok continuation => .ok continuation

/-- OBSERVE runs the accepted recorder once, serves every owned complement
queue, confirms against the original pending set, and calls actual
`finishRound`, in the same failure order as the accepted service operation. -/
noncomputable def observeOwnFeedback
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p}
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (observation : Fin (D p + 1)) :
    Except CoordinatorLiveServiceFinish.Failure
      (CoordinatorLiveServiceFinish.ExactOutputCode r q) := by
  classical
  exact match CoordinatorRecorderComplementBridge.run
      (CoordinatorLiveChoiceRecorderStep.recorderInput continuation observation) with
  | none => .error .recorderRejected
  | some recording =>
      match CoordinatorLiveServiceFinish.servicePass r q recording with
      | .error failure => .error failure
      | .ok serviced =>
          match CoordinatorLocalArmChoice.confirmationUpdate r.payload
              r.pendingAtChoice continuation.sourceCutoff r.time row observation with
          | none => .error .confirmationRejected
          | some pendingAfter =>
              match CoordinatorPhaseClock.finishRound p eta.val r.time
                  continuation.startRoundResult.clock pendingAfter row with
              | .error failure =>
                  .error (CoordinatorLiveServiceFinish.finishFailureCode failure)
              | .ok finishResult =>
                  .ok (CoordinatorLiveServiceFinish.codeOfServiced r q
                    continuation.ownArm recording pendingAfter
                    finishResult.clock.lastProposal serviced)

/-- The visible PREPARE-then-OBSERVE operation. -/
noncomputable def runPrepared
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row : CompleteRow p) (observation : Fin (D p + 1)) :
    Except CoordinatorLiveServiceFinish.Failure
      (CoordinatorLiveServiceFinish.ExactOutputCode r q) := by
  classical
  exact match prepareCut r row with
  | .error failure => .error failure
  | .ok continuation => observeOwnFeedback r q continuation observation

/-- The exposed cut is lossless: all preparation, recorder, service,
confirmation, clock, and finite-code fields and failures equal the integrated
`run` operation for every input, without a preparation-domain premise. -/
theorem runPrepared_eq_run
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row : CompleteRow p) (observation : Fin (D p + 1)) :
    runPrepared r q row observation =
      CoordinatorLiveServiceFinish.run r q row observation := by
  classical
  unfold runPrepared prepareCut CoordinatorLiveServiceFinish.run
  cases hprepare : CoordinatorLiveChoiceRecorderStep.prepare r row with
  | error failure => simp [CoordinatorLiveServiceFinish.prepareFailureCode]
  | ok continuation => rfl

/-- On any rejected local preparation, the accepted check order determines a
single failure tag independently of the complete row. The proof follows the
literal `prepare` branches and uses their accepted branch equations. -/
theorem prepare_error_of_not_domain
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (hnot : ¬ Nonempty (CoordinatorLiveChoiceRecorderStep.PreparationDomain r)) :
    ∃ failure, ∀ row : CompleteRow p,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .error failure := by
  classical
  cases hstart : CoordinatorPhaseClock.startRound p eta.val r.time
      r.priorClock r.clockPending with
  | error clockFailure =>
      exact ⟨.clockRejected, fun row =>
        CoordinatorLiveChoiceRecorderStep.prepare_clock_failure hstart⟩
  | ok startResult =>
      by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          r startResult
      · by_cases hsigma : r.priorClock.sigma = some r.payload.sigma
        · by_cases hgrid : r.gridBoundary = r.priorClock.g
          · by_cases hscore : r.scoreDomainValid
            · by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
                  r.time
              · by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                    r.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
                    r.time r.complementWeights
                · by_cases hboundary : r.gridBoundary ≤ p.T + 1
                  · by_cases henvelope : r.complementEnvelopeValid
                    · let domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r :=
                        { startResult := startResult
                          startRound_eq := hstart
                          clockFrame := hframe
                          payloadClockStart := hsigma
                          gridBoundary_eq_clock := hgrid
                          scoreDomainValid := hscore
                          assignmentLive := hlive
                          choiceInputsValid := hchoice
                          recorderInputsValid := ⟨hboundary, henvelope⟩ }
                      exact False.elim (hnot ⟨domain⟩)
                    · exact ⟨.complementEnvelopeFailure, fun row =>
                        CoordinatorLiveChoiceRecorderStep.prepare_complement_envelope_failure
                          hstart hframe hsigma hgrid hscore hlive hchoice
                          hboundary henvelope⟩
                  · exact ⟨.recorderBoundaryFailure, fun row =>
                      CoordinatorLiveChoiceRecorderStep.prepare_recorder_boundary_failure
                        hstart hframe hsigma hgrid hscore hlive hchoice hboundary⟩
                · exact ⟨.choiceDomainFailure, fun row =>
                    CoordinatorLiveChoiceRecorderStep.prepare_choice_domain_failure
                      hstart hframe hsigma hgrid hscore hlive hchoice⟩
              · exact ⟨.notLive, fun row =>
                  CoordinatorLiveChoiceRecorderStep.prepare_not_live_failure
                    hstart hframe hsigma hgrid hscore hlive⟩
            · exact ⟨.scoreDomainFailure, fun row =>
                CoordinatorLiveChoiceRecorderStep.prepare_score_domain_failure
                  hstart hframe hsigma hgrid hscore⟩
          · exact ⟨.gridBoundaryMismatch, fun row =>
              CoordinatorLiveChoiceRecorderStep.prepare_grid_boundary_failure
                hstart hframe hsigma hgrid⟩
        · exact ⟨.payloadClockMismatch, fun row =>
            CoordinatorLiveChoiceRecorderStep.prepare_payload_clock_failure
              hstart hframe hsigma⟩
      · exact ⟨.clockTransition, fun row =>
          CoordinatorLiveChoiceRecorderStep.prepare_clock_transition_failure
            hstart hframe⟩

/-- The accepted fixed-input recorder depends on a complete row only through
the time-control slice at its retained calendar coordinate. -/
theorem recorderRun_eq_of_same_current_timeControl
    (base : CoordinatorRecordingOperation.Input p)
    (row₁ row₂ : CompleteRow p) (arm : Fin p.K)
    (observation : Fin (D p + 1))
    (hcurrent : row₁.2 base.time = row₂.2 base.time) :
    CoordinatorRecordingOperation.run
        (CoordinatorRecordingMeasurability.inputAt base
          (row₁, (arm, observation))) =
      CoordinatorRecordingOperation.run
        (CoordinatorRecordingMeasurability.inputAt base
          (row₂, (arm, observation))) := by
  have hslice : ContinuousLearningRows.sliceAt base.time row₁.2 =
      ContinuousLearningRows.sliceAt base.time row₂.2 := by
    change (row₁.2 base.time).1 = (row₂.2 base.time).1
    rw [hcurrent]
  exact CoordinatorRecordingMeasurability.run_eq_of_current_slice_eq base
    (row₁, (arm, observation)) (row₂, (arm, observation)) hslice rfl rfl

/-- The finite post-preparation decoder used by the output factorization.
Every accepted failure tag is preserved by the actual recorder and service
operations. -/
noncomputable def outputCodeFactor
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    Option (CoordinatorRecordingOperation.Output p) ×
      (Option (Finset (ActiveRoundActions.Follower p.m)) ×
        (Fin p.K × Bool)) →
      Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ExactOutputCode r q) := by
  classical
  intro data
  exact match data.1 with
  | none => .error .recorderRejected
  | some recording =>
      match CoordinatorLiveServiceFinish.servicePass r q recording with
      | .error failure => .error failure
      | .ok serviced =>
          match data.2.1 with
          | none => .error .confirmationRejected
          | some pendingAfter =>
              .ok (CoordinatorLiveServiceFinish.codeOfServiced r q data.2.2.1
                recording pendingAfter
                (some (r.time, data.2.2.2)) serviced)

/-- On the accepted preparation domain, the integrated run factors through
the actual recorder, original-pending confirmation, selected arm, and current
proposal bit. The final saved clock is the accepted live `finishRound`. -/
theorem run_eq_outputCodeFactor_of_domain
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
    (value : CompleteRow p × Fin (D p + 1)) :
    CoordinatorLiveServiceFinish.run r q value.1 value.2 =
      outputCodeFactor r q
        (CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value,
          (CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r value,
            (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1,
              FollowerCutoffScan.completeRowProposalBit p eta.val value.1 r.time))) := by
  classical
  rcases CoordinatorLiveChoiceRecorderStep.prepare_success_of_domain domain
      value.1 with ⟨c, hprepare, _⟩
  have harm : c.ownArm =
      CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1 := by
    change c.ownArm =
      (CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
        r.pendingAtChoice
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
        r.time r.complementWeights value.1).getD ⟨0, K_pos p⟩
    rw [c.armChoice_eq]
    rfl
  have hrecord : CoordinatorRecorderComplementBridge.run
      (CoordinatorLiveChoiceRecorderStep.recorderInput c value.2) =
      CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value := by
    have hweights :
        CoordinatorRecorderComplementBridge.extendedCurrentWeights
          (CoordinatorLiveChoiceRecorderStep.flowRecorderInput r value.1
            (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1) value.2) =
        CoordinatorRecorderComplementBridge.extendedCurrentWeights
          (CoordinatorLiveChoiceRecorderStep.flowRecorderInput r
            (CoordinatorLiveChoiceRecorderStep.dummyCompleteRow p)
            ⟨0, K_pos p⟩ (CoordinatorLiveChoiceRecorderStep.zeroObservation p)) := by
      funext arm
      by_cases hslow : arm ∈ r.payload.slowSet.val
      · rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
            _ arm hslow,
          CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_anchor
            _ arm hslow]
      · let fast : FastArm r.payload.slowSet :=
          ⟨arm, Finset.mem_sdiff.mpr ⟨Finset.mem_univ arm, hslow⟩⟩
        rw [CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
              _ fast,
          CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement
              _ fast]
        rfl
    have hc : CoordinatorLiveChoiceRecorderStep.recorderInput c value.2 =
        CoordinatorLiveChoiceRecorderStep.flowRecorderInput r value.1
          c.ownArm value.2 := by
      simp only [CoordinatorLiveChoiceRecorderStep.recorderInput,
        CoordinatorLiveChoiceRecorderStep.flowRecorderInput, c.preChoiceMode_eq]
    have hinput : CoordinatorRecorderComplementBridge.recorderInput
        (CoordinatorLiveChoiceRecorderStep.recorderInput c value.2) =
      CoordinatorRecordingMeasurability.inputAt
        (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)
        (value.1, (CoordinatorLiveChoiceRecorderStep.flowArmAt r value.1,
          value.2)) := by
      rw [hc, harm]
      simp only [CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        CoordinatorRecordingMeasurability.inputAt,
        CoordinatorLiveChoiceRecorderStep.flowRecorderBase]
      rw [hweights]
      rfl
    rw [CoordinatorRecorderComplementBridge.run_eq_accepted, hinput]
    rfl
  cases hrecording : CoordinatorLiveChoiceRecorderStep.flowRecorderAt r value with
  | none => simp [CoordinatorLiveServiceFinish.run, hprepare, hrecord, hrecording,
      outputCodeFactor]
  | some recording =>
      cases hserviced : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error failure =>
          simp [CoordinatorLiveServiceFinish.run, hprepare, hrecord, hrecording,
            hserviced, outputCodeFactor]
      | ok serviced =>
          have hconfirmation :
              CoordinatorLocalArmChoice.confirmationUpdate r.payload
                r.pendingAtChoice c.sourceCutoff r.time value.1 value.2 =
              CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r value := rfl
          cases hpending : CoordinatorLiveChoiceRecorderStep.flowConfirmationAt
              r value with
          | none =>
              simp [CoordinatorLiveServiceFinish.run, hprepare, hrecord,
                hrecording, hserviced, hconfirmation, hpending, outputCodeFactor]
          | some pendingAfter =>
              obtain ⟨finishResult, hfinish, hclock, _, _⟩ :=
                CoordinatorLiveServiceFinish.finishRound_live_success domain c
                  hprepare pendingAfter
              simp [CoordinatorLiveServiceFinish.run, hprepare, hrecord,
                hrecording, hserviced, hconfirmation, hpending, hfinish,
                hclock, outputCodeFactor, CoordinatorLiveServiceFinish.codeOfServiced,
                CoordinatorLiveServiceFinish.savedProposalClock, harm]

/-- Complete output codes, including all rejection tags and finite fields,
depend on a row only through its current `TimeControl` and own observation. -/
theorem run_eq_of_same_current_timeControl
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row₁ row₂ : CompleteRow p) (observation : Fin (D p + 1))
    (hcurrent : row₁.2 r.time = row₂.2 r.time) :
    CoordinatorLiveServiceFinish.run r q row₁ observation =
      CoordinatorLiveServiceFinish.run r q row₂ observation := by
  classical
  by_cases hdomain : Nonempty (CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
  · let domain := hdomain.some
    rw [run_eq_outputCodeFactor_of_domain r q domain (row₁, observation),
      run_eq_outputCodeFactor_of_domain r q domain (row₂, observation)]
    congr 1
    have harmChoice :=
      CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
        r.payload r.pendingAtChoice
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
        r.time r.complementWeights row₁ row₂ hcurrent
    have harm : CoordinatorLiveChoiceRecorderStep.flowArmAt r row₁ =
        CoordinatorLiveChoiceRecorderStep.flowArmAt r row₂ := by
      simp [CoordinatorLiveChoiceRecorderStep.flowArmAt, harmChoice]
    have hrecord : CoordinatorLiveChoiceRecorderStep.flowRecorderAt r
        (row₁, observation) =
        CoordinatorLiveChoiceRecorderStep.flowRecorderAt r (row₂, observation) := by
      unfold CoordinatorLiveChoiceRecorderStep.flowRecorderAt
      calc
        CoordinatorRecordingOperation.run
            (CoordinatorRecordingMeasurability.inputAt
              (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)
              (row₁, (CoordinatorLiveChoiceRecorderStep.flowArmAt r row₁,
                observation))) =
          CoordinatorRecordingOperation.run
            (CoordinatorRecordingMeasurability.inputAt
              (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)
              (row₂, (CoordinatorLiveChoiceRecorderStep.flowArmAt r row₁,
                observation))) :=
          recorderRun_eq_of_same_current_timeControl _ row₁ row₂
            (CoordinatorLiveChoiceRecorderStep.flowArmAt r row₁) observation hcurrent
        _ = CoordinatorRecordingOperation.run
            (CoordinatorRecordingMeasurability.inputAt
              (CoordinatorLiveChoiceRecorderStep.flowRecorderBase r)
              (row₂, (CoordinatorLiveChoiceRecorderStep.flowArmAt r row₂,
                observation))) := by rw [harm]
    have hconfirmation :
        CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r (row₁, observation) =
          CoordinatorLiveChoiceRecorderStep.flowConfirmationAt r (row₂, observation) := by
      exact CoordinatorLocalArmChoice.confirmationUpdate_eq_of_same_current_timeControl
        r.payload r.pendingAtChoice
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
        r.time row₁ row₂ observation hcurrent
    have hproposal :
        FollowerCutoffScan.completeRowProposalBit p eta.val row₁ r.time =
          FollowerCutoffScan.completeRowProposalBit p eta.val row₂ r.time := by
      change FollowerCutoffScan.thresholdProposalBit
          ((row₁.2 r.time).1 ContinuousControlSlice.Label.prop)
          (FollowerCutoffScan.proposalHazard p eta.val) =
        FollowerCutoffScan.thresholdProposalBit
          ((row₂.2 r.time).1 ContinuousControlSlice.Label.prop)
          (FollowerCutoffScan.proposalHazard p eta.val)
      rw [hcurrent]
    simp only [hrecord, hconfirmation, harm, hproposal]
  · obtain ⟨failure, hfailure⟩ := prepare_error_of_not_domain r hdomain
    simp [CoordinatorLiveServiceFinish.run, hfailure row₁, hfailure row₂]

/-- A successful PREPARE arm is exactly the accepted current-row arm choice.
The continuation stores that arm before any own observation is supplied. -/
theorem prepared_arm_eq_choice
    {r : CoordinatorLiveChoiceRecorderStep.Registers p eta}
    {row : CompleteRow p}
    {continuation : CoordinatorLiveChoiceRecorderStep.Continuation r row}
    (h : prepareCut r row = .ok continuation) :
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload r.pendingAtChoice
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
      r.time r.complementWeights row = some continuation.ownArm := by
  have hprepare : CoordinatorLiveChoiceRecorderStep.prepare r row = .ok continuation := by
    cases hprepare : CoordinatorLiveChoiceRecorderStep.prepare r row with
    | error failure => simp [prepareCut, hprepare] at h
    | ok prepared =>
        have heq : (Except.ok prepared : Except CoordinatorLiveChoiceRecorderStep.PrepareFailure
            (CoordinatorLiveChoiceRecorderStep.Continuation r row)) = .ok continuation := by
          simpa [prepareCut, hprepare] using h
        have hprepared : prepared = continuation := Except.ok.inj heq
        rw [← hprepared]
  exact CoordinatorLiveChoiceRecorderStep.prepare_success_arm hprepare

/-- Any successful OBSERVE output retains the arm already stored in PREPARE. -/
theorem observe_success_arm
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p}
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (observation : Fin (D p + 1))
    {code : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h : observeOwnFeedback r q continuation observation = .ok code) :
    code.ownArm = continuation.ownArm := by
  classical
  unfold observeOwnFeedback at h
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (CoordinatorLiveChoiceRecorderStep.recorderInput continuation observation) with
  | none => simp [hrecording] at h
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error failure => simp [hrecording, hservice] at h
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate
              r.payload r.pendingAtChoice continuation.sourceCutoff r.time row observation with
          | none => simp [hrecording, hservice, hconfirmation] at h
          | some pendingAfter =>
              cases hfinish : CoordinatorPhaseClock.finishRound p eta.val r.time
                  continuation.startRoundResult.clock pendingAfter row with
              | error failure => simp [hrecording, hservice, hconfirmation, hfinish] at h
              | ok finishResult =>
                  have hcode : CoordinatorLiveServiceFinish.codeOfServiced r q
                      continuation.ownArm recording pendingAfter finishResult.clock.lastProposal
                      serviced = code := by
                    simpa [observeOwnFeedback, hrecording, hservice, hconfirmation,
                      hfinish] using h
                  simpa [CoordinatorLiveServiceFinish.codeOfServiced] using
                    congrArg (fun out : CoordinatorLiveServiceFinish.ExactOutputCode r q =>
                      out.ownArm) hcode.symm

/-- The observation-stage arm is independent of which own observation is
supplied; when both calls succeed, their retained arm fields are equal. -/
theorem observe_success_arms_eq
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p}
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation r row)
    (observation₁ observation₂ : Fin (D p + 1))
    {code₁ code₂ : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h₁ : observeOwnFeedback r q continuation observation₁ = .ok code₁)
    (h₂ : observeOwnFeedback r q continuation observation₂ = .ok code₂) :
    code₁.ownArm = code₂.ownArm := by
  rw [observe_success_arm r q continuation observation₁ h₁,
    observe_success_arm r q continuation observation₂ h₂]

/-- If the full run succeeds, its actual accepted preparation supplies the
row-independent domain needed by the existing recorder/service/clock
reconstruction theorem. -/
theorem preparationDomain_nonempty_of_run_success
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p} {observation : Fin (D p + 1)}
    {code : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h : CoordinatorLiveServiceFinish.run r q row observation = .ok code) :
    Nonempty (CoordinatorLiveChoiceRecorderStep.PreparationDomain r) := by
  by_contra hdomain
  obtain ⟨failure, hfailure⟩ := prepare_error_of_not_domain r hdomain
  simp [CoordinatorLiveServiceFinish.run, hfailure row] at h

/-- Extract the checked data package only after success has established that
its row-independent preparation domain is inhabited. -/
noncomputable def preparationDomain_of_run_success
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p} {observation : Fin (D p + 1)}
    {code : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h : CoordinatorLiveServiceFinish.run r q row observation = .ok code) :
    CoordinatorLiveChoiceRecorderStep.PreparationDomain r :=
  Classical.choice (preparationDomain_nonempty_of_run_success r q h)

/-- Every finite successful output field is the accepted recorder, service,
confirmation, and saved-clock result on the same prepared continuation. -/
theorem run_success_equations
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p} {observation : Fin (D p + 1)}
    {code : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h : CoordinatorLiveServiceFinish.run r q row observation = .ok code) :
    ∃ c recording serviced pendingAfter,
      CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
      CoordinatorRecorderComplementBridge.run
        (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) = some recording ∧
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
        c.sourceCutoff r.time row observation = some pendingAfter ∧
      c.ownArm = code.ownArm ∧ recording.gateArm = code.gateArm ∧
      recording.rawArrival = code.rawArrival.val ∧ pendingAfter = code.pendingAfter ∧
      (∀ j : FastArm r.payload.slowSet,
        code.arrival j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
          (serviced.arrival j) (serviced.arrivalDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.service j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
          (serviced.service j) (serviced.serviceDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.queue j.1 = some (CoordinatorLiveServiceFinish.codeNat (p.T * D p)
          (serviced.queue j) (serviced.queueDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.score j.1 = some (CoordinatorLiveServiceFinish.codeNat (p.T * D p)
          (serviced.score j) (serviced.scoreDomain j))) ∧
      (∀ j : FastArm r.payload.slowSet,
        code.previousService j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
          (serviced.previousService j) (serviced.previousServiceDomain j))) ∧
      code.savedProposal = some
        (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) := by
  exact CoordinatorLiveServiceFinish.run_success_equations
    (preparationDomain_of_run_success r q h) h

/-- A successful returned code is tied to the same prepared continuation,
single recorder result, complete service arrays, confirmation, and actual
saved proposal clock; the accepted decoder re-encodes each finite field. -/
theorem run_success_reconstruction
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    {row : CompleteRow p} {observation : Fin (D p + 1)}
    {code : CoordinatorLiveServiceFinish.ExactOutputCode r q}
    (h : CoordinatorLiveServiceFinish.run r q row observation = .ok code) :
    ∃ c recording serviced pendingAfter finishResult,
      (CoordinatorLiveChoiceRecorderStep.prepare r row = .ok c ∧
        CoordinatorRecorderComplementBridge.run
          (CoordinatorLiveChoiceRecorderStep.recorderInput c observation) =
            some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload r.pendingAtChoice
          c.sourceCutoff r.time row observation = some pendingAfter ∧
        c.ownArm = code.ownArm ∧ recording.gateArm = code.gateArm ∧
        recording.rawArrival = code.rawArrival.val ∧
        pendingAfter = code.pendingAfter ∧
        (∀ j : FastArm r.payload.slowSet,
          code.arrival j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
            (serviced.arrival j) (serviced.arrivalDomain j))) ∧
        (∀ j : FastArm r.payload.slowSet,
          code.service j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
            (serviced.service j) (serviced.serviceDomain j))) ∧
        (∀ j : FastArm r.payload.slowSet,
          code.queue j.1 = some (CoordinatorLiveServiceFinish.codeNat (p.T * D p)
            (serviced.queue j) (serviced.queueDomain j))) ∧
        (∀ j : FastArm r.payload.slowSet,
          code.score j.1 = some (CoordinatorLiveServiceFinish.codeNat (p.T * D p)
            (serviced.score j) (serviced.scoreDomain j))) ∧
        (∀ j : FastArm r.payload.slowSet,
          code.previousService j.1 = some (CoordinatorLiveServiceFinish.codeNat (D p)
            (serviced.previousService j) (serviced.previousServiceDomain j))) ∧
        code.savedProposal = some
          (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time)) ∧
      CoordinatorPhaseClock.finishRound p eta.val r.time c.startRoundResult.clock
        pendingAfter row = .ok finishResult ∧
      finishResult.clock = CoordinatorLiveServiceFinish.savedProposalClock
        eta r.priorClock r.time row ∧
      finishResult.clock.lastProposal = some
        (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) ∧
      finishResult.pending = pendingAfter ∧ finishResult.ledgerCommand = none ∧
      (let decoded := CoordinatorLiveServiceFinish.reconstructOutput c code;
        decoded.choice.ownArm = code.ownArm ∧
        decoded.choice.recorderOutput.gateArm = code.gateArm ∧
        decoded.choice.recorderOutput.rawArrival = code.rawArrival.val ∧
        decoded.choice.pendingAfter = code.pendingAfter ∧
        (∀ j, decoded.arrival j = code.arrival j.1) ∧
        (∀ j, decoded.service j = code.service j.1) ∧
        (∀ j, decoded.queue j = code.queue j.1) ∧
        (∀ j, decoded.score j = code.score j.1) ∧
        (∀ j, decoded.previousService j = code.previousService j.1) ∧
        decoded.savedProposal = code.savedProposal) := by
  classical
  rcases run_success_equations r q h with
    ⟨c, recording, serviced, pendingAfter, hfields⟩
  obtain ⟨finishResult, hfinish, hclock, hpending, hledger⟩ :=
    CoordinatorLiveServiceFinish.finishRound_live_success
      (preparationDomain_of_run_success r q h) c hfields.1 pendingAfter
  have hproposal : finishResult.clock.lastProposal = some
      (r.time, FollowerCutoffScan.completeRowProposalBit p eta.val row r.time) := by
    rw [hclock]
    simp [CoordinatorLiveServiceFinish.savedProposalClock]
  have hdecoded := CoordinatorLiveServiceFinish.code_reconstructOutput c code
  rcases hdecoded with
    ⟨hown, hgate, hraw, hcodePending, harrivals, hservices, hqueues, hscores, hsaved⟩
  have hprevious : ∀ j : FastArm r.payload.slowSet,
      (CoordinatorLiveServiceFinish.reconstructOutput c code).previousService j =
        code.previousService j.1 := by
    intro j
    rfl
  refine ⟨c, recording, serviced, pendingAfter, finishResult, hfields,
    hfinish, hclock, hproposal, hpending, hledger, ?_⟩
  simpa only using
    (show
      (CoordinatorLiveServiceFinish.reconstructOutput c code).choice.ownArm =
          code.ownArm ∧
        (CoordinatorLiveServiceFinish.reconstructOutput c code).choice.recorderOutput.gateArm =
          code.gateArm ∧
        (CoordinatorLiveServiceFinish.reconstructOutput c code).choice.recorderOutput.rawArrival =
          code.rawArrival.val ∧
        (CoordinatorLiveServiceFinish.reconstructOutput c code).choice.pendingAfter =
          code.pendingAfter ∧
        (∀ j, (CoordinatorLiveServiceFinish.reconstructOutput c code).arrival j =
          code.arrival j.1) ∧
        (∀ j, (CoordinatorLiveServiceFinish.reconstructOutput c code).service j =
          code.service j.1) ∧
        (∀ j, (CoordinatorLiveServiceFinish.reconstructOutput c code).queue j =
          code.queue j.1) ∧
        (∀ j, (CoordinatorLiveServiceFinish.reconstructOutput c code).score j =
          code.score j.1) ∧
        (∀ j, (CoordinatorLiveServiceFinish.reconstructOutput c code).previousService j =
          code.previousService j.1) ∧
        (CoordinatorLiveServiceFinish.reconstructOutput c code).savedProposal =
          code.savedProposal from
      ⟨hown, hgate, hraw, hcodePending, harrivals, hservices, hqueues, hscores,
        hprevious, hsaved⟩)

/-- Full joint measurability of the actual finite output code for arbitrary
fixed registers, including every rejected preparation branch. -/
theorem measurable_outputCode
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    Measurable (fun value : CompleteRow p × Fin (D p + 1) =>
      CoordinatorLiveServiceFinish.run r q value.1 value.2) := by
  classical
  by_cases hdomain : Nonempty (CoordinatorLiveChoiceRecorderStep.PreparationDomain r)
  · exact CoordinatorLiveServiceFinish.measurable_outputCode r q hdomain.some
  · obtain ⟨failure, hfailure⟩ := prepare_error_of_not_domain r hdomain
    have heq : (fun value : CompleteRow p × Fin (D p + 1) =>
        CoordinatorLiveServiceFinish.run r q value.1 value.2) =
        fun _ => .error (CoordinatorLiveServiceFinish.prepareFailureCode failure) := by
      funext value
      simp [CoordinatorLiveServiceFinish.run, hfailure value.1]
    rw [heq]
    exact measurable_const

/-- Composition with any measurable row/own-observation base map. -/
theorem measurable_outputCode_comp
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : α → CompleteRow p × Fin (D p + 1)) (hbase : Measurable base) :
    Measurable (fun x => CoordinatorLiveServiceFinish.run r q
      (base x).1 (base x).2) :=
  (measurable_outputCode r q).comp hbase

/-- Composition with separately supplied measurable complete-row and
coordinator-own-feedback maps. -/
theorem measurable_outputCode_comp_maps
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row : α → CompleteRow p) (observation : α → Fin (D p + 1))
    (hrow : Measurable row) (hobservation : Measurable observation) :
    Measurable (fun x => CoordinatorLiveServiceFinish.run r q
      (row x) (observation x)) := by
  exact measurable_outputCode_comp r q (fun x => (row x, observation x))
    (hrow.prodMk hobservation)

/-- Success-code events are measurable for the entire row/own-feedback
product. -/
theorem measurableSet_successEvent
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) :
    MeasurableSet {value : CompleteRow p × Fin (D p + 1) |
      ∃ code : CoordinatorLiveServiceFinish.ExactOutputCode r q,
        CoordinatorLiveServiceFinish.run r q value.1 value.2 = .ok code} := by
  have hrun := measurable_outputCode r q
  have hset : MeasurableSet
      ({result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ExactOutputCode r q) |
        ∃ code, result = .ok code} : Set (Except _ _)) := MeasurableSet.of_discrete
  change MeasurableSet ((fun value : CompleteRow p × Fin (D p + 1) =>
    CoordinatorLiveServiceFinish.run r q value.1 value.2) ⁻¹'
      {result | ∃ code, result = .ok code})
  exact hset.preimage hrun

/-- Each individual failure tag has a measurable inverse-image event. The
failure parameter ranges over every constructor of the accepted failure type. -/
theorem measurableSet_failureEvent
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (failure : CoordinatorLiveServiceFinish.Failure) :
    MeasurableSet {value : CompleteRow p × Fin (D p + 1) |
      CoordinatorLiveServiceFinish.run r q value.1 value.2 = .error failure} := by
  have hrun := measurable_outputCode r q
  have hset : MeasurableSet
      ({result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ExactOutputCode r q) |
        result = .error failure} : Set (Except _ _)) := MeasurableSet.of_discrete
  change MeasurableSet ((fun value : CompleteRow p × Fin (D p + 1) =>
    CoordinatorLiveServiceFinish.run r q value.1 value.2) ⁻¹'
      {result | result = .error failure})
  exact hset.preimage hrun

/-- Success events compose with any measurable row/own-observation map. -/
theorem measurableSet_successEvent_comp
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : α → CompleteRow p × Fin (D p + 1)) (hbase : Measurable base) :
    MeasurableSet {x : α |
      ∃ code : CoordinatorLiveServiceFinish.ExactOutputCode r q,
        CoordinatorLiveServiceFinish.run r q (base x).1 (base x).2 = .ok code} := by
  have hrun := measurable_outputCode_comp r q base hbase
  have hset : MeasurableSet
      ({result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ExactOutputCode r q) |
        ∃ code, result = .ok code} : Set (Except _ _)) := MeasurableSet.of_discrete
  change MeasurableSet ((fun x : α => CoordinatorLiveServiceFinish.run r q
    (base x).1 (base x).2) ⁻¹' {result | ∃ code, result = .ok code})
  exact hset.preimage hrun

/-- Every tagged failure event composes with any measurable
row/own-observation map. -/
theorem measurableSet_failureEvent_comp
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : α → CompleteRow p × Fin (D p + 1)) (hbase : Measurable base)
    (failure : CoordinatorLiveServiceFinish.Failure) :
    MeasurableSet {x : α |
      CoordinatorLiveServiceFinish.run r q (base x).1 (base x).2 = .error failure} := by
  have hrun := measurable_outputCode_comp r q base hbase
  have hset : MeasurableSet
      ({result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ExactOutputCode r q) |
        result = .error failure} : Set (Except _ _)) := MeasurableSet.of_discrete
  change MeasurableSet ((fun x : α => CoordinatorLiveServiceFinish.run r q
    (base x).1 (base x).2) ⁻¹' {result | result = .error failure})
  exact hset.preimage hrun

/-- Success events also compose directly with separate measurable maps for the
complete row and coordinator-own feedback. -/
theorem measurableSet_successEvent_comp_maps
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row : α → CompleteRow p) (observation : α → Fin (D p + 1))
    (hrow : Measurable row) (hobservation : Measurable observation) :
    MeasurableSet {x : α |
      ∃ code : CoordinatorLiveServiceFinish.ExactOutputCode r q,
        CoordinatorLiveServiceFinish.run r q (row x) (observation x) = .ok code} := by
  simpa using measurableSet_successEvent_comp r q
    (fun x => (row x, observation x)) (hrow.prodMk hobservation)

/-- Every tagged failure event composes directly with separate measurable
complete-row and coordinator-own-feedback maps. -/
theorem measurableSet_failureEvent_comp_maps
    {α : Type*} [MeasurableSpace α]
    (r : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (row : α → CompleteRow p) (observation : α → Fin (D p + 1))
    (hrow : Measurable row) (hobservation : Measurable observation)
    (failure : CoordinatorLiveServiceFinish.Failure) :
    MeasurableSet {x : α |
      CoordinatorLiveServiceFinish.run r q (row x) (observation x) =
        .error failure} := by
  simpa using measurableSet_failureEvent_comp r q
    (fun x => (row x, observation x)) (hrow.prodMk hobservation) failure

end Bandits.Support.CoordinatorLiveInteractive

end
