/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEpisodeScoreGrowth
public import Bandits.Support.ReferenceCompleteCollectionDispatchCore
public import Bandits.Support.ReferenceCompleteContinuingCollectionReception

import Lean.Elab.Tactic.Omega

/-!
# Actual nonempty continuing-collection choice domains

For each actual collection record on the complete source suffix, the retained
core and episode-envelope producers supply the real local data needed by the
continuing collection arm choice. This module constructs the successful
choice, then composes the actual recorder, UP reception, ledger FINISH, and
phase-clock FINISH. It makes no claim for empty-pending, first, live, or error
branches, and proves no sampler law or queue truth.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-114,140-188,219-243`,
`sources/zip4/manuscript/06_interruptions.tex:16-30,64-100,164-177,246-299,355-390`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorCollectionInteractive
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ReferenceUpReception

namespace Bandits.Support.ReferenceCompleteContinuingCollectionChoiceDomains

variable {p : ConstructorDimensions.Parameters}

private theorem collection_choice_inputs_valid_of_envelopes
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input)
    (envelope : ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
      (current : CoordinatorCollectionLedger.CurrentRegister),
      input.ledger.cutoffRegisters a = some cut →
      input.ledger.currentRegisters a = some current →
      input.payload.anchor a ≤
          AssignmentScoreReconstruction.sourceWeightBase p ^
            (cut.score + input.ledger.increment a) ∧
        AssignmentScoreReconstruction.sourceWeightBase p ^
            (cut.score + input.ledger.increment a) ≤ 2 * input.payload.anchor a) :
    CoordinatorLocalArmChoice.ChoiceInputsValid input.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
      input.time
      (CoordinatorCollectionInteractive.PreObservationInputs.weights input
        core.ledger_valid core.assignment_eq) := by
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    core.ledger_valid core.assignment_eq
  have htime := core.clock_start_time_valid
  simp only [CoordinatorPhaseClock.startRoundTimeValid, core.clock_sigma_eq,
    core.clock_cutoff_eq] at htime
  have hstarted : CoordinatorLocalArmChoice.assignmentStart input.payload ≤
      CoordinatorLocalArmChoice.sourceRound input.time := by
    dsimp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound]
    omega
  have hsigmaCutoff : input.payload.sigma.val < input.cutoffIndex.val := by
    have hclock := core.clock_registers_valid
    simp only [CoordinatorPhaseClock.clockRegistersValid, core.clock_sigma_eq,
      core.clock_cutoff_eq] at hclock
    rcases hclock with ⟨_, _, _, ⟨hsigmaCutoff, _⟩⟩
    exact hsigmaCutoff
  have hcutoff : CoordinatorLocalArmChoice.assignmentStart input.payload ≤
      CoordinatorLocalArmChoice.cutoffRound
        (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex)) := by
    dsimp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.cutoffRound,
      CoordinatorCollectionUpRoundStep.localCutoff,
      CoordinatorCollectionUpRoundStep.sourceCutoff]
    omega
  have hweights : ∀ j, 0 < weights j ∧ input.payload.anchor j.1 ≤ weights j ∧
      weights j ≤ 2 * input.payload.anchor j.1 := by
    intro j
    let a : Fin p.K := j.1
    have ha : a ∉ input.payload.slowSet.1 := (Finset.mem_sdiff.mp j.2).2
    obtain ⟨cut, hcut, current, hcurrent⟩ :=
      CoordinatorCollectionUpRoundStep.complementRegisters_known
        input.ledger input.payload core.ledger_valid core.assignment_eq a ha
    have hbound := envelope a cut current hcut hcurrent
    have hweightEq : weights j =
        AssignmentScoreReconstruction.sourceWeightBase p ^
          (cut.score + input.ledger.increment a) := by
      change ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (CoordinatorCollectionUpRoundStep.complementCurrentScore input.ledger
          input.payload core.ledger_valid core.assignment_eq a ha) = _
      rw [CoordinatorRoundDispatch.collection_complementCurrentScore_eq
        input core a ha cut hcut]
      rfl
    rw [hweightEq]
    exact ⟨lt_of_lt_of_le (input.payload.anchor_pos a) hbound.1,
      hbound.1, hbound.2⟩
  exact CoordinatorLocalArmChoice.choiceInputsValid_mk input.payload
    (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
    input.time weights hstarted hcutoff hweights

private theorem dispatchCollection_continuing_of_domains
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input)
    (hpending : input.ledger.pending.Nonempty)
    (hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .ok started)
    (hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid input.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
      input.time (CoordinatorCollectionInteractive.PreObservationInputs.weights input
        core.ledger_valid core.assignment_eq)) :
    ∃ snapshot : CoordinatorCollectionInteractive.PreparedSnapshot input,
      ∃ boundary : snapshot.clockStarted.clock.g ≤ p.T + 1,
        CoordinatorRoundDispatch.dispatchCollection input =
          .continuing core snapshot boundary hscores ∧
        snapshot.clockStarted = started := by
  classical
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    core.ledger_valid core.assignment_eq
  have hne := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    input.payload
    (by
      simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
        using started.pending)
    (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
    input.time weights input.row hchoice
  have hneActual : CoordinatorLocalArmChoice.coordinatorArmChoice input.payload
      started.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
      input.time weights input.row ≠ none := by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hne
  obtain ⟨arm, hselected⟩ := Option.ne_none_iff_exists.mp hneActual
  have hframe : started.clock = input.clock ∧ started.pending = input.ledger.pending ∧
      started.ledgerCommand = none ∧ started.assignmentStart = none := by
    have hut : input.cutoffIndex.val ≤ input.time.val := by
      have htimes := core.clock_start_time_valid
      simp only [CoordinatorPhaseClock.startRoundTimeValid, core.clock_sigma_eq,
        core.clock_cutoff_eq] at htimes
      exact htimes.2
    have hknown := CoordinatorPhaseClock.startRound_collection_pending
      p input.etaReal input.time input.payload.sigma input.cutoffIndex input.clock
      input.ledger.pending core.clock_parameter_valid core.clock_registers_valid
      core.clock_sigma_eq core.clock_cutoff_eq hut
      (Finset.nonempty_iff_ne_empty.mp hpending)
    have heq := Except.ok.inj (hstart.symm.trans hknown)
    rw [heq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
      some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex) := by
    rw [hframe.1, core.clock_cutoff_eq]
    rfl
  have hselectedDispatch : CoordinatorLocalArmChoice.coordinatorArmChoice input.payload
      (by
        simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
          using started.pending)
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      input.time (CoordinatorCollectionInteractive.PreObservationInputs.weights input
        core.ledger_valid core.assignment_eq) input.row = some arm := by
    simpa [hcutoff, weights, ActiveRoundActions.Follower,
      PublicDiscreteDraws.followerCount] using hselected.symm
  have hboundary : started.clock.g ≤ p.T + 1 := by
    have hgrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
      p input.etaReal input.clock core.clock_registers_valid
    have hgrid' := hgrid
    simp only [CoordinatorPhaseClock.clockGridDomain, core.clock_sigma_eq] at hgrid'
    simpa [hframe.1] using hgrid'.2
  let snapshot : CoordinatorCollectionInteractive.PreparedSnapshot input := {
    inputsValid := {
      ledger_valid := core.ledger_valid
      ledger_ready := core.ledger_ready
      pending_nonempty := hpending
      assignment_eq := core.assignment_eq
      base_score_eq := core.base_score_eq
      clock_parameter_valid := core.clock_parameter_valid
      clock_registers_valid := core.clock_registers_valid
      clock_start_time_valid := core.clock_start_time_valid
      clock_sigma_eq := core.clock_sigma_eq
      clock_cutoff_eq := core.clock_cutoff_eq
      ledger_sigma_eq := core.ledger_sigma_eq
      ledger_cutoff_eq := core.ledger_cutoff_eq
      ledger_freeze_eq := core.ledger_freeze_eq
      ledger_cursor_eq := core.ledger_cursor_eq
      decoder_bank_valid := core.decoder_bank_valid
      choice_valid := hchoice }
    clockStarted := started
    clockStarted_eq := hstart
    clockStarted_frame := hframe
    arm := arm
    armChoice_eq := by
      simpa [weights, CoordinatorCollectionInteractive.PreObservationInputs.weights,
        ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hselected.symm }
  have hdispatch : CoordinatorRoundDispatch.dispatchCollection input =
      .continuing core snapshot hboundary hscores := by
    unfold CoordinatorRoundDispatch.dispatchCollection
    split
    · rename_i failure hcall
      rw [hstart] at hcall
      contradiction
    · rename_i started' hcall
      have hstarted : started' = started := Except.ok.inj (hcall.symm.trans hstart)
      subst started'
      simp only [dite_eq_left core, dite_eq_left hpending,
        dite_eq_left hscores, dite_eq_left hchoice]
      split
      · rename_i hnone
        have hnone' : CoordinatorLocalArmChoice.coordinatorArmChoice input.payload
            (by
              simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
                using started.pending)
            (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
            input.time weights input.row = none := by
          simpa [hcutoff, ActiveRoundActions.Follower,
            PublicDiscreteDraws.followerCount] using hnone
        exact False.elim (hneActual hnone')
      · rename_i selected hsome
        have hselectedEq : selected = arm := Option.some.inj
          (hsome.symm.trans hselectedDispatch)
        subst selected
        simp [snapshot]
  exact ⟨snapshot, hboundary, hdispatch, rfl⟩

/-- Every actual nonempty continuing collection branch on the complete
source suffix has its checked arm-choice domains, an actual selected
continuing dispatch, and the original post-choice no-error result. The
retained incoming core supplies the checked registers and START; the retained
episode envelope is applied to those same present registers at this same
calendar coordinate. The theorem is conditional only on the literal source
collection state and its nonempty pending set.
-/
theorem complete_nonempty_continuing_collection_choice_domains
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
  ∀ (k : Fin records.length),
      let x := records[k.val]'k.isLt |>.input
      ∀ (P : ReferenceActivePhysicalStep.Payload rate)
        (l : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        (hstate : x.state.coordinator = .collection P l saved) →
        l.pending.Nonempty →
        ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
          let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
          let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
          ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
            (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true)
            (started : CoordinatorPhaseClock.StartRoundResult p),
            CoordinatorPhaseClock.startRound p rate.eta.val x.time input.clock
              l.pending = .ok started ∧
            (started.clock = input.clock ∧ started.pending = l.pending ∧
              started.ledgerCommand = none ∧ started.assignmentStart = none) ∧
            ∃ (choiceInputs : CoordinatorLocalArmChoice.ChoiceInputsValid input.payload
              (some (CoordinatorCollectionUpRoundStep.localCutoff u)) x.time
              (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                core.ledger_valid core.assignment_eq)),
            ∃ (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot input)
              (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1),
              CoordinatorRoundDispatch.dispatchCollection input =
                .continuing core snapshot boundary scores ∧
              snapshot.inputsValid.choice_valid = choiceInputs ∧
              snapshot.clockStarted = started ∧
              CoordinatorLocalArmChoice.coordinatorArmChoice input.payload started.pending
                (some (CoordinatorCollectionUpRoundStep.localCutoff u)) x.time
                (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                  core.ledger_valid core.assignment_eq) x.row = some snapshot.arm ∧
              ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate),
                ReferenceCollectionSegmentExtraction.choice x = some c ∧
                c = ⟨P, l, snapshot.clockStarted,
                  CoordinatorCollectionInteractive.PreObservationInputs.weights input
                    core.ledger_valid core.assignment_eq, none⟩ ∧
                CoordinatorLocalArmChoice.ChoiceInputsValid c.payload
                  (some (CoordinatorCollectionUpRoundStep.localCutoff u)) x.time c.weights ∧
                CoordinatorLocalArmChoice.coordinatorArmChoice c.payload started.pending
                  (some (CoordinatorCollectionUpRoundStep.localCutoff u)) x.time
                  c.weights x.row = some snapshot.arm ∧
                  ∃ (o : CoordinatorRecordingOperation.Output p)
                  (startedLedger finished : ReferenceActivePhysicalStep.Ledger rate)
                  (bank : CoordinatorUpReception.UpDecoderBank p)
                  (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
                    ⟨.collection P finished clockFinished.clock.lastProposal, bank, none,
                      some o, (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare x) startedLedger).diagnostic⟩ ∧
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator.failure = none ∧
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                    .collection P finished clockFinished.clock.lastProposal ∧
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator.upDecoderBank = bank ∧
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some o ∧
                  (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up =
                    (ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare x) startedLedger).diagnostic ∧
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare x) startedLedger).diagnostic =
                    some {
                      input := ReferenceUpReception.receptionInputAtRow rate x.row
                        (ReferenceActivePhysicalStep.upInputs
                          (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time
                      expected := ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare x)
                      decoderAfter := (CoordinatorUpReception.decoderTransition
                        (ReferenceUpReception.receptionInputAtRow rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time)).1
                      raw := (CoordinatorUpReception.decoderTransition
                        (ReferenceUpReception.receptionInputAtRow rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time)).2
                      parsed := ReferenceUpReception.rawParsedOutput rate
                        (ReferenceUpReception.receptionInputAtRow rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time)
                      locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate
                        (ReferenceUpReception.receptionInputAtRow rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time)
                      rawMatches := decide ((CoordinatorUpReception.decoderTransition
                        (ReferenceUpReception.receptionInputAtRow rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time)).2 =
                        ReferenceActivePhysicalStep.upExpected
                          (ReferenceActivePhysicalStep.prepare x))
                      wrongUniqueAccepted :=
                        ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                          rate x.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare x) startedLedger) x.time
                          ((ReferenceActivePhysicalStep.prepare x).followers.followers
                            (ReferenceActivePhysicalStep.upSenderIndex x))
                          ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                            (ReferenceActivePhysicalStep.upSenderIndex x)).1
                          (by simpa only [ReferenceUpReception.receptionInputAtRow_selectedFollower,
                            ReferenceActivePhysicalStep.upSenderIndex] using
                            ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                              (ReferenceActivePhysicalStep.upSenderIndex x)).2.1)
                          ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                            (ReferenceActivePhysicalStep.upSenderIndex x)).2.2.1 rfl } := by
  classical
  dsimp only
  intro k
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  intro P l saved hstate hpending
  have hstate' : x.state.coordinator = .collection P l saved := by
    simpa only [x] using hstate
  have hcoreRoot :=
    ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
      rate rewards C_star C_h source
  dsimp only at hcoreRoot
  obtain ⟨u, hu, core, scores, started, hstart, hframe, _hempty⟩ :=
    hcoreRoot k P l saved (by simpa only [x] using hstate)
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
  let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
  have henvelopeRoot :=
    ReferenceCompleteEpisodeScoreGrowth.complete_retained_episode_weight_envelopes
      p rate rewards C_star C_h source k
  rw [hstate] at henvelopeRoot
  have henvelope : ∀ (a : Fin p.K) (cut : CoordinatorCollectionLedger.CutoffRegister)
      (current : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
      P.anchor a ≤ AssignmentScoreReconstruction.sourceWeightBase p ^
          (cut.score + l.increment a) ∧
        AssignmentScoreReconstruction.sourceWeightBase p ^
          (cut.score + l.increment a) ≤ 2 * P.anchor a := by
    intro a cut current hcut hcurrent
    exact henvelopeRoot a cut current hcut hcurrent
  have hchoiceValid := collection_choice_inputs_valid_of_envelopes input core henvelope
  obtain ⟨snapshot, boundary, hdispatch, hclockStarted⟩ :=
    dispatchCollection_continuing_of_domains input core hpending scores started hstart
      hchoiceValid
  have hprepare : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection P l clock u (.continuing core snapshot boundary scores) := by
    have hcutoffRange : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
      constructor <;> have := u.isLt <;> omega
    have hcutoffVal : l.cutoff - 1 = u.val := by omega
    let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
    have hcutoff : cutoff = u := Fin.ext hcutoffVal
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate', dite_eq_left hcutoffRange, CoordinatorRoundDispatch.dispatch]
    change DispatchCut.collection P l
        (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x P l
            (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff)) =
      DispatchCut.collection P l clock u
        (.continuing core snapshot boundary scores)
    rw [hcutoff]
    simpa [clock, input] using hdispatch
  let c : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨P, l, snapshot.clockStarted,
      CoordinatorCollectionInteractive.PreObservationInputs.weights input
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
  have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
    simp [ReferenceCollectionSegmentExtraction.choice, hprepare,
      ReferenceCollectionSegmentExtraction.choiceOfCut,
      DispatchCut.selection, c,
      CoordinatorCollectionInteractive.PreObservationInputs.weights,
      ReferenceActivePhysicalStep.collectionInput, input, clock]
  have hchoiceEq :
      CoordinatorLocalArmChoice.ChoiceInputsValid c.payload
        (some (CoordinatorCollectionUpRoundStep.localCutoff u)) x.time c.weights := by
    change CoordinatorLocalArmChoice.ChoiceInputsValid input.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex)) input.time
      (CoordinatorCollectionInteractive.PreObservationInputs.weights input
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
    exact snapshot.inputsValid.choice_valid
  have harm : CoordinatorLocalArmChoice.coordinatorArmChoice c.payload
      started.pending (some (CoordinatorCollectionUpRoundStep.localCutoff u))
      x.time c.weights x.row = some snapshot.arm := by
    change CoordinatorLocalArmChoice.coordinatorArmChoice input.payload
      (by simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
        using started.pending)
      (some (CoordinatorCollectionUpRoundStep.localCutoff input.cutoffIndex))
      input.time (CoordinatorCollectionInteractive.PreObservationInputs.weights input
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) input.row =
      some snapshot.arm
    have hselectedSnap := snapshot.armChoice_eq
    rw [hclockStarted] at hselectedSnap
    simpa [id_eq, ActiveRoundActions.Follower,
      PublicDiscreteDraws.followerCount] using hselectedSnap
  refine ⟨u, hu, ?_⟩
  refine ⟨core, scores, started, hstart, hframe hpending, hchoiceValid, ?_⟩
  refine ⟨snapshot, boundary, hdispatch, rfl, hclockStarted, ?_, ?_⟩
  · exact harm
  · refine ⟨c, hchoice, rfl, hchoiceEq, harm, ?_⟩
    have hReception :=
      ReferenceCompleteContinuingCollectionReception.actual_continuing_collection_reception_finish
        rate rewards C_star C_h source k P l saved
        (by simpa only [x] using hstate) c hchoice
    rcases hReception with ⟨o, startedLedger, _decoded, bank, finished, clockFinished, hrest⟩
    rcases hrest with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, hclockRest⟩
    rcases hclockRest with ⟨_hclockValid, _hclockSigma, hclockTail⟩
    rcases hclockTail with ⟨_clockCutoff, hclockTail⟩
    rcases hclockTail with ⟨_hclockCutoff, hclockTail⟩
    rcases hclockTail with ⟨_hclockCutoffTime, hclockTail⟩
    rcases hclockTail with ⟨_hstartTime, hclockTail⟩
    rcases hclockTail with ⟨_hfinishTime, hclockTail⟩
    rcases hclockTail with ⟨_hclockFinish, hpostTail⟩
    rcases hpostTail with ⟨_hclockFinishActual, hpostTail⟩
    rcases hpostTail with ⟨_hpostChoice, hpostTail⟩
    rcases hpostTail with ⟨_hfinishOutput, hpostTail⟩
    rcases hpostTail with ⟨hobserve, hpostTail⟩
    rcases hpostTail with ⟨hdiagnostic, _hmismatch⟩
    have hfailure :
        (ReferenceActivePhysicalStep.prepare x).observeCoordinator.failure = none := by
      rw [hobserve]
    refine ⟨o, startedLedger, finished, bank, clockFinished,
      hobserve, hfailure, ?_, ?_, ?_, ?_, hdiagnostic⟩
    · exact congrArg CoordinatorObservation.configuration hobserve
    · exact congrArg CoordinatorObservation.upDecoderBank hobserve
    · exact congrArg CoordinatorObservation.recording hobserve
    · exact congrArg CoordinatorObservation.up hobserve
