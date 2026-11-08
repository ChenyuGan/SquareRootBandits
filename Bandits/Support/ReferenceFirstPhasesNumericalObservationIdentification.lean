/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterCollectionCalendarMeasurability
public import Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream

import Lean.Elab.Tactic.Omega

/-!
# Numerical observations on the actual first phases

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,192-233,246-295`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

These internal identities connect the literal first-live and first-collection
records to their existing full numerical queue inputs. They preserve the
actual marker, enabled bit, reward vector and rate vector, including zero
arrivals and disabled collection cells. They make no total-calendar or
regret-closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstCollectionReadyStream
open Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream
open Bandits.Support.ReferenceFirstCollectionCheckedSourcePrefix
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceLaterCollectionArrivalReadout
open Bandits.Support.RecordedQueueRun
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ReferenceFirstPhasesNumericalObservationIdentification

variable {p : ConstructorDimensions.Parameters}

private theorem run_crossing_completed_pos
    (x : ReferenceInitializationRun.Input p) :
    ∀ r, (ReferenceInitializationRun.run x r).crossing.isSome = true →
      0 < (ReferenceInitializationRun.run x r).completed := by
  intro r
  induction r with
  | zero =>
      intro hc
      simp [ReferenceInitializationRun.run_zero,
        ReferenceInitializationRun.initial] at hc
  | succ r ih =>
      intro hc
      by_cases hprior : (ReferenceInitializationRun.run x r).crossing.isSome = true
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_crossing x _ hprior]
        exact ih hprior
      · have hnone : (ReferenceInitializationRun.run x r).crossing = none := by
          cases h : (ReferenceInitializationRun.run x r).crossing with
          | none => rfl
          | some value => simp [h] at hprior
        by_cases hlt : (ReferenceInitializationRun.run x r).completed < BootstrapDimensions.n_boot p
        · have hrun : ReferenceInitializationRun.run x (r + 1) =
              ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r) hlt := by
            rw [ReferenceInitializationRun.run_succ,
              ReferenceInitializationRun.advance_of_no_crossing x _ hnone hlt]
          rw [hrun, (ReferenceInitializationRun.finishBlock_equations x _ hlt).1]
          omega
        · have hexhausted : BootstrapDimensions.n_boot p ≤ (ReferenceInitializationRun.run x r).completed :=
            Nat.le_of_not_gt hlt
          have hrun : ReferenceInitializationRun.run x (r + 1) =
              ReferenceInitializationRun.run x r := by
            rw [ReferenceInitializationRun.run_succ,
              ReferenceInitializationRun.advance_of_exhausted x _ hexhausted]
          rw [hrun] at hc
          simp [hnone] at hc

private theorem first_live_collection_readout_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :
    ∀ k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hcross count hspan).length,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hcross count hspan)[k.val] = none := by
  classical
  let boot := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let start := ReferenceInitializationRun.elapsed p boot.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hcross
  let execution := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hcross count hspan
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
    seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  dsimp only at htruth
  intro k
  change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
    ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        seed.activeAtStart).records)[k.val]) = none
  have hk := htruth k
  rcases hk with ⟨_, _, states, memories, hordinary, hbranches⟩
  rcases hbranches with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, hcoord, _hfields, _htime, _selected, _rest⟩
    change ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        seed.activeAtStart).records)[k.val]).output.preparation.coordinator = _ at hcoord
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord]
  · rcases hcontinuing with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hcoord,
        _hfields, _selected, _rest⟩
    change ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        seed.activeAtStart).records)[k.val]).output.preparation.coordinator = _ at hcoord
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord]

private theorem numericalRoundInput_ext {K : ℕ}
    (a b : RecordedQueueRun.RoundInput K)
    (henabled : a.enabled = b.enabled)
    (hmarker : a.recordedArm = b.recordedArm)
    (hreward : a.reward = b.reward)
    (hrate : a.rate = b.rate) : a = b := by
  cases a
  cases b
  cases henabled
  cases hmarker
  cases hreward
  cases hrate
  rfl

/-- At the first cutoff, the literal C readout is the same cell as the
checked source prefix. The head's actual choice fixes payload, ledger, clock
and weights; C's public readout fields identify the enabled bit and marker. -/
private theorem first_cutoff_readout_sourceCell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (head : ReferenceCollectionSegmentExtraction.Choice rate)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hrewards : record.input.rewards = rewards)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        head.payload head.started head.weights))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : ∃ dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected,
      record.output.preparation.coordinator =
        .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected))
    (hfollowers : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record)
    (hsigma : 0 < registers.payload.sigma.val)
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some head) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record =
      some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate record head rewards valid) := by
  classical
  rcases hcoord with ⟨dispatched, hstart, ledger, hinit, hcand, hdomain,
    hclock, hpending, hnone, selected, hcoord⟩
  let cutoffCell := ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
    record registers owned base dispatched selected
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcoordInput : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected) := by
    rw [← hprep]
    exact hcoord
  have hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record =
      some cutoffCell := by
    simp [cutoffCell, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      hfollowers, hcoord, hsigma]
  obtain ⟨payload, callLedger, started, weights, recorder, hcall, _hpost,
    _hrun, hEnabled, hstartedClock, hrate, hreward, _hdiag, _hgate, _harrivals⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
        0 record cutoffCell hread
  let actualChoice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
      dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
        base record.input.time)⟩
  have hselection :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
    rw [hcoordInput]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  have hchoiceActual : ReferenceCollectionSegmentExtraction.choice record.input =
      some actualChoice := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [if_neg hselection]
    simp [actualChoice, ReferenceCollectionSegmentExtraction.choiceOfCut, hcoordInput]
  have hactualHead : actualChoice = head :=
    Option.some.inj (hchoiceActual.symm.trans hchoice)
  let actualCall : Σ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
        (CanonicalFastSampling.FastArm payload.slowSet → ℝ) :=
    ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
      dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights⟩
  have hcallActual : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
      some actualCall := by
    simp [actualCall, ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
      hfollowers, hcoord, hsigma]
  have hparamsChoice : actualCall =
      (⟨head.payload, head.preLedger, head.started, head.weights⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) := by
    exact congrArg (fun c : ReferenceCollectionSegmentExtraction.Choice rate =>
      (⟨c.payload, c.preLedger, c.started, c.weights⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
            (CanonicalFastSampling.FastArm payload.slowSet → ℝ))) hactualHead
  have hcallParams :
      (⟨payload, callLedger, started, weights⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
      (⟨head.payload, head.preLedger, head.started, head.weights⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) := by
    exact (Option.some.inj (hcallActual.symm.trans hcall)).symm.trans hparamsChoice
  cases hcallParams
  have hEnabled' : cutoffCell.enabled =
      ReferenceActivePhysicalStep.collectionEnabled head.preLedger record.input.time := by
    simpa [cutoffCell] using hEnabled
  have hstartedEq : head.started = dispatched.startResult := by
    have h := congrArg ReferenceCollectionSegmentExtraction.Choice.started hactualHead.symm
    simpa [actualChoice] using h
  have hpayload : head.payload = registers.payload := by
    have h := congrArg ReferenceCollectionSegmentExtraction.Choice.payload hactualHead
    simpa [actualChoice] using h.symm
  have hclockJoin :
      ReferenceActivePhysicalStep.collectionEnabled head.preLedger record.input.time =
        decide (record.input.time.val + 1 < dispatched.startResult.clock.g) := by
    calc
      _ = cutoffCell.enabled := hEnabled'.symm
      _ = decide (record.input.time.val + 1 < head.started.clock.g) := hstartedClock
      _ = decide (record.input.time.val + 1 < dispatched.startResult.clock.g) := by
        rw [hstartedEq]
  have hsourceEnabled :
      (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate record head rewards valid).enabled = cutoffCell.enabled := by
    calc
      _ = ReferenceActivePhysicalStep.collectionEnabled head.preLedger record.input.time := rfl
      _ = decide (record.input.time.val + 1 < dispatched.startResult.clock.g) := hclockJoin
      _ = decide (record.input.time.val + 1 < head.started.clock.g) := by rw [hstartedEq.symm]
      _ = cutoffCell.enabled := hstartedClock.symm
  let headInput := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation head.payload head.started head.weights
  let actualInput := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation registers.payload dispatched.startResult
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
  let headOperation := CoordinatorRecorderComplementBridge.recorderInput headInput
  let actualOperation := CoordinatorRecorderComplementBridge.recorderInput actualInput
  let headValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid headInput valid
  let actualLocalValid : CoordinatorRecorderComplementBridge.LocalInputsValid actualInput :=
    ⟨selected.recorderBoundaryValid, fun j =>
      ⟨selected.choiceInputsValid.anchor_le_current j,
        selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
  let actualValid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    actualInput actualLocalValid
  have hoperation : headOperation = actualOperation := by
    have h := congrArg (fun call : ReferenceCollectionSegmentExtraction.Choice rate =>
      CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.collectionRecordingInput
          record.output.preparation call.payload call.started call.weights)) hactualHead.symm
    simpa [headOperation, actualOperation, headInput, actualInput, actualChoice] using h
  let verifiedOperation :=
    { input : CoordinatorRecordingOperation.Input p //
      CoordinatorRecordingOperation.InputsValid input }
  have hoperationPackage :
      (⟨headOperation, headValid⟩ : verifiedOperation) =
        ⟨actualOperation, actualValid⟩ := by
    apply Subtype.ext
    exact hoperation
  have hsourceMap :
      (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate record head rewards valid).recordedArm =
        CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
          headOperation headValid
          (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate record head rewards valid).enabled := by
    have hm := ReferenceLaterCollectionArrivalReadout.collectionRecordingMap_eq_projection
      head.payload headInput headValid
      (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record head rewards valid).enabled
    simpa [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell,
      headInput, headOperation, headValid, hprep,
      ReferenceActivePhysicalStep.collectionRecordingInput,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      ContinuousLearningRows.sliceAt] using hm
  have hcutoffMap := ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput_map_eq_projection
    record registers owned base dispatched selected
  have hcutoffSource : cutoffCell.recordedArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
        actualOperation actualValid cutoffCell.enabled := by
    by_cases hfrozen : CoordinatorRecordingOperation.isFrozen actualOperation
    · simpa [cutoffCell, ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
        actualInput, actualOperation, actualValid, actualLocalValid, hfrozen] using hcutoffMap
    · simpa [cutoffCell, ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput,
        actualInput, actualOperation, actualValid, actualLocalValid, hfrozen] using hcutoffMap
  have hprojection :
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
          headOperation headValid
          (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate record head rewards valid).enabled =
        CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
          actualOperation actualValid cutoffCell.enabled := by
    calc
      _ = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
          headOperation headValid cutoffCell.enabled := by rw [hsourceEnabled]
      _ = CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
          actualOperation actualValid cutoffCell.enabled := by
            exact congrArg (fun pair : verifiedOperation =>
              CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
                pair.1 pair.2 cutoffCell.enabled) hoperationPackage
  have hmarker' : (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record head rewards valid).recordedArm = cutoffCell.recordedArm := by
    exact hsourceMap.trans (hprojection.trans hcutoffSource.symm)
  have hreward' : (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record head rewards valid).reward = cutoffCell.reward := by
    simp [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell, cutoffCell,
      ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput, hrewards]
  have hrate' : (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record head rewards valid).rate = cutoffCell.rate := by
    simpa [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell, cutoffCell,
      ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput] using
        congrArg AssignmentStartPayload.Input.rate hpayload
  have hcell : ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record head rewards valid = cutoffCell := by
    apply numericalRoundInput_ext
    · exact hsourceEnabled
    · exact hmarker'
    · exact hreward'
    · exact hrate'
  rw [hcell]
  exact hread

private theorem later_collection_readout_zero_of_some
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s : Nat) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
  classical
  have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome = true := by
    rw [hread]
    rfl
  rcases (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp hsome with
    ⟨hfollowers, hbranch⟩
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hfollowers, hcoord] using hread
      | _ => simp [hcoord] at hbranch
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hguard : s < registers.payload.sigma.val := by
            simpa [hcoord] using hbranch
          have hguard0 : 0 < registers.payload.sigma.val := by omega
          have hcell : ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
              record registers owned base dispatched selected = cell := by
            apply Option.some.inj
            simpa [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              hfollowers, hcoord, hguard] using hread
          rw [← hcell]
          simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hfollowers, hcoord, hguard0]
      | _ => simp [hcoord] at hbranch
  | first outcome => cases outcome <;> simp [hcoord] at hbranch
  | invalidCollectionCutoff => simp [hcoord] at hbranch
  | dagger => simp [hcoord] at hbranch

private theorem later_live_readout_none_of_collection_continuing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) = true)
    (hcoord : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores))
    (hfuture : ledger.cutoff ≤ record.input.time.val + 1) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
  apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 record).2
  rintro ⟨selected, hselection, _hstart, hlive, _hordinary⟩
  have hselection' := hselection
  rw [hcoord] at hselection'
  have hcutoffSelection : selected.view.cutoff =
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u := by
    have h := congrArg (Option.map
      (fun choice : ReferenceActivePhysicalStep.Selection record.input => choice.view.cutoff)) hselection'
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt] at h
    exact h.symm
  have hstartedClock : snapshot.clockStarted.clock.u = some cutoff := by
    calc
      _ = clock.u := congrArg (fun c : CoordinatorPhaseClock.ClockRegisters p => c.u)
        snapshot.clockStarted_frame.1
      _ = some cutoff := snapshot.inputsValid.clock_cutoff_eq
  have hledgerCutoff : ledger.cutoff = cutoff.val + 1 := by
    simpa [ReferenceActivePhysicalStep.collectionInput,
      CoordinatorCollectionUpRoundStep.sourceCutoff] using
      snapshot.inputsValid.ledger_cutoff_eq
  have hcutoffRound : CoordinatorLocalArmChoice.cutoffRound selected.view.cutoff = ledger.cutoff := by
    rw [hcutoffSelection, CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hstartedClock]
    exact hledgerCutoff.symm
  have hliveTime := hlive.2
  change record.input.time.val + 1 <
    CoordinatorLocalArmChoice.cutoffRound selected.view.cutoff at hliveTime
  omega

private theorem later_live_readout_none_of_live_cutoff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).clockPending =
        .ok dispatched.startResult)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time))
    (hinit : dispatched.collectionInitialization = .success (some ledger))
    (hcand : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base record.input.time)
    (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base record.input.time)
    (hclock : dispatched.startResult.clock =
      { (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).priorClock with
        u := some (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).time })
    (hpending : dispatched.startResult.pending = Finset.univ)
    (hnone : dispatched.startResult.assignmentStart = none)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
      record.input.row)
    (hcoord : record.output.preparation.coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected)) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
  apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 record).2
  rintro ⟨actualSelection, hselection, _hstart, hlive, _hordinary⟩
  have hselection' := hselection
  rw [hcoord] at hselection'
  have hcutoffSelection : actualSelection.view.cutoff =
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u := by
    have h := congrArg (Option.map
      (fun choice : ReferenceActivePhysicalStep.Selection record.input => choice.view.cutoff)) hselection'
    simp [ReferenceActivePhysicalStep.DispatchCut.selection] at h
    rcases h with ⟨a, ha, hcutoffEq⟩
    have haCutoff : a.view.cutoff =
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u := by
      have hmap := congrArg (Option.map
        (fun choice : ReferenceActivePhysicalStep.Selection record.input => choice.view.cutoff)) ha
      simpa [ReferenceActivePhysicalStep.selectionAt] using hmap.symm
    exact hcutoffEq.symm.trans haCutoff
  have hclockU : dispatched.startResult.clock.u = some record.input.time := by
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using
      congrArg (fun c : CoordinatorPhaseClock.ClockRegisters p => c.u) hclock
  have hcutoffRound : CoordinatorLocalArmChoice.cutoffRound actualSelection.view.cutoff =
      record.input.time.val + 1 := by
    rw [hcutoffSelection, CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hclockU]
    rfl
  have hliveTime := hlive.2
  change record.input.time.val + 1 <
    CoordinatorLocalArmChoice.cutoffRound actualSelection.view.cutoff at hliveTime
  omega

private theorem connected_adjacent_records
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : Nat) (hn : n + 1 < records.length) :
    (records[n + 1]'(by omega)).input.state = (records[n]'(by omega)).output.next := by
  induction n generalizing records initial with
  | zero =>
      cases records with
      | nil => simp at hn
      | cons first rest =>
          cases rest with
          | nil => simp at hn
          | cons second tail =>
              change first.input.state = initial ∧
                ReferenceActivePhysicalHorizon.Connected first.output.next (second :: tail) final
                at hconnected
              simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hconnected.2.1
  | succ n ih =>
      cases records with
      | nil => simp at hn
      | cons first rest =>
          have hrest : ReferenceActivePhysicalHorizon.Connected first.output.next rest final := by
            cases rest with
            | nil => simp at hn
            | cons second tail =>
                change first.input.state = initial ∧
                  ReferenceActivePhysicalHorizon.Connected first.output.next (second :: tail) final
                  at hconnected
                exact hconnected.2
          have hnRest : n + 1 < rest.length := by simp at hn; omega
          have h := ih hrest hnRest
          simpa only [List.getElem_cons_succ] using h

/-- Every actual first-live record reads back the same full numerical cell
selected by the actual source-cell producer. The initialization seed and its
positive physical start are produced from the literal crossing. -/
theorem actual_first_live_numerical_observation_identity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hcross count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hcross count hspan
    ∃ seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross) start,
      0 < start ∧
      ∀ k : Fin window.length,
        let record := window[k.val]
        let cell := cells[k.val]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact k.isLt)
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some cell ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = none ∧
        record.input.time.val = start + k.val ∧
        record.input.rows = source.1.2 ∧
        record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        record.input.rewards = rewards ∧
        cell.enabled = true ∧
        cell.reward = (fun arm => ((record.input.rewards record.input.time arm).val : ℝ) /
          (D p : ℝ)) ∧
        cell.rate = (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hcross count hspan k).selected.view.payload.rate ∧
        cell.recordedArm = ReferenceFirstWindowNumericalStream.sourceArm record
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.payload
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.pendingAtChoice
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).states
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.complementWeights
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.cutoff
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).choiceInputsValid ∧
        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
          (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell) =
        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell := by
  classical
  dsimp only
  let boot := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let start := ReferenceInitializationRun.elapsed p boot.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hcross
  have hcompleted : 0 < boot.completed := by
    apply run_crossing_completed_pos
    exact hcross
  have hstart : 0 < start := by
    dsimp [start, ReferenceInitializationRun.elapsed]
    have hmul : 0 < boot.completed * BootstrapDimensions.B_boot p :=
      Nat.mul_pos hcompleted (BootstrapDimensions.B_boot_pos p)
    have hT : 0 < p.T := ConstructorDimensions.T_pos p
    omega
  refine ⟨seed, hstart, ?_⟩
  intro k
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hcross count hspan
  let record := window[k.val]
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  let cell := cells[k.val]'(by
    rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
    exact k.isLt)
  have hcellGet := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
    rate source rewards C_star C_h hcross count hspan k
  have hcell : cell =
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate source rewards C_star C_h hcross count hspan k).input := by
    dsimp [cell, cells]
    exact hcellGet
  let actualCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hcross count hspan k
  let sourceRecord := window[k.val]
  have hgeometry := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst k actualCell.selected
    actualCell.selection_actual
  dsimp only [window, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
    initial, seed, start, boot] at hgeometry
  obtain ⟨hsigma, htime, _hgrid, _hproposal⟩ := hgeometry
  have hprepared : ReferenceLaterLiveNumericalReadout.preparedOrdinary sourceRecord := by
    intro i
    change (ReferenceLaterLiveNumericalReadout.ordinaryData
      ((window[k.val]).output.preparation.followers.followers i).configuration).isSome = true
    rw [actualCell.ordinary i]
    rfl
  have hstates : ReferenceLaterLiveNumericalReadout.preparedStates sourceRecord hprepared =
      actualCell.states := by
    funext i
    have hpreparedConfig := ReferenceLaterLiveNumericalReadout.prepared_configuration
      sourceRecord hprepared i
    have hsame := hpreparedConfig.symm.trans (actualCell.ordinary i)
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hsame).1
  have hsource :
      ReferenceFirstWindowNumericalStream.sourceCell sourceRecord
        actualCell.selected.view.payload actualCell.selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates sourceRecord hprepared)
        actualCell.selected.view.complementWeights actualCell.selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid actualCell.selected) =
      actualCell.input := by
    rw [hstates]
    have hvalid : ReferenceLaterLiveNumericalReadout.selection_choiceValid actualCell.selected =
        actualCell.choiceInputsValid := Subsingleton.elim _ _
    rw [hvalid]
    exact actualCell.input_eq.symm
  have hliveReadout :
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 sourceRecord = some cell := by
    have hsigmaEq : actualCell.selected.view.payload.sigma.val = start := by
      simpa [start, boot] using hsigma
    have hsigmaPos : 0 < actualCell.selected.view.payload.sigma.val := by omega
    have hread :
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 sourceRecord =
          some actualCell.input := by
      unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
      rw [actualCell.selection_actual]
      have hguard : 0 < actualCell.selected.view.payload.sigma.val ∧
          CoordinatorLocalArmChoice.assignmentIsLive actualCell.selected.view.payload
            actualCell.selected.view.cutoff sourceRecord.input.time :=
        ⟨hsigmaPos, actualCell.assignment_live⟩
      simp only [if_pos hguard, dif_pos hprepared]
      exact congrArg some hsource
    simpa [hcell] using hread
  have hcollectionNone :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 sourceRecord = none := by
    have hshape := first_live_collection_readout_none rate source rewards C_star C_h hcross count hspan k
    simpa [sourceRecord, window] using hshape
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate source rewards C_star C_h hcross count hspan k
  have htime' : sourceRecord.input.time.val = start + k.val := by
    simpa [sourceRecord, window, start, boot,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using htime
  rcases hfacts with ⟨hrows, hselected, hrewards, _hcalendar, henabled,
    hreward, hrate, hmarker, _harrivals⟩
  refine ⟨by simpa [record, cell] using hliveReadout,
    by simpa [record] using hcollectionNone, htime', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sourceRecord] using hrows
  · simpa [sourceRecord] using hselected
  · simpa [sourceRecord] using hrewards
  · change cell.enabled = true
    rw [hcell]
    exact henabled
  · change cell.reward = _
    rw [hcell]
    exact hreward
  · change cell.rate = _
    rw [hcell]
    exact hrate
  · change cell.recordedArm = _
    rw [hcell]
    exact hmarker
  · change ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
      (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell) = _
    exact ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates
      rate cell

/-! The same actual source prefix through the first collection stream, with the
zero-index cutoff cell joined to C's literal numerical readout. -/
theorem actual_first_collection_numerical_observation_identity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records
    ∃ seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross) s,
      0 < s ∧
      ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
        let out := d.stream
        ∃ (head : ReferenceCollectionSegmentExtraction.Choice rate)
          (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
          (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
              head.payload head.started head.weights))
          (D : List (RecordedQueueRun.RoundInput p.K)),
          ReferenceCollectionSegmentExtraction.choice out.cutoff.cut.input = some head ∧
          head.payload = out.payload ∧ head.initializer = some initializer ∧
          initializer.checkedStart rate = .success head.preLedger ∧
          ∃ hDlen : D.length = out.ell,
          D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
            ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
              rate out.cutoff.cut head rewards valid ∧
          ∀ n : Fin out.ell,
            let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
            let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
            ∃ (call : ReferenceCollectionSegmentExtraction.Choice rate)
              (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                  call.payload call.started call.weights)),
              ReferenceCollectionSegmentExtraction.choice record.input = some call ∧
              call.payload = out.payload ∧
              CollectionBufferProvenance.collectionContext call.preLedger =
                CollectionBufferProvenance.collectionContext head.preLedger ∧
              cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
                rate record call rewards validCall ∧
              record.input.rows = source.1.2 ∧
              record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              record.input.rewards = rewards ∧
              record.input.time.val = s + W.length + n.val ∧
              cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
              cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
                (ConstructorDimensions.D p : ℝ)) ∧
              cell.rate = out.payload.rate ∧
              (∀ a : Fin p.K,
                ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
                  (cell.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
              ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell ∧
              ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
  classical
  dsimp only
  let s := ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) source rewards C_star C_h
  let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
  have hrunRecords :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hcross count hspan).records = epoch.records := by
    calc
      _ = (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records := by rfl
      _ = epoch.records :=
        ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_records_eq
          source rewards C_star C_h hcross count hspan
  have hwindowEq : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hcross count hspan = W :=
    congrArg ReferenceFirstLiveConfirmationHistory.firstLiveWindow hrunRecords
  have hshortFirst : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hcross count hspan).length < count := by
    simpa [W, hwindowEq] using hshort
  have hfirst := actual_first_live_numerical_observation_identity rate source rewards
    C_star C_h hcross count (by simpa [s] using hspan)
  obtain ⟨seed, hstartPos, _hfirstCells⟩ := hfirst
  rcases ReferenceFirstCollectionAllArmNumericalStream.actual_initialized_first_collection_all_arm_numerical_stream
      rate source rewards C_star C_h hcross count hspan hshort with
    ⟨d, hUdata⟩
  dsimp only at hUdata
  rcases hUdata with ⟨head, initializer, valid, D, hhead, hpay, hinit, hchecked,
    hDlen, hzero, hrest⟩
  let out := d.stream
  let hcells := hrest.1
  have hcutProducer := ReferenceFirstCutoffNumericalSource.actual_first_cutoff_numerical_source
    rate source rewards C_star C_h hcross count (by simpa [s] using hspan) hshortFirst
  dsimp only at hcutProducer
  rcases hcutProducer with ⟨cut, suffix, registers, owned, base, hcutIndex,
    hrecords, hcutTime, hcutRows, hcutSelected, hcutRewards, hcutState,
    hcutSigma, _hcarried, dispatched, hstart, cutoffLedger, hinitCut, hcand,
    hdomainCut, hclock, hpending, hnone, selected, hcoordCut, _hcutoffTime,
    htimeBound, hgridBound, hledgerSigma, hledgerCutoff, _hfollowersTail,
    hpositiveCount, hordinary, _hcutoffRest⟩
  have hcutoffRecordEq : cut = out.cutoff.cut := by
    have hboundOut : W.length < epoch.records.length :=
      (List.getElem?_eq_some_iff.mp out.cutoff.cutIndex).1
    have hgetOut : epoch.records[W.length]? = some out.cutoff.cut := by
      simpa [epoch, W] using out.cutoff.cutIndex
    have hboundRun : W.length <
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hcross count hspan).records.length := by
      simpa [hrunRecords] using hboundOut
    have hcutAt : cut =
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hcross count hspan).records[W.length]'hboundRun := by
      simpa [W, hwindowEq] using hcutIndex
    have hgetCut := (List.getElem?_eq_getElem hboundRun).trans (congrArg some hcutAt.symm)
    exact Option.some.inj (hgetCut.symm.trans hgetOut)
  have hfollowersCut : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied cut := by
    intro i
    rcases hordinary i with ⟨before, memory, _hbefore, _hstart, hprepared,
      hunoccupied, _hrest⟩
    simpa [ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied,
      hprepared] using hunoccupied
  have hsourceSigma : 0 < registers.payload.sigma.val := by
    rw [hcutSigma]
    exact hstartPos
  let actualHead : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger cutoffLedger,
      dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time)
        base cut.input.time)⟩
  have hpreparedCut : cut.output.preparation =
      ReferenceActivePhysicalStep.prepare cut.input := by
    rw [cut.output_eq]
    rfl
  have hselectionNonempty :
      (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection ≠ none := by
    rw [← hpreparedCut, hcoordCut]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  have hactualHead : ReferenceCollectionSegmentExtraction.choice cut.input =
      some actualHead := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [if_neg hselectionNonempty, ← hpreparedCut, hcoordCut]
    simp [actualHead, ReferenceCollectionSegmentExtraction.choiceOfCut]
  have hheadCut : ReferenceCollectionSegmentExtraction.choice cut.input = some head :=
    hcutoffRecordEq ▸ hhead
  have hheadEq : actualHead = head := Option.some.inj (hactualHead.symm.trans hheadCut)
  have hheadCutoff : head.preLedger.cutoff = s + W.length + 1 := by
    have hledger := congrArg ReferenceCollectionSegmentExtraction.Choice.preLedger hheadEq
    have hcutoff := congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.cutoff) hledger
    have hsharedCutoff := (ReferenceActivePhysicalStep.sharedLedger_fields cutoffLedger).2.2.1
    have hheadCutoff' : head.preLedger.cutoff = cutoffLedger.cutoff := by
      calc
        _ = actualHead.preLedger.cutoff := hcutoff.symm
        _ = cutoffLedger.cutoff := by simpa [actualHead] using hsharedCutoff
    calc
      _ = cutoffLedger.cutoff := hheadCutoff'
      _ = s + W.length + 1 := by
        simpa [W, hwindowEq] using hledgerCutoff
  have validCut : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
        head.payload head.started head.weights) := hcutoffRecordEq.symm ▸ valid
  have hcutReadout := first_cutoff_readout_sourceCell rate cut head rewards
    hcutRewards validCut registers owned base
    ⟨dispatched, hstart, cutoffLedger, hinitCut, hcand, hdomainCut,
      hclock, hpending, hnone, selected, hcoordCut⟩
    hfollowersCut hsourceSigma hheadCut
  have hcutReadoutOut :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 out.cutoff.cut =
        some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate out.cutoff.cut head rewards valid) := hcutoffRecordEq ▸ hcutReadout
  refine ⟨seed, hstartPos, d, head, initializer, valid, D,
    hhead, hpay, hinit, hchecked, hDlen, hzero, ?_⟩
  intro n
  let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
  let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
  obtain ⟨call, validCall, hcall, hcallPayload, hcontext, hsourceCell,
    hrows, hselectedRecord, hrecordRewards, htime, henabled, hreward, hrate,
    hphysical, hread⟩ := hcells n
  have hcollectionReadout :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
    by_cases hn : 0 < n.val
    · exact later_collection_readout_zero_of_some rate s record cell (hread hn)
    · have hnzero : n.val = 0 := by omega
      have hrecordCut : record = out.cutoff.cut := by
        dsimp [record]
        simpa [hnzero] using out.cutoffIsHead
      rw [hrecordCut]
      have hcellZero : cell =
          ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate out.cutoff.cut head rewards valid := by
        simpa [cell, hnzero] using hzero
      simpa [hcellZero] using hcutReadoutOut
  have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    have hpreparedRecord : record.output.preparation =
        ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    cases hcoord : record.output.preparation.coordinator with
    | live liveRegisters liveOwned liveBase outcome =>
        cases outcome with
        | cutoffChosen cutDispatch cutStart newLedger cutInit cutCandidate cutDomain
            cutClock cutPending cutNoStart cutSelection =>
            exact later_live_readout_none_of_live_cutoff rate record liveRegisters liveOwned
              liveBase cutDispatch cutStart newLedger cutInit cutCandidate cutDomain cutClock
              cutPending cutNoStart cutSelection hcoord
        | _ =>
            unfold ReferenceCollectionSegmentExtraction.choice at hcall
            rw [← hpreparedRecord, hcoord] at hcall
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hcall
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            let actualCall : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨payload, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            have hprepared : record.output.preparation =
                ReferenceActivePhysicalStep.prepare record.input := by
              rw [record.output_eq]
              rfl
            have hselection :
                (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
              rw [← hprepared, hcoord]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt]
            have hactualCall : ReferenceCollectionSegmentExtraction.choice record.input =
                some actualCall := by
              unfold ReferenceCollectionSegmentExtraction.choice
              rw [if_neg hselection, ← hprepared, hcoord]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt,
                ReferenceCollectionSegmentExtraction.choiceOfCut, actualCall]
            have hactualCallEq : call = actualCall :=
              Option.some.inj (hcall.symm.trans hactualCall)
            have hcontextLedger :
                CollectionBufferProvenance.collectionContext ledger =
                  CollectionBufferProvenance.collectionContext head.preLedger := by
              have hc := hcontext
              rw [hactualCallEq] at hc
              simpa [actualCall] using hc
            have hledgerCut : ledger.cutoff = head.preLedger.cutoff := by
              have hc := hcontextLedger
              simp only [CollectionBufferProvenance.collectionContext, Prod.mk.injEq] at hc
              exact hc.2.2.1
            have hfuture : ledger.cutoff ≤ record.input.time.val + 1 := by
              have htimeSucc : s + W.length + n.val + 1 = record.input.time.val + 1 := by
                rw [htime]
              calc
                ledger.cutoff = head.preLedger.cutoff := hledgerCut
                _ = s + W.length + 1 := hheadCutoff
                _ ≤ s + W.length + n.val + 1 := by omega
                _ = record.input.time.val + 1 := htimeSucc
            exact later_live_readout_none_of_collection_continuing rate record
              payload ledger clock cutoff core snapshot boundary scores hcoord hfuture
        | _ =>
            unfold ReferenceCollectionSegmentExtraction.choice at hcall
            rw [← hpreparedRecord, hcoord] at hcall
            simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hcall
    | first outcome =>
        cases outcome <;>
          (unfold ReferenceCollectionSegmentExtraction.choice at hcall;
           rw [← hpreparedRecord, hcoord] at hcall;
           simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hcall)
    | invalidCollectionCutoff =>
        unfold ReferenceCollectionSegmentExtraction.choice at hcall
        rw [← hpreparedRecord, hcoord] at hcall
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hcall
    | dagger =>
        unfold ReferenceCollectionSegmentExtraction.choice at hcall
        rw [← hpreparedRecord, hcoord] at hcall
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hcall
  exact ⟨call, validCall, hcall, hcallPayload, hcontext, hsourceCell, hrows,
    hselectedRecord, hrecordRewards, htime, henabled, hreward, hrate, hphysical,
    hcollectionReadout, hliveNone⟩

end Bandits.Support.ReferenceFirstPhasesNumericalObservationIdentification

end
