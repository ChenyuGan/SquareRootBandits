/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceReleaseSupport

/-!
# Decoder silence on the actual first-live release suffix

Sources: `sources/zip4/manuscript/05_binary_transport.tex:45-55,74-124,293-345`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

These internal results follow the original corrected launch, complete private
row stream, shared reward table, and retained physical records. On the actual
first-live release suffix they establish that no retained UP or DOWN decoder
decision is made. They do not rule out an earlier decoder failure or assert a
source-facing stopping, cost, or regret theorem. The coordinator UP diagnostic
is distinct from any UP service observation. These results leave overflow
events and the existing prelaunch suppression, forced-correction, and
inclusive detecting-round conventions untouched.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLiveSourceReleaseSupport
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceLocalReleaseGateChronology
open Bandits.Support.ReferenceGeneratedSavedWrongEvent
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceRetainedReleasePhaseObservation
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveReleaseDecoderSilence

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem livePostChoice_retains_bank_and_has_no_up
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).up = none ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).upDecoderBank =
        x.state.upDecoderBank := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none =>
      exact ⟨rfl, rfl⟩
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason =>
          simp only [hservice]
          exact ⟨rfl, rfl⟩
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp only [hservice]
              exact ⟨rfl, rfl⟩
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp only [hservice, hfinish]
                  exact ⟨rfl, rfl⟩
              | ok finished => simp [hservice, hfinish]

private theorem firstLiveRecord_coordinator_silence
    (record : Record (p := p) (rate := rate))
    (hbranch :
      (∃ installed arm selected,
        record.output.preparation.coordinator = .first (.chosen installed arm) ∧
          record.output.preparation.coordinator.selection = some selected) ∨
      ∃ r q base dispatched hstart continuation arm selected,
        record.output.preparation.coordinator = .live r q base
          (.continuingChosen dispatched hstart continuation arm) ∧
          record.output.preparation.coordinator.selection = some selected) :
    record.output.coordinator.up = none ∧
      record.output.coordinator.upDecoderBank = record.input.state.upDecoderBank := by
  have hobserve : record.output.coordinator = record.output.preparation.observeCoordinator := by
    rw [record.output_eq]
    rfl
  rcases hbranch with ⟨installed, arm, selected, hfirst, hselected⟩ |
      ⟨r, q, base, dispatched, hstart, continuation, arm, selected, hlive, hselected⟩
  · have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
      record.output.preparation (.chosen installed arm) hfirst
    have hsel :
        (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed arm)).selection ≠ none := by
      intro hnone
      have hs : record.output.preparation.coordinator.selection = none := by
        simpa only [hfirst] using hnone
      rw [hselected] at hs
      cases hs
    have htail := livePostChoice_retains_bank_and_has_no_up
      record.output.preparation installed.registers installed.ownedRegisters
      installed.followerBaseScore installed.startRoundResult
    rw [hobserve, heq]
    simp [hsel]
    exact htail
  · have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
      record.output.preparation r q base
      (.continuingChosen dispatched hstart continuation arm) hlive
    have hsel :
        (ReferenceActivePhysicalStep.DispatchCut.live r q base
          (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
      intro hnone
      have hs : record.output.preparation.coordinator.selection = none := by
        simpa only [hlive] using hnone
      rw [hselected] at hs
      cases hs
    have htail := livePostChoice_retains_bank_and_has_no_up
      record.output.preparation (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base dispatched.startResult
    rw [hobserve, heq]
    simp [hsel]
    exact htail

private theorem actual_gate_index
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (r : Record (p := p) (rate := rate))
    (hr : r ∈ (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count rfl hspan).records.filter (fun record =>
        localReleaseGate rate
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          record.input.time (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state))) :
    ∃ k : Fin count,
      (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
        hcross (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        count rfl hspan).records[k.val]'(by
          simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count] using k.isLt) = r ∧
      localReleaseGate rate
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        ((ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
          hcross (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count rfl hspan).records[k.val]'(by
            simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)).input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState
          ((ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
            hcross (ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
            count rfl hspan).records[k.val]'(by
              simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
                ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)).input.state) = true := by
  rcases List.mem_filter.mp hr with ⟨hrecords, hgate⟩
  rcases List.mem_iff_getElem.mp hrecords with ⟨j, hj, hget⟩
  have hlength : (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count rfl hspan).records.length = count := by
    simp [ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceActivePhysicalHorizon.run_record_count]
  have hj' : j < count := by rw [← hlength]; exact hj
  refine ⟨⟨j, hj'⟩, ?_, ?_⟩
  · simpa only [Fin.val_mk] using hget
  · rw [hget]
    exact hgate

private theorem actual_gate_record_in_window
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (k : Fin count)
    (hgate : localReleaseGate rate
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      ((ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
        hcross (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        count rfl hspan).records[k.val]'(by
          simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
          hcross (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count rfl hspan).records[k.val]'(by
            simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)).input.state) = true) :
    k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
        hcross (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        count rfl hspan).records).length ∧
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
          hcross (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count rfl hspan).records)[k.val]'(by
            exact ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_in_window
              source rewards C_star C_h count hspan hcross k hgate) =
        (ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
          hcross (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count rfl hspan).records[k.val]'(by
            simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count] using k.isLt) := by
  let I := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let s := ReferenceInitializationRun.elapsed p I.completed
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
  have hindex := ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_in_window
    source rewards C_star C_h count hspan hcross k hgate
  have hprefix : W.IsPrefix R.records := List.takeWhile_prefix _
  refine ⟨?_, ?_⟩
  · simpa only [I, s, R, W] using hindex
  · have hget := hprefix.getElem (by simpa only [I, s, R, W] using hindex)
    simpa only [I, s, R, W] using hget

private theorem finishFollower_occupied_no_down
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = none ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = none := by
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration,
    ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem connected_bank_preserve
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hstep : ∀ r ∈ records,
      r.output.next.upDecoderBank = r.input.state.upDecoderBank) :
    final.upDecoderBank = initial.upDecoderBank := by
  induction records generalizing initial final with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hconnected
      subst final
      rfl
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hconnected
      rcases hconnected with ⟨hinput, htail⟩
      have htailBank := ih htail (fun r hr => hstep r (List.mem_cons_of_mem _ hr))
      have hrecordBank := hstep record (by simp)
      calc
        final.upDecoderBank = record.output.next.upDecoderBank := htailBank
        _ = record.input.state.upDecoderBank := hrecordBank
        _ = initial.upDecoderBank := by rw [hinput]

private theorem first_live_record_silence
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ k : Fin W.length,
      (W[k.val]).output.coordinator.up = none ∧
        (W[k.val]).output.coordinator.upDecoderBank = (W[k.val]).input.state.upDecoderBank := by
  intro I s R W k
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hcross
  have hseedLaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate source rewards C_star C_h hcross
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hinitial : initial = ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross :=
    Option.some.inj (hseedLaunch.symm.trans hlaunch)
  subst initial
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
    seed.activeAtStart seed.coordinatorFirst seed.followers seed.memory seed.configuration
    seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none seed.unoccupied
    seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hentry := htruth k
  obtain ⟨cell, _hrows, _hselectedRow, _hrewards, _htime⟩ :=
    ReferenceFirstWindowNumericalStream.actual_first_live_source_cell
      rate source rewards C_star C_h hcross count hspan k
  rcases hentry with ⟨_, _, _, _, _, hbranch⟩
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, hbranch, _, _, selected, hselected, _, _, _, _, _, _⟩
    have hsil := firstLiveRecord_coordinator_silence (W[k.val])
      (Or.inl ⟨installed, arm, cell.selected, hbranch, cell.selection_actual⟩)
    exact hsil
  · rcases hcontinuing with
      ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, _, selected,
        hselected, _, _, _, _, _, _⟩
    have hsil := firstLiveRecord_coordinator_silence (W[k.val])
      (Or.inr ⟨r, q, base, dispatched, hstart, continuation, arm, cell.selected,
        hbranch, cell.selection_actual⟩)
    exact hsil

/-- Every record in the original first-live window has no coordinator UP
diagnostic. -/
theorem first_live_up_diagnostic_eq_none
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ k : Fin W.length, (W[k.val]).output.coordinator.up = none := by
  intro I s R W k
  exact (first_live_record_silence source rewards C_star C_h count hspan hcross k).1

/-- At every boundary through the inclusive end of the actual first-live
window, the original physical run still carries its corrected-launch UP bank. -/
theorem first_live_up_bank_eq_initial
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (b : ℕ) (hb : b ≤ W.length),
      (ReferenceActivePhysicalHorizon.run
        (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
        (by
          have hwindowPrefix : W.IsPrefix R.records := List.takeWhile_prefix _
          have hrunLength : R.records.length = count := by
            simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun] using
              ReferenceActivePhysicalHorizon.run_record_count
                (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
                source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards s count hspan
                (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                  rate source rewards C_star C_h hcross |>.2.1)
          have hcount : b ≤ count := by
            calc
              b ≤ W.length := hb
              _ ≤ R.records.length := hwindowPrefix.length_le
              _ = count := hrunLength
          have hspanLocal : s + count ≤ p.T := hspan
          omega)
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate source rewards C_star C_h hcross |>.2.1)).finalState.upDecoderBank =
        CoordinatorUpReception.initialUpDecoderBank p := by
  intro I s R W b hb
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross
  let hmode := (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate source rewards C_star C_h hcross).2.1
  have hspanLocal : s + count ≤ p.T := hspan
  have hshortSpan : s + b ≤ p.T := by
    have hle := List.takeWhile_prefix
      (fun r : Record (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (l := R.records)
    have hcount : b ≤ count := by
      calc
        b ≤ W.length := hb
        _ ≤ R.records.length := hle.length_le
        _ = count := by
          simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun] using
            ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspanLocal hmode
    omega
  let short := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b hshortSpan hmode
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate source rewards C_star C_h hcross
  have hlaunch' := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hinitial : initial = ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross :=
    Option.some.inj (hlaunch.symm.trans hlaunch')
  have hlaunchStateBank :
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross).upDecoderBank =
        CoordinatorUpReception.initialUpDecoderBank p := by
    rcases ReferenceFirstLaunchNumericalCell.actual_launch_seed
        rate source rewards C_star C_h hcross with
      ⟨_, _, _, _, hbank, _⟩
    exact hbank
  have hbank : initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
    rw [hinitial]
    exact hlaunchStateBank
  have hwindowPrefix : W.IsPrefix R.records := List.takeWhile_prefix _
  have hbcount : b ≤ count := by
    calc
      b ≤ W.length := hb
      _ ≤ R.records.length := hwindowPrefix.length_le
      _ = count := by
        simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun] using
          ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspanLocal hmode
  have hprefixSpan : s + (b + (count - b)) ≤ p.T := by
    rw [Nat.add_sub_of_le hbcount]
    exact hspanLocal
  obtain ⟨tail, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s b (count - b) hprefixSpan hmode
  have hshortPrefix : short.records.IsPrefix R.records := by
    have hsum : b + (count - b) = count := Nat.add_sub_of_le hbcount
    refine ⟨tail, ?_⟩
    simpa only [short, R, ReferenceLocalReleaseGateChronology.sourceRun, hsum] using hrecords.symm
  have hshortLength : short.records.length = b := by
    dsimp only [short]
    exact ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b hshortSpan hmode
  have hshortBank := connected_bank_preserve short.connected
    (by
      intro record hrecord
      obtain ⟨j, hj, _heq⟩ := List.mem_iff_getElem.mp hrecord
      have hjW : j < W.length := by rw [hshortLength] at hj; omega
      have hshortGet := hshortPrefix.getElem hj
      have hwindowGet := hwindowPrefix.getElem hjW
      have hsame : short.records[j] = W[j] := hshortGet.trans hwindowGet.symm
      have hrecordWindow : record = W[j] := _heq.symm.trans hsame
      have hsil := first_live_record_silence source rewards C_star C_h count hspan hcross
        ⟨j, hjW⟩
      calc
        record.output.next.upDecoderBank = (W[j]).output.next.upDecoderBank := by rw [hrecordWindow]
        _ = (W[j]).output.coordinator.upDecoderBank := by rw [(W[j]).output_eq]; rfl
        _ = (W[j]).input.state.upDecoderBank := hsil.2
        _ = record.input.state.upDecoderBank := by rw [← hrecordWindow])
  exact hshortBank.trans hbank

/-- Every actual release gate record retains no follower DOWN call input and
no DOWN decoder output, including all logging, service, and finish failures. -/
theorem release_down_diagnostics_eq_none
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let G := R.records.filter (fun r => localReleaseGate rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))
    ∀ r ∈ G, ∀ i : Fin (p.m - 1),
      (r.output.followers i).downInput = none ∧ (r.output.followers i).down = none := by
  intro I s R G r hr i
  obtain ⟨k, hget, hgate⟩ := actual_gate_index source rewards C_star C_h count hspan hcross r hr
  have hwindow := actual_gate_record_in_window source rewards C_star C_h count hspan hcross k hgate
  have hkW : k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
    simpa only [I, s, R] using hwindow.1
  have hrecord : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val] = r := by
    have h := hwindow.2
    simpa only [I, s, R] using h.trans hget
  obtain ⟨selected, hselected, payload, hpayload, hempty, hsigma⟩ :=
    ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_selected_empty
      source rewards C_star C_h count hspan hcross k hgate
  have hRtoW : R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt) =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val]'hkW := by
    have h := hwindow.2.symm
    simpa only [I, s, R] using h
  have hselectionOnWindow : ∃ selectedWindow : ReferenceActivePhysicalStep.Selection
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val]).input,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val].output.preparation.coordinator.selection =
        some selectedWindow ∧ selectedWindow.view.pendingAtChoice = ∅ := by
    exact hRtoW ▸ ⟨selected, hselected, hempty⟩
  have hprojection := ReferenceFirstLiveReleaseGeometry.original_source_first_live_release_projection
    source rewards C_star C_h hcross s count rfl hspan
  obtain ⟨initial, seed, memory, hmode, hlaunch, hfirst, hseed, hS, hdelta,
      hbacklog, hnone, haccepted, hunoccupied, hvalid, hpair, htime, hbatch,
      hsourceProofs⟩ := hprojection
  have hseedLaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate source rewards C_star C_h hcross
  have hinitial : initial = ReferenceLocalReleaseGateChronology.sourceSeed
      rate source rewards C_star C_h hcross :=
    Option.some.inj (hlaunch.symm.trans hseedLaunch)
  subst initial
  rcases hsourceProofs with ⟨hselectors, _hterminal⟩
  obtain ⟨selectedWindow, hselectedWindow, hemptyWindow⟩ := hselectionOnWindow
  have hgeometryWindow :
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run
            (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan hmode).records =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records := by
    rfl
  have hselectedGeometry : ∃ selectedGeometry : ReferenceActivePhysicalStep.Selection
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hmode).records)[k.val]).input,
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hmode).records)[k.val]).output.preparation.coordinator.selection =
        some selectedGeometry ∧ selectedGeometry.view.pendingAtChoice = ∅ := by
    simpa only [hgeometryWindow] using ⟨selectedWindow, hselectedWindow, hemptyWindow⟩
  obtain ⟨selectedGeometry, hselectedGeometry, hemptyGeometry⟩ := hselectedGeometry
  have hkGeometry : k.val <
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hmode).records).length := by
    simpa only [hgeometryWindow] using hkW
  obtain ⟨hchoiceValid, states, memories, hordinary, hoccupied, _hchoiceData⟩ :=
    hselectors ⟨k.val, hkGeometry⟩ selectedGeometry hselectedGeometry hemptyGeometry
  let geometryWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.run
      (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s count hspan hmode).records
  let geometryRecord := geometryWindow[k.val]'hkGeometry
  have hrecordGeometry : geometryRecord = r := by
    simpa only [geometryRecord, geometryWindow, hgeometryWindow] using hrecord
  have hprepared :
      (r.output.preparation.followers.followers i).configuration = .ordinary (states i) (memories i) := by
    rw [← hrecordGeometry]
    exact hordinary i
  have hpreparedStep :
      (r.output.followers i).downInput =
          (ReferenceActivePhysicalStep.finishFollower r.output.preparation.coordinator.downView
            (r.output.preparation.followers.followers i)
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))).downInput ∧
        (r.output.followers i).down =
          (ReferenceActivePhysicalStep.finishFollower r.output.preparation.coordinator.downView
            (r.output.preparation.followers.followers i)
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))).down := by
    rw [r.output_eq]
    exact ⟨rfl, rfl⟩
  have hnoDown := finishFollower_occupied_no_down r.output.preparation.coordinator.downView
    (r.output.preparation.followers.followers i)
    (r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    (states i) (memories i) hprepared (hoccupied i).1
  exact ⟨hpreparedStep.1.trans hnoDown.1, hpreparedStep.2.trans hnoDown.2⟩

/-- The literal saved-wrong-record diagnostic is false throughout the actual
release gate list. -/
theorem release_saved_wrong_flag_eq_false
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let G := R.records.filter (fun r => localReleaseGate rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))
    ∀ r ∈ G, ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = false := by
  intro I s R G r hr
  have hdown := release_down_diagnostics_eq_none source rewards C_star C_h count hspan hcross r hr
  obtain ⟨k, hget, hgate⟩ := actual_gate_index source rewards C_star C_h count hspan hcross r hr
  have hwindow := actual_gate_record_in_window source rewards C_star C_h count hspan hcross k hgate
  have hkW : k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
    simpa only [I, s, R] using hwindow.1
  have hrecord : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val] = r := by
    have h := hwindow.2
    simpa only [I, s, R] using h.trans hget
  have hup := first_live_up_diagnostic_eq_none source rewards C_star C_h count hspan hcross
  have hrup : r.output.coordinator.up = none := by
    rw [← hrecord]
    exact hup ⟨k.val, hkW⟩
  have hdowns : ∀ i, (r.output.followers i).down = none := by
    intro i
    exact (hdown i).2
  simp [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
    ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted, hrup, hdowns]

private theorem filterMap_up_nil_of_absent
    (records : List (Record (p := p) (rate := rate)))
    (h : ∀ r ∈ records, r.output.coordinator.up = none) :
    records.filterMap (fun r => r.output.coordinator.up) = [] := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
      have hr := h r (by simp)
      have hrs : ∀ x ∈ rs, x.output.coordinator.up = none := by
        intro x hx
        exact h x (by simp [hx])
      simp [hr, ih hrs]

private theorem filterMap_down_nil_of_absent
    (records : List (Record (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (h : ∀ r ∈ records, (r.output.followers i).down = none) :
    records.filterMap (fun r => (r.output.followers i).down) = [] := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
      have hr := h r (by simp)
      have hrs : ∀ x ∈ rs, (x.output.followers i).down = none := by
        intro x hx
        exact h x (by simp [hx])
      simp [hr, ih hrs]

private theorem actual_gate_suffix_decomposition
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    let G := R.records.filter (fun r => localReleaseGate rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))
    ∃ prior : List (Record (p := p) (rate := rate)), prior ++ G = W := by
  intro I s R W G
  classical
  by_cases hnil : G = []
  · exact ⟨W, by simp [hnil]⟩
  · have hnonempty : G ≠ [] := hnil
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil G hnonempty
    obtain ⟨k, hget, hgate⟩ := actual_gate_index source rewards C_star C_h count hspan hcross r hr
    obtain ⟨hkw, c, hck, selected, hselected, payload, hpayload, hpending, hactual,
        _hdraw, _hconfirmation, next, owned, base, hnext, hpayloadNext, hpendingNext,
        hsuffix, _quotas, _counts, _htiming, _hsource⟩ :=
      ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_support_eq_release_suffix
        rate source rewards C_star C_h count hcross hspan k hgate
    have hGsuffix : G = W.drop (c.val + 1) := by
      simpa only [I, s, R, W, G] using hsuffix
    refine ⟨W.take (c.val + 1), ?_⟩
    calc
      W.take (c.val + 1) ++ G = W.take (c.val + 1) ++ W.drop (c.val + 1) := by rw [hGsuffix]
      _ = W := List.take_append_drop _ _

/-- No retained UP or DOWN decoder diagnostics are appended while traversing
the actual release gate suffix. The completed-decision lists therefore remain
those of the actual pre-release prefix. -/
theorem release_decoder_diagnostics_append
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hcross s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    let G := R.records.filter (fun r => localReleaseGate rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))
    ∃ prior : List (Record (p := p) (rate := rate)),
      prior ++ G = W ∧
      W.filterMap (fun r => r.output.coordinator.up) =
        prior.filterMap (fun r => r.output.coordinator.up) ∧
      ∀ i : Fin (p.m - 1),
        W.filterMap (fun r => (r.output.followers i).down) =
          prior.filterMap (fun r => (r.output.followers i).down) := by
  intro I s R W G
  have hdecomposition : ∃ prior : List (Record (p := p) (rate := rate)), prior ++ G = W := by
    simpa only [I, s, R, W, G] using
      actual_gate_suffix_decomposition source rewards C_star C_h count hspan hcross
  obtain ⟨prior, happend⟩ := hdecomposition
  have hsil : ∀ k : Fin W.length, W[k.val].output.coordinator.up = none := by
    simpa only [I, s, R, W] using
      first_live_up_diagnostic_eq_none source rewards C_star C_h count hspan hcross
  have hgateUp : ∀ r ∈ G, r.output.coordinator.up = none := by
    intro r hr
    obtain ⟨k, hget, hgate⟩ := actual_gate_index source rewards C_star C_h count hspan hcross r hr
    have hwindow := actual_gate_record_in_window source rewards C_star C_h count hspan hcross k hgate
    have hkW : k.val < W.length := by simpa only [I, s, R, W] using hwindow.1
    have hrecord : W[k.val] = r := by
      have h := hwindow.2
      simpa only [I, s, R, W] using h.trans hget
    rw [← hrecord]
    exact hsil ⟨k.val, hkW⟩
  have hdown : ∀ r ∈ G, ∀ i : Fin (p.m - 1),
      (r.output.followers i).downInput = none ∧ (r.output.followers i).down = none := by
    simpa only [I, s, R, G] using
      release_down_diagnostics_eq_none source rewards C_star C_h count hspan hcross
  have hgateDown : ∀ i, ∀ r ∈ G, (r.output.followers i).down = none := by
    intro i r hr
    exact (hdown r hr i).2
  have hnilUp := filterMap_up_nil_of_absent G hgateUp
  refine ⟨prior, happend, ?_, ?_⟩
  · calc
      W.filterMap (fun r => r.output.coordinator.up) =
          (prior ++ G).filterMap (fun r => r.output.coordinator.up) := by rw [← happend]
      _ = prior.filterMap (fun r => r.output.coordinator.up) ++
          G.filterMap (fun r => r.output.coordinator.up) := List.filterMap_append
      _ = prior.filterMap (fun r => r.output.coordinator.up) := by simp [hnilUp]
  · intro i
    have hnilDown := filterMap_down_nil_of_absent G i (hgateDown i)
    calc
      W.filterMap (fun r => (r.output.followers i).down) =
          (prior ++ G).filterMap (fun r => (r.output.followers i).down) := by rw [← happend]
      _ = prior.filterMap (fun r => (r.output.followers i).down) ++
          G.filterMap (fun r => (r.output.followers i).down) := List.filterMap_append
      _ = prior.filterMap (fun r => (r.output.followers i).down) := by simp [hnilDown]

/-- No-crossing source inputs carry the existing no-actual-record tag. -/
theorem actual_record_none_of_no_crossing
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing = none)
    (t : Fin p.T) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source = none :=
  ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
    rate rewards C_star C_h t source hnone

end Bandits.Support.ReferenceFirstLiveReleaseDecoderSilence

end
