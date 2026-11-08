/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpResetCalendar
public import Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent

/-!
# Actual generated UP reset to observable prefix bridge

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,74-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module composes the actual generated UP reset interval with the existing
observable batch-prefix marker. It does not construct a second run, reset
selector, decoder bank, or history, and it makes no probability or tail claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AdaptiveAffineBatchTail

namespace Bandits.Support.ReferenceGeneratedUpResetPrefixBridge

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} {rate : RateInput p}

/-- A real retained diagnostic contributes exactly its literal stamped test,
or the empty list when this channel is not selected or eligible. The saved
sender option is retained even when it is `none`. -/
theorem evidenceUpTest_of_diagnostic
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : record.output.coordinator.up = some d) :
    (d.input.selectedFollower = i ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
      (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest i record.evidence).toList =
        [⟨d.input.time.val, d.input.affineSample, d.expected⟩]) ∧
    (¬ (d.input.selectedFollower = i ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)) →
      (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest i record.evidence).toList = []) := by
  classical
  constructor
  · intro h
    change (ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i
      record.output.coordinator.up).toList = _
    simp [hd, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, h]
  · intro h
    change (ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i
      record.output.coordinator.up).toList = []
    simp [hd, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, h]

/-- A physical record without an UP diagnostic contributes no UP test. -/
theorem evidenceUpTest_of_no_diagnostic
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hd : record.output.coordinator.up = none) :
    (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest i record.evidence).toList = [] := by
  change (ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i
    record.output.coordinator.up).toList = []
  rw [hd]
  rfl

private theorem recordUpTests_coordinates_eq
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ((ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest (p := p) (rate := rate)
        i record.evidence).toList.map fun test => (test.time, test.sample)) =
      (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i).map
        fun entry => (entry.time.val, entry.sample) := by
  classical
  change ((ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic (p := p) (rate := rate)
      i record.output.coordinator.up).toList.map fun test => (test.time, test.sample)) =
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i).map
      fun entry => (entry.time.val, entry.sample)
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hdiagnostic]
  | some diagnostic =>
      by_cases hselected : diagnostic.input.selectedFollower = i
      · by_cases heligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput diagnostic.input)
        · simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
            ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
            ReferenceCoordinatorUpDecoderReplay.retainedUpTime,
            ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
            AffineBatchDecoder.positiveAt, AffineBatchDecoder.entry,
            hdiagnostic, hselected, heligible]
          rfl
        · simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
            ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
            ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
            AffineBatchDecoder.positiveAt, hdiagnostic, hselected, heligible]
      · simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          hdiagnostic, hselected]

private theorem recordsUpTests_coordinates_eq
    (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    ((ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests (p := p) (rate := rate)
      i records).map fun test => (test.time, test.sample)) =
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).map
        fun entry => (entry.time.val, entry.sample) := by
  classical
  change ((records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).filterMap
      (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest (p := p) (rate := rate) i)).map
        (fun test => (test.time, test.sample)) =
    (records.flatMap (fun record =>
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i)).map
        (fun entry => (entry.time.val, entry.sample))
  rw [List.filterMap_eq_flatMap_toList, List.map_flatMap, List.flatMap_map,
    List.map_flatMap]
  apply List.flatMap_congr
  intro record hrecord
  exact recordUpTests_coordinates_eq i record

/-- A retained test keeps every field of its actual selected eligible UP
diagnostic, including the saved `Option Word` sender. -/
theorem evidenceUpTest_sender_fields
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (htest : ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest i record.evidence = some test) :
    ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
      test.time = diagnostic.input.time.val ∧
      test.sample = diagnostic.input.affineSample ∧
      test.sent = diagnostic.expected := by
  classical
  change ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i
      record.output.coordinator.up = some test at htest
  cases hdiagnostic : record.output.coordinator.up with
  | none => simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, hdiagnostic] at htest
  | some diagnostic =>
      by_cases heligible : diagnostic.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)
      · simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, hdiagnostic, heligible] at htest
        cases htest
        exact ⟨diagnostic, rfl, rfl, rfl, rfl⟩
      · simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, hdiagnostic, heligible] at htest

/-- Every test in a retained list has the timestamp, sample and saved sender
from the original diagnostic of its actual physical record. -/
theorem recordsUpTests_sender_fields
    (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (htest : test ∈ ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests i records) :
    ∃ record, record ∈ records ∧ ∃ diagnostic,
      record.output.coordinator.up = some diagnostic ∧
      test.time = diagnostic.input.time.val ∧
      test.sample = diagnostic.input.affineSample ∧
      test.sent = diagnostic.expected := by
  classical
  rw [ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests] at htest
  rcases List.mem_filterMap.mp htest with ⟨evidence, hevidence, htest⟩
  rcases List.mem_map.mp hevidence with ⟨record, hrecord, rfl⟩
  obtain ⟨diagnostic, hdiagnostic, htime, hsample, hsent⟩ :=
    evidenceUpTest_sender_fields i record test htest
  exact ⟨record, hrecord, diagnostic, hdiagnostic, htime, hsample, hsent⟩

/-- Once the actual channel has its birth boundary and ordinary incoming
state, the source marker is exactly prior candidate survival at the literal
tests-since-birth length. -/
theorem actualUpBatchPrefixMarker_iff_testsSince
    (ell : ℕ) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial incoming : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)))
    (hBirth : ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i start alpha initial records)
    (hOrdinary : incoming.coordinator ≠ .dagger) :
    ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker ell candidate i start alpha
      initial incoming records ↔
    (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i start alpha records).length = ell - 1 ∧
      AdaptiveAffineBatchTail.survives candidate (ell - 1)
        (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i start alpha records) := by
  unfold ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
  constructor
  · rintro ⟨_, _, hlength, hsurvives⟩
    exact ⟨hlength, hsurvives⟩
  · rintro ⟨hlength, hsurvives⟩
    exact ⟨hBirth, hOrdinary, hlength, hsurvives⟩

/-- Every actual generated UP diagnostic has a canonical reset birth on the
same physical prefix. The inherited birth is extracted from the exact earlier
quota-completing record, and its eligibility comes from the physical-call
ledger rather than an additional premise. -/
theorem generated_up_actual_call_reset_birth
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (count : ℕ) (hcount : count ≤ p.T - s) :
    let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
      rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
      (by omega) hmode
    ∀ (k : Fin fullRun.records.length)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let record := fullRun.records[k.val]'k.isLt
      (hd : record.output.coordinator.up = some d) →
      have hfullLength : fullRun.records.length = count := by
        simpa [fullRun] using ReferenceActivePhysicalHorizon.run_record_count active rows selected
          rewards s count (by omega) hmode
      have hkcount : k.val < count := Nat.lt_of_lt_of_eq k.isLt hfullLength
      have hkspan : s + k.val ≤ p.T := by omega
      let prefixRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val
        hkspan hmode
      prefixRun.records = fullRun.records.take k.val ∧
      record.input.state = prefixRun.finalState ∧
      record.input.rows = rows ∧ record.input.selected = selected ∧
      record.input.rewards = rewards ∧ record.input.time.val = s + k.val ∧
      record.input.state.coordinator ≠ .dagger ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state ∧
      (∃ ledger,
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
        d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
        d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
        d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
        d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
        d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input) ∧
      ((∃ ledger,
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid ∧
          record.output.next.upDecoderBank = record.input.state.upDecoderBank) ∨
        ∃ ledger out,
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .success out ∨
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .rejected out) ∧
          out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
          record.output.next.upDecoderBank = out.2) ∧
      (record.output.next.coordinator ≠ .dagger →
        record.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter d.input ∧
        ∀ channel,
          d.input.selectedFollower = channel →
          ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true →
          (record.input.state.upDecoderBank channel).pending.length + 1 =
            AffineBatchDecoder.quota p →
          record.output.next.upDecoderBank channel = d.decoderAfter ∧
          (record.output.next.upDecoderBank channel).pending = [] ∧
          (record.output.next.upDecoderBank channel).completed =
            (record.input.state.upDecoderBank channel).completed ++
              [(record.input.state.upDecoderBank channel).pending ++
                [AffineBatchDecoder.entry p
                  (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                  d.input.time]]) ∧
      ∃ alpha resetCount resetState,
        alpha = s + resetCount ∧
        (∃ _hresetCount : resetCount ≤ k.val,
          alpha ≤ s + k.val ∧
          ∃ hresetSpan : s + resetCount ≤ p.T,
            (∃ hresetState : resetState =
                (ReferenceActivePhysicalHorizon.run active rows selected rewards s resetCount
                  hresetSpan hmode).finalState,
              (resetState.upDecoderBank d.input.selectedFollower).pending = [] ∧
              ReferenceUpDecoderBankInvariant.upBankInvariant resetState ∧
              resetState.coordinator ≠ .dagger ∧
              ((resetCount = 0 ∧ alpha = s ∧ resetState = active ∧
                  (resetState.upDecoderBank d.input.selectedFollower).completed =
                    (active.upDecoderBank d.input.selectedFollower).completed) ∨
                ∃ j : Fin k.val,
                  ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    let marker := fullRun.records[j.val]'(by omega)
                    alpha = s + j.val + 1 ∧
                    marker.output.coordinator.up = some diagnostic ∧
                    diagnostic.input.selectedFollower = d.input.selectedFollower ∧
                    ReferenceGeneratedAffineHashHalf.directionPositive 1 marker.input = true ∧
                    (marker.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                      AffineBatchDecoder.quota p ∧
                    (∀ l : Fin k.val,
                      (∃ earlier : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                        let earlierRecord := prefixRun.records[l.val]'(by
                          have h := ReferenceActivePhysicalHorizon.run_record_count active rows
                            selected rewards s k.val hkspan hmode
                          have hprefLength : prefixRun.records.length = k.val := by
                            simpa [prefixRun] using h
                          omega)
                        earlierRecord.output.coordinator.up = some earlier ∧
                        earlier.input.selectedFollower = d.input.selectedFollower ∧
                        ReferenceGeneratedAffineHashHalf.directionPositive 1 earlierRecord.input =
                          true ∧
                        (earlierRecord.input.state.upDecoderBank d.input.selectedFollower).pending.length +
                            1 = AffineBatchDecoder.quota p) → l.val ≤ j.val) ∧
                    resetCount = j.val + 1 ∧ resetState = marker.output.next ∧
                    marker.output.next.coordinator ≠ .dagger ∧
                    ReferenceUpDecoderBankInvariant.upBankInvariant marker.input.state ∧
                    (marker.output.next.upDecoderBank d.input.selectedFollower).completed =
                      (marker.input.state.upDecoderBank d.input.selectedFollower).completed ++
                        [(marker.input.state.upDecoderBank d.input.selectedFollower).pending ++
                          [AffineBatchDecoder.entry p
                            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                            diagnostic.input.time]]) ∧
            (∀ marker, marker ∈ prefixRun.records.drop resetCount →
              ¬ ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                marker.output.coordinator.up = some diagnostic ∧
                diagnostic.input.selectedFollower = d.input.selectedFollower ∧
                ReferenceGeneratedAffineHashHalf.directionPositive 1 marker.input = true ∧
                (marker.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                  AffineBatchDecoder.quota p) ∧
            ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha active
              (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
              some resetState ∧
            ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth d.input.selectedFollower s alpha active
              (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
            ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount?
                d.input.selectedFollower s alpha active
                  (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
              some (resetState.upDecoderBank d.input.selectedFollower).completed.length ∧
            (record.input.state.upDecoderBank d.input.selectedFollower).completed =
              (resetState.upDecoderBank d.input.selectedFollower).completed ∧
            ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
                (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
              ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests d.input.selectedFollower
                (prefixRun.records.drop resetCount) ∧
            (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
                (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).map
                  (fun test => (test.time, test.sample)) =
              (record.input.state.upDecoderBank d.input.selectedFollower).pending.map
                (fun entry => (entry.time.val, entry.sample)) ∧
            (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
                (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).length =
              (record.input.state.upDecoderBank d.input.selectedFollower).pending.length ∧
            1 ≤ (record.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 ∧
            (record.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 ≤
              AffineBatchDecoder.quota p ∧
            (∀ (ell : ℕ) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)),
              ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker ell candidate
                  d.input.selectedFollower s alpha active record.input.state
                  (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ↔
                (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower
                    s alpha (prefixRun.records.map
                      ReferenceActivePhysicalHorizon.RoundRecord.evidence)).length = ell - 1 ∧
                  AdaptiveAffineBatchTail.survives candidate (ell - 1)
                    (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower
                      s alpha (prefixRun.records.map
                        ReferenceActivePhysicalHorizon.RoundRecord.evidence))) ∧
            ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount?
                d.input.selectedFollower s alpha active
                  (prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
              some (record.input.state.upDecoderBank d.input.selectedFollower).completed.length ∧
            let resetMode := Eq.mp
              (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
                (s + resetCount)) hresetState).symm
              (ReferenceActivePhysicalHorizon.run_allActiveAtEnd active rows selected rewards
                s resetCount hresetSpan hmode)
            let suffixRun := ReferenceActivePhysicalHorizon.run resetState rows selected rewards
              (s + resetCount) (k.val - resetCount) (by omega) resetMode
            suffixRun.records = prefixRun.records.drop resetCount ∧
            suffixRun.finalState = record.input.state ∧
            ReferenceActivePhysicalHorizon.Connected resetState suffixRun.records suffixRun.finalState ∧
            suffixRun.records.map (fun prior => prior.input.time.val) =
              ReferenceActivePhysicalHorizon.calendar (s + resetCount) (k.val - resetCount) ∧
            (∀ prior, prior ∈ suffixRun.records →
              prior.input.rows = rows ∧ prior.input.selected = selected ∧
                prior.input.rewards = rewards) ∧
            (ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true →
              (record.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 =
                AffineBatchDecoder.quota p →
              d.decoderAfter.pending = [] ∧
              d.decoderAfter.completed =
                (resetState.upDecoderBank d.input.selectedFollower).completed ++
                  [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries suffixRun.records
                      d.input.selectedFollower ++
                    [AffineBatchDecoder.entry p
                      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                      d.input.time]]))) := by
  dsimp only
  intro k d hd
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
    (by omega) hmode
  let record := fullRun.records[k.val]'k.isLt
  have hprefix := ReferenceGeneratedUpResetCalendar.generated_up_actual_call_prefix
    rate rewards C_star C_h q t s hs control0 x control count hcount
  dsimp only at hprefix
  obtain ⟨hstate, hprefixRecords, hrows, hselected, hrew, htime, hordinary, hinvariant,
    _, hcall, hphysical, hsurviving⟩ := hprefix k d hd
  have hreset := ReferenceGeneratedUpResetCalendar.generated_up_actual_call_reset_interval
    rate rewards C_star C_h q t s hs control0 x control count hcount
  dsimp only at hreset
  obtain ⟨hresetRecords, alpha, resetCount, resetState, hAlpha,
      ⟨hresetCount, hAlphaBound, hresetSpan, hresetState,
        ⟨hresetPending, hresetInvariant, hresetOrdinary, hbranch, hnoAfterReset, htail⟩⟩⟩ :=
    hreset k d hd
  let prefixRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val
    (by omega) hmode
  have hprefixRecords' : prefixRun.records = fullRun.records.take k.val := hprefixRecords
  have hresetState' : resetState =
      (ReferenceActivePhysicalHorizon.run active rows selected rewards s resetCount
        hresetSpan hmode).finalState := hresetState
  rcases htail with ⟨hSuffixRecords, hSuffixFinal, hConnected, hCalendar,
    hSuffixInvariant, hSuffixNo, hCompleted, hPending, hPendingSmall,
    hSuffixRoots, hCurrentDecoder⟩
  let resetMode := Eq.mp
    (congrArg (fun state => ReferenceActivePhysicalHorizon.allActiveAtStart state
      (s + resetCount)) hresetState').symm
    (ReferenceActivePhysicalHorizon.run_allActiveAtEnd active rows selected rewards
      s resetCount hresetSpan hmode)
  let suffixRun := ReferenceActivePhysicalHorizon.run resetState rows selected rewards
    (s + resetCount) (k.val - resetCount) (by omega) resetMode
  let prefixEvidence := prefixRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence
  have hSuffixRecords' : suffixRun.records = prefixRun.records.drop resetCount := hSuffixRecords
  have hSuffixFinal' : suffixRun.finalState = record.input.state := hSuffixFinal
  have hfullLength : fullRun.records.length = count := by
    exact ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards s count
      (by omega) hmode
  have hkcount : k.val < count := Nat.lt_of_lt_of_eq k.isLt hfullLength
  have hprefixLength : prefixRun.records.length = k.val := by
    exact ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards s k.val
      (by omega) hmode
  have hincoming :
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha active prefixEvidence =
        some resetState := by
    rcases hbranch with ⟨_, hAlphaStart, hresetActive, _⟩ |
      ⟨j, diagnostic, hAlphaMarker, hdiagnostic, _, _, _, _, hresetCountMarker,
        hresetStateMarker, _, _, _⟩
    · unfold ReferenceGeneratedUpBatchPrefixEvent.incomingState?
      rw [ite_eq_left (by omega), hresetActive]
    · have hjk := j.isLt
      have hjFull : j.val < fullRun.records.length := by omega
      have hjPrefix : j.val < prefixRun.records.length := by omega
      have hprefixMarker : prefixRun.records[j.val]'hjPrefix = fullRun.records[j.val]'hjFull := by
        have hget : prefixRun.records[j.val]? = (fullRun.records.take k.val)[j.val]? :=
          congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate)) => records[j.val]?) hprefixRecords'
        have htake : (fullRun.records.take k.val)[j.val]? = fullRun.records[j.val]? := by
          simp [j.isLt]
        have hget' := hget.trans htake
        rw [List.getElem?_eq_getElem hjPrefix, List.getElem?_eq_getElem hjFull] at hget'
        exact Option.some.inj hget'
      have hprefixEvidenceAt : prefixEvidence[j.val]? =
          some (fullRun.records[j.val]'hjFull).evidence := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hjPrefix, hprefixMarker]
        rfl
      have hmarkerAfter : (fullRun.records[j.val]'hjFull).evidence.after = resetState := by
        calc
          _ = (fullRun.records[j.val]'hjFull).output.next := rfl
          _ = resetState := hresetStateMarker.symm
      unfold ReferenceGeneratedUpBatchPrefixEvent.incomingState?
      have hoffset : alpha - s - 1 = j.val := by omega
      rw [ite_eq_right (by omega), hoffset, hprefixEvidenceAt]
      simpa only [Option.map_some] using congrArg some hmarkerAfter
  have hbirth :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth d.input.selectedFollower s alpha active
        prefixEvidence := by
    classical
    unfold ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth
    refine ⟨by omega, ?_⟩
    rw [hincoming]
    refine ⟨hresetOrdinary, ?_⟩
    rcases hbranch with ⟨_, hAlphaStart, _, _⟩ |
      ⟨j, diagnostic, hAlphaMarker, hdiagnostic, hselectedMarker, hpositiveMarker,
        hquotaMarker, _, _, hresetStateMarker, _, _, _⟩
    · exact Or.inl hAlphaStart
    · right
      have hjk := j.isLt
      have hjFull : j.val < fullRun.records.length := by omega
      let markerRecord := fullRun.records[j.val]'hjFull
      have hphysical := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
        markerRecord diagnostic hdiagnostic
      rcases hphysical with ⟨ledger, hsite, hledger, hbank, _, _, _, _, _, _, _, _, _, _⟩
      have hdirection :
          ReferenceGeneratedAffineHashHalf.directionPositive 1
              markerRecord.input =
            decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) := by
        calc
          _ = ReferenceActiveAffinePositiveTest.upPositive
                markerRecord.input := by
              simp [ReferenceGeneratedAffineHashHalf.directionPositive]
          _ = ReferenceActiveAffinePositiveTest.upDiagnosticPositive
                markerRecord.output.coordinator.up :=
              ReferenceActiveAffinePositiveTest.record_upPositive _
          _ = decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) := by
              rw [hdiagnostic]
              rfl
      have hdecision :
          decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) =
            true := by
        rw [← hdirection]
        exact hpositiveMarker
      have heligible :
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) :=
        of_decide_eq_true hdecision
      have hbankChannel :
          diagnostic.input.upDecoderBank d.input.selectedFollower =
            markerRecord.input.state.upDecoderBank
              d.input.selectedFollower := congrFun hbank d.input.selectedFollower
      have hquotaActual :
          (diagnostic.input.upDecoderBank d.input.selectedFollower).pending.length + 1 =
            AffineBatchDecoder.quota p := by
        rw [hbankChannel]
        exact hquotaMarker
      have hprefixEvidenceIndex :
          prefixEvidence[alpha - s - 1]? =
            some markerRecord.evidence := by
        have hprefixEvidenceAt : prefixEvidence[j.val]? =
            some markerRecord.evidence := by
          have hjPrefix : j.val < prefixRun.records.length := by omega
          have hmarkerEq : prefixRun.records[j.val]'hjPrefix = fullRun.records[j.val]'hjFull := by
            have hget : prefixRun.records[j.val]? = (fullRun.records.take k.val)[j.val]? :=
              congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate)) => records[j.val]?) hprefixRecords'
            have htake : (fullRun.records.take k.val)[j.val]? = fullRun.records[j.val]? := by
              simp [j.isLt]
            have hget' := hget.trans htake
            rw [List.getElem?_eq_getElem hjPrefix, List.getElem?_eq_getElem hjFull] at hget'
            exact Option.some.inj hget'
          rw [List.getElem?_map, List.getElem?_eq_getElem hjPrefix, hmarkerEq]
          rfl
        have hoffset : alpha - s - 1 = j.val := by omega
        rw [hoffset]
        exact hprefixEvidenceAt
      refine ⟨markerRecord.evidence, diagnostic,
        hprefixEvidenceIndex, ?_, hselectedMarker, heligible, hquotaActual⟩
      change markerRecord.output.coordinator.up = some diagnostic
      exact hdiagnostic
  have hcompletedCount :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount?
          d.input.selectedFollower s alpha active prefixEvidence =
        some (resetState.upDecoderBank d.input.selectedFollower).completed.length := by
    unfold ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount?
    rw [hincoming]
    rfl
  have hcompleted :
      (record.input.state.upDecoderBank d.input.selectedFollower).completed =
        (resetState.upDecoderBank d.input.selectedFollower).completed := by
    rw [← hSuffixFinal']
    exact hCompleted
  have htests :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
          prefixEvidence =
        ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests d.input.selectedFollower
          (prefixRun.records.drop resetCount) := by
    have hOffset : alpha - s = resetCount := by omega
    calc
      _ = (prefixEvidence.drop resetCount).filterMap
            (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest d.input.selectedFollower) := by
          simp only [ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince, hOffset]
      _ = ((prefixRun.records.drop resetCount).map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence).filterMap
              (ReferenceGeneratedUpBatchPrefixEvent.evidenceUpTest d.input.selectedFollower) := by
          simp only [prefixEvidence, ← List.map_drop]
      _ = ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests d.input.selectedFollower
            (prefixRun.records.drop resetCount) := rfl
  have hPending' :
      (record.input.state.upDecoderBank d.input.selectedFollower).pending =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (prefixRun.records.drop resetCount) d.input.selectedFollower := by
    rw [← hSuffixRecords', ← hSuffixFinal']
    exact hPending
  have htestCoordinates :
      (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
        prefixEvidence).map (fun test => (test.time, test.sample)) =
      (record.input.state.upDecoderBank d.input.selectedFollower).pending.map
        (fun entry => (entry.time.val, entry.sample)) := by
    calc
      _ = (ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests d.input.selectedFollower
            (prefixRun.records.drop resetCount)).map (fun test => (test.time, test.sample)) :=
        congrArg (fun tests : List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) =>
          tests.map (fun test => (test.time, test.sample))) htests
      _ = (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (prefixRun.records.drop resetCount) d.input.selectedFollower).map
              (fun entry => (entry.time.val, entry.sample)) :=
        recordsUpTests_coordinates_eq d.input.selectedFollower
          (prefixRun.records.drop resetCount)
      _ = (record.input.state.upDecoderBank d.input.selectedFollower).pending.map
            (fun entry => (entry.time.val, entry.sample)) := by
        rw [hPending']
  have htestsLength :
      (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince d.input.selectedFollower s alpha
        prefixEvidence).length =
      (record.input.state.upDecoderBank d.input.selectedFollower).pending.length := by
    have h := congrArg List.length htestCoordinates
    simpa only [List.length_map] using h
  have hpendingSmallActual :
      (record.input.state.upDecoderBank d.input.selectedFollower).pending.length <
        AffineBatchDecoder.quota p := by
    rw [← hSuffixFinal']
    exact hPendingSmall
  have hquotaActual :
      (record.input.state.upDecoderBank d.input.selectedFollower).pending.length + 1 ≤
        AffineBatchDecoder.quota p := by omega
  refine ⟨hprefixRecords', hstate, hrows, hselected, hrew, htime, hordinary, hinvariant,
    hcall, hphysical, hsurviving, alpha, resetCount, resetState, hAlpha,
    ⟨hresetCount, hAlphaBound, hresetSpan,
      ⟨hresetState', hresetPending, hresetInvariant, hresetOrdinary, hbranch,
        hnoAfterReset, hincoming, hbirth, hcompletedCount, hcompleted, htests,
        htestCoordinates, htestsLength, by omega, hquotaActual,
        (fun ell candidate => actualUpBatchPrefixMarker_iff_testsSince ell candidate
          d.input.selectedFollower s alpha active record.input.state prefixEvidence hbirth hordinary),
        ?_, hSuffixRecords, hSuffixFinal, hConnected, hCalendar, hSuffixRoots, hCurrentDecoder⟩⟩⟩
  rw [hcompleted]
  exact hcompletedCount

/-- On U's original UP,i source branch, `originalSourceRunInput_eq` identifies
the whole original source run with the same retained generated seed, original
rows and J, fixed current control, rewards, and physical calendar used by the
reset bridge. -/
theorem original_source_run_eq_generated
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (count : ℕ) (hcount : count ≤ p.T - s) :
    let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
    let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s launch.1 launch.2.1 control0 control).mp launch.2.2
    let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
      rate rewards C_star C_h q t s hs control0 launch
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart).2.1
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let hspan : s + count ≤ p.T := by omega
    let originalInput := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    let originalRun := ReferenceActiveHorizonMeasurability.runOfInput s count hspan originalInput
    let generatedRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
      hspan hmode
    source = z.1 ∧
      originalInput.val = (active, rows, selected, rewards) ∧
      originalRun.records = generatedRun.records ∧
    originalRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        generatedRun.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence ∧
      originalRun.finalState = generatedRun.finalState := by
  dsimp only
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s launch.1 launch.2.1 control0 control).mp launch.2.2
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 launch
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let hspan : s + count ≤ p.T := by omega
  let originalInput := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let originalRun := ReferenceActiveHorizonMeasurability.runOfInput s count hspan originalInput
  let generatedRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s count
    hspan hmode
  have hlaunchRemainder :=
    ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  have hsource : source = z.1 := by
    dsimp [source, control]
    rw [hlaunchRemainder]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  have hinput := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_eq
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hinputVal : originalInput.val = (active, rows, selected, rewards) := by
    have h := congrArg Subtype.val hinput
    change originalInput.val = (active, rows, selected, rewards) at h
    exact h
  let rootInput : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s := ⟨(active, rows, selected, rewards), hmode⟩
  have hinputFull : originalInput = rootInput := Subtype.ext hinputVal
  have hrunProjection := congrArg
    (fun input : ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) s =>
      ((ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records,
        (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).finalState))
    hinputFull
  have hrunProjection' :
      (originalRun.records, originalRun.finalState) =
        (generatedRun.records, generatedRun.finalState) := by
    simpa [originalRun, generatedRun, rootInput,
      ReferenceActiveHorizonMeasurability.runOfInput] using hrunProjection
  have hrecords : originalRun.records = generatedRun.records := congrArg Prod.fst hrunProjection'
  exact ⟨hsource, hinputVal, hrecords,
    congrArg (List.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hrecords,
    congrArg Prod.snd hrunProjection'⟩

/-- Consume the bridge on U's original UP,i source constructor, at the
actual current record (offset `t.val - s`). The marker is the before-current
event, and the optional current test keeps the current diagnostic's saved
expected option and original row sample. -/
theorem original_source_actual_up_marker
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (hinput : input = ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t s hs control0 i z)
    (current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcurrent :
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega) input).records[
        t.val - s]? = some current)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : current.output.coordinator.up = some d)
    (hselected : d.input.selectedFollower = i) :
    ∃ alpha resetCount resetState, ∃ (hresetSpan : s + resetCount ≤ p.T),
      alpha = s + resetCount ∧ resetCount ≤ t.val - s ∧ alpha ≤ t.val ∧
      resetState =
        (ReferenceActiveHorizonMeasurability.runOfInput s resetCount hresetSpan input).finalState ∧
      (resetState.upDecoderBank i).pending = [] ∧
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha input.val.1
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) = some resetState ∧
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha input.val.1
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha input.val.1
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
        some (resetState.upDecoderBank i).completed.length ∧
      (current.input.state.upDecoderBank i).completed =
        (resetState.upDecoderBank i).completed ∧
      let tests := ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence)
      tests = ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests i
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.drop
          resetCount) ∧
      tests.map (fun test => (test.time, test.sample)) =
        ((current.input.state.upDecoderBank i).pending.map
          (fun entry => (entry.time.val, entry.sample))) ∧
      tests.length = (current.input.state.upDecoderBank i).pending.length ∧
      current.input.rows = z.1.1.2 ∧ current.input.selected = q ∧
      current.input.rewards = rewards ∧ current.input.state =
        (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).finalState ∧
      current.input.time.val = t.val ∧
      1 ≤ (current.input.state.upDecoderBank i).pending.length + 1 ∧
      (current.input.state.upDecoderBank i).pending.length + 1 ≤ AffineBatchDecoder.quota p ∧
      (ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
        (rate := rate) rewards C_star C_h q t s hs control0 alpha
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i z ↔
        AdaptiveAffineBatchTail.survives candidate (current.input.state.upDecoderBank i).pending.length
          tests) ∧
      (ReferenceGeneratedAffineHashHalf.directionPositive 1 current.input = true →
        ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i (some d) = some test ∧
          test.time = current.input.time.val ∧
          test.sample = ((z.1.1.2 q).2 current.input.time).2 (1, i) ∧
          test.sent = d.expected ∧
          test.sent = ReferenceActiveAffinePositiveTest.upSent current.input) := by
  dsimp only
  classical
  subst input
  let n := t.val - s
  let sourceInput := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 launch
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s launch.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hspanPrefix : s + n ≤ p.T := by dsimp [n]; omega
  have hspanFull : s + (n + 1) ≤ p.T := by dsimp [n]; omega
  have hprefixRun := original_source_run_eq_generated rate rewards C_star C_h q t s hs
    control0 i z n (by dsimp [n]; omega)
  rcases hprefixRun with
    ⟨hsource, hinputValue, hprefixRecords, hprefixEvidence, hprefixFinal⟩
  have hsourceInit : sourceInput.val.1 = active := congrArg Prod.fst hinputValue
  have hfullRun := original_source_run_eq_generated rate rewards C_star C_h q t s hs
    control0 i z (n + 1) (by dsimp [n]; omega)
  rcases hfullRun with
    ⟨_, _, hfullRecords, _, _⟩
  have hcurrentLength :
      (ReferenceActiveHorizonMeasurability.runOfInput s (n + 1) hspanFull sourceInput).records.length =
        n + 1 := by
    exact ReferenceActivePhysicalHorizon.run_record_count sourceInput.val.1 sourceInput.val.2.1
      sourceInput.val.2.2.1 sourceInput.val.2.2.2 s (n + 1) hspanFull sourceInput.property
  have hcurrentIndex : n <
      (ReferenceActiveHorizonMeasurability.runOfInput s (n + 1) hspanFull sourceInput).records.length := by
    rw [hcurrentLength]
    omega
  have hrootLength :
      (ReferenceActivePhysicalHorizon.run active rows selected rewards s (n + 1) hspanFull hmode).records.length =
        n + 1 := by
    exact ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards s
      (n + 1) hspanFull hmode
  have hrootIndex : n <
      (ReferenceActivePhysicalHorizon.run active rows selected rewards s (n + 1) hspanFull hmode).records.length := by
    rw [hrootLength]
    omega
  let currentRoot := (ReferenceActivePhysicalHorizon.run active rows selected rewards s (n + 1)
    hspanFull hmode).records[n]'hrootIndex
  have hcurrentEq : current = currentRoot := by
    have hget := congrArg (fun records : List
        (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) => records[n]?) hfullRecords
    rw [List.getElem?_eq_getElem hcurrentIndex, List.getElem?_eq_getElem hrootIndex] at hget
    have hcurrentAt :
        (ReferenceActiveHorizonMeasurability.runOfInput s (n + 1) hspanFull sourceInput).records[
          n]? = some current := by
      simpa [n] using hcurrent
    have hrunRecord := Option.some.inj hget
    have hsourceRecord :
        (ReferenceActiveHorizonMeasurability.runOfInput s (n + 1) hspanFull sourceInput).records[
          n]'hcurrentIndex = current := by
      have h := hcurrentAt
      rw [List.getElem?_eq_getElem hcurrentIndex] at h
      exact Option.some.inj h
    exact hsourceRecord.symm.trans hrunRecord
  have hrootDiagnostic : currentRoot.output.coordinator.up = some d := by
    rw [← hcurrentEq]
    exact hdiagnostic
  have hroot := generated_up_actual_call_reset_birth rate rewards C_star C_h q t s hs
    control0 launch control (n + 1) (by dsimp [n]; omega)
  dsimp only at hroot
  have hrootAt := hroot ⟨n, hrootIndex⟩ d hrootDiagnostic
  rw [hselected] at hrootAt
  rcases hrootAt with
    ⟨hrootPrefixRecords, hrootState, hrootRows, hrootSelected, hrootRewards, hrootTime,
      hrootOrdinary, hrootInvariant, hrootCall, hrootPhysical, hrootSurviving,
      alpha, resetCount, resetState, hAlpha,
      ⟨hresetCount, hAlphaBound, hresetSpan, hresetState,
        ⟨hresetPending, hresetInvariant, hresetOrdinary, hresetOrigin,
          hnoLaterReset, hincoming, hbirth, hcompletedCount, hcompleted, htests,
          htestCoordinates, htestsLength, htestsPositive, htestsQuota, _⟩⟩⟩
  have hresetRun := original_source_run_eq_generated rate rewards C_star C_h q t s hs
    control0 i z resetCount (by dsimp [n] at hresetCount ⊢; omega)
  rcases hresetRun with ⟨_, _, _, _, hresetRunFinal⟩
  have hresetFinal :
      resetState =
        (ReferenceActiveHorizonMeasurability.runOfInput s resetCount hresetSpan sourceInput).finalState := by
    calc
      _ = (ReferenceActivePhysicalHorizon.run active rows selected rewards s resetCount
          hresetSpan hmode).finalState := hresetState
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s resetCount hresetSpan
          sourceInput).finalState := hresetRunFinal.symm
  have hsourceRows : current.input.rows = z.1.1.2 := by
    calc
      _ = currentRoot.input.rows := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input.rows)
        hcurrentEq
      _ = rows := hrootRows
      _ = z.1.1.2 := by
        change (ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1).1.2 = z.1.1.2
        exact congrArg (fun x : ReferenceGeneratedUpBatchPrefixEvent.SourceInput p => x.1.2) hsource
  have hselectedActual : current.input.selected = q := by
    calc
      _ = currentRoot.input.selected := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input.selected)
        hcurrentEq
      _ = selected := hrootSelected
      _ = q := by
        change ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1) = q
        rw [hsource]
        exact ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
          (rate := rate) rewards C_star C_h q t (1, i) s z
  have hn : s + n = t.val := by simpa [n] using Nat.add_sub_of_le hs
  have hcurrentTime : current.input.time.val = t.val := by
    have hrootTime' : currentRoot.input.time.val = s + n := by simpa using hrootTime
    calc
      _ = currentRoot.input.time.val := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input.time.val)
        hcurrentEq
      _ = s + n := hrootTime'
      _ = t.val := hn
  let sourcePrefix :=
    ReferenceActiveHorizonMeasurability.runOfInput s n hspanPrefix sourceInput
  let rootPrefix := ReferenceActivePhysicalHorizon.run active rows selected rewards s n
    hspanPrefix hmode
  have hprefixRecordsEq : sourcePrefix.records = rootPrefix.records := by
    simpa [sourcePrefix, rootPrefix, n] using hprefixRecords
  have hprefixEvidenceEq :
      (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    simpa [sourcePrefix, rootPrefix, n] using hprefixEvidence
  have hprefixFinalEq : sourcePrefix.finalState = rootPrefix.finalState := by
    simpa [sourcePrefix, rootPrefix, n] using hprefixFinal
  have hcurrentState : current.input.state = sourcePrefix.finalState := by
    calc
      _ = currentRoot.input.state := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input.state)
        hcurrentEq
      _ = rootPrefix.finalState := hrootState
      _ = sourcePrefix.finalState := hprefixFinalEq.symm
  have hcurrentRewards : current.input.rewards = rewards := by
    calc
      _ = currentRoot.input.rewards := congrArg
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input.rewards)
        hcurrentEq
      _ = rewards := hrootRewards
  have hcurrentBank : current.input.state.upDecoderBank i =
      currentRoot.input.state.upDecoderBank i := by
    exact congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input.state.upDecoderBank i) hcurrentEq
  have htestsEqRoot :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
          (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
        ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
          (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    rw [hprefixEvidenceEq]
  have htestsSource :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
          (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
        ReferenceGeneratedUpBatchPrefixEvent.recordsUpTests i (sourcePrefix.records.drop resetCount) := by
    rw [hprefixEvidenceEq, hprefixRecordsEq]
    simpa [rootPrefix, n] using htests
  have htestsLengthSource :
      (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).length =
        (current.input.state.upDecoderBank i).pending.length := by
    calc
      _ = (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
            (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).length :=
        congrArg List.length htestsEqRoot
      _ = (currentRoot.input.state.upDecoderBank i).pending.length := htestsLength
      _ = (current.input.state.upDecoderBank i).pending.length := by
        rw [hcurrentBank]
  have htestCoordinatesSource :
      (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).map
          (fun test => (test.time, test.sample)) =
        (current.input.state.upDecoderBank i).pending.map
          (fun entry => (entry.time.val, entry.sample)) := by
    calc
      _ = (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
            (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)).map
              (fun test => (test.time, test.sample)) :=
        congrArg (fun tests : List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) =>
          tests.map (fun test => (test.time, test.sample))) htestsEqRoot
      _ = (currentRoot.input.state.upDecoderBank i).pending.map
            (fun entry => (entry.time.val, entry.sample)) := htestCoordinates
      _ = (current.input.state.upDecoderBank i).pending.map
            (fun entry => (entry.time.val, entry.sample)) := by
        rw [hcurrentBank]
  have hcompletedSource :
      (current.input.state.upDecoderBank i).completed = (resetState.upDecoderBank i).completed := by
    calc
      _ = (currentRoot.input.state.upDecoderBank i).completed := by rw [hcurrentBank]
      _ = (resetState.upDecoderBank i).completed := hcompleted
  have hincomingEvidence :
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha sourceInput.val.1
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun evidence => ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha
      sourceInput.val.1 evidence) hprefixEvidenceEq
  have hincomingInitial :
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha active
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun initial => ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha initial
      (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) hsourceInit
  have hincomingSource :
      ReferenceGeneratedUpBatchPrefixEvent.incomingState? s alpha sourceInput.val.1
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
          some resetState := by
    exact hincomingEvidence.trans (hincomingInitial.trans hincoming)
  have hbirthEvidence :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha sourceInput.val.1
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun evidence => ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha
      sourceInput.val.1 evidence) hprefixEvidenceEq
  have hbirthInitial :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha active
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun initial => ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha initial
      (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) hsourceInit
  have hbirthSource : ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha sourceInput.val.1
      (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    rw [hbirthEvidence, hbirthInitial]
    exact hbirth
  have hcompletedCountEvidence :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha sourceInput.val.1
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun evidence => ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha
      sourceInput.val.1 evidence) hprefixEvidenceEq
  have hcompletedCountInitial :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha sourceInput.val.1
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha active
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun initial => ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha initial
      (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) hsourceInit
  have hcompletedCountSource :
      ReferenceGeneratedUpBatchPrefixEvent.upBatchBirthCompletedCount? i s alpha sourceInput.val.1
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
          some (resetState.upDecoderBank i).completed.length := by
    exact hcompletedCountEvidence.trans (hcompletedCountInitial.trans hcompletedCount)
  have hrootBirth : ReferenceGeneratedUpBatchPrefixEvent.upBatchBirth i s alpha active
      (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
    simpa [rootPrefix, n] using hbirth
  have hmarkerCore := actualUpBatchPrefixMarker_iff_testsSince
    (ell := (current.input.state.upDecoderBank i).pending.length + 1)
    candidate i s alpha active currentRoot.input.state
    (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
    hrootBirth hrootOrdinary
  have hAlphaLower : s ≤ alpha := by rw [hAlpha]; omega
  have hAlphaUpper' : alpha ≤ s + n := by simpa using hAlphaBound
  have hAlphaUpper : alpha ≤ t.val := by rw [← hn]; exact hAlphaUpper'
  have hquotaSource :
      (current.input.state.upDecoderBank i).pending.length + 1 ≤ AffineBatchDecoder.quota p := by
    calc
      _ = (currentRoot.input.state.upDecoderBank i).pending.length + 1 := by rw [hcurrentBank]
      _ ≤ AffineBatchDecoder.quota p := htestsQuota
  have hmarkerIncoming : sourcePrefix.finalState = currentRoot.input.state :=
    hprefixFinalEq.trans hrootState.symm
  have hmarkerInitial :
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        sourceInput.val.1 sourcePrefix.finalState
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        active sourcePrefix.finalState
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun initial => ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
      ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha initial
      sourcePrefix.finalState (sourcePrefix.records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence)) hsourceInit
  have hmarkerIncoming' :
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        active sourcePrefix.finalState
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        active currentRoot.input.state
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun incoming => ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
      ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha active incoming
      (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) hmarkerIncoming
  have hmarkerEvidence :
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        active currentRoot.input.state
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        active currentRoot.input.state
        (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :=
    congrArg (fun evidence => ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
      ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha active
      currentRoot.input.state evidence) hprefixEvidenceEq
  have hmarkerSource :
      ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
        (rate := rate) rewards C_star C_h q t s hs control0 alpha
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i z ↔
      AdaptiveAffineBatchTail.survives candidate (current.input.state.upDecoderBank i).pending.length
        (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
          (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) := by
    unfold ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
    change (s ≤ alpha ∧ alpha ≤ t.val ∧ 1 ≤ (current.input.state.upDecoderBank i).pending.length + 1 ∧
      (current.input.state.upDecoderBank i).pending.length + 1 ≤ AffineBatchDecoder.quota p ∧
      ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
        ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha
        sourceInput.val.1 sourcePrefix.finalState
        (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) ↔
      AdaptiveAffineBatchTail.survives candidate (current.input.state.upDecoderBank i).pending.length
        (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
          (sourcePrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence))
    rw [hmarkerInitial, hmarkerIncoming', hmarkerEvidence]
    constructor
    · rintro ⟨_, _, _, _, hmarker⟩
      obtain ⟨_, hgood⟩ := hmarkerCore.mp hmarker
      have hindex : (current.input.state.upDecoderBank i).pending.length =
          (currentRoot.input.state.upDecoderBank i).pending.length := by
        exact congrArg List.length (congrArg (fun bank => bank.pending) hcurrentBank)
      have hlen : (current.input.state.upDecoderBank i).pending.length + 1 - 1 =
          (current.input.state.upDecoderBank i).pending.length := by omega
      have hgoodCurrent : AdaptiveAffineBatchTail.survives candidate
          (current.input.state.upDecoderBank i).pending.length
          (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
            (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) := by
        simpa only [hlen] using hgood
      rw [← htestsEqRoot] at hgoodCurrent
      exact hgoodCurrent
    · intro hgood
      have hindex : (current.input.state.upDecoderBank i).pending.length =
          (currentRoot.input.state.upDecoderBank i).pending.length := by
        exact congrArg List.length (congrArg (fun bank => bank.pending) hcurrentBank)
      have hlen : (current.input.state.upDecoderBank i).pending.length + 1 - 1 =
          (current.input.state.upDecoderBank i).pending.length := by omega
      have hgoodRoot : AdaptiveAffineBatchTail.survives candidate
          (currentRoot.input.state.upDecoderBank i).pending.length
          (ReferenceGeneratedUpBatchPrefixEvent.upBatchTestsSince i s alpha
            (rootPrefix.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) := by
        rw [htestsEqRoot] at hgood
        simpa [hindex] using hgood
      have hmarker : ReferenceGeneratedUpBatchPrefixEvent.actualUpBatchPrefixMarker
          ((current.input.state.upDecoderBank i).pending.length + 1) candidate i s alpha active
          currentRoot.input.state (rootPrefix.records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
        have hlenRoot : (current.input.state.upDecoderBank i).pending.length + 1 - 1 =
            (currentRoot.input.state.upDecoderBank i).pending.length := by omega
        apply hmarkerCore.mpr
        constructor
        · rw [htestsLength, ← hlenRoot]
        · rw [hlenRoot]
          exact hgoodRoot
      exact ⟨hAlphaLower, hAlphaUpper, by omega, hquotaSource, hmarker⟩
  have hpositiveTest :
      ReferenceGeneratedAffineHashHalf.directionPositive 1 current.input = true →
        ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic i (some d) = some test ∧
          test.time = current.input.time.val ∧
          test.sample = ((z.1.1.2 q).2 current.input.time).2 (1, i) ∧
          test.sent = d.expected ∧
          test.sent = ReferenceActiveAffinePositiveTest.upSent current.input := by
    intro hpositive
    have hdirection :
        ReferenceGeneratedAffineHashHalf.directionPositive 1 current.input =
          decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)) := by
      calc
        _ = ReferenceActiveAffinePositiveTest.upPositive current.input := by
          simp [ReferenceGeneratedAffineHashHalf.directionPositive]
        _ = ReferenceActiveAffinePositiveTest.upDiagnosticPositive current.output.coordinator.up :=
          ReferenceActiveAffinePositiveTest.record_upPositive current
        _ = decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)) := by
          rw [hdiagnostic]
          rfl
    have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) :=
      of_decide_eq_true (by rw [← hdirection]; exact hpositive)
    obtain ⟨test, htest, htime, hsample, hsent⟩ :=
      ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpTest_sourceFields i current d
        z.1.1.2 q hsourceRows hselectedActual hdiagnostic hselected heligible
    have hexpected := ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected
      current d hdiagnostic
    exact ⟨test, htest, htime, hsample, hsent, hsent.trans hexpected⟩
  refine ⟨alpha, resetCount, resetState, hresetSpan, hAlpha, hresetCount, ?_, hresetFinal,
    hresetPending, hincomingSource, hbirthSource, hcompletedCountSource, hcompletedSource,
    htestsSource, htestCoordinatesSource, htestsLengthSource, hsourceRows, hselectedActual,
    hcurrentRewards, hcurrentState, hcurrentTime, ?_, hquotaSource,
    hmarkerSource, hpositiveTest⟩
  · have hn : s + n = t.val := by simpa [n] using Nat.add_sub_of_le hs
    have hAlphaUpper' : alpha ≤ s + n := by simpa using hAlphaBound
    rw [← hn]
    exact hAlphaUpper'
  · omega

end Bandits.Support.ReferenceGeneratedUpResetPrefixBridge

end
