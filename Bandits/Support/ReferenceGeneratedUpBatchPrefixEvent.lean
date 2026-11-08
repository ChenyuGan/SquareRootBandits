/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAffineHashHalf
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

/-!
# Observable prefixes of a generated UP batch

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-150`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module projects the real retained UP diagnostics of the existing
source-generated physical run.  It defines no second execution, reset rule,
or supplied history.  The projections retain the original launch fibre,
whole rows, reward table, and private coordinates. All results are internal:
physical bank/reset chronology, q-th calendar unions, half recurrences/tails,
exceptional-event coverage, and the main regret theorem remain outside this leaf.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceCollectionServiceTailMeasurability
open Bandits.Support.ReferenceActiveAffinePositiveTest
open Bandits.Support.AdaptiveAffineBatchTail

namespace Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent

abbrev Parameters := ReferenceGeneratedAffineHashHalf.Parameters
abbrev RateInput := ReferenceGeneratedAffineHashHalf.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RetainedRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t
abbrev LaunchStart {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :=
  ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
    rate rewards C_star C_h q t s hs control0

variable {p : Parameters} {rate : RateInput p}

/-- The actual positive-test projection of a retained UP diagnostic. -/
def upTestOfDiagnostic (i : Fin (p.m - 1))
    (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate)) :
    Option (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) := by
  classical
  exact match diagnostic with
    | none => none
    | some d =>
        if d.input.selectedFollower = i ∧
            AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) then
          some ⟨d.input.time.val, d.input.affineSample, d.expected⟩
        else none

/-- A record-code projection through the canonical retained UP diagnostic. -/
def roundRecordUpDiagnosticCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate) :=
  (code.2.2.1.2.2.2.2).2.2.2.2

/-- Convert the canonical diagnostic code to exactly the actual test fields. -/
def roundRecordUpTestCode (i : Fin (p.m - 1))
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
  upTestOfDiagnostic i
    ((roundRecordUpDiagnosticCode (p := p) (rate := rate) code).map
      ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic)

/-- The canonical diagnostic code reconstructs the actual record diagnostic. -/
theorem roundRecordUpDiagnosticCode_reconstructs
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ((roundRecordUpDiagnosticCode (p := p) (rate := rate)
      (ReferenceActiveHorizonMeasurability.roundRecordCode record)).map
        ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic) =
      record.output.coordinator.up := by
  have h := (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record).2.1
  change ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.2.2.2.2 =
    record.output.coordinator at h
  have hup := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up h
  simpa [ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation,
    roundRecordUpDiagnosticCode] using hup

/-- The code-level test is exactly the selected-i eligible test in the real
record, with the diagnostic's original time, affine sample, and expected
option. -/
theorem roundRecordUpTestCode_reconstructs
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    roundRecordUpTestCode (p := p) (rate := rate) i
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      upTestOfDiagnostic i record.output.coordinator.up := by
  rw [roundRecordUpTestCode, roundRecordUpDiagnosticCode_reconstructs]

/-- At an actual selected-i eligible call, the saved test sample is the
unchanged original selected-row `(UP,i)` coordinate and its sent option is the
physical round's prepared UP offer. -/
theorem actualRecordUpTest_fields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hselected : diagnostic.input.selectedFollower = i)
    (heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input)) :
    ∃ test, upTestOfDiagnostic (p := p) (rate := rate) i (some diagnostic) = some test ∧
      test.time = record.input.time.val ∧
      test.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      test.sent = diagnostic.expected := by
  obtain ⟨_, _, _, _, htime, _, hselectedRow, hsample, _, _, _, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      record diagnostic hdiagnostic
  have hsender : CoordinatorUpMeasurability.selectedFollowerIndex
      ((record.input.rows record.input.selected).2 record.input.time) = i := by
    calc
      _ = diagnostic.input.selectedFollower := hselectedRow.symm
      _ = i := hselected
  have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
      ((record.input.rows record.input.selected).2 record.input.time) = i := by
    apply Fin.ext
    exact congrArg Fin.val hsender
  have hsample' : diagnostic.input.affineSample =
      ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) := by
    simpa only [hchannel] using hsample
  refine ⟨⟨diagnostic.input.time.val, diagnostic.input.affineSample, diagnostic.expected⟩,
    ?_, ?_, ?_, ?_⟩
  · simp [upTestOfDiagnostic, hselected, heligible]
  · rw [htime]
  · exact hsample'
  · rfl

/-- The actual diagnostic test keeps the source row's selected `(UP,i)` sample
and its own saved expected offer when the run retains the original selected
row and coordinator index. -/
theorem actualRecordUpTest_sourceFields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (rows : CompletePublicTable.CompleteRows p) (q : Fin (M p))
    (hrows : record.input.rows = rows) (hselectedRow : record.input.selected = q)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hselected : diagnostic.input.selectedFollower = i)
    (heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input)) :
    ∃ test, upTestOfDiagnostic (p := p) (rate := rate) i (some diagnostic) = some test ∧
      test.time = record.input.time.val ∧
      test.sample = ((rows q).2 record.input.time).2 (1, i) ∧
      test.sent = diagnostic.expected := by
  obtain ⟨test, htest, htime, hsample, hsent⟩ :=
    actualRecordUpTest_fields (p := p) (rate := rate) i record diagnostic
      hdiagnostic hselected heligible
  refine ⟨test, htest, htime, ?_, hsent⟩
  simpa only [hrows, hselectedRow] using hsample

/-- The original selected-row control at every physical time before `t` is
unchanged when the selected complete current-time control is replaced. This
is the row frame used to interpret the actual samples in every prior record. -/
theorem splitSource_selectedRow_priorTime_eq
    (q : Fin (M p)) (t : Fin p.T)
    (remainder : RetainedRemainder p q t)
    (control control' : TimeControl p) (v : Fin p.T) (hv : v.val < t.val) :
    ((ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder).1.2 q).2 v =
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control' remainder).1.2 q).2 v := by
  have hvne : v ≠ t := by
    intro h
    have := congrArg Fin.val h
    omega
  let other : ReferenceSelectedAffinePairLaw.Other t := ⟨v, hvne⟩
  change (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control, remainder)).1.2 q).2 v =
    (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control', remainder)).1.2 q).2 v
  rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
      p q t control remainder other,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
      p q t control' remainder other]

/-- All focal actual tests in an ordered list of physical records. -/
def evidenceUpTest (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) :=
  upTestOfDiagnostic i record.coordinator.up

/-- All focal actual tests in an ordered list of physical records. -/
def recordsUpTests (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
  (records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).filterMap
    (evidenceUpTest i)

/-- The actual test stream is a function only of the actual ordered evidence
stream, so equal evidence streams have equal literal tests (including sample
and saved expected option). -/
theorem recordsUpTests_eq_of_evidence (i : Fin (p.m - 1))
    (records records' : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)))
    (hevidence : records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      records'.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :
    recordsUpTests (p := p) (rate := rate) i records =
      recordsUpTests (p := p) (rate := rate) i records' := by
  unfold recordsUpTests
  rw [hevidence]

/-- The same test list read from the existing lossless run observation. -/
def observationUpTests (i : Fin (p.m - 1))
    (observation : ReferenceActiveHorizonMeasurability.RunObservationCode
      (p := p) (rate := rate)) :
    List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
  observation.2.filterMap (roundRecordUpTestCode (p := p) (rate := rate) i)

/-- The retained observation's test list agrees with direct projection of the
actual run records. -/
theorem observationUpTests_eq_recordsUpTests (i : Fin (p.m - 1))
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    observationUpTests (p := p) (rate := rate) i
        (ReferenceActiveHorizonMeasurability.runObservation start count hspan
          ⟨(initial, (rows, (selected, rewards))), hmode⟩) =
      recordsUpTests (p := p) (rate := rate) i
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records := by
  classical
  unfold observationUpTests recordsUpTests
  rw [ReferenceActiveHorizonMeasurability.runObservation_records]
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start := ⟨(initial, (rows, (selected, rewards))), hmode⟩
  have hrun : ReferenceActiveHorizonMeasurability.runOfInput
      (p := p) (rate := rate) start count hspan input =
      ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode := rfl
  rw [← hrun]
  simp only [List.filterMap_map]
  apply List.filterMap_congr
  intro record hrecord
  change roundRecordUpTestCode (p := p) (rate := rate) i
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
    evidenceUpTest (p := p) (rate := rate) i record.evidence
  rw [roundRecordUpTestCode_reconstructs]
  rfl

/-- The incoming state at a calendar boundary, reconstructed from the initial
state or the actual preceding record. `none` is retained on malformed or
out-of-range code; no default state is introduced. -/
def incomingState? (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    Option (ReferenceActivePhysicalStep.State p rate) :=
  if alpha = start then some initial
  else (records[alpha - start - 1]?).map (fun record => record.after)

/-- The literal UP batch birth condition at `alpha`: an ordinary incoming
state, with either the observed launch start itself or the actual preceding
eligible selected-i diagnostic whose incoming pending count reaches quota. -/
def upBatchBirth (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) : Prop :=
  start ≤ alpha ∧
    match incomingState? (p := p) (rate := rate) start alpha initial records with
    | none => False
    | some incoming =>
        incoming.coordinator ≠ .dagger ∧
          (alpha = start ∨ ∃ record diagnostic,
            records[alpha - start - 1]? = some record ∧
            record.coordinator.up = some diagnostic ∧
            diagnostic.input.selectedFollower = i ∧
            AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
            (diagnostic.input.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p)

/-- Completed-batch ordinal at birth, read from the actual incoming bank. -/
def upBatchBirthCompletedCount? (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    Option ℕ :=
  (incomingState? (p := p) (rate := rate) start alpha initial records).map
    (fun state => (state.upDecoderBank i).completed.length)

/-- The actual test list from the birth boundary up to, but excluding, the
current incoming physical time. -/
def upBatchTestsSince (i : Fin (p.m - 1)) (start alpha : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
  (records.drop (alpha - start)).filterMap (evidenceUpTest i)

/-- Literal before-current-control prefix marker. The run supplied here is
the existing physical prefix `[start, current)`, so no current or future
positive test is consulted. -/
def actualUpBatchPrefixMarker (ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (incoming : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) : Prop :=
  upBatchBirth (p := p) (rate := rate) i start alpha initial records ∧
    incoming.coordinator ≠ .dagger ∧
    (upBatchTestsSince (p := p) (rate := rate) i start alpha records).length = ell - 1 ∧
    AdaptiveAffineBatchTail.survives candidate (ell - 1)
      (upBatchTestsSince (p := p) (rate := rate) i start alpha records)

/-- The completed ordinal and the entire tests before the birth are observable
projections, retained alongside the current incoming bank and all tests since
birth. -/
def upBatchBirthPastTests (i : Fin (p.m - 1)) (start alpha : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) :=
  (records.take (alpha - start)).filterMap (evidenceUpTest i)

/-- The literal event in the actual retained launch subtype, at arbitrary alpha. -/
def upBatchPrefixSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (alpha ell : ℕ) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    Set (LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :=
  {x | s ≤ alpha ∧ alpha ≤ t.val ∧ 1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧
      let run := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs x.2.2 (by omega)
      actualUpBatchPrefixMarker (p := p) (rate := rate) ell candidate i s alpha
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
          rate rewards C_star C_h q t s hs control0 x) run.finalState
        (run.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)}

/-- Replacing the whole selected-row control at the current time leaves the
actual before-current-control batch marker unchanged. The common launch state,
the full evidence list, and the final incoming state come from G's genuine
generated-prefix comparison. -/
theorem actualUpBatchPrefixMarker_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (control control' : TimeControl p)
    (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
    let hstart' := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 x.2.1 control0 control').mp x.2.2
    actualUpBatchPrefixMarker (p := p) (rate := rate) ell candidate i s alpha
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x)
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control x.1 x.2.1 s (t.val - s) hs hstart (by omega)).finalState
      ((ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control x.1 x.2.1 s (t.val - s) hs hstart (by omega)).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) ↔
    actualUpBatchPrefixMarker (p := p) (rate := rate) ell candidate i s alpha
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x)
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control' x.1 x.2.1 s (t.val - s) hs hstart' (by omega)).finalState
      ((ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control' x.1 x.2.1 s (t.val - s) hs hstart' (by omega)).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
  let hstart' := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control').mp x.2.2
  have hcount : s + (t.val - s) ≤ t.val := by omega
  let run := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rate rewards C_star C_h q t control x.1 x.2.1 s (t.val - s) hs hstart hcount
  let run' := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rate rewards C_star C_h q t control' x.1 x.2.1 s (t.val - s) hs hstart' hcount
  obtain ⟨active, hlaunch0, hlaunch, hlaunch', _, _, hfinal, hevidence⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.1 x.2.1 control0 s (t.val - s) hs hcount
    x.2.2 control control'
  change (actualUpBatchPrefixMarker (p := p) (rate := rate) ell candidate i s alpha
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x) run.finalState
      (run.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)) ↔
    (actualUpBatchPrefixMarker (p := p) (rate := rate) ell candidate i s alpha
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x) run'.finalState
      (run'.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence))
  rw [hfinal, hevidence]

/-- The ordinary/dagger tag in the inherited coordinator sum code. -/
def ordinaryCode : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

/-- Only the incoming ordinary flag and the actual completed-batch count. -/
abbrev BoundaryObservation := Bool × ℕ

/-- Projection of an existing lossless state code, retaining no continuous
state coordinate that the marker does not inspect. -/
def stateBoundaryCode (i : Fin (p.m - 1))
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) : BoundaryObservation :=
  (ordinaryCode code.1, (code.2.1 i).completed.length)

/-- The same literal projection of an actual physical state. -/
def stateBoundary (i : Fin (p.m - 1)) (state : ReferenceActivePhysicalStep.State p rate) :
    BoundaryObservation :=
  stateBoundaryCode i (ReferenceActivePhysicalStepMeasurability.encodeState state)

theorem stateBoundary_ordinary (i : Fin (p.m - 1))
    (state : ReferenceActivePhysicalStep.State p rate) :
    (stateBoundary i state).1 = true ↔ state.coordinator ≠ .dagger := by
  cases hc : state.coordinator <;>
    simp [stateBoundary, stateBoundaryCode, ordinaryCode,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]

theorem measurable_stateBoundaryCode (i : Fin (p.m - 1)) :
    Measurable (stateBoundaryCode (p := p) (rate := rate) i) := by
  have ho : Measurable (ordinaryCode (p := p) (rate := rate)) :=
    Measurable.sumElim measurable_const
      (Measurable.sumElim measurable_const
        (Measurable.sumElim measurable_const measurable_const))
  exact (ho.comp measurable_fst).prodMk
    ((measurable_from_top : Measurable (fun bank : CoordinatorUpReception.UpDecoderBank p =>
      (bank i).completed.length)).comp (measurable_fst.comp measurable_snd))

/-- A countable observable of one real record: the after-boundary projection
and the entire canonical UP diagnostic, including sample and expected option. -/
abbrev PrefixRecordObservation := BoundaryObservation ×
  Option (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate)

def evidencePrefixObservation (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) :
    PrefixRecordObservation (p := p) (rate := rate) :=
  (stateBoundary i record.after,
    record.coordinator.up.map ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic)

def roundRecordPrefixCode (i : Fin (p.m - 1))
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    PrefixRecordObservation (p := p) (rate := rate) :=
  (stateBoundaryCode i code.2.2.2.2, roundRecordUpDiagnosticCode code)

theorem roundRecordPrefixCode_reconstructs (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    roundRecordPrefixCode i (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      evidencePrefixObservation i record.evidence := by
  apply Prod.ext
  · -- On real records this code is the original output state's encoding.
    have hc : (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.2.2 =
        ReferenceActivePhysicalStepMeasurability.encodeState record.output.next := by
      rw [record.output_eq]
      rfl
    change stateBoundaryCode i _ = stateBoundary i record.output.next
    rw [hc]
    rfl
  · have h := roundRecordUpDiagnosticCode_reconstructs record
    have he := congrArg (Option.map ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic) h
    have hinv : (fun code : ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate =>
        ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic
          (ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic code)) = id := by
      funext code
      cases code
      rfl
    change roundRecordUpDiagnosticCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      record.output.coordinator.up.map ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic
    simpa only [Option.map_map, Function.comp_def, hinv, Option.map_id, id_eq] using he

theorem measurable_roundRecordPrefixCode (i : Fin (p.m - 1)) :
    Measurable (roundRecordPrefixCode (p := p) (rate := rate) i) := by
  have hs : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hd : Measurable (roundRecordUpDiagnosticCode (p := p) (rate := rate)) := by
    unfold roundRecordUpDiagnosticCode
    exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
          (measurable_snd.comp measurable_snd)))))))))
  exact ((measurable_stateBoundaryCode i).comp hs).prodMk hd

/-- Indexed list observations have measurable singletons when their element
space does. This uses their actual inherited list space, not a replacement. -/
private theorem measurableSingleton_list {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] : MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective (ReferenceActiveHorizonMeasurability.listObservationCoordinates
      (α := α)) := by
    intro left right h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt left n =
      ReferenceActiveHorizonMeasurability.listObservationAt right n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hl : left[n]? <;> cases hr : right[n]? <;> simp_all
  constructor
  intro records
  have heq : ({records} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨congrArg _, fun h => hinj h⟩
  let : MeasurableSingletonClass (Unit ⊕ α) := ⟨fun tag => by
    cases tag with
    | inl value => simpa only [Set.image_singleton] using (measurableSet_singleton value).inl_image
    | inr value => simpa only [Set.image_singleton] using (measurableSet_singleton value).inr_image⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

/-- Initial and current boundary projections and all intervening actual
record observations. Every field is countable; the original state is not. -/
abbrev PrefixObservation := BoundaryObservation × (BoundaryObservation ×
  List (PrefixRecordObservation (p := p) (rate := rate)))

/-- Recover the incoming boundary observation at the independent birth. -/
def incomingBoundary? (start alpha : ℕ) (initial : BoundaryObservation)
    (records : List (PrefixRecordObservation (p := p) (rate := rate))) :
    Option BoundaryObservation :=
  if alpha = start then some initial else (records[alpha - start - 1]?).map Prod.fst

/-- Literal positive-test projection of a canonical record observation. -/
def prefixObservationTest (i : Fin (p.m - 1))
    (record : PrefixRecordObservation (p := p) (rate := rate)) :=
  upTestOfDiagnostic i (record.2.map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic)

/-- Birth read only from the incoming ordinary tag and the preceding actual
selected eligible diagnostic completing quota. Acceptance is not consulted. -/
def prefixObservationBirth (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : BoundaryObservation)
    (records : List (PrefixRecordObservation (p := p) (rate := rate))) : Prop :=
  start ≤ alpha ∧
    match incomingBoundary? start alpha initial records with
    | none => False
    | some incoming => incoming.1 = true ∧
        (alpha = start ∨ ∃ record diagnostic,
          records[alpha - start - 1]? = some record ∧
          record.2 = some diagnostic ∧
          diagnostic.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
          (diagnostic.input.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p)

/-- The complete before-current-control marker on its countable observation. -/
def prefixObservationMarker (ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (start alpha : ℕ)
    (code : PrefixObservation (p := p) (rate := rate)) : Prop :=
  prefixObservationBirth i start alpha code.1 code.2.2 ∧ code.2.1.1 = true ∧
    ((code.2.2.drop (alpha - start)).filterMap (prefixObservationTest i)).length = ell - 1 ∧
    AdaptiveAffineBatchTail.survives candidate (ell - 1)
      ((code.2.2.drop (alpha - start)).filterMap (prefixObservationTest i))

theorem incomingBoundary_reconstructs (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    incomingBoundary? start alpha (stateBoundary i initial)
        (records.map (evidencePrefixObservation i)) =
      (incomingState? start alpha initial records).map (stateBoundary i) := by
  unfold incomingBoundary? incomingState?
  split <;> simp only [List.getElem?_map, Option.map_map, Option.map_some]
  rfl

theorem prefixObservationBirth_reconstructs (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    prefixObservationBirth i start alpha (stateBoundary i initial)
        (records.map (evidencePrefixObservation i)) ↔
      upBatchBirth i start alpha initial records := by
  classical
  unfold prefixObservationBirth upBatchBirth
  rw [incomingBoundary_reconstructs]
  cases hi : incomingState? (p := p) (rate := rate) start alpha initial records with
  | none => rfl
  | some incoming =>
    simp only [Option.map_some, stateBoundary_ordinary]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply or_congr_right
    simp only [List.getElem?_map, Option.map_eq_some_iff]
    constructor
    · rintro ⟨record, diagnostic, ⟨actual, ha, heq⟩, hd, hselected, heligible, hquota⟩
      subst record
      change actual.coordinator.up.map _ = some diagnostic at hd
      obtain ⟨d, hactual, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact ⟨actual, d, ha, hactual, hselected, heligible, hquota⟩
    · rintro ⟨record, diagnostic, hr, hd, hselected, heligible, hquota⟩
      exact ⟨evidencePrefixObservation i record,
        ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic diagnostic,
        ⟨record, hr, rfl⟩, by simp [evidencePrefixObservation, hd],
        hselected, heligible, hquota⟩

theorem prefixObservationTest_reconstructs (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)) :
    prefixObservationTest i (evidencePrefixObservation i record) = evidenceUpTest i record := by
  unfold prefixObservationTest evidencePrefixObservation evidenceUpTest
  simp only [Option.map_map]
  have heq : (fun d : ReferenceActivePhysicalStep.UpDiagnostic p rate =>
      ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic
        (ReferenceCollectionServiceTailMeasurability.encodeUpDiagnostic d)) = id :=
    funext ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic_encodeUpDiagnostic
  simp only [Function.comp_def, heq, Option.map_id, id_eq]

/-- Reconstruction includes birth, count and all past good tests, at the
same arbitrary alpha used by the retained set. -/
theorem prefixObservationMarker_reconstructs (ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial incoming : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    prefixObservationMarker ell candidate i start alpha
        (stateBoundary i initial, stateBoundary i incoming,
          records.map (evidencePrefixObservation i)) ↔
      actualUpBatchPrefixMarker ell candidate i start alpha initial incoming records := by
  unfold prefixObservationMarker actualUpBatchPrefixMarker upBatchTestsSince
  rw [prefixObservationBirth_reconstructs, stateBoundary_ordinary]
  simp only [← List.map_drop, List.filterMap_map, Function.comp_def]
  have heq : (fun record : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
      prefixObservationTest i (evidencePrefixObservation i record)) = evidenceUpTest i :=
    funext (prefixObservationTest_reconstructs i)
  rw [heq]

/-- Actual baseline run input, formed from the retained generated seed,
reconstructed whole rows, original private J, and unchanged reward table. -/
def retainedRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
  ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0 x,
    (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2,
    ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1), rewards),
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1⟩

theorem measurable_retainedRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (retainedRunInput (rate := rate) rewards C_star C_h q t s hs control0) := by
  have hsource : Measurable (fun x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 =>
      ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hselected : Measurable (fun x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 =>
      ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)) := by
    have heq : (fun x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 =>
        ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)) = fun _ => q := by
      funext x
      rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 x.2.1
    rw [heq]
    exact measurable_const
  exact ((ReferenceRetainedBoundaryMeasurability.measurable_retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0).prodMk
    ((measurable_snd.comp (measurable_fst.comp hsource)).prodMk
      (hselected.prodMk measurable_const))).subtype_mk

/-- Complete measurable observation of the before-current physical prefix. -/
def retainedPrefixObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    PrefixObservation (p := p) (rate := rate) :=
  let input := retainedRunInput (rate := rate) rewards C_star C_h q t s hs control0 x
  let hspan : s + (t.val - s) ≤ p.T := by omega
  (stateBoundary i input.val.1,
    stateBoundary i (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) hspan input).finalState,
    (ReferenceActiveHorizonMeasurability.runObservation s (t.val - s) hspan input).2.map
      (roundRecordPrefixCode i))

theorem measurable_retainedPrefixObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    Measurable (retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i) := by
  let input := retainedRunInput (rate := rate) rewards C_star C_h q t s hs control0
  have hinput := measurable_retainedRunInput (rate := rate) rewards C_star C_h q t s hs control0
  have hspan : s + (t.val - s) ≤ p.T := by omega
  have hboundary := (measurable_stateBoundaryCode (rate := rate) i).comp
    ReferenceActivePhysicalStepMeasurability.measurable_encodeState
  have hinitial := hboundary.comp (measurable_fst.comp (measurable_subtype_coe.comp hinput))
  have hfinal := hboundary.comp
    ((ReferenceActiveHorizonMeasurability.measurable_runFinalState
      (p := p) (rate := rate) s (t.val - s) hspan).comp hinput)
  have hrecords := measurable_snd.comp
    ((ReferenceActiveHorizonMeasurability.measurable_runObservation
      (p := p) (rate := rate) s (t.val - s) hspan).comp hinput)
  have hmap := ReferenceActiveHorizonMeasurability.measurable_list_map _ hrecords
    (roundRecordPrefixCode i) (measurable_roundRecordPrefixCode i)
  exact hinitial.prodMk (hfinal.prodMk hmap)

/-- The measurable observation is exactly the projection of G's actual
prefix state and complete evidence; no whole row-bearing record equality. -/
theorem retainedPrefixObservation_reconstructs
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i x =
      let run := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs x.2.2 (by omega)
      (stateBoundary i (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
          rate rewards C_star C_h q t s hs control0 x),
        stateBoundary i run.finalState,
        (run.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).map
          (evidencePrefixObservation i)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change List.map (roundRecordPrefixCode i)
        (List.map ReferenceActiveHorizonMeasurability.roundRecordCode _) = _
      simp only [List.map_map]
      apply List.map_congr_left
      intro record _
      exact roundRecordPrefixCode_reconstructs i record

/-- Borel measurability of S_I for the independent birth alpha and ordinal.
The range conditions are explicit members of this same set. -/
theorem measurableSet_upBatchPrefixSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    MeasurableSet (upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i) := by
  let : MeasurableSingletonClass (List (PrefixRecordObservation (p := p) (rate := rate))) :=
    measurableSingleton_list
  let event : Set (PrefixObservation (p := p) (rate := rate)) :=
    {code | s ≤ alpha ∧ alpha ≤ t.val ∧ 1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧
      prefixObservationMarker ell candidate i s alpha code}
  have hevent : MeasurableSet event := event.to_countable.measurableSet
  have heq : upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i =
      retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i ⁻¹' event := by
    ext x
    change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
    rw [retainedPrefixObservation_reconstructs]
    simp only [prefixObservationMarker_reconstructs]
  rw [heq]
  exact hevent.preimage (measurable_retainedPrefixObservation
    (rate := rate) rewards C_star C_h q t s hs control0 i)

/-- The concrete UP pair remainder cylinder C_I = rho^{-1}(val '' S_I). -/
def upBatchPrefixCylinder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    Set (ReferenceGeneratedAffineHashHalf.PairRemainder p q t (1, i)) :=
  ReferenceGeneratedAffineHashHalf.retainedControlProjection ⁻¹'
    (Subtype.val '' upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i)

/-- The image uses the proved Borel launch subtype, then the actual rho
projection. There is no normalization or extra selected-row factor. -/
theorem measurableSet_upBatchPrefixCylinder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    MeasurableSet (upBatchPrefixCylinder (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i) := by
  have hemb := MeasurableEmbedding.subtype_coe
    (ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
      rate rewards C_star C_h q t s hs control0)
  exact (hemb.measurableSet_image.mpr (measurableSet_upBatchPrefixSet
    (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)).preimage
      ReferenceGeneratedAffineHashHalf.measurable_retainedControlProjection

private theorem generatedLaunch_control_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 control : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1) rewards C_star C_h := by
  have hcount : s + (t.val - s) ≤ t.val := by omega
  obtain ⟨_, h0, _, hcontrol, _, _, _, _⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.1 x.2.1 control0 s (t.val - s) hs hcount x.2.2 control0 control
  exact h0.trans hcontrol.symm

private theorem generatedSeed_congr
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 control : TimeControl p)
    (r : RetainedRemainder p q t)
    (hr : r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (hstart0 : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control0)
    (hstart : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 r) rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control r) rewards C_star C_h) :
    ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
        rate rewards C_star C_h q t control0 r hr s hs hstart0 =
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
        rate rewards C_star C_h q t control r hr s hs hstart := by
  have hleft := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 r hr s hs hstart0).1
  have hright := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control r hr s hs hstart).1
  exact Option.some.inj (hleft.symm.trans (hlaunch.trans hright))

/-- The actual generated launch seed is invariant as well as the final
state and complete evidence in the prefix comparison. -/
theorem retainedSeed_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 control : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x =
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control ⟨x.1, x.2.1, hstart⟩ := by
  intro hstart
  exact generatedSeed_congr (rate := rate) rewards C_star C_h q t s hs control0 control x.1 x.2.1
    x.2.2 hstart
    (generatedLaunch_control_eq (rate := rate) rewards C_star C_h q t s hs control0 control x)

private theorem marker_initial_congr (ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial initial' incoming : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)))
    (hinitial : initial = initial') :
    actualUpBatchPrefixMarker ell candidate i start alpha initial incoming records ↔
      actualUpBatchPrefixMarker ell candidate i start alpha initial' incoming records := by
  cases hinitial
  rfl

/-- The corrected S_I itself, including the same alpha/ell range, is
invariant under every replacement of the removed whole current control. -/
theorem upBatchPrefixSet_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 control : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (alpha ell : ℕ) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    x ∈ upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i ↔
      (⟨x.1, x.2.1,
        (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2⟩ :
      LaunchStart (p := p) rate rewards C_star C_h q t s hs control) ∈
        upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control alpha ell candidate i := by
  have hmarker := actualUpBatchPrefixMarker_control_independent (rate := rate)
    rewards C_star C_h q t s hs control0 x control0 control alpha ell candidate i
  have hseed := retainedSeed_control_independent (rate := rate)
    rewards C_star C_h q t s hs control0 control x
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact hmarker.trans (marker_initial_congr ell candidate i s alpha _ _ _ _ hseed)

/-- The entire count/ordinary/diagnostic observation is unchanged by every
replacement of the removed whole current control, including the saved sample
and expected option in every prior retained diagnostic. -/
theorem retainedPrefixObservation_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 control : TimeControl p) (i : Fin (p.m - 1))
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0) :
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
    retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i x =
      retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control i
        ⟨x.1, x.2.1, hstart⟩ := by
  intro hstart
  rw [retainedPrefixObservation_reconstructs, retainedPrefixObservation_reconstructs]
  obtain ⟨_, _, _, _, _, _, hfinal, hevidence⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.1 x.2.1 control0 s (t.val - s) hs (by omega) x.2.2 control0 control
  exact Prod.ext
    (congrArg (stateBoundary i) (retainedSeed_control_independent
      (rate := rate) rewards C_star C_h q t s hs control0 control x))
    (Prod.ext (congrArg (stateBoundary i) hfinal)
      (congrArg (List.map (evidencePrefixObservation i)) hevidence))

/-- Original source branch: the actual selector is UP,i and launch starts s. -/
abbrev UpLaunchSource
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (i : Fin (p.m - 1)) :=
  {z : SourceInput p // z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
    (rate := rate) rewards C_star C_h q t (1, i) s}

/-- Restore the original whole source rows and original private J to the
actual generated seed; the launch subtype is constructed by R's original
source constructor (through A's branch specialization). -/
def originalSourceRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
  let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0 x,
    z.1.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards),
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1⟩

/-- The run input on the original source is the retained input with its
actual current control restored. This equality concerns inputs at that same
source, not whole records across different row tables. -/
theorem originalSourceRunInput_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z =
      let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
        (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
      let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
      retainedRunInput (rate := rate) rewards C_star C_h q t s hs control
        ((⟨x.1, x.2.1,
        (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2⟩ :
      LaunchStart (p := p) rate rewards C_star C_h q t s hs control)) := by
  let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1 = z.1 :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  apply Subtype.ext
  apply Prod.ext
  · exact retainedSeed_control_independent (rate := rate)
      rewards C_star C_h q t s hs control0 control x
  · change (z.1.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards) =
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1).1.2,
        ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1), rewards)
    rw [hsource]

/-- On the real source, the restored seed is exactly its corrected launch. -/
theorem originalSourceRunInput_launch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.1 rewards C_star C_h =
      some (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1 := by
  rw [originalSourceRunInput_eq]
  let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let y := (⟨x.1, x.2.1,
        (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2⟩ :
      LaunchStart (p := p) rate rewards C_star C_h q t s hs control)
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control y.1 = z.1 :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  have h := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control y.1 y.2.1 s hs y.2.2).1
  rw [hsource] at h
  exact h

/-- Canonical prefix observation on the run with ORIGINAL source rows/J.
This is a projection of that same run, not an independently supplied history. -/
def originalSourcePrefixObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    PrefixObservation (p := p) (rate := rate) :=
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let hspan : s + (t.val - s) ≤ p.T := by omega
  (stateBoundary i input.val.1,
    stateBoundary i (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) hspan input).finalState,
    (ReferenceActiveHorizonMeasurability.runObservation s (t.val - s) hspan input).2.map
      (roundRecordPrefixCode i))

/-- Source factorization of the complete observable, so the actual completed
count at arbitrary alpha and all pre-birth tests have the same source factor
as the marker; no row-bearing record equality is asserted. -/
theorem originalSourcePrefixObservation_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    originalSourcePrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i z =
      retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i
        (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
          (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z) := by
  unfold originalSourcePrefixObservation
  rw [originalSourceRunInput_eq]
  exact (retainedPrefixObservation_control_independent (rate := rate)
    rewards C_star C_h q t s hs control0
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1 i
    (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z)).symm

theorem measurable_originalSourcePrefixObservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    Measurable (originalSourcePrefixObservation (rate := rate)
      rewards C_star C_h q t s hs control0 i) := by
  have hmap : Measurable (fun z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i =>
      ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
        (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z) :=
    ((measurable_snd.comp (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).measurable).comp
      measurable_subtype_coe).subtype_mk
  have heq : originalSourcePrefixObservation (rate := rate)
      rewards C_star C_h q t s hs control0 i = fun z =>
      retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i
        (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
          (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z) :=
    funext (originalSourcePrefixObservation_eq (rate := rate) rewards C_star C_h q t s hs control0 i)
  rw [heq]
  exact (measurable_retainedPrefixObservation (rate := rate)
    rewards C_star C_h q t s hs control0 i).comp hmap

/-- The same literal arbitrary-birth marker evaluated on ORIGINAL source
rows, J, rewards, actual launch seed and the physical calendar [s,t). -/
def originalSourcePrefixMarker
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) : Prop :=
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let run := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input
  s ≤ alpha ∧ alpha ≤ t.val ∧ 1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧
    actualUpBatchPrefixMarker ell candidate i s alpha input.val.1 run.finalState
      (run.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)

/-- Original-source specialization and every-control invariance use precisely
S_I's alpha and ell, including dormant and earlier births. -/
theorem originalSourcePrefixMarker_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    originalSourcePrefixMarker (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i z ↔
      ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
        (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z ∈
      upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i := by
  unfold originalSourcePrefixMarker
  rw [originalSourceRunInput_eq]
  exact (upBatchPrefixSet_control_independent (rate := rate) rewards C_star C_h q t s hs control0
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
    (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z)
    alpha ell candidate i).symm

/-- Exact pair-cylinder identification on every reconstructed original source
in the genuine selector/launch branch. -/
theorem upBatchPrefixCylinder_originalSource_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (a : ReferenceGeneratedAffineHashHalf.Pair p)
    (r : ReferenceGeneratedAffineHashHalf.PairRemainder p q t (1, i))
    (hbranch : (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r) ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s) :
    r ∈ upBatchPrefixCylinder (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i ↔
      originalSourcePrefixMarker (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
        ⟨(ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r), hbranch⟩ := by
  let z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i :=
    ⟨(ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r), hbranch⟩
  let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  have hx : x.1 = ReferenceGeneratedAffineHashHalf.retainedControlProjection r :=
    ReferenceGeneratedAffineHashHalf.fixedControlSplit_pair_remainder a r
  rw [originalSourcePrefixMarker_iff]
  change ReferenceGeneratedAffineHashHalf.retainedControlProjection r ∈
      Subtype.val '' upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i ↔
    x ∈ upBatchPrefixSet (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
  rw [← hx]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := Subtype.ext heq
    rwa [← hxy]
  · intro h
    exact ⟨x, h, rfl⟩

/-- The original-source event, with the actual selector and launch branch
retained explicitly. The quantified proof only types the original run input. -/
def upBatchPrefixSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    Set (SourceInput p) :=
  {z | ∃ hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s,
    originalSourcePrefixMarker (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i ⟨z, hz⟩}

/-- Unconditional source factorization: selector/launch and THIS SAME marker
on the reconstructed source are exactly the selector remainder and C_I. -/
theorem upBatchPrefixSourceEvent_fixedPairSplit_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (a : ReferenceGeneratedAffineHashHalf.Pair p)
    (r : ReferenceGeneratedAffineHashHalf.PairRemainder p q t (1, i)) :
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r) ∈
        upBatchPrefixSourceEvent (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i ↔
      r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent p q t (1, i) ∧
      r ∈ upBatchPrefixCylinder (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i := by
  constructor
  · rintro ⟨hz, hmarker⟩
    have hbranch := (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 a r).mp hz
    exact ⟨hbranch.1, (upBatchPrefixCylinder_originalSource_iff (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i a r hz).mpr hmarker⟩
  · rintro ⟨hselector, hcylinder⟩
    have hcylinderSaved := hcylinder
    obtain ⟨x, _, hx⟩ := hcylinder
    have hretained : ReferenceGeneratedAffineHashHalf.retainedControlProjection r ∈
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 := by
      rw [← hx]
      exact x.2
    have hz := (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0 a r).mpr ⟨hselector, hretained⟩
    exact ⟨hz, (upBatchPrefixCylinder_originalSource_iff (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i a r hz).mp hcylinderSaved⟩

/-- The source event is a Borel cylinder on the actual original product
space, including its original selected-row law. -/
theorem measurableSet_upBatchPrefixSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    MeasurableSet (upBatchPrefixSourceEvent (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i) := by
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)
  let event := ReferenceSelectedAffinePairLaw.remainderSelectorEvent p q t (1, i) ∩
    upBatchPrefixCylinder (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
  have heq : upBatchPrefixSourceEvent (rate := rate) rewards C_star C_h q t s hs control0
      alpha ell candidate i = split ⁻¹' (Set.univ ×ˢ event) := by
    ext z
    have hz : split.symm ((split z).1, (split z).2) = z := split.symm_apply_apply z
    change z ∈ upBatchPrefixSourceEvent (rate := rate) rewards C_star C_h q t s hs control0
        alpha ell candidate i ↔ _ ∧ _
    simp only [Set.mem_univ, true_and]
    rw [← hz]
    simp only [split.apply_symm_apply]
    exact upBatchPrefixSourceEvent_fixedPairSplit_iff (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i (split z).1 (split z).2
  rw [heq]
  exact (MeasurableSet.univ.prod
    ((ReferenceSelectedAffinePairLaw.measurableSet_remainderSelectorEvent p q t (1, i)).inter
      (measurableSet_upBatchPrefixCylinder (rate := rate)
        rewards C_star C_h q t s hs control0 alpha ell candidate i))).preimage split.measurable

/-- Observable completed count, entire pre-birth test list and entire
since-birth test list; all are literal functions of the retained code. -/
def birthObservables (i : Fin (p.m - 1)) (start alpha : ℕ)
    (code : PrefixObservation (p := p) (rate := rate)) :=
  ((incomingBoundary? start alpha code.1 code.2.2).map Prod.snd,
    (code.2.2.take (alpha - start)).filterMap (prefixObservationTest i),
    (code.2.2.drop (alpha - start)).filterMap (prefixObservationTest i))

theorem birthObservables_reconstructs (i : Fin (p.m - 1)) (start alpha : ℕ)
    (initial incoming : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    birthObservables i start alpha
        (stateBoundary i initial, stateBoundary i incoming, records.map (evidencePrefixObservation i)) =
      (upBatchBirthCompletedCount? i start alpha initial records,
        upBatchBirthPastTests i start alpha records, upBatchTestsSince i start alpha records) := by
  unfold birthObservables upBatchBirthCompletedCount? upBatchBirthPastTests upBatchTestsSince
  rw [incomingBoundary_reconstructs]
  simp only [Option.map_map, ← List.map_take, ← List.map_drop, List.filterMap_map, Function.comp_def]
  have heq : (fun record : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
      prefixObservationTest i (evidencePrefixObservation i record)) = evidenceUpTest i :=
    funext (prefixObservationTest_reconstructs i)
  rw [heq]
  rfl

/-- Every event of these literal birth/count/past-test observables is Borel.
No measurable history, marker or boundary is supplied as a premise. -/
theorem measurableSet_retainedBirthObservables
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ) (i : Fin (p.m - 1))
    (event : Set (Option ℕ × (List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) ×
      List (AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))))) :
    MeasurableSet {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
      birthObservables i s alpha
        (retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i x) ∈ event} := by
  let : MeasurableSingletonClass (List (PrefixRecordObservation (p := p) (rate := rate))) :=
    measurableSingleton_list
  exact (Set.to_countable {code : PrefixObservation (p := p) (rate := rate) |
      birthObservables i s alpha code ∈ event}).measurableSet.preimage
    (measurable_retainedPrefixObservation (rate := rate) rewards C_star C_h q t s hs control0 i)

private theorem livePostChoice_up_none {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r owned base started).up = none := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem receiveUp_expected {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared := by
  unfold ReferenceActivePhysicalStep.receiveUp at hd
  dsimp only at hd
  split at hd
  · cases Option.some.inj hd
    rfl
  · cases hd

private theorem collectionPostChoice_expected {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up =
      some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hd
  split at hd
  · cases hd
  · dsimp only at hd
    split at hd
    · cases hd
    · cases hd
    · rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
      exact receiveUp_expected prepared _ diagnostic hd

/-- The diagnostic's saved expected offer is the actual prepared upSent,
derived from receiveUp on every retaining path, with no matching-offer input. -/
theorem actualRecordUpDiagnostic_expected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : record.output.coordinator.up = some diagnostic) :
    diagnostic.expected = ReferenceActiveAffinePositiveTest.upSent record.input := by
  rw [record.output_eq] at hd
  change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.up = some diagnostic at hd
  change diagnostic.expected = ReferenceActivePhysicalStep.upExpected
    (ReferenceActivePhysicalStep.prepare record.input)
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hd
  split at hd
  · split at hd <;> cases hd
  · split at hd
    all_goals first
    | exact collectionPostChoice_expected _ _ _ _ _ diagnostic hd
    | cases hd
    | (have hn : (none : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate)) = some diagnostic :=
         (livePostChoice_up_none _ _ _ _ _).symm.trans hd
       cases hn)

/-- Generated-record membership supplies the original whole rows, private J,
reward table and calendar time simultaneously. The saved option is the actual
upSent, including bottom; neither row nor matching-offer identities are inputs. -/
theorem originalSourceRun_recordUpTest_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega)
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).records)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hselected : diagnostic.input.selectedFollower = i)
    (heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) :
    record.input.rows = z.1.1.2 ∧ record.input.selected = q ∧ record.input.rewards = rewards ∧
      s ≤ record.input.time.val ∧ record.input.time.val < t.val ∧
      diagnostic.expected = ReferenceActiveAffinePositiveTest.upSent record.input ∧
      ∃ test, upTestOfDiagnostic i (some diagnostic) = some test ∧
        test.time = record.input.time.val ∧
        test.sample = ((z.1.1.2 q).2 record.input.time).2 (1, i) ∧
        test.sent = ReferenceActiveAffinePositiveTest.upSent record.input := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hspan : s + (t.val - s) ≤ p.T := by omega
  have hfields := ReferenceActivePhysicalHorizon.run_record_inputs input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s (t.val - s) hspan input.2 record hrecord
  have hindex := ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
    (rate := rate) rewards C_star C_h q t (1, i) s z
  change record.input.rows = z.1.1.2 ∧
    record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z.1 ∧
    record.input.rewards = rewards at hfields
  rw [hindex] at hfields
  have htimes := ReferenceActivePhysicalHorizon.run_time_values input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s (t.val - s) hspan input.2
  have htime : record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar s (t.val - s) := by
    rw [← htimes]
    exact List.mem_map.mpr ⟨record, hrecord, rfl⟩
  obtain ⟨offset, hoffset, htimeEq⟩ := List.mem_range'.mp htime
  have hbounds : s ≤ record.input.time.val ∧ record.input.time.val < t.val := by omega
  have hexpected := actualRecordUpDiagnostic_expected record diagnostic hdiagnostic
  obtain ⟨test, htest, htestTime, hsample, hsent⟩ := actualRecordUpTest_sourceFields
    i record diagnostic z.1.1.2 q hfields.1 hfields.2.1 hdiagnostic hselected heligible
  exact ⟨hfields.1, hfields.2.1, hfields.2.2, hbounds.1, hbounds.2, hexpected,
    test, htest, htestTime, hsample, hsent.trans hexpected⟩

end Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent

end
