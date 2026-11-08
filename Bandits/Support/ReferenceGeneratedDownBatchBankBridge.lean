/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceExecutedDownBankRecurrence
public import Bandits.Support.ReferenceGeneratedDownBatchCalendar

import Lean.Elab.Tactic.Omega

/-!
# Physical projection for generated DOWN batches

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module connects the calendar's literal executed-test projection to the
physical follower records and the existing executed-bank recurrence. Every
ordinary-output selector and source condition remains an explicit premise.
These results do not prove global survival, a tail estimate, queue truth, or
manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceExecutedDownBankRecurrence
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability

namespace Bandits.Support.ReferenceGeneratedDownBatchBankBridge

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
variable {p : Parameters} {rate : RateInput p}

private theorem carriedStateCode_reconstruct (carry :
    FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
    FollowerDownMeasurability.followerStateCode rate
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2) =
        carry.1.1 := by
  have hstatus (status : Fin 3) : FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode status) = status := by
    fin_cases status <;> rfl
  rcases carry with ⟨⟨code, skeleton⟩, values⟩
  cases code
  simp only [FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
    FollowerDownMeasurability.followerStateOfCode,
    FollowerDownMeasurability.followerStateCode, hstatus,
    FollowerDownMeasurability.decoderBatchOfCode,
    FollowerDownMeasurability.decoderBatchCode, List.map_map, Function.comp_def,
    FollowerDownMeasurability.decoderEntryCode,
    FollowerDownMeasurability.decoderEntryOfCode, Prod.eta, List.map_id']

private theorem diagnosticProjection_reconstruct_fields
    (output : ReferenceFollowerTailComposition.FollowerObservable p rate) :
    ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection output =
      ((ReferenceFollowerTailComposition.reconstructFollowerObservable output).downInput.map
        (FollowerDownMeasurability.followerStateCode rate),
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).failure,
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).down.map
        ReferenceDownCompletedAmbiguityMeasurability.cutFields) := by
  rcases output with ⟨incoming, failure, input, cut⟩
  cases input with
  | inl absent => rfl
  | inr carry =>
      cases cut with
      | none =>
          simp only [ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown,
            Option.map_some, Option.map_none,
            ReferenceFollowerTailComposition.reconstructCarry]
          exact congrArg (fun code => (some code, failure, none))
            (carriedStateCode_reconstruct carry).symm
      | some code =>
          simp only [ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection,
            ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown,
            Option.map_some, ReferenceFollowerTailComposition.reconstructCarry]
          rw [carriedStateCode_reconstruct]
          congr 2
          simp only [ReferenceDownCompletedAmbiguityMeasurability.cutFields,
            ReferenceDownCompletedAmbiguityMeasurability.cutCodeFields,
            ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
            decide_eq_true_eq]
          cases code.ordinaryAcceptance <;> rfl

/-- The literal diagnostic projection on one record reconstructs the
record's actual logged input and actual receiver cut. This includes a cut
retained before a later finish failure. -/
theorem roundDownObservation_diagnostics_eq_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.2 =
      ((record.output.followers i).downInput.map
        (FollowerDownMeasurability.followerStateCode rate),
       (record.output.followers i).failure,
       (record.output.followers i).down.map
        ReferenceDownCompletedAmbiguityMeasurability.cutFields) := by
  rw [show (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
      record.input i).2.2.2 =
      ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
        ((ReferenceActiveStepCompositionMeasurability.wholeStepCode record.input).2.1 i)
      from rfl,
    diagnosticProjection_reconstruct_fields]
  obtain ⟨_, _, hrecord, _, _⟩ :=
    ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record
  have hrecord := hrecord i
  change ReferenceFollowerTailComposition.reconstructFollowerObservable
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode record.input).2.1 i) =
        record.output.followers i at hrecord
  rw [hrecord]

private theorem preparedOwnObservation_eq_grid
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
  have hgrid :
      ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
        record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    exact congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
      record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  rw [hgrid]
  exact record.output.preparation.feedback.observations_eq _

/-- Literal D completion diagnostics identify the actual record's call,
logged state, cut and quota-sized pending bank. The raw comparison may be
either Boolean value; only its presence and positive own feedback matter. -/
theorem completedBatchAtRound_actual_fields
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)) :
    ∃ callCode logged cut,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
        some callCode ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
  classical
  dsimp only [ReferenceGeneratedDownBatchCalendar.completedBatchAtRound] at hcomplete
  rcases hcomplete with ⟨callCode, loggedCode, cutCode, hcall, hloggedCode,
    hcutCode, _htime, hcomparison, hpositiveGrid, hquota, _hdecodedBank⟩
  have hdiagnostics := roundDownObservation_diagnostics_eq_actual record i
  have hcall' :
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
        some callCode := by
    change ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
      record.input i = some callCode
    exact hcall
  rw [hdiagnostics] at hloggedCode hcutCode
  obtain ⟨logged, hlogged, hloggedCodeEq⟩ : ∃ logged,
      (record.output.followers i).downInput = some logged ∧
      FollowerDownMeasurability.followerStateCode rate logged = loggedCode := by
    cases hdown : (record.output.followers i).downInput with
    | none => simp [hdown] at hloggedCode
    | some logged =>
        have hcode :
            some (FollowerDownMeasurability.followerStateCode rate logged) =
              some loggedCode := by simpa [hdown] using hloggedCode
        exact ⟨logged, rfl, Option.some.inj hcode⟩
  obtain ⟨cut, hcut, hcutCodeEq⟩ : ∃ cut,
      (record.output.followers i).down = some cut ∧
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode := by
    cases hdown : (record.output.followers i).down with
    | none => simp [hdown] at hcutCode
    | some cut =>
        have hcode : some (ReferenceDownCompletedAmbiguityMeasurability.cutFields cut) =
            some cutCode := by simpa [hdown] using hcutCode
        exact ⟨cut, rfl, Option.some.inj hcode⟩
  have hcomparison' : cut.rawComparison.isSome = true := by
    have hfields := congrArg
      (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
        fields.2.2.1.isSome) hcutCodeEq
    exact hfields.trans hcomparison
  have hpositive :
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [preparedOwnObservation_eq_grid]
    simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using
      hpositiveGrid
  have hquota' : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
    have hbatch :
        FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch = logged.downBatch := by
      rw [← hloggedCodeEq]
      exact FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
    rw [← hbatch]
    exact hquota
  exact ⟨callCode, logged, cut, hcall', hlogged, hcut,
    hcomparison', hpositive, hquota'⟩

/-- A genuine D retained boundary has an empty actual pending bank on its
computed ordinary successor. The reset is produced by B from the logged
quota-completion evidence on the same generated run. -/
theorem retainedBatchBoundary_pending_empty
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (qJ : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h qJ r s hsr control0)
    (hboundary : ReferenceGeneratedDownBatchCalendar.retainedBatchBoundary
      rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x) :
    ∃ state memory,
      (ReferenceActivePhysicalHorizon.run
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
          rate rewards C_star C_h qJ r s hsr control0 x)
        (ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1))
        rewards s (alpha - s) (by omega)
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
          rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2).2.1).finalState.followers i =
            .ordinary state memory ∧
      state.downBatch.pending = [] := by
  classical
  let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  let hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s :=
    ⟨(seed, (rows, (selected, rewards))), hspec.2.1⟩
  let inputQ : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s :=
    ⟨(seed, (rows, (qJ, rewards))), hspec.2.1⟩
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = qJ := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p qJ r control0 x.1 x.2.1
  let priorCount := alpha - s - 1
  let prefixInput := ReferenceDownCompletedAmbiguityMeasurability.prefixInput
    (p := p) (rate := rate) s priorCount (by omega) input
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨prefixInput, ReferenceActivePhysicalStep.step prefixInput, rfl⟩
  let physicalRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (alpha - s) (by omega) hspec.2.1
  dsimp only [ReferenceGeneratedDownBatchCalendar.retainedBatchBoundary] at hboundary
  rcases hboundary with ⟨hcomplete, state, memory, hordinary⟩
  have hcompleteQ :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
            (p := p) (rate := rate) s (alpha - 1 - s) (by omega) inputQ) i) := by
    exact hcomplete
  have hcount : priorCount = alpha - 1 - s := by omega
  have hselectedVar : selected = qJ := by simpa only [selected] using hselected
  have hinputEq : input = inputQ := by
    apply Subtype.ext
    simp only [input, inputQ]
    simp [hselectedVar]
  have hprefixSame := congrArg
    (fun runInput : ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) s =>
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        (p := p) (rate := rate) s priorCount (by omega) runInput) hinputEq
  have hprefix :
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput
          (p := p) (rate := rate) s priorCount (by omega) input =
        ReferenceDownCompletedAmbiguityMeasurability.prefixInput
          (p := p) (rate := rate) s (alpha - 1 - s) (by omega) inputQ := by
    simpa only [hcount] using hprefixSame
  have hcomplete' :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i) := by
    change ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
          (p := p) (rate := rate) s priorCount (by omega) input) i)
    rw [hprefix]
    exact hcompleteQ
  obtain ⟨callCode, logged, cut, hcall, hlogged, hcut, hcomparison, hpositive, hquota⟩ :=
    completedBatchAtRound_actual_fields record i hcomplete'
  have hordinaryRun : physicalRun.finalState.followers i = .ordinary state memory := by
    simpa [ReferenceGeneratedDownBatchCalendar.retainedBatchIncoming,
      ReferenceActiveHorizonMeasurability.runOfInput,
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed,
      physicalRun, input, rows, selected, source, seed, hselected] using hordinary
  have hreset := ReferenceExecutedDownBankRecurrence.retainedGenerated_completion_pending_empty
    (p := p) (rate := rate) rewards C_star C_h qJ r s hsr control0 i alpha halpha
    halphaR x ⟨state, memory, hordinaryRun⟩
    ⟨callCode, logged, cut, hcall, hlogged, hcut, hcomparison, hpositive, hquota⟩
  rcases hreset with ⟨resetState, resetMemory, hresetOrdinary, hreset⟩
  have hsame : resetState = state ∧ resetMemory = memory := by
    have heq := hresetOrdinary.symm.trans hordinaryRun
    injection heq with hstate hmemory
    exact ⟨hstate, hmemory⟩
  refine ⟨state, memory, hordinaryRun, ?_⟩
  ·
    rw [← hsame.1]
    exact hreset

/-- The concrete calendar test from one executed physical record retains its
original time, original focal sample, and actual optional DOWN word. The
logged/cut/raw-comparison witnesses are required; raw `some false` is accepted
as execution evidence, and absence is not turned into a test. -/
theorem executedTestOfRound_eq_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (callCode : ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
          cut.expectedWord⟩ ∧
      cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record =
        some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
      AffineBatchDecoder.eligible
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 := by
  classical
  have hfields := record_executed_down_call_fields record i callCode logged cut
    hcall hlogged hcut hcomparison hpositive
  have hdiagnostics := roundDownObservation_diagnostics_eq_actual record i
  have hcutCode :
      ((ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.2).2.2 =
        some (ReferenceDownCompletedAmbiguityMeasurability.cutFields cut) := by
    rw [hdiagnostics, hcut]
    rfl
  have hgrid :
      0 < (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.1).val.val := by
    have hown :
        ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
          record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      exact congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
        record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    have hobs :
        ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
          ActualInitializationPhysicalStep.observationOfGrid p
            (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
      rw [hown]
      exact record.output.preparation.feedback.observations_eq _
    change 0 < (ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val
    rw [← hobs]
    exact hpositive
  have hcallCode :
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.1 = some callCode := by
    change ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
      record.input i = some callCode
    exact hcall
  rcases hfields with
    ⟨hactual, htime, hsample, _horiginal, _hselected, _henabled, _hreward,
      heligible, hexpected, _hdownPositive⟩
  have htimeCode : callCode.1 = record.input.time := by
    simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using htime
  have hsampleCode : callCode.2.2.2.1 =
      (record.input.row.2 record.input.time).2 (0, i) := by
    simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hsample
  refine ⟨?_, hexpected, hactual, heligible⟩
  simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
    hcallCode, hcutCode, hgrid, hcomparison,
    ReferenceDownCompletedAmbiguityMeasurability.cutFields,
    htimeCode, hsampleCode]


end Bandits.Support.ReferenceGeneratedDownBatchBankBridge

end
