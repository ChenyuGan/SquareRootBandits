/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
public import Bandits.Support.ReferenceGeneratedInheritedDownFirstCompletion

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop

/-!
# Physical provenance of the first inherited DOWN cohort

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-153`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module joins the literal prelaunch census to the actual postlaunch
executed-test prefix at the first completion. It retains the original source,
physical records, reset boundary, and failure diagnostics. It proves no
probability or regret estimate.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedInheritedDownCohort

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual prelaunch tests remaining in the inherited pending cohort. -/
def generatedInheritedDownOldFirstTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  (ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
    rate rewards C_star C_h z.val i).drop
      (AffineBatchDecoder.quota p *
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.completed.length)

/-- The actual first residual-quota prefix of the generated postlaunch tests. -/
def generatedInheritedDownNewFirstTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
    rate rewards C_star C_h s hs i z

/-- The chronological old/new actual cohort; entries use the existing test carrier. -/
def generatedInheritedDownFirstCohortTests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i ++
    generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z

/-- The two admitted entry maps are the same existing decoder-entry projection. -/
theorem testEntry_eq_inheritedTestEntry
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    ReferenceGeneratedPrelaunchDownCohort.testEntry test =
      ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry test := rfl

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

private theorem roundDownObservation_diagnostics_eq_actual
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
      from rfl, diagnosticProjection_reconstruct_fields]
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
  have hgrid : ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
      record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    exact congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
      record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  rw [hgrid]
  exact record.output.preparation.feedback.observations_eq _

private theorem actual_finishFollower_diagnostic_pair
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    ((ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput,
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down) =
    match prepared.configuration with
    | .dagger => (none, none)
    | .ordinary state _ =>
        let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm
          observation state
        (recorded.downInput, recorded.down) := by
  cases hconfig : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hconfig]
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfig]
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm
          observation state).result with
      | error failure => rfl
      | ok post =>
          dsimp only
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem actual_record_down_some_logged
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut) :
    ∃ logged, (record.output.followers i).downInput = some logged := by
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i]
    at hcut ⊢
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hp := actual_finishFollower_diagnostic_pair
    record.output.preparation.coordinator.downView prepared observation
  change ((record.output.preparation.observeFollower i).downInput,
      (record.output.preparation.observeFollower i).down) = _ at hp
  cases hconfig : prepared.configuration with
  | dagger =>
      rw [hconfig] at hp
      have hnone := congrArg Prod.snd hp
      rw [hcut] at hnone
      cases hnone
  | ordinary state memory =>
      rw [hconfig] at hp
      have hdown := (congrArg Prod.snd hp).symm.trans hcut
      have hlogged := congrArg Prod.fst hp
      dsimp only at hlogged
      by_cases hstatus : state.status = .unoccupied
      · simp only [ReferenceActivePhysicalStep.recordFollower,
          dite_eq_left hstatus] at hdown
        cases hlog : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, observation) state with
        | error failure => simp only [hlog, reduceCtorEq] at hdown
        | ok logged =>
            refine ⟨logged, ?_⟩
            rw [hlogged]
            simp only [ReferenceActivePhysicalStep.recordFollower,
              dite_eq_left hstatus, hlog]
      · simp only [ReferenceActivePhysicalStep.recordFollower,
          dite_eq_right hstatus, reduceCtorEq] at hdown

private theorem actual_executedTestOfRound_record
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test) :
    ∃ call cut,
      ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
      (record.output.followers i).down = some cut ∧
      call.1 = record.input.time ∧
      call.2.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
      test.time = record.input.time ∧
      test.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
      test.sent = cut.expectedWord ∧
      cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      cut.rawComparison.isSome = true := by
  classical
  have htestOriginal := htest
  have hdiag := roundDownObservation_diagnostics_eq_actual record i
  unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound at htest
  dsimp only at htest
  rw [hdiag] at htest
  change (match ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record,
      (record.output.followers i).down.map
        ReferenceDownCompletedAmbiguityMeasurability.cutFields with
    | some call, some cut =>
        if 0 < (ActualInitializationPhysicalStep.observationOfGrid p
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                record.input i).2.1).val.val ∧ cut.2.2.1.isSome then
          some ⟨call.1, call.2.2.2.1, cut.2.1⟩
        else none
    | _, _ => none) = some test at htest
  cases hcallCode : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
  | none => simp only [hcallCode] at htest; cases htest
  | some callCode =>
      cases hcut : (record.output.followers i).down with
      | none => simp only [hcallCode, hcut, Option.map_none] at htest; cases htest
      | some cut =>
          simp only [hcallCode, hcut, Option.map_some] at htest
          split at htest
          next hpositive =>
            obtain ⟨logged, hlogged⟩ := actual_record_down_some_logged record i cut hcut
            have hcallActual :
                ReferenceFollowerDownDecoderReplay.actualDownCall i record =
                  some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
              rw [← ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs
                i record, hcallCode]
              rfl
            have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
              record i _ hcallActual
            have hcutCode :
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                  record.input i).2.2.2.2.2 =
                    some (ReferenceDownCompletedAmbiguityMeasurability.cutFields cut) := by
              rw [roundDownObservation_diagnostics_eq_actual record i, hcut]
              rfl
            have hcomparison : cut.rawComparison.isSome = true := by
              simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hpositive.2
            have hpositiveActual :
                0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
              have hobs := preparedOwnObservation_eq_grid record i
              rw [hobs]
              exact hpositive.1
            have hcutActual :=
              ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
                record i logged cut hlogged hcut
            have hcomparisonActual :
                (ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView i record.input.row
                  record.input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
                  rate logged).rawComparison.isSome = true := by
              rw [← hcutActual]
              exact hcomparison
            have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i
                record.input.row record.input.time logged := by
              rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call] at hcomparisonActual
              exact of_decide_eq_true hcomparisonActual
            have hview : record.output.preparation.coordinator.downView =
                (ReferenceActivePhysicalStep.dispatch record.input).downView := by
              have hprepared : record.output.preparation =
                  ReferenceActivePhysicalStep.prepare record.input := by
                rw [record.output_eq]
                rfl
              rw [hprepared]
              rfl
            have hexpected : cut.expectedWord =
                ReferenceActiveAffinePositiveTest.downSent record.input := by
              calc
                cut.expectedWord =
                    (ReferenceDownReception.referenceDownCut p
                      record.output.preparation.coordinator.downView i record.input.row
                      record.input.time
                      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
                      rate logged).expectedWord :=
                  congrArg ReferenceDownReception.ReferenceDownCutOutput.expectedWord hcutActual
                _ = ReferenceDownReception.expectedDownFlatWord
                    record.output.preparation.coordinator.downView i record.input.row
                    record.input.time := by
                  unfold ReferenceDownReception.referenceDownCut
                  split
                  · split
                    · split
                      · split
                        · split
                          · dsimp only
                            split <;> rfl
                          · rfl
                        · rfl
                      · rfl
                    · rfl
                  · rfl
                _ = ReferenceActiveAffinePositiveTest.downSent record.input := by
                  have hsender : i = ReferenceActivePhysicalStep.upSenderIndex record.input := by
                    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
                    exact hgate.1.2.symm
                  simp [ReferenceActiveAffinePositiveTest.downSent, hview, hsender]
            have hsampleCode : callCode.2.2.2.1 =
                (record.input.row.2 record.input.time).2 (0, i) := by
              simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.2.1
            have htimeCode : callCode.1 = record.input.time := by
              simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.1
            have htestEq : test =
                ⟨record.input.time,
                  (record.input.row.2 record.input.time).2 (0, i), cut.expectedWord⟩ := by
              have he := (Option.some.inj htest).symm
              simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields,
                htimeCode, hsampleCode] using he
            refine ⟨ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode, cut,
              hcallActual, rfl, ?_, ?_, ?_, ?_, ?_, hexpected, hpositiveActual, hcomparison⟩
            · exact hfields.1
            · exact hfields.2.1
            · rw [htestEq]
            · rw [htestEq]
            · rw [htestEq]
          next hnegative =>
            simp only [reduceCtorEq] at htest

private theorem generatedSourceObservation_round_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (k : Fin (p.T - s)) :
    ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i z).2 k).1.val = s + k.val := by
  simp [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
    ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
    ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
    ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
    ReferenceActivePhysicalHorizon.roundInputAt]

private theorem generatedSourceObservation_test_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (k : Fin (p.T - s))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 k) = some test) :
    test.time.val = s + k.val := by
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input), rfl⟩
  have htestRecord :
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
          some test := by
    simpa [record, input, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput] using htest
  obtain ⟨_, _, _, _, _, _, htime, _, _, _, _, _⟩ :=
    actual_executedTestOfRound_record record i test htestRecord
  have hround := generatedSourceObservation_round_time rewards C_star C_h s hs i z k
  have hrecordTime : record.input.time.val = s + k.val := by
    simpa [record, input, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using hround
  rw [htime]
  exact hrecordTime

private theorem generatedInheritedDownTests_member_offset
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z (p.T - s)) :
    ∃ k : Fin (p.T - s),
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 k) = some test ∧
      test.time.val = s + k.val := by
  classical
  have htake :
      (List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2).take (p.T - s) =
        List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 := by
    exact List.take_of_length_le (by simp)
  unfold ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests at hmem
  rw [htake] at hmem
  rcases List.mem_filterMap.mp hmem with ⟨round, hround, htest⟩
  rcases List.mem_ofFn.mp hround with ⟨k, hk⟩
  subst round
  exact ⟨k, htest,
    generatedSourceObservation_test_time rewards C_star C_h s hs i z k test htest⟩

private theorem generatedInheritedDownNew_member_full
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z) :
    test ∈ ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z (p.T - s) := by
  exact List.mem_of_mem_take hmem

/-- The literal prelaunch drop is the pending bank of the same launch source. -/
theorem generated_inherited_down_old_pending
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i).downBatch
    let Old := generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i
    Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending ∧
      Old.length = B0.pending.length := by
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let sourceTests := ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
    rate rewards C_star C_h z.val i
  let W := sourceTests.map ReferenceGeneratedPrelaunchDownCohort.testEntry
  let Q := AffineBatchDecoder.quota p
  have hcohorts := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
    rate rewards C_star C_h z.val i
  have hcohorts' :
      W = AffineBatchDecoder.collected B0 ∧
      B0.pending = W.drop (Q * B0.completed.length) ∧
      (∀ k (hk : k < B0.completed.length),
        B0.completed[k] = (W.drop (k * Q)).take Q ∧
          B0.completed[k].length = Q) ∧
      B0.pending.length < Q := by
    simpa [B0, W, sourceTests, Q,
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower] using hcohorts
  have holdMap :
      (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending := by
    rw [generatedInheritedDownOldFirstTests, List.map_drop]
    exact hcohorts'.2.1.symm
  change
    (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending ∧
      (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i).length =
        B0.pending.length
  exact ⟨holdMap, by rw [← holdMap, List.length_map]⟩

/-- The old pending bank, quota residual, and new prefix have exact actual lengths. -/
theorem generated_inherited_down_cohort_sizes
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i).downBatch
    let Q := AffineBatchDecoder.quota p
    let h := Q - B0.pending.length
    let Old := generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i
    let New := generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z
    let Cohort := generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z
    Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending ∧
      Old.length = B0.pending.length ∧
      New.length = min h
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z (p.T - s)).length ∧
      Cohort.length ≤ Q := by
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let Q := AffineBatchDecoder.quota p
  let h := Q - B0.pending.length
  let Old := generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i
  let New := generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z
  let Cohort := generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z
  have hold := generated_inherited_down_old_pending rewards C_star C_h s hs z i
  have hresidual := ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
    rate rewards C_star C_h s hs z i
  have hnew : New.length = min h
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z (p.T - s)).length := by
    simp [New, generatedInheritedDownNewFirstTests,
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests,
      h, Q, B0, List.length_take]
  have hq : B0.pending.length + h = Q := by
    have hbound : B0.pending.length < Q := by simpa [B0, Q] using hresidual.1
    dsimp [h, Q]
    omega
  have hlen : Old.length = B0.pending.length := by
    simpa [Old, B0] using hold.2
  change
    Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending ∧
      Old.length = B0.pending.length ∧
      New.length = min h
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z (p.T - s)).length ∧
      Cohort.length ≤ Q
  refine ⟨?_, hlen, hnew, ?_⟩
  · simpa [Old, B0] using hold.1
  · dsimp [Cohort, generatedInheritedDownFirstCohortTests]
    simp only [List.length_append]
    rw [hlen, hnew]
    calc
      B0.pending.length + min h
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i z (p.T - s)).length
        ≤ B0.pending.length + h := Nat.add_le_add_left (Nat.min_le_left _ _) _
      _ = Q := hq

/-- Cohort quota completion is equivalent to F's inline actual first-completion event. -/
theorem generated_inherited_down_cohort_complete_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i).downBatch
    let Q := AffineBatchDecoder.quota p
    let h := Q - B0.pending.length
    let Cohort := generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z
    Cohort.length = Q ↔
      ∃ k, ∃ hk : k < p.T - s,
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
        ∀ l (hl : l < k),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩) := by
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let Q := AffineBatchDecoder.quota p
  let h := Q - B0.pending.length
  let Cohort := generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z
  let tests := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i z (p.T - s)
  have hsizes := generated_inherited_down_cohort_sizes rewards C_star C_h s hs z i
  have hresidual := ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
    rate rewards C_star C_h s hs z i
  have hquota : B0.pending.length + h = Q := by
    have hbound : B0.pending.length < Q := by simpa [B0, Q] using hresidual.1
    dsimp [h, Q]
    omega
  have hlen_iff : Cohort.length = Q ↔ h ≤ tests.length := by
    have hlen : Cohort.length = B0.pending.length + min h tests.length := by
      change (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i ++
        generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z).length = _
      rw [List.length_append]
      have hold := generated_inherited_down_old_pending rewards C_star C_h s hs z i
      rw [hold.2]
      simp [generatedInheritedDownNewFirstTests, tests,
        ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests,
        h, Q, B0, List.length_take]
    rw [hlen, ← hquota]
    constructor
    · intro heq
      by_contra hnot
      have hlt : tests.length < h := Nat.lt_of_not_ge hnot
      rw [Nat.min_eq_right (Nat.le_of_lt hlt)] at heq
      omega
    · intro hle
      rw [Nat.min_eq_left hle]
  have hexists := ReferenceGeneratedInheritedDownFirstCompletion.generated_inherited_down_first_completion_exists_iff
    rewards C_star C_h s hs z i
  change Cohort.length = Q ↔ _
  rw [hlen_iff]
  simpa [B0, h, Q, tests] using hexists.symm

/-- The actual generated launch supplies its source, activation, correction flags,
and the empty-bank creation or real last-completion reset boundary. -/
theorem generated_inherited_down_cohort_launch_provenance
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed < p.T)
    (hCrossing : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let s0 := ReferenceInitializationRun.elapsed p b.completed
    ∃ launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h
        s0 hElapsed,
      launchSource.val = source ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
          rate rewards C_star C_h s0 hElapsed launchSource) ∧
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s0 hElapsed launchSource).followers i =
        .ordinary (ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) ∧
      ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
          rate rewards C_star C_h s0 hElapsed launchSource) s0 ∧
      ReferenceInitializationRun.initializationFailure x b
          (ActualReferenceInitializationBlock.refFollower i) =
        (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) ||
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)).initializationFailure) ∧
      ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        ((b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.initial p rate.eta ∧ a.val = s0 + 1) ∨
         (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.replay rate.eta i x.row a
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                  (ActualReferenceInitializationBlock.refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed))) := by
  exact ReferenceGeneratedPrelaunchDownCohort.source_launch_down_cohort_provenance
    rate rewards C_star C_h source i hElapsed hCrossing

theorem generated_inherited_down_cohort_birth
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    ∃ alpha, alpha ≤ s ∧
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h z.val i
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
              rate rewards C_star C_h s hs z i).downBatch.completed.length = some alpha := by
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let x := ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  have hlaunch := ReferenceGeneratedPrelaunchDownCohort.source_launch_down_cohort_provenance
    rate rewards C_star C_h z.val i (by rw [z.property.2]; exact hs) z.property.1
  have hinitial := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_boundary
    rate rewards C_star C_h z.val i
  have hcompletedEq :
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length =
        B0.completed.length := rfl
  obtain ⟨launchSource, hsource, hcorrected, hfollowers, hseed, hfailure,
      activation, hactivation, hactivationMode⟩ := hlaunch
  by_cases hzero : B0.completed.length = 0
  · refine ⟨activation.val - 1, ?_, ?_⟩
    · have hb := hinitial.2 activation hactivation
      simpa [z.property.2] using hb.1
    · rw [hzero]
      rw [hinitial.1, hactivation]
      rfl
  · have hpositive : 0 < B0.completed.length := Nat.pos_of_ne_zero hzero
    have hresetIndex :
        B0.completed.length - 1 <
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length := by
      rw [hcompletedEq]
      omega
    obtain ⟨t, ht, hlast, hboundary⟩ :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_reset_boundary
        rate rewards C_star C_h z.val i (B0.completed.length - 1) hresetIndex
    refine ⟨t.val + 1, ?_, ?_⟩
    · rw [z.property.2] at ht
      omega
    · have hidx : B0.completed.length - 1 + 1 = B0.completed.length := by omega
      rw [hidx] at hboundary
      exact hboundary

private theorem old_test_time_after_birth
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (alpha : ℕ)
    (hbirth : ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
      rate rewards C_star C_h z.val i
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.completed.length = some alpha)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i) :
    alpha ≤ test.time.val := by
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let sourceTests := ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
    rate rewards C_star C_h z.val i
  let W := sourceTests.map ReferenceGeneratedPrelaunchDownCohort.testEntry
  let Q := AffineBatchDecoder.quota p
  have hcohorts := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
    rate rewards C_star C_h z.val i
  have hcohorts' :
      W = AffineBatchDecoder.collected B0 ∧
      B0.pending = W.drop (Q * B0.completed.length) ∧
      (∀ k (hk : k < B0.completed.length),
        B0.completed[k] = (W.drop (k * Q)).take Q ∧
          B0.completed[k].length = Q) ∧
      B0.pending.length < Q := by
    simpa [B0, W, sourceTests, Q,
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower] using hcohorts
  have hOldMap :
      (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry = W.drop
            (Q * B0.completed.length) := by
    rw [generatedInheritedDownOldFirstTests, List.map_drop]
  have hpair := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_tests_pairwise
    rate rewards C_star C_h z.val i
  have hWPair : W.Pairwise (fun a b => a.time.val < b.time.val) := by
    dsimp [W, sourceTests]
    exact List.Pairwise.map ReferenceGeneratedPrelaunchDownCohort.testEntry
      (fun a b hab => hab) hpair
  by_cases hzero : B0.completed.length = 0
  · obtain ⟨launchSource, hsource, hcorrected, hfollowers, hseed, hfailure,
        activation, hactivation, hactivationMode⟩ :=
      ReferenceGeneratedPrelaunchDownCohort.source_launch_down_cohort_provenance
        rate rewards C_star C_h z.val i (by rw [z.property.2]; exact hs) z.property.1
    have hinitial := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_boundary
      rate rewards C_star C_h z.val i
    have hboundary0 :
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h z.val i 0 = some (activation.val - 1) := by
      rw [hinitial.1, hactivation]
      rfl
    have hzeroActual :
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.completed.length = 0 := by
      simpa [B0] using hzero
    rw [hzeroActual] at hbirth
    have halpha : alpha = activation.val - 1 := by
      exact Option.some.inj (hbirth.symm.trans hboundary0)
    have hsourceMem : test ∈ sourceTests := List.mem_of_mem_drop hmem
    obtain ⟨actualActivation, hactualActivation, hactive, _, _, _, _⟩ :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
        rate rewards C_star C_h z.val i test hsourceMem
    have hactivationEq : actualActivation = activation :=
      Option.some.inj (hactualActivation.symm.trans hactivation)
    rw [halpha, ← hactivationEq]
    omega
  · have hpositive : 0 < B0.completed.length := Nat.pos_of_ne_zero hzero
    let k := B0.completed.length
    let m := (k - 1) * Q
    let n := Q * k
    obtain ⟨t, ht, hlast, hboundary⟩ :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_reset_boundary
        rate rewards C_star C_h z.val i (k - 1) (by
          have hcompletedEq :
              (ReferenceInitializationRun.ordinary
                (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)
                (ReferenceInitializationRun.output
                  (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate))
                (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length =
              B0.completed.length := rfl
          rw [hcompletedEq]
          dsimp [k]
          omega)
    have hbatch := hcohorts'.2.2.1 (k - 1) (by omega)
    have hsegmentLast :
        ((W.drop m).take Q).getLast? =
          some ⟨t, ((ActualReferenceInitializationBlock.referenceInput z.val rewards
            C_star C_h rate).row.2 t).2 (0, i)⟩ := by
      have hlastBank : (B0.completed[k - 1]).getLast? =
          some ⟨t, ((ActualReferenceInitializationBlock.referenceInput z.val rewards
            C_star C_h rate).row.2 t).2 (0, i)⟩ := by
        simpa [B0, ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower] using hlast
      rw [hbatch.1] at hlastBank
      simpa [k, B0, W, m, Q,
        ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower] using hlastBank
    have hmn : m + Q = n := by
      have hk : k - 1 + 1 = k := by dsimp [k]; omega
      dsimp [m, n]
      calc
        (k - 1) * Q + Q = (k - 1) * Q + 1 * Q := by simp
        _ = (k - 1 + 1) * Q := (Nat.add_mul _ _ _).symm
        _ = k * Q := by rw [hk]
        _ = Q * k := Nat.mul_comm _ _
    have htake : W.take n = W.take m ++ (W.drop m).take Q := by
      rw [← hmn, List.take_add]
    have hsegment : List.Sublist ((W.drop m).take Q) (W.take n) := by
      rw [htake]
      exact (List.nil_sublist _).append (List.Sublist.refl _)
    have hlastMem :
        (⟨t, ((ActualReferenceInitializationBlock.referenceInput z.val rewards
          C_star C_h rate).row.2 t).2 (0, i)⟩ :
            AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) ∈ W.take n := by
      apply hsegment.subset
      exact List.mem_of_mem_getLast? (by simpa using hsegmentLast)
    have hsplitPair : (W.take n ++ W.drop n).Pairwise
        (fun a b => a.time.val < b.time.val) := by
      rw [List.take_append_drop]
      exact hWPair
    have hcross := (List.pairwise_append.mp hsplitPair).2.2
    have htestEntryMem :
        ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ W.drop n := by
      have hmapped : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈
          (generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i).map
            ReferenceGeneratedPrelaunchDownCohort.testEntry :=
        List.mem_map.mpr ⟨test, hmem, rfl⟩
      rw [hOldMap] at hmapped
      simpa [n, k, Q, Nat.mul_comm] using hmapped
    have htime := hcross _ hlastMem _ htestEntryMem
    have halpha : alpha = t.val + 1 := by
      have hb : ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h z.val i k = some (t.val + 1) := by
        simpa [k, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)] using hboundary
      exact Option.some.inj (hbirth.symm.trans hb)
    rw [halpha]
    exact htime

/-- The birth is the actual empty-bank creation/reset boundary, and every old
test is at or after it. -/
theorem generated_inherited_down_old_test_birth
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    ∃ alpha, alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h z.val i
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.completed.length = some alpha ∧
      ∀ test (hmem : test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i),
        alpha ≤ test.time.val ∧
        test.time.val < s ∧
        test.sample = ((z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 test.time).2 (0, i) ∧
        test.sent = none := by
  obtain ⟨alpha, halpha, hbirth⟩ :=
    generated_inherited_down_cohort_birth rewards C_star C_h s hs z i
  refine ⟨alpha, halpha, hbirth, ?_⟩
  intro test hmem
  have hsource := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
    rate rewards C_star C_h z.val i test (List.mem_of_mem_drop hmem)
  dsimp only at hsource
  rcases hsource with ⟨activation, hactivation, hactivationTime, hbefore, hsample,
    hslot, hselected, q, hq, hcrossing, hrunActivation, hbeforeRun, hafterRun,
    u, hu, hhistory, hpositive, hcoordinator, hcoordinatorAction, hplayerAction,
    hsent⟩
  have hbeforeS : test.time.val < s := by simpa [z.property.2] using hbefore
  exact ⟨old_test_time_after_birth rewards C_star C_h s hs z i alpha hbirth test hmem,
    hbeforeS, hsample, hsent⟩

/-- The old test's complete source-level physical witness is the original
bootstrap block execution, including its same-block coordinator and follower
actions and the absent sent word. -/
theorem generated_inherited_down_old_test_physical
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i) :
    let x := ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    ∃ a, b.activation f = some a ∧ a.val ≤ test.time.val + 1 ∧
      test.time.val < ReferenceInitializationRun.elapsed p b.completed ∧
      test.sample = ((z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2
        test.time).2 (0, i) ∧
      PublicDiscreteDraws.slotDraw (x.row.2 test.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 test.time).1 = i ∧
      ∃ q, ∃ h : (ReferenceInitializationRun.run x q).completed < BootstrapDimensions.n_boot p,
        (ReferenceInitializationRun.run x q).crossing = none ∧
        (ReferenceInitializationRun.run x q).activation f = some a ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x q).completed ≤ test.time.val ∧
        test.time.val < ReferenceInitializationRun.elapsed p
          ((ReferenceInitializationRun.run x q).completed + 1) ∧
        ∃ u : Fin (ReferenceInitializationRun.elapsed p b.completed),
          u.val = test.time.val ∧
          b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u =
            ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m f) test.time ∧
          0 < (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u).2.val.val ∧
          ReferenceInitializationRun.coordinatorLearner (ReferenceInitializationRun.run x q) = none ∧
          BootstrapPhysicalBlock.actions
            (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
            (BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time.val) test.time (coordinator p.two_le_m) =
            (BootstrapPhysicalBlock.tuple
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time).val (coordinator p.two_le_m) ∧
          BootstrapPhysicalBlock.actions
            (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
            (BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time.val) test.time (PublicDiscreteDraws.followerPlayer p.two_le_m f) =
            (BootstrapPhysicalBlock.tuple
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time).val (PublicDiscreteDraws.followerPlayer p.two_le_m f) ∧
          test.sent = none := by
  exact ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
    rate rewards C_star C_h z.val i test (List.mem_of_mem_drop hmem)

/-- Every new test comes from one original postlaunch physical record and its
same actual DOWN call/cut, with the actual sent word and positive diagnostic. -/
theorem generated_inherited_down_new_test_physical
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z) :
    ∃ k : Fin (p.T - s),
      ∃ record : ReferenceFollowerDownDecoderReplay.Record p rate,
        record ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
          rate rewards C_star C_h s hs z).records ∧
        record.input.time.val = s + k.val ∧
        test.time = record.input.time ∧
        test.sample = ((z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 test.time).2 (0, i) ∧
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
            record.input i) = some test ∧
        ∃ call cut,
          ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
          (record.output.followers i).down = some cut ∧
          call.1 = record.input.time ∧
          call.2.sample = ((z.val.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 record.input.time).2 (0, i) ∧
          test.sent = cut.expectedWord ∧
          cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input ∧
          0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
          cut.rawComparison.isSome = true := by
  have hfull := generatedInheritedDownNew_member_full rewards C_star C_h s hs i z test hmem
  obtain ⟨k, htest, htime⟩ :=
    generatedInheritedDownTests_member_offset rewards C_star C_h s hs i z test hfull
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input), rfl⟩
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s (p.T - s) (by omega) input
  have hrecord : record ∈
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
        rate rewards C_star C_h s hs z).records := by
    change record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
      (by omega) input).records
    rw [hrecords]
    exact List.mem_ofFn.mpr ⟨k, rfl⟩
  have htestRecord :
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
          some test := by
    simpa [record, input, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput] using htest
  obtain ⟨call, cut, hcall, hcut, hcallTime, hcallSample, htestTime, htestSample,
      hsent, hexpected, hpositive, hcomparison⟩ :=
    actual_executedTestOfRound_record record i test htestRecord
  have hrow : record.input.row =
      z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) := by
    change record.input.rows record.input.selected = _
    simp [record, input, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
  have htimeRecord : record.input.time.val = s + k.val := by
    simpa [record, input, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using htime
  refine ⟨k, record, hrecord, htimeRecord, htestTime, ?_, htestRecord,
    call, cut, hcall, hcut, hcallTime, ?_, hsent, hexpected, hpositive, hcomparison⟩
  · rw [htestTime, ← hrow]
    exact htestSample
  · rw [← hrow]
    exact hcallSample

/-- The actual birth is no later than any test in the old/new cohort, with the
original sample and physical provenance retained on each side. -/
theorem generated_inherited_down_cohort_test_origin
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    ∃ alpha, alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h z.val i
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.completed.length = some alpha ∧
      ∀ test, test ∈ generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z →
        alpha ≤ test.time.val ∧
        test.sample = ((z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 test.time).2 (0, i) ∧
        ((∃ hOld : test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i,
          test.time.val < s ∧ test.sent = none) ∨
        (∃ hNew : test ∈ generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z,
          ∃ k : Fin (p.T - s),
            ∃ record : ReferenceFollowerDownDecoderReplay.Record p rate,
              record ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs z).records ∧
              record.input.time.val = s + k.val ∧
              test.time = record.input.time ∧
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                  record.input i) = some test ∧
              test.sent = ReferenceActiveAffinePositiveTest.downSent record.input ∧
              0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val)) := by
  obtain ⟨alpha, halpha, hbirth, holdProv⟩ :=
    generated_inherited_down_old_test_birth rewards C_star C_h s hs z i
  refine ⟨alpha, halpha, hbirth, ?_⟩
  intro test hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · have hsource := holdProv test hold
    rcases hsource with ⟨_, hbeforeS, hsample, hsent⟩
    exact ⟨old_test_time_after_birth rewards C_star C_h s hs z i alpha hbirth test hold,
      hsample, Or.inl ⟨hold, hbeforeS, hsent⟩⟩
  · have hnewPhysical := generated_inherited_down_new_test_physical
      rewards C_star C_h s hs z i test hnew
    obtain ⟨k, record, hrecord, htime, htestTime, hsample, htest, call, cut,
      hcall, hcut, hcallTime, hcallSample, hsent, hexpected, hpositive, hcomparison⟩ := hnewPhysical
    have htimeLower : s ≤ test.time.val := by rw [htestTime, htime]; omega
    exact ⟨Nat.le_trans halpha htimeLower, hsample,
      Or.inr ⟨hnew, k, record, hrecord, htime, htestTime, htest,
        hsent.trans hexpected, hpositive⟩⟩

/-- The old/new list is strictly chronological and hence has no duplicate
calendar index. -/
theorem generated_inherited_down_cohort_pairwise
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    (generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z).Pairwise
      (fun a b => a.time.val < b.time.val) ∧
    (generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z).Nodup := by
  let Old := generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs z i
  let New := generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z
  let tests := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i z (p.T - s)
  have holdPairSource := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_tests_pairwise
    rate rewards C_star C_h z.val i
  have hOldPair : Old.Pairwise (fun a b => a.time.val < b.time.val) := by
    dsimp [Old, generatedInheritedDownOldFirstTests]
    exact holdPairSource.sublist (List.drop_sublist _ _)
  have hroundPair :
      (List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2).Pairwise
        (fun round₁ round₂ =>
          ∀ test₁ test₂,
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round₁ = some test₁ →
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round₂ = some test₂ →
            test₁.time.val < test₂.time.val) := by
    apply List.pairwise_ofFn.mpr
    intro k₁ k₂ hlt test₁ test₂ htest₁ htest₂
    have htime₁ := generatedSourceObservation_test_time
      rewards C_star C_h s hs i z k₁ test₁ htest₁
    have htime₂ := generatedSourceObservation_test_time
      rewards C_star C_h s hs i z k₂ test₂ htest₂
    omega
  have htestsPair : tests.Pairwise (fun a b => a.time.val < b.time.val) := by
    have hbase := List.Pairwise.filterMap
      (fun round => ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round)
      (fun round₁ round₂ hround test₁ htest₁ test₂ htest₂ =>
        hround test₁ test₂ htest₁ htest₂) hroundPair
    have htake :
        (List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2).take (p.T - s) =
          List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 := List.take_of_length_le (by simp)
    simpa [tests, ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests,
      htake] using hbase
  have hNewPair : New.Pairwise (fun a b => a.time.val < b.time.val) := by
    dsimp [New, generatedInheritedDownNewFirstTests]
    exact htestsPair.sublist (List.take_sublist _ _)
  have hOldBeforeNew : ∀ a ∈ Old, ∀ b ∈ New, a.time.val < b.time.val := by
    intro a ha b hb
    have hsource := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
      rate rewards C_star C_h z.val i a (List.mem_of_mem_drop ha)
    dsimp only at hsource
    rcases hsource with ⟨activation, hactivation, hactivationTime, hbefore, _⟩
    have haBefore : a.time.val < s := by
      simpa [z.property.2] using hbefore
    have hfull := generatedInheritedDownNew_member_full rewards C_star C_h s hs i z b hb
    obtain ⟨k, _, hbTime⟩ := generatedInheritedDownTests_member_offset
      rewards C_star C_h s hs i z b hfull
    rw [hbTime]
    omega
  have hpair : (Old ++ New).Pairwise (fun a b => a.time.val < b.time.val) := by
    apply List.pairwise_append.mpr
    exact ⟨hOldPair, hNewPair, hOldBeforeNew⟩
  have hnodup : (Old ++ New).Nodup := by
    apply hpair.imp
    intro a b hab heq
    rw [heq] at hab
    exact (Nat.lt_irrefl _) hab
  simpa [Old, New, generatedInheritedDownFirstCohortTests] using ⟨hpair, hnodup⟩

/-- At the explicit first-completion selector, F's actual physical bank and
full failure cut are identified with this produced old/new cohort. -/
theorem generated_inherited_down_cohort_first_completion_bank
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T - s)
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
        ∀ l (hl : l < k),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)) :
    ∃ record callCode loggedCode cutCode logged cut,
      record.input = ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k
        (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs z) ∧
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
        some callCode ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record =
        some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      FollowerDownMeasurability.followerStateCode rate logged = loggedCode ∧
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode ∧
      callCode.1 = record.input.time ∧
      logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
      cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      cut.raw = AffineBatchDecoder.batchOutput
        (logged.downBatch.pending ++
          [⟨record.input.time,
            (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]) ∧
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode loggedCode =
        ⟨[], logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ ∧
      logged.downBatch.pending =
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.pending ++
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z k).map
            ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry ∧
      logged.downBatch.completed =
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.completed ∧
      (logged.downBatch.pending ++
        [({ time := record.input.time,
            sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
          AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))]).length =
        AffineBatchDecoder.quota p ∧
      logged.downBatch.pending ++
        [({ time := record.input.time,
            sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
          AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))] =
        (generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry := by
  obtain ⟨record, callCode, loggedCode, cutCode, logged, cut,
      hrecordInput, hcall, hactualCall, hlogged, hcut, hloggedCode, hcutCode,
      hcallTime, hquota, hcomparison, hpositive, hraw, hdecoded,
      hpending, hcompleted, hlength, hjoin⟩ :=
    ReferenceGeneratedInheritedDownFirstCompletion.generated_inherited_down_first_completion_bank
      rewards C_star C_h s hs z i k hk hfirst
  have hold := generated_inherited_down_old_pending rewards C_star C_h s hs z i
  have hsameEntries :
      (generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry =
        (generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z).map
          ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := rfl
  have hcohortMap :
      (generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i z).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry =
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.pending ++
          (generatedInheritedDownNewFirstTests rate rewards C_star C_h s hs i z).map
            ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := by
    rw [generatedInheritedDownFirstCohortTests, List.map_append]
    rw [hold.1, hsameEntries]
  have hfinal := hjoin.trans hcohortMap.symm
  exact ⟨record, callCode, loggedCode, cutCode, logged, cut,
    hrecordInput, hcall, hactualCall, hlogged, hcut, hloggedCode, hcutCode,
    hcallTime, hquota, hcomparison, hpositive, hraw, hdecoded,
    hpending, hcompleted, hlength, hfinal⟩

end Bandits.Support.ReferenceGeneratedInheritedDownCohort

end
