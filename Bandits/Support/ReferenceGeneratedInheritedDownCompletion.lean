/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownBatchCalendar

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Take

/-!
# The inherited first postlaunch DOWN completion

Sources: `sources/zip4/manuscript/05_binary_transport.tex:27-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142,157-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-138`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module follows the actual generated crossing, corrected launch, and
whole postlaunch physical run. Its first decoder batch inherits the pending
equations already present at launch. It preserves the actual call and cut
diagnostics, including rejection and failure branches; it makes no affine
probability claim and proves no regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedInheritedDownCompletion

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
variable {p : Parameters} {rate : RateInput p}

/-- The original ordinary follower state at the actual generated crossing. -/
def generatedInheritedInitialFollower
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) : ReferencePrelaunchFollower.State p rate.eta :=
  ReferenceInitializationRun.ordinary
    (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate)
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate))
    (ActualReferenceInitializationBlock.refFollower i)

/-- The exact original DOWN calendar prefix: offsets in the code are physical
rounds `s + k + 1`, and an absent call or absent cut adds no test. -/
def generatedInheritedDownTests
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (n : ℕ) : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  ((List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i z).2).take n).filterMap
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate)

/-- The actual first inherited cohort: the first residual-quota tests in the
whole postlaunch calendar, with sent fields supplied only by the real cut. -/
def generatedInheritedDownNewFirstTests
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  (generatedInheritedDownTests rate rewards C_star C_h s hs i z (p.T - s)).take
    (AffineBatchDecoder.quota p -
      (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.pending.length)

/-- An executed test contributes the existing decoder entry, with no
historical sent field assigned to entries already present at launch. -/
def inheritedTestEntry (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
  ⟨test.time, test.sample⟩

/-- The real generated seed spec bounds the inherited bank and fixes its
ordinary follower to the same initialization replay state used below. -/
private theorem generatedInheritedInitialBank_lt_quota
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    (∃ memory,
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs z).followers i =
          .ordinary (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i) memory) ∧
      (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.pending.length <
        AffineBatchDecoder.quota p := by
  let source := z.1
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs z
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs z
  have hc : (ReferenceInitializationRun.output x).crossing.isSome = true := z.2.1
  obtain ⟨active, hactive, _hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hc
  have hactiveSeed : active = seed := by
    exact Option.some.inj (hactive.1.symm.trans hseed.1)
  obtain ⟨seedState, seedMemory, hconfig, _hstatus, hwell, _hchron, _htimes⟩ :=
    hseed.2.2 i
  have hfollowers := hactive.2.2.2.2 i
  have hstate : seedState = generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i := by
    have hconfigEq :
        (DeclaredFollowerLocalRound.LocalConfiguration.ordinary seedState seedMemory :
          DeclaredFollowerLocalRound.LocalConfiguration p rate) =
          .ordinary (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i)
            (ActiveFollowerLifecycle.initialMemory p) := by
      calc
        _ = seed.followers i := hconfig.symm
        _ = active.followers i := by rw [hactiveSeed]
        _ = _ := hfollowers
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfigEq).1
  have hinitial : seed.followers i = .ordinary
      (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i)
      (ActiveFollowerLifecycle.initialMemory p) := by
    change seed.followers i = .ordinary
      (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i)
      (ActiveFollowerLifecycle.initialMemory p)
    rw [← hactiveSeed]
    exact hfollowers
  refine ⟨⟨ActiveFollowerLifecycle.initialMemory p, hinitial⟩, ?_⟩
  simpa [generatedInheritedInitialFollower, source, x, b, seed, hstate,
    ReferenceFollowerDecoderChronology.downBatchWellFormed] using hwell.1

/-- The inherited launch bank is nonempty in its residual quota, and its
remaining quota is strictly positive. -/
theorem generated_inherited_down_initial_residual
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    let m0 := (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.pending.length
    let h := AffineBatchDecoder.quota p - m0
    m0 < AffineBatchDecoder.quota p ∧ 0 < h := by
  dsimp only
  have hlt := (generatedInheritedInitialBank_lt_quota rate rewards C_star C_h s hs z i).2
  omega

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

private theorem finishFollower_downInput_none_of_occupied
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)
    ) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory)
    (hoccupied : state.status ≠ .unoccupied) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = none := by
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration,
    ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
  cases hrecord : DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm observation state with
  | error failure => simp [hrecord]
  | ok postRecord =>
      cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
          prepared.time observation state memory postRecord with
      | error failure => simp [hrecord, hrelease]
      | ok next => simp [hrecord, hrelease]

/-- The countable round code reconstructs all same-round diagnostics from the
actual physical record, including receiver failures after the call. -/
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

private theorem record_logged_choice
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogged : (record.output.followers i).downInput = some logged) :
    ∃ state memory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary state memory ∧
      state.status = .unoccupied ∧ logged.status = state.status ∧
      logged.downBatch = state.downBatch := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hdiagnostic := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
    record i
  have hlogged' : (record.output.preparation.observeFollower i).downInput = some logged := by
    rw [hdiagnostic]
    exact hlogged
  have hfinish :
      (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared observation).downInput =
        some logged := by
    simpa only [prepared, observation,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hlogged'
  cases hconfiguration : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hfinish
  | ordinary state memory =>
      by_cases hstatus : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, observation) state with
        | error failure =>
            simp [ReferenceActivePhysicalStep.finishFollower,
              ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
              hlogging] at hfinish
        | ok actualLogged =>
            cases hresult : DeclaredFollowerLocalRound.consumeDownResult rate
                (ReferenceDownReception.referenceDownCut p
                  record.output.preparation.coordinator.downView prepared.follower prepared.row
                  prepared.time observation rate actualLogged).outcome with
            | error failure =>
                have hloggedEq : actualLogged = logged := by
                  simpa [ReferenceActivePhysicalStep.finishFollower,
                    ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                    hlogging, hresult] using hfinish
                subst actualLogged
                have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                  prepared.follower prepared.row prepared.activation prepared.time
                  (prepared.arm, observation) state logged hlogging
                rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                exact ⟨state, memory, by simp [prepared,
                  ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                  hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
            | ok post =>
                cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                    prepared.follower prepared.row prepared.time observation state memory post with
                | error failure =>
                    have hloggedEq : actualLogged = logged := by
                      simpa [ReferenceActivePhysicalStep.finishFollower,
                        ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                        hlogging, hresult, hrelease] using hfinish
                    subst actualLogged
                    have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                      prepared.follower prepared.row prepared.activation prepared.time
                      (prepared.arm, observation) state logged hlogging
                    rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                    exact ⟨state, memory, by simp [prepared,
                      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                      hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
                | ok result =>
                    cases result with
                    | mk final finalMemory =>
                        have hloggedEq : actualLogged = logged := by
                          simpa [ReferenceActivePhysicalStep.finishFollower,
                            ReferenceActivePhysicalStep.recordFollower, hconfiguration,
                            hstatus, hlogging, hresult, hrelease] using hfinish
                        subst actualLogged
                        have hframe := ActiveFollowerLogging.checkedLogging_success_frame
                          prepared.follower prepared.row prepared.activation prepared.time
                          (prepared.arm, observation) state logged hlogging
                        rcases hframe with ⟨_, _, _, _, hloggedStatus, hloggedBatch, _⟩
                        exact ⟨state, memory, by simp [prepared,
                          ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration,
                          hconfiguration], hstatus, hloggedStatus, hloggedBatch⟩
      · rw [finishFollower_downInput_none_of_occupied
          record.output.preparation.coordinator.downView prepared observation state memory
          hconfiguration hstatus] at hfinish
        cases hfinish

private theorem finishFollower_diagnostic_pair
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
      cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm
          observation state).result with
      | error failure => rfl
      | ok post =>
          dsimp only
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem record_down_some_logged
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut) :
    ∃ logged, (record.output.followers i).downInput = some logged := by
  classical
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i]
    at hcut ⊢
  have hp := finishFollower_diagnostic_pair record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i)
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
  change ((record.output.preparation.observeFollower i).downInput,
    (record.output.preparation.observeFollower i).down) = _ at hp
  cases hc : (record.output.preparation.followers.followers i).configuration with
  | dagger =>
      rw [hc] at hp
      have he := congrArg Prod.snd hp
      rw [hcut] at he
      cases he
  | ordinary choice memory =>
      rw [hc] at hp
      have hd := (congrArg Prod.snd hp).symm.trans hcut
      by_cases hs : choice.status = .unoccupied
      · cases hl : ActiveFollowerLogging.checkedLogging
            (record.output.preparation.followers.followers i).follower
            (record.output.preparation.followers.followers i).row
            (record.output.preparation.followers.followers i).activation
            (record.output.preparation.followers.followers i).time
            ((record.output.preparation.followers.followers i).arm,
              ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) choice with
        | error failure =>
            simp only [ReferenceActivePhysicalStep.recordFollower,
              dite_eq_left hs, hl, reduceCtorEq] at hd
        | ok logged =>
            refine ⟨logged, ?_⟩
            have he := congrArg Prod.fst hp
            dsimp only at he
            rw [he]
            simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, hl]
      · simp only [ReferenceActivePhysicalStep.recordFollower,
          dite_eq_right hs, reduceCtorEq] at hd

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

private theorem executedTestOfRound_eq_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (callCode : ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 <
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
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
  obtain ⟨state, memory, hconfiguration, hstatus, hloggedStatus, _hloggedBatch⟩ :=
    record_logged_choice record i logged hlogged
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hcomparisonActual :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison.isSome =
          true := by
    rw [← hcutActual]
    exact hcomparison
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
      record.input.time logged := by
    rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call] at hcomparisonActual
    exact of_decide_eq_true hcomparisonActual
  have hactualCall : ReferenceFollowerDownDecoderReplay.actualDownCall i record =
      some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
    rw [← ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i record,
      hcall]
    rfl
  have hactualFields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
    record i _ hactualCall
  have hchoiceStatus : state.status = .unoccupied := hloggedStatus.symm.trans hgate.2.1
  have hcallEq : ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode =
      (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
        ActiveFollowerDownAcceptance.currentRoundInput p i
          (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
          (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate state) := by
    exact (Option.some.inj
      ((ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i state memory
        hconfiguration).symm.trans hactualCall)).symm
  have hselected :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.selected = true :=
    hactualFields.2.2.mpr hgate.1
  have henabled :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.receiverEnabled = true := by
    rw [hcallEq]
    simp [ActiveFollowerDownAcceptance.currentRoundInput, hchoiceStatus]
  have hrounding :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.roundedReward =
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [hcallEq]
    rfl
  have heligible : AffineBatchDecoder.eligible
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 :=
    ⟨hselected, henabled, by rw [hrounding]; exact hpositive⟩
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hsender : i = ReferenceActivePhysicalStep.upSenderIndex record.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    exact hgate.1.2.symm
  have hview : record.output.preparation.coordinator.downView =
      (ReferenceActivePhysicalStep.dispatch record.input).downView := by
    rw [hprepared]
    rfl
  have hexpected : cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent record.input := by
    calc
      cut.expectedWord =
          (ReferenceDownReception.referenceDownCut p
            record.output.preparation.coordinator.downView i record.input.row record.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).expectedWord :=
        congrArg ReferenceDownReception.ReferenceDownCutOutput.expectedWord hcutActual
      _ = ReferenceDownReception.expectedDownFlatWord
          record.output.preparation.coordinator.downView i record.input.row record.input.time := by
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
        simp [ReferenceActiveAffinePositiveTest.downSent, hview, hsender]
  have hgrid :
      0 < (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.1).val.val := by
    have hown : ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
        record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      exact congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
        record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    have hobs : ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
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
  have hcutCode :
      ((ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.2).2.2 =
        some (ReferenceDownCompletedAmbiguityMeasurability.cutFields cut) := by
    rw [roundDownObservation_diagnostics_eq_actual record i, hcut]
    rfl
  have htime : callCode.1 = record.input.time := by
    have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      record i _ hactualCall
    simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.1
  have hsample : callCode.2.2.2.1 = (record.input.row.2 record.input.time).2 (0, i) := by
    have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      record i _ hactualCall
    simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.2.1
  refine ⟨?_, hexpected, hactualCall, heligible⟩
  simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
    hcallCode, hcutCode, hgrid, hcomparison,
    ReferenceDownCompletedAmbiguityMeasurability.cutFields, htime, hsample]

private theorem executedTestOfRound_some_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test) :
    ∃ call,
      ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
      AffineBatchDecoder.eligible call.2 ∧
      test.time = call.1 ∧ test.sample = call.2.sample ∧
      test.time = record.input.time ∧
      test.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.downSent record.input := by
  classical
  have htest0 := htest
  have hd := roundDownObservation_diagnostics_eq_actual record i
  unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound at htest
  dsimp only at htest
  rw [hd] at htest
  change (match ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record,
      (record.output.followers i).down.map ReferenceDownCompletedAmbiguityMeasurability.cutFields with
    | some call, some cut =>
        if 0 < (ActualInitializationPhysicalStep.observationOfGrid p
              (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val ∧
            cut.2.2.1.isSome then
          some ⟨call.1, call.2.2.2.1, cut.2.1⟩ else none
    | _, _ => none) = some test at htest
  cases hc : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
  | none => simp only [hc] at htest; cases htest
  | some callCode =>
      cases hcut : (record.output.followers i).down with
      | none => simp only [hc, hcut, Option.map_none] at htest; cases htest
      | some cut =>
          simp only [hc, hcut, Option.map_some] at htest
          split at htest
          next hpositive =>
            obtain ⟨logged, hlogged⟩ := record_down_some_logged record i cut hcut
            have hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation
                i record = some callCode := hc
            have hcmp : cut.rawComparison.isSome = true := hpositive.2
            have hp : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                record i).val.val := by
              rw [preparedOwnObservation_eq_grid]
              exact hpositive.1
            obtain ⟨htestEq, hsent, hactual, heligible⟩ :=
              executedTestOfRound_eq_actual record i callCode logged cut hcall hlogged hcut hcmp hp
            have htestFields := Option.some.inj (htestEq.symm.trans htest0)
            obtain ⟨htime, hsample, _⟩ :=
              ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
                record i _ hactual
            refine ⟨_, hactual, heligible, ?_, ?_, ?_, ?_, ?_⟩
            · rw [← htestFields]; exact htime.symm
            · rw [← htestFields]; exact hsample.symm
            · rw [← htestFields]
            · rw [← htestFields]
            · rw [← htestFields]; exact hsent
          next hnegative => cases htest

private theorem referenceDownCut_compared_of_success
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (logged post : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hstatus : logged.status = .unoccupied)
    (hout : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
        .ok post) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).rawComparison.isSome = true := by
  classical
  have hr : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  have hd : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hr, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  have hb : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hr, hd, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call]
  exact decide_eq_true ⟨hselected, hstatus, hr, hd, hb⟩

private theorem finishFollower_ordinary_record
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : prepared.configuration = .ordinary choice memory)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary after afterMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation choice memory post = .ok (after, afterMemory) := by
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr] at hout
  | ok post =>
      cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
          prepared.time observation choice memory post with
      | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf] at hout
      | ok result =>
          cases result with
          | mk final finalMemory =>
              simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf,
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at hout
              rcases hout with ⟨rfl, rfl⟩
              exact ⟨post, rfl, hf⟩

private theorem eligible_actualDownCall_executedTestOfRound
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (call : ReferenceFollowerDownDecoderReplay.Call p)
    (hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call)
    (heligible : AffineBatchDecoder.eligible call.2) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
          ReferenceActiveAffinePositiveTest.downSent record.input⟩ := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  let view := record.output.preparation.coordinator.downView
  have hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary after afterMemory := by
    change (record.output.preparation.observeFollower i).configuration = _
    have hn := hafter
    rw [record.output_eq] at hn ⊢
    exact hn
  cases hc : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
  | dagger => simp only [ReferenceFollowerDownDecoderReplay.actualDownCall, hc, reduceCtorEq] at hcall
  | ordinary choice memory =>
      have hcallEq := Option.some.inj
        ((ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i choice memory hc).symm.trans hcall)
      have he : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            observation rate choice) := by
        rw [← hcallEq] at heligible
        exact heligible
      obtain ⟨hselected, hstatus, hpositive⟩ :=
        (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff record i choice).mp he
      have hconfig : prepared.configuration = .ordinary choice memory := hc
      obtain ⟨post, hrecord, hfinish⟩ := finishFollower_ordinary_record view prepared observation
        choice after memory afterMemory hconfig hout
      cases hl : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) choice with
      | error failure =>
          simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hl] at hrecord
      | ok logged =>
          have hframe := ActiveFollowerLogging.checkedLogging_success_frame prepared.follower
            prepared.row prepared.activation prepared.time (prepared.arm, observation)
            choice logged hl
          have hloggedStatus : logged.status = .unoccupied := hframe.2.2.2.2.1.trans hstatus
          have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
              (ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
                prepared.time observation rate logged).outcome = .ok post := by
            simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl]
              using hrecord
          have hindex : prepared.follower = i :=
            (record.output.preparation.follower_alignment i).2.1
          have hselected' : ActiveFollowerDownAcceptance.downSelected p prepared.follower
              prepared.row prepared.time := by
            rw [hindex]
            exact hselected
          have hcomparison := referenceDownCut_compared_of_success view prepared.follower
            prepared.row prepared.time observation logged post hselected' hloggedStatus hconsume
          let cut := ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
            prepared.time observation rate logged
          have hdiag := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
            record i
          have hlogged : (record.output.followers i).downInput = some logged := by
            rw [← hdiag]
            change (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = _
            simp only [ReferenceActivePhysicalStep.finishFollower, hconfig,
              ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl, hconsume, hfinish]
          have hcut : (record.output.followers i).down = some cut := by
            rw [← hdiag]
            change (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = _
            simp only [ReferenceActivePhysicalStep.finishFollower, hconfig,
              ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl, hconsume, hfinish]
            rfl
          obtain ⟨callCode, hcode⟩ : ∃ callCode,
              ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
                some callCode := by
            cases hc' : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
            | none =>
                have hn := (ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_eq_none_iff
                  i record).mp hc'
                rw [hc] at hn
                cases hn
            | some callCode => exact ⟨callCode, rfl⟩
          obtain ⟨htest, hexpected, _, _⟩ :=
            executedTestOfRound_eq_actual record i callCode logged cut hcode hlogged hcut
              hcomparison hpositive
          rw [hexpected] at htest
          exact htest

private theorem record_executedTest_entries_eq_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : record.output.next.followers i = .ordinary after memory) :
    ((ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).toList).map
        inheritedTestEntry =
      (ReferenceFollowerDownDecoderReplay.actualDownCall i record).toList.flatMap (fun call =>
        AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) := by
  classical
  cases ht : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) with
  | none =>
      cases hc : ReferenceFollowerDownDecoderReplay.actualDownCall i record with
      | none => rfl
      | some call =>
          by_cases he : AffineBatchDecoder.eligible call.2
          · have hs := eligible_actualDownCall_executedTestOfRound record i after memory
              hafter call hc he
            rw [ht] at hs
            cases hs
          · simp only [Option.toList_none, List.map_nil, Option.toList_some,
              List.flatMap_singleton, AffineBatchDecoder.positiveAt,
              ActiveFollowerDownAcceptance.currentInputExtension]
            exact (ite_eq_right he).symm
  | some test =>
      obtain ⟨call, hc, he, htime, hsample, _⟩ :=
        executedTestOfRound_some_actual record i test ht
      simp only [hc, Option.toList_some, List.map_singleton, List.flatMap_singleton,
        AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
        AffineBatchDecoder.entry, inheritedTestEntry, htime, hsample]
      exact (ite_eq_left he).symm

private theorem connected_ordinary_successors
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceFollowerDownDecoderReplay.Record p rate)}
    (i : Fin (p.m - 1))
    (hc : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hf : ∃ state memory, final.followers i = .ordinary state memory) :
    (∃ state memory, initial.followers i = .ordinary state memory) ∧
    ∀ record ∈ records, ∃ state memory,
      record.output.next.followers i = .ordinary state memory := by
  induction records generalizing initial final with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hc
      subst final
      exact ⟨hf, by intro record hm; cases hm⟩
  | cons record rest ih =>
      rcases hc with ⟨hinput, htail⟩
      obtain ⟨hmiddle, hrest⟩ := ih htail hf
      have hbefore : ∃ state memory, initial.followers i = .ordinary state memory := by
        cases hb : record.input.state.followers i with
        | dagger =>
            have hd : record.output.next.followers i = .dagger := by
              rw [record.output_eq]
              exact ReferenceActivePhysicalStep.step_follower_dagger record.input i hb
            obtain ⟨state, memory, hs⟩ := hmiddle
            rw [hd] at hs
            cases hs
        | ordinary state memory => exact ⟨state, memory, by rw [← hinput]; exact hb⟩
      refine ⟨hbefore, ?_⟩
      intro current hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hmiddle
      · exact hrest current hm

private theorem records_executedTests_map_eq_actualDownPositives
    (records : List (ReferenceFollowerDownDecoderReplay.Record p rate))
    (i : Fin (p.m - 1))
    (hordinary : ∀ record ∈ records, ∃ state memory,
      record.output.next.followers i = .ordinary state memory) :
    (records.filterMap (fun record => ReferenceGeneratedDownBatchCalendar.executedTestOfRound
      rate (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))).map
        inheritedTestEntry = ReferenceFollowerDownDecoderReplay.actualDownPositives i records := by
  simp only [List.filterMap_eq_flatMap_toList, List.map_flatMap,
    ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.positiveCallEntries,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.flatMap_assoc]
  apply List.flatMap_congr
  intro record hm
  obtain ⟨state, memory, hs⟩ := hordinary record hm
  exact record_executedTest_entries_eq_actual record i state memory hs

private theorem foldDownCalls_below_quota
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hbound : bank.pending.length +
      (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length <
        AffineBatchDecoder.quota p) :
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls bank =
      ⟨bank.pending ++ ReferenceFollowerDownDecoderReplay.positiveCallEntries calls,
        bank.completed⟩ := by
  induction calls generalizing bank with
  | nil => simp [ReferenceFollowerDownDecoderReplay.foldDownCalls,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries]
  | cons call rest ih =>
      let trace := ActiveFollowerDownAcceptance.currentInputExtension p call.2
      let first := ReferenceFollowerDownDecoderReplay.positiveCallEntries [call]
      let later := ReferenceFollowerDownDecoderReplay.positiveCallEntries rest
      have hsplit : ReferenceFollowerDownDecoderReplay.positiveCallEntries (call :: rest) =
          first ++ later := by
        simp [ReferenceFollowerDownDecoderReplay.positiveCallEntries, first, later]
      have hbound' : bank.pending.length + first.length + later.length <
          AffineBatchDecoder.quota p := by
        simpa [hsplit, List.length_append, Nat.add_assoc] using hbound
      have hfirst : first = AffineBatchDecoder.positiveAt p trace call.1 := by
        simp [first, ReferenceFollowerDownDecoderReplay.positiveCallEntries, trace,
          ActiveFollowerDownAcceptance.currentInputExtension]
      have hnext : ReferenceFollowerDownDecoderReplay.replayDownCall bank call =
          ⟨bank.pending ++ first, bank.completed⟩ := by
        by_cases heligible : AffineBatchDecoder.eligible (trace call.1)
        · have hfirstEq : first = [AffineBatchDecoder.entry p trace call.1] := by
            rw [hfirst]
            simp [AffineBatchDecoder.positiveAt, heligible]
          have hsmall : (bank.pending ++ [AffineBatchDecoder.entry p trace call.1]).length <
              AffineBatchDecoder.quota p := by
            have hlt : bank.pending.length + 1 + later.length <
                AffineBatchDecoder.quota p := by
              simpa [hfirstEq] using hbound'
            simp only [List.length_append, List.length_singleton]
            omega
          have hsmall' : (bank.pending ++ AffineBatchDecoder.positiveAt p trace call.1).length <
              AffineBatchDecoder.quota p := by
            simpa [AffineBatchDecoder.positiveAt, heligible] using hsmall
          unfold ReferenceFollowerDownDecoderReplay.replayDownCall
          change AffineBatchDecoder.step p trace bank call.1 = _
          unfold AffineBatchDecoder.step
          rw [if_pos hsmall']
          simp [AffineBatchDecoder.positiveAt, heligible, hfirstEq]
        · have hfirstEq : first = [] := by
            rw [hfirst]
            simp [AffineBatchDecoder.positiveAt, heligible]
          have hpending : bank.pending.length < AffineBatchDecoder.quota p := by
            have hlt : bank.pending.length + first.length + later.length <
                AffineBatchDecoder.quota p := hbound'
            rw [hfirstEq] at hlt
            omega
          have hdecode := AffineBatchDecoder.decodeStep_ineligible p trace bank call.1
            hpending (by simpa [trace, ActiveFollowerDownAcceptance.currentInputExtension]
              using heligible)
          unfold ReferenceFollowerDownDecoderReplay.replayDownCall
          rw [hdecode]
          simp [hfirstEq]
      have hboundRest : (bank.pending ++ first).length + later.length <
          AffineBatchDecoder.quota p := by
        rw [List.length_append]
        omega
      change ReferenceFollowerDownDecoderReplay.foldDownCalls rest
          (ReferenceFollowerDownDecoderReplay.replayDownCall bank call) = _
      rw [hnext, ih ⟨bank.pending ++ first, bank.completed⟩ hboundRest]
      simp [hsplit, first, later, List.append_assoc]

private theorem ofFn_prefix {α : Type*} {n m : ℕ} (h : m ≤ n) (f : Fin n → α) :
    List.ofFn (fun k : Fin m => f ⟨k.val, by omega⟩) = (List.ofFn f).take m := by
  have hf : (fun k : Fin m => f ⟨k.val, by omega⟩) = Fin.take m h f := by
    funext k
    rfl
  rw [hf]
  exact Fin.ofFn_take_eq_take_ofFn h f

/-- The exact inherited test prefix, after erasing only its sent-word field,
is the actual positive-call list whenever the computed prefix endpoint is
ordinary. -/
theorem generated_inherited_down_tests_map_eq_actualDownPositives
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (n : ℕ) (hn : s + n ≤ p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary :
      (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
        s n hn (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs z)).finalState.followers i = .ordinary state memory) :
    (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).map inheritedTestEntry =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i
        (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
          s n hn (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs z)).records := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let shortCode := ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
    (p := p) (rate := rate) s n hn i input
  let fullCode := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i z
  let run := ReferenceActiveHorizonMeasurability.runOfInput
    (p := p) (rate := rate) s n hn input
  have hprefix : List.ofFn shortCode.2 = (List.ofFn fullCode.2).take n := by
    have hround : ∀ k : Fin n, shortCode.2 k = fullCode.2 ⟨k.val, by omega⟩ := by
      intro k
      rfl
    have hfunction : shortCode.2 = fun k : Fin n => fullCode.2 ⟨k.val, by omega⟩ :=
      funext hround
    rw [hfunction]
    exact ofFn_prefix (by omega) fullCode.2
  have hobs := ReferenceDownCompletedAmbiguityMeasurability.runDownObservation_eq_actual
    s n hn i input
  have hconnected := ReferenceActivePhysicalHorizon.run_connected
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n hn input.property
  have hfinal :
      (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s n hn input.property).finalState.followers i =
        .ordinary state memory := by
    exact hordinary
  have hsuccessors := connected_ordinary_successors i hconnected ⟨state, memory, hfinal⟩
  change (((List.ofFn fullCode.2).take n).filterMap
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate)).map inheritedTestEntry =
    ReferenceFollowerDownDecoderReplay.actualDownPositives i run.records
  rw [← hprefix, hobs.2]
  simp only [List.filterMap_map]
  exact records_executedTests_map_eq_actualDownPositives run.records i
    (by
      intro record hrecord
      exact hsuccessors.2 record hrecord)

/-- Before the inherited quota is reached, split on the actual computed
prefix endpoint. A dagger endpoint makes no bank claim; an ordinary endpoint
has exactly the inherited pending bank followed by these original tests. -/
theorem generated_inherited_down_prefix_bank
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (n : ℕ) (hn : s + n ≤ p.T)
    (hbefore : (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).length <
      AffineBatchDecoder.quota p -
        (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.pending.length) :
    (let run := ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
      s n hn (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s hs z)
    run.finalState.followers i = .dagger ∨
      ∃ state memory, run.finalState.followers i = .ordinary state memory ∧
        state.downBatch =
          ⟨(generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.pending ++
              (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).map inheritedTestEntry,
            (generatedInheritedInitialFollower rate rewards C_star C_h s hs z i).downBatch.completed⟩) := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let run := ReferenceActiveHorizonMeasurability.runOfInput
    (p := p) (rate := rate) s n hn input
  let initialFollower := generatedInheritedInitialFollower rate rewards C_star C_h s hs z i
  let initialBank := initialFollower.downBatch
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs z
  obtain ⟨initialMemory, hinitial⟩ :=
    (generatedInheritedInitialBank_lt_quota rate rewards C_star C_h s hs z i).1
  cases hendpoint : run.finalState.followers i with
  | dagger => exact Or.inl hendpoint
  | ordinary state memory =>
      have htests := generated_inherited_down_tests_map_eq_actualDownPositives
        rate rewards C_star C_h s hs i z n hn state memory hendpoint
      have htestLength :
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i run.records).length =
            (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).length := by
        rw [← htests]
        simp
      have hresidual := generated_inherited_down_initial_residual
        rate rewards C_star C_h s hs z i
      have hbound : initialBank.pending.length +
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i run.records).length <
            AffineBatchDecoder.quota p := by
        dsimp [initialBank, initialFollower] at hresidual ⊢
        omega
      have hreplay := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n hn input.property
        hseed.2.2 i initialFollower initialMemory hinitial state memory hendpoint
      have hfold := foldDownCalls_below_quota
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i run.records) initialBank
        (by simpa [ReferenceFollowerDownDecoderReplay.actualDownPositives,
          ReferenceFollowerDownDecoderReplay.positiveCallEntries,
          ReferenceFollowerDownDecoderReplay.replayDownCalls] using hbound)
      have hbank : state.downBatch =
          ⟨initialBank.pending ++
              (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).map inheritedTestEntry,
            initialBank.completed⟩ := by
        calc
          state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls
              i run.records initialFollower.downBatch := hreplay.1
          _ = ⟨initialBank.pending ++
                ReferenceFollowerDownDecoderReplay.actualDownPositives i run.records,
              initialBank.completed⟩ := by
              simpa [ReferenceFollowerDownDecoderReplay.replayDownCalls,
                ReferenceFollowerDownDecoderReplay.actualDownPositives] using hfold
          _ = ⟨initialBank.pending ++
                (generatedInheritedDownTests rate rewards C_star C_h s hs i z n).map
                  inheritedTestEntry,
              initialBank.completed⟩ := by
              rw [← htests]
      exact Or.inr ⟨state, memory, hendpoint, by simpa [initialFollower, initialBank] using hbank⟩

private theorem completedBatchAtRound_actual_fields
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)) :
    ∃ callCode loggedCode cutCode logged cut,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = some callCode ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      FollowerDownMeasurability.followerStateCode rate logged = loggedCode ∧
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode ∧
      callCode.1 = record.input.time ∧
      cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode loggedCode =
        ⟨[], (FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch).completed ++
          [(FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch).pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ := by
  classical
  dsimp only [ReferenceGeneratedDownBatchCalendar.completedBatchAtRound] at hcomplete
  rcases hcomplete with ⟨callCode, loggedCode, cutCode, hcall, hloggedCode,
    hcutCode, htime, hcomparison, hpositive, hquota, hdecoded⟩
  have hdiagnostics := roundDownObservation_diagnostics_eq_actual record i
  have hcall' : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
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
        have hcode : some (FollowerDownMeasurability.followerStateCode rate logged) =
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
  have hpositive' :
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [preparedOwnObservation_eq_grid]
    simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using hpositive
  have hquota' : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
    have hbatch : FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch =
        logged.downBatch := by
      rw [← hloggedCodeEq]
      exact FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
    rw [← hbatch]
    exact hquota
  refine ⟨callCode, loggedCode, cutCode, logged, cut, hcall', hlogged, hcut,
    hloggedCodeEq, hcutCodeEq, htime, hcomparison', hpositive', hquota', ?_⟩
  exact hdecoded

/-- A completion in D's exact postlaunch observation yields the original
physical record and same-call diagnostics. The retained raw word is the
decoder's actual quota-sized batch output, including `none`. -/
theorem generated_inherited_down_completion_diagnostics
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (k : ℕ) (hk : k < p.T - s)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩)) :
    ∃ record callCode loggedCode cutCode logged cut,
      record.input = ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k
        (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs z) ∧
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = some callCode ∧
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
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) =
        ⟨[], logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k (by omega) input,
      ReferenceActivePhysicalStep.step (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
        s k (by omega) input), rfl⟩
  have hround :
      (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩ =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i := rfl
  have hcomplete' := hcomplete
  rw [hround] at hcomplete'
  obtain ⟨callCode, loggedCode, cutCode, logged, cut, hcall, hlogged, hcut,
    hloggedCode, hcutCode, htime, hcomparison, hpositive, hquota, hdecoded⟩ :=
    completedBatchAtRound_actual_fields record i hcomplete'
  have hactualCall : ReferenceFollowerDownDecoderReplay.actualDownCall i record =
      some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
    have hrec := ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs
      i record
    rw [hcall] at hrec
    simpa only [Option.map_some] using hrec.symm
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hcomparisonNE : cut.rawComparison ≠ none := by
    cases hraw : cut.rawComparison <;> simp_all
  have hraw := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged
    (by rw [← hcutActual]; exact hcomparisonNE)
  have hgateEq := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged
  have hgate : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
      logged.status = .unoccupied ∧
      ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
      ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
      ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    rw [hcutActual] at hcomparison
    rw [hgateEq] at hcomparison
    by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row
        record.input.time
    · by_cases hstatus : logged.status = .unoccupied
      · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged
        · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch
          · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer
            · exact ⟨hselected, hstatus, hregisters, hbatch, hbuffer⟩
            · simp [ReferenceActiveAffinePositiveTest.downReceiverGate, hselected,
                hstatus, hregisters, hbatch, hbuffer] at hcomparison
          · simp [ReferenceActiveAffinePositiveTest.downReceiverGate, hselected,
              hstatus, hregisters, hbatch] at hcomparison
        · simp [ReferenceActiveAffinePositiveTest.downReceiverGate, hselected,
            hstatus, hregisters] at hcomparison
      · simp [ReferenceActiveAffinePositiveTest.downReceiverGate, hselected, hstatus]
          at hcomparison
    · simp [ReferenceActiveAffinePositiveTest.downReceiverGate, hselected] at hcomparison
  have heligible : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged) :=
    (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i record.input.row
      record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
      rate logged).2 ⟨hgate.1, hgate.2.1, hpositive⟩
  have hdecode := AffineBatchDecoder.decodeStep_complete p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
    logged.downBatch record.input.time heligible hquota
  have hrawBatch : cut.raw = AffineBatchDecoder.batchOutput
      (logged.downBatch.pending ++
        [⟨record.input.time,
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]) := by
    have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      record i _ hactualCall
    have hsample : (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample =
        (record.input.row.2 record.input.time).2 (0, i) := by
      simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.2.1
    calc
      cut.raw = (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).raw :=
          congrArg ReferenceDownReception.ReferenceDownCutOutput.raw hcutActual
      _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).2 := hraw
      _ = AffineBatchDecoder.batchOutput
          (logged.downBatch.pending ++
            [⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i)⟩]) := by
            simpa [ActiveFollowerDownAcceptance.currentDecodeStep,
              ActiveFollowerDownAcceptance.currentRoundInput,
              ActiveFollowerDownAcceptance.currentInputExtension,
              AffineBatchDecoder.entry] using
              congrArg Prod.snd hdecode
      _ = AffineBatchDecoder.batchOutput
          (logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]) := by
            rw [hsample]
  have hdecoded' :
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) =
        ⟨[], logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ := by
    rw [← hloggedCode] at hdecoded
    have hbatch :
        FollowerDownMeasurability.decoderBatchOfCode
            (FollowerDownMeasurability.followerStateCode rate logged).downBatch =
          logged.downBatch := by
      simpa [FollowerDownMeasurability.followerStateCode] using
        FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
    rw [hbatch] at hdecoded
    exact hdecoded
  exact ⟨record, callCode, loggedCode, cutCode, logged, cut, rfl, hcall, hactualCall,
    hlogged, hcut, hloggedCode, hcutCode, htime, hquota, hcomparison, hpositive,
    hrawBatch, hdecoded'⟩

end Bandits.Support.ReferenceGeneratedInheritedDownCompletion

end
