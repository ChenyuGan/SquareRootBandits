/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownCompletion

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.Infix
import Mathlib.Data.List.TakeDrop

/-!
# First completion of the inherited generated DOWN batch

Sources: `sources/zip4/manuscript/05_binary_transport.tex:27-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-142,157-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-138`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module identifies the first quota call in the original generated
postlaunch run. It starts from the actual launch stratum and inherited bank,
and counts only actual logged positive tests. It retains the complete physical
cut and its failure distinctions. No conditional probability or regret claim
is proved here.
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
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedInheritedDownFirstCompletion

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

private theorem finishFollower_downInput_none_of_occupied
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
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
  | error failure => simp
  | ok postRecord =>
      cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory postRecord with
      | error failure => simp [hrelease]
      | ok next => simp [hrelease]

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

private theorem preparedChoice_ordinary_implies_input
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
      .ordinary choice memory) :
    ∃ state inputMemory, record.input.state.followers i = .ordinary state inputMemory := by
  have hprepared :
      (DeclaredFollowerLocalRound.prepare rate i (record.input.rows record.input.selected)
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).configuration = .ordinary choice memory := by
    have h := hchoice
    unfold ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration at h
    rw [record.output_eq] at h
    simpa [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActiveFeedbackCut.prepareFollowers_apply,
      ReferenceActiveFeedbackCut.prepare,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using h
  cases hinput : record.input.state.followers i with
  | dagger =>
      simp [hinput, DeclaredFollowerLocalRound.prepare] at hprepared
  | ordinary state inputMemory => exact ⟨state, inputMemory, rfl⟩

private theorem executedTestOfRound_fields
    (round : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate)
    (h : (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round).isSome = true) :
    ∃ callCode cutCode,
      round.2.2.1 = some callCode ∧
      round.2.2.2.2.2 = some cutCode ∧
      0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
      cutCode.2.2.1.isSome = true := by
  unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound at h
  cases hcall : round.2.2.1 with
  | none => simp [hcall] at h
  | some callCode =>
      cases hcut : round.2.2.2.2.2 with
      | none => simp [hcall, hcut] at h
      | some cutCode =>
          have hcondition :
              0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
                cutCode.2.2.1.isSome = true := by
            by_cases hc :
                0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
                  cutCode.2.2.1.isSome = true
            · exact hc
            · simp [hcall, hcut] at h
              have hcondition' :
                  0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
                    cutCode.2.2.1.isSome = true := by
                exact ⟨by exact_mod_cast h.1, h.2⟩
              exact (hc hcondition').elim
          exact ⟨callCode, cutCode, rfl, rfl, hcondition.1, hcondition.2⟩

private theorem generatedInheritedDownTests_succ
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T - s) :
    ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z (n + 1) =
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n ++
        (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨n, hn⟩)).toList := by
  unfold ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
  let hlist := List.ofFn
    (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i z).2
  have hlen : hlist.length = p.T - s := by simp [hlist]
  have hnlen : n < hlist.length := by omega
  rw [← List.take_concat_get' hlist n hnlen]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  simp [hlist]
  rfl

private theorem generatedInheritedDownTests_length_mono
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) {n m : ℕ} (hn : n ≤ p.T - s) (hm : m ≤ p.T - s)
    (hnm : n ≤ m) :
    (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z n).length ≤
    (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z m).length := by
  induction m generalizing n with
  | zero => simp_all
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · have hm' : m + 1 ≤ p.T - s := hm
        have hsucc := generatedInheritedDownTests_succ
          rewards C_star C_h s hs z i m (by omega)
        rw [hsucc]
        exact le_trans (ih (by omega) (by omega) hnm') (by simp)
      · have hn' : n = m + 1 := by omega
        subst n
        exact Nat.le_refl _

private theorem generatedInheritedDownTests_threshold
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (h : ℕ) (hh : 0 < h)
    {n : ℕ} (hn : n ≤ p.T - s)
    (hcount : h ≤
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n).length) :
    ∃ k, ∃ hk : k < n,
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z k).length = h - 1 ∧
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, by omega⟩)).isSome = true := by
  induction n with
  | zero =>
      simp [ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests] at hcount
      omega
  | succ n ih =>
      have hsucc := generatedInheritedDownTests_succ rewards C_star C_h s hs z i n
        (by omega)
      rw [hsucc] at hcount
      have hlen : (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z n).length ≤
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i z n).length +
            (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                rate rewards C_star C_h s hs i z).2 ⟨n, by omega⟩)).toList.length := by
        omega
      have hprevBound : n ≤ p.T - s := by omega
      by_cases hcurrent :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨n, by omega⟩) = none
      · simp [hcurrent] at hcount
        obtain ⟨k, hk, hthreshold, htest⟩ := ih hprevBound (by omega)
        exact ⟨k, by omega, hthreshold, htest⟩
      · cases htestOption : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨n, by omega⟩) with
        | none => exact (hcurrent htestOption).elim
        | some test =>
            have hcount' : h ≤
                (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
                  rate rewards C_star C_h s hs i z n).length + 1 := by
              simpa [htestOption] using hcount
            by_cases hthreshold :
                (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
                  rate rewards C_star C_h s hs i z n).length = h - 1
            · refine ⟨n, by omega, hthreshold, ?_⟩
              simp [htestOption]
            · have hcountPrev : h ≤
                  (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
                    rate rewards C_star C_h s hs i z n).length := by omega
              obtain ⟨k, hk, hprevThreshold, hprevTest⟩ :=
                ih hprevBound hcountPrev
              exact ⟨k, by omega, hprevThreshold, hprevTest⟩

private theorem record_test_data
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1))
    (htest : (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome =
        true) :
    ∃ callCode cutCode logged cut,
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.1 = some callCode ∧
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.2.2.2 = some cutCode ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.2.1 =
          some (FollowerDownMeasurability.followerStateCode rate logged) ∧
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record =
        some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
      callCode.1 = record.input.time ∧
      0 < (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.1).val.val ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      cut.rawComparison.isSome = true := by
  classical
  obtain ⟨callCode, cutCode, hcallCode, hcutCode, hpositive, hcomparison⟩ :=
    executedTestOfRound_fields
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)
      htest
  have hcallObs : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode := by
    exact hcallCode
  have hactualCall : ReferenceFollowerDownDecoderReplay.actualDownCall i record =
      some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
    have h := ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs
      i record
    rw [hcallObs] at h
    exact h.symm
  have hdiag := roundDownObservation_diagnostics_eq_actual record i
  have hcutOption :
      (record.output.followers i).down.map
        ReferenceDownCompletedAmbiguityMeasurability.cutFields = some cutCode := by
    have h := hcutCode
    rw [hdiag] at h
    exact h
  obtain ⟨cut, hcut, hcutFields⟩ : ∃ cut,
      (record.output.followers i).down = some cut ∧
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode := by
    cases hdown : (record.output.followers i).down with
    | none => simp [hdown] at hcutOption
    | some cut =>
        refine ⟨cut, rfl, ?_⟩
        simpa [hdown] using hcutOption
  obtain ⟨logged, hlogged⟩ := record_down_some_logged record i cut hcut
  have hloggedCode :
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        record.input i).2.2.2.1 =
          some (FollowerDownMeasurability.followerStateCode rate logged) := by
    rw [roundDownObservation_diagnostics_eq_actual record i]
    simp [hlogged]
  have hcallTime : callCode.1 = record.input.time := by
    have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      record i _ hactualCall
    simpa [ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hfields.1
  have hpositive' :
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
    rw [preparedOwnObservation_eq_grid]
    simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using hpositive
  have hcomparison' : cut.rawComparison.isSome = true := by
    have hfields := congrArg
      (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
        fields.2.2.1.isSome) hcutFields
    exact hfields.trans hcomparison
  exact ⟨callCode, cutCode, logged, cut, hcallCode, hcutCode, hlogged, hcut,
    hloggedCode, hcutFields, hactualCall, hcallTime, hpositive, hpositive', hcomparison'⟩

private theorem logged_bank_of_record_test
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T - s)
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (hrecordInput : record.input =
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs z))
    (hbelow :
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n).length <
        AffineBatchDecoder.quota p -
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending.length)
    (htest : (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome =
        true) :
    ∃ logged,
      (record.output.followers i).downInput = some logged ∧
      logged.downBatch =
        ⟨(ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending ++
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
              rate rewards C_star C_h s hs i z n).map
                ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry,
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.completed⟩ := by
  classical
  obtain ⟨_, _, logged, _, _, _, hlogged, _, _, _, _, _, _, _, _⟩ :=
    record_test_data record i htest
  obtain ⟨choice, choiceMemory, hchoice, _, _, hloggedBank⟩ :=
    record_logged_choice record i logged hlogged
  obtain ⟨before, beforeMemory, hinput⟩ :=
    preparedChoice_ordinary_implies_input record i choice choiceMemory hchoice
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let run := ReferenceActiveHorizonMeasurability.runOfInput s n (by omega) input
  have hendpoint : run.finalState.followers i = .ordinary before beforeMemory := by
    have h := hinput
    rw [hrecordInput] at h
    simpa [input, run,
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using h
  have hprefix :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_prefix_bank
      rate rewards C_star C_h s hs i z n (by omega) hbelow
  rcases hprefix with hdagger | ⟨bankState, bankMemory, hbankEndpoint, hbank⟩
  · rw [hendpoint] at hdagger
    cases hdagger
  · have hstate : bankState = before := by
      have heq :
          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary bankState bankMemory :
            DeclaredFollowerLocalRound.LocalConfiguration p rate) =
          .ordinary before beforeMemory := hbankEndpoint.symm.trans hendpoint
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj heq).1
    have hbankBefore : before.downBatch =
        ⟨(ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending ++
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
              rate rewards C_star C_h s hs i z n).map
                ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry,
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.completed⟩ := by
      simpa [hstate] using hbank
    have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
      rate rewards C_star C_h s hs z
    have hchron := ReferenceFollowerDecoderChronology.run_downBatch_spec
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n (by omega)
      input.property hseed.2.2 i before beforeMemory hendpoint
    have hframe := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
      record i before choice beforeMemory choiceMemory hinput hchoice hchron.2
    refine ⟨logged, hlogged, ?_⟩
    calc
      logged.downBatch = choice.downBatch := hloggedBank
      _ = before.downBatch := hframe.1
      _ = _ := hbankBefore

private theorem completed_of_residual_test
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T - s)
    (hcount :
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n).length =
        AffineBatchDecoder.quota p -
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending.length - 1)
    (htest : (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨n, hn⟩)).isSome = true) :
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨n, hn⟩) := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs z
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n (by omega) input), rfl⟩
  have htestRecord :
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome =
          true := by
    simpa [record, input, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using htest
  obtain ⟨callCode, cutCode, logged, cut, hcallCode, hcutCode, hlogged,
      hcut, hloggedCode, hcutFields, hactualCall, hcallTime, hpositiveGrid,
      hpositive, hcomparison⟩ := record_test_data record i htestRecord
  have hresidual :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
      rate rewards C_star C_h s hs z i
  have hbelow :
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n).length <
        AffineBatchDecoder.quota p -
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending.length := by
    dsimp only at hresidual
    omega
  obtain ⟨loggedBank, hloggedBankInput, hloggedBank⟩ :=
    logged_bank_of_record_test rewards C_star C_h s hs z i n hn record rfl hbelow htestRecord
  have hloggedEq : logged = loggedBank := Option.some.inj (hlogged.symm.trans hloggedBankInput)
  subst loggedBank
  have hquota : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
    rw [hloggedBank]
    simp only [List.length_append, List.length_map]
    dsimp only at hcount hresidual
    omega
  obtain ⟨choice, choiceMemory, hchoice, hchoiceUnoccupied, hloggedStatus,
      hloggedBatch⟩ := record_logged_choice record i logged hlogged
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
  have hchoiceStatus : choice.status = .unoccupied := by
    exact hchoiceUnoccupied
  have hcallOrd := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    record i choice choiceMemory hchoice
  have hcallChoice :
      ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode =
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i,
          ActiveFollowerDownAcceptance.currentRoundInput p i
            (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
            (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
    exact Option.some.inj (hcallOrd.symm.trans hactualCall).symm
  have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
    record i _ hactualCall
  have hprepTime :
      ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i = record.input.time :=
    (congrArg Prod.fst hcallChoice).symm.trans hfields.1
  have hprepRow :
      ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
    (record.output.preparation.follower_alignment i).1
  have hcallInputChoice :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 =
        ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice := by
    have h := congrArg Prod.snd hcallChoice
    rw [hprepTime, hprepRow] at h
    simpa using h
  have hcallInput :
      (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 =
        ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
    calc
      _ = ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice :=
            hcallInputChoice
      _ = ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
            simp [ActiveFollowerDownAcceptance.currentRoundInput, hchoiceStatus, hgate.2.1]
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
  let loggedCode := FollowerDownMeasurability.followerStateCode rate logged
  have hbatchCode : FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch =
      logged.downBatch := by
    simpa [loggedCode, FollowerDownMeasurability.followerStateCode] using
      FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
  have hdecodedInput :
      { (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 with
          receiverEnabled := decide
            (FollowerDownMeasurability.followerStatusOfCode loggedCode.status = .unoccupied) } =
        ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
    rw [hcallInput]
    simp [loggedCode, FollowerDownMeasurability.followerStateCode,
      FollowerDownMeasurability.followerStatusOfCode_code, hgate.2.1,
      ActiveFollowerDownAcceptance.currentRoundInput]
  have hdecoded :
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode loggedCode =
        ({ pending := [], completed := logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time,
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]] } :
          AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank
    rw [hbatchCode, hdecodedInput, hcallTime]
    simpa [ActiveFollowerDownAcceptance.currentInputExtension, AffineBatchDecoder.entry,
      hcallInput] using congrArg Prod.fst hdecode
  have hcutComparison : cutCode.2.2.1.isSome = true := by
    have hfields' := congrArg
      (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
        fields.2.2.1.isSome) hcutFields
    exact hfields'.symm.trans hcomparison
  have htimeCode : callCode.1 =
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).1 := by
    simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using hcallTime
  have hquotaCode :
      (FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch).pending.length + 1 =
        AffineBatchDecoder.quota p := by
    rw [hbatchCode]
    exact hquota
  have hdecodedCode :
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode loggedCode =
        ⟨[],
          (FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch).completed ++
            [(FollowerDownMeasurability.decoderBatchOfCode loggedCode.downBatch).pending ++
              [⟨(ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                    record.input i).1,
                (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]]⟩ := by
    simpa [hbatchCode, ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
      hcallTime] using hdecoded
  change ∃ call logged cut,
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.1 =
        some call ∧
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.2.1 =
        some logged ∧
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.2.2.2 =
        some cut ∧
      call.1 = (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).1 ∧
      cut.2.2.1.isSome = true ∧
      0 < (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.1).val.val ∧
      (FollowerDownMeasurability.decoderBatchOfCode logged.downBatch).pending.length + 1 =
        AffineBatchDecoder.quota p ∧
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank call logged =
        ({ pending := [], completed :=
          (FollowerDownMeasurability.decoderBatchOfCode logged.downBatch).completed ++
            [(FollowerDownMeasurability.decoderBatchOfCode logged.downBatch).pending ++
              [⟨(ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                    record.input i).1,
                (ReferenceDownCompletedAmbiguityMeasurability.decodeCall call).2.sample⟩]] } :
          AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
  refine ⟨callCode, loggedCode, cutCode, hcallCode, hloggedCode, hcutCode,
      htimeCode, hcutComparison, hpositiveGrid, hquotaCode, hdecodedCode⟩

private theorem completed_implies_executed_test
    (round : ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate round) :
    (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round).isSome = true := by
  unfold ReferenceGeneratedDownBatchCalendar.completedBatchAtRound at hcomplete
  dsimp only at hcomplete
  obtain ⟨call, logged, cut, hcall, hlogged, hcut, htime, hcomparison, hpositive,
    hquota, hreset⟩ := hcomplete
  unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound
  dsimp only
  simp [hcall, hcut, hpositive, hcomparison]

private theorem completion_count_of_residual
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T - s)
    (hbelow :
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z n).length <
        AffineBatchDecoder.quota p -
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
            rate rewards C_star C_h s hs z i).downBatch.pending.length)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨n, hn⟩)) :
    (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z n).length =
      AffineBatchDecoder.quota p -
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.pending.length - 1 := by
  classical
  have htest := completed_implies_executed_test
    ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i z).2 ⟨n, hn⟩) hcomplete
  obtain ⟨record, callCode, loggedCode, cutCode, logged, cut,
      hrecordInput, hcall, hactualCall, hlogged, hcut, hloggedCode, hcutCode,
      hcallTime, hquota, hcomparison, hpositive, hraw, hdecoded⟩ :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_completion_diagnostics
      rate rewards C_star C_h s hs i z n hn hcomplete
  have htestRecord :
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome =
          true := by
    rw [hrecordInput]
    simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using htest
  obtain ⟨loggedFromTest, hloggedFromTest, hbank⟩ :=
    logged_bank_of_record_test rewards C_star C_h s hs z i n hn record hrecordInput hbelow
      htestRecord
  have hloggedEq : logged = loggedFromTest :=
    Option.some.inj (hlogged.symm.trans hloggedFromTest)
  subst loggedFromTest
  have hresidual :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
      rate rewards C_star C_h s hs z i
  rw [hbank] at hquota
  simp only [List.length_append, List.length_map] at hquota
  dsimp only at hresidual
  omega

/-- The actual first postlaunch inherited completion is exactly the residual
number of logged positive tests followed by the current real executed test. -/
theorem generated_inherited_down_first_completion_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T - s) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i).downBatch
    let m0 := B0.pending.length
    let h := AffineBatchDecoder.quota p - m0
    let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z
    (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
      ∀ l (hl : l < k),
        ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)) ↔
    (U k).length = h - 1 ∧
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩)).isSome = true := by
  classical
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let m0 := B0.pending.length
  let h := AffineBatchDecoder.quota p - m0
  let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i z
  have hresidual :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
      rate rewards C_star C_h s hs z i
  have hh : 0 < h := by
    dsimp [h, m0, B0]
    exact hresidual.2
  change
    (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
      ∀ l (hl : l < k),
        ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)) ↔
    (U k).length = h - 1 ∧
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩)).isSome = true
  constructor
  · rintro ⟨hcomplete, hnoEarlier⟩
    have hcurrentTest := completed_implies_executed_test
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) hcomplete
    by_cases hge : h ≤ (U k).length
    · obtain ⟨j, hj, hthreshold, htest⟩ :=
        generatedInheritedDownTests_threshold rewards C_star C_h s hs z i h hh
          (n := k) (by omega) hge
      have hcompletedEarlier := completed_of_residual_test rewards C_star C_h s hs z i j
        (by omega) (by simpa [U, h, B0, m0] using hthreshold) htest
      exact False.elim (hnoEarlier j hj hcompletedEarlier)
    · have hbelow : (U k).length < h := Nat.lt_of_not_ge hge
      have hcount := completion_count_of_residual rewards C_star C_h s hs z i k hk
        (by simpa [U, h, B0, m0] using hbelow) hcomplete
      exact ⟨by simpa [U, h, B0, m0] using hcount, hcurrentTest⟩
  · rintro ⟨hcount, hcurrentTest⟩
    have hbelow : (U k).length < h := by omega
    have hcount' :
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z k).length =
          AffineBatchDecoder.quota p -
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
              rate rewards C_star C_h s hs z i).downBatch.pending.length - 1 := by
      simpa [U, h, B0, m0] using hcount
    have hcomplete := completed_of_residual_test rewards C_star C_h s hs z i k hk
      hcount' hcurrentTest
    have hnoEarlier : ∀ l (hl : l < k),
        ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩) := by
      intro l hl hcompleteL
      have hmono := generatedInheritedDownTests_length_mono rewards C_star C_h s hs z i
        (n := l) (m := k) (by omega) (by omega) (by omega)
      have hmono' : (U l).length ≤ (U k).length := by simpa [U] using hmono
      have hbelowL : (U l).length < h := by omega
      have hcountL := completion_count_of_residual rewards C_star C_h s hs z i l
        (lt_trans hl hk) (by simpa [U, h, B0, m0] using hbelowL) hcompleteL
      have hcountL' : (U l).length = h - 1 := by
        simpa [h, B0, m0] using hcountL
      have htestL := completed_implies_executed_test
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩) hcompleteL
      have hsuccessor := generatedInheritedDownTests_succ rewards C_star C_h s hs z i l
        (lt_trans hl hk)
      have hcountSuccessor : (U (l + 1)).length = h := by
        have hsuccessor' : U (l + 1) = U l ++
            (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)).toList := by
          simpa [U] using hsuccessor
        rw [hsuccessor']
        cases htestOption : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩) with
        | none => simp [htestOption] at htestL
        | some test =>
            simp only [Option.toList_some, List.length_append,
              List.length_singleton]
            rw [hcountL']
            dsimp only at hresidual
            omega
      have hmonoAfter := generatedInheritedDownTests_length_mono rewards C_star C_h s hs z i
        (n := l + 1) (m := k) (by omega) (by omega) (by omega)
      have hmonoAfter' : (U (l + 1)).length ≤ (U k).length := by
        simpa [U] using hmonoAfter
      omega
    exact ⟨hcomplete, hnoEarlier⟩

private theorem filterMap_prefix {α β : Type*} {left right : List α}
    (hprefix : left <+: right) (f : α → Option β) :
    left.filterMap f <+: right.filterMap f := by
  rcases hprefix with ⟨tail, rfl⟩
  refine ⟨tail.filterMap f, ?_⟩
  rw [← List.filterMap_append]

private theorem take_eq_of_prefix_length {α : Type*}
    {left right : List α} {n : ℕ}
    (hprefix : left <+: right) (hlen : left.length = n) :
    right.take n = left := by
  rcases hprefix with ⟨tail, rfl⟩
  subst n
  simp

private theorem generatedInheritedDownNewFirstTests_eq_at_first
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T - s)
    (h : ℕ) (hh : 0 < h)
    (hdef : h = AffineBatchDecoder.quota p -
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
        rate rewards C_star C_h s hs z i).downBatch.pending.length)
    (hcount :
      (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
        rate rewards C_star C_h s hs i z k).length = h - 1)
    (htest : (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩)).isSome = true) :
    ∃ test,
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) = some test ∧
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
        rate rewards C_star C_h s hs i z =
        ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s hs i z k ++ [test] := by
  classical
  let rounds := List.ofFn
    (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i z).2
  let tests := fun n =>
    ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z n
  cases hcurrent : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) with
  | none =>
      have : False := by simp [hcurrent] at htest
      exact this.elim
  | some test =>
      have hsucc := generatedInheritedDownTests_succ rewards C_star C_h s hs z i k hk
      have hsucc' : tests (k + 1) = tests k ++ [test] := by
        simpa [hcurrent] using hsucc
      have hcount' : (tests k).length = h - 1 := by
        simpa [tests] using hcount
      have hlen : (tests (k + 1)).length = h := by
        rw [hsucc']
        simp only [List.length_append, List.length_singleton]
        rw [hcount']
        omega
      have htake : rounds.take (k + 1) <+: rounds.take (p.T - s) := by
        exact (List.take_isPrefix_take).2 (Or.inl (by omega))
      have hprefix' : tests (k + 1) <+:
          ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i z (p.T - s) := by
        dsimp [tests, ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests]
        exact filterMap_prefix htake _
      have hprefix'' : tests k ++ [test] <+:
          ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i z (p.T - s) := by
        rw [← hsucc']
        exact hprefix'
      have htake := take_eq_of_prefix_length hprefix'' (by simpa [hsucc'] using hlen)
      refine ⟨test, ?_, ?_⟩
      · rfl
      · unfold ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
        rw [← hdef]
        simpa [tests] using htake

/-- A completed inherited cohort exists in the finite physical suffix exactly
when it has enough actual executed tests. If the threshold is not reached, the
uncompleted bank is allowed to be abandoned on the actual dagger path. -/
theorem generated_inherited_down_first_completion_exists_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (z : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs z i).downBatch
    let m0 := B0.pending.length
    let h := AffineBatchDecoder.quota p - m0
    let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i z;
    (∃ k, ∃ hk : k < p.T - s,
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
        ∀ l (hl : l < k),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)) ↔
    h ≤ (U (p.T - s)).length := by
  classical
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let m0 := B0.pending.length
  let h := AffineBatchDecoder.quota p - m0
  let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i z
  have hresidual :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
      rate rewards C_star C_h s hs z i
  have hh : 0 < h := by
    dsimp [h, m0, B0]
    exact hresidual.2
  change
    (∃ k, ∃ hk : k < p.T - s,
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) ∧
        ∀ l (hl : l < k),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i z).2 ⟨l, lt_trans hl hk⟩)) ↔
    h ≤ (U (p.T - s)).length
  constructor
  · rintro ⟨k, hk, hfirst⟩
    have hcharacter := (generated_inherited_down_first_completion_iff
      rewards C_star C_h s hs z i k hk).1 hfirst
    have hsuccessor := generatedInheritedDownTests_succ rewards C_star C_h s hs z i k hk
    have hsuccessor' : U (k + 1) = U k ++
        (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩)).toList := by
      simpa [U] using hsuccessor
    have hcountSuccessor : (U (k + 1)).length = h := by
      rw [hsuccessor']
      cases hcurrent : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i z).2 ⟨k, hk⟩) with
      | none => simp [hcurrent] at hcharacter
      | some test =>
          have hlen : (U k).length = h - 1 := by
            simpa [U, h, B0, m0] using hcharacter.1
          simp only [List.length_append]
          rw [hlen]
          exact Nat.sub_add_cancel (by omega : 1 ≤ h)
    have hmono := generatedInheritedDownTests_length_mono rewards C_star C_h s hs z i
      (n := k + 1) (m := p.T - s) (by omega) (by omega) (by omega)
    have hmono' : (U (k + 1)).length ≤ (U (p.T - s)).length := by
      simpa [U] using hmono
    omega
  · intro hcount
    obtain ⟨k, hk, hthreshold, htest⟩ :=
      generatedInheritedDownTests_threshold rewards C_star C_h s hs z i h hh
        (n := p.T - s) (by omega) (by simpa [U] using hcount)
    have hcharacter := (generated_inherited_down_first_completion_iff
      rewards C_star C_h s hs z i k hk).2
      ⟨by simpa [U, h, B0, m0] using hthreshold, htest⟩
    exact ⟨k, hk, hcharacter.1, hcharacter.2⟩

/-- At the produced first completion, the same physical call and full cut retain
the inherited bank followed by the first `h` actual postlaunch tests. The
decoder reset uses its literal quota transition, independent of raw parsing,
comparison truth, acceptance, or later recovery success. -/
theorem generated_inherited_down_first_completion_bank
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
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.pending ++
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
          rate rewards C_star C_h s hs i z).map
            ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := by
  classical
  have hcharacter := (generated_inherited_down_first_completion_iff
    rewards C_star C_h s hs z i k hk).1 hfirst
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs z i).downBatch
  let m0 := B0.pending.length
  let h := AffineBatchDecoder.quota p - m0
  let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i z
  have hresidual :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
      rate rewards C_star C_h s hs z i
  have hh : 0 < h := by
    dsimp [h, m0, B0]
    exact hresidual.2
  have hcount : (U k).length = h - 1 := by
    simpa [U, h, B0, m0] using hcharacter.1
  have hbelow : (U k).length < h := by omega
  obtain ⟨record, callCode, loggedCode, cutCode, logged, cut,
      hrecordInput, hcall, hactualCall, hlogged, hcut, hloggedCode, hcutCode,
      hcallTime, hquota, hcomparison, hpositive, hraw, hdecoded⟩ :=
    ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_completion_diagnostics
      rate rewards C_star C_h s hs i z k hk hfirst.1
  have hdecodedLoggedCode := hdecoded
  rw [hloggedCode] at hdecodedLoggedCode
  have htest := hcharacter.2
  have htestRecord :
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome =
          true := by
    rw [hrecordInput]
    simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using htest
  obtain ⟨loggedFromTest, hloggedFromTest, hbank⟩ :=
    logged_bank_of_record_test rewards C_star C_h s hs z i k hk record hrecordInput
      (by simpa [U, h, B0, m0] using hbelow) htestRecord
  have hloggedEq : logged = loggedFromTest :=
    Option.some.inj (hlogged.symm.trans hloggedFromTest)
  subst loggedFromTest
  have hpending : logged.downBatch.pending = B0.pending ++
      (U k).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := by
    have h := congrArg (fun bank : AffineBatchDecoder.State p.T
        (AffineBatchDecoder.width p) => bank.pending) hbank
    simpa [U, B0] using h
  have hcompleted : logged.downBatch.completed = B0.completed := by
    have h := congrArg (fun bank : AffineBatchDecoder.State p.T
        (AffineBatchDecoder.width p) => bank.completed) hbank
    simpa [B0] using h
  obtain ⟨test, htestSome, hcohort⟩ :=
    generatedInheritedDownNewFirstTests_eq_at_first rewards C_star C_h s hs z i k hk h hh
      (by rfl) (by simpa [U, h, B0, m0] using hcount) htest
  obtain ⟨callCodeFromTest, cutCodeFromTest, loggedFromTest', _, hcallRound, hcutRound, hloggedAgain,
      _, _, _, _, _, hpositiveGrid, _, _⟩ := record_test_data record i htestRecord
  have hloggedAgainEq : loggedFromTest' = logged :=
    Option.some.inj (hloggedAgain.symm.trans hlogged)
  subst loggedFromTest'
  have hcallCodeEq : callCodeFromTest = callCode := by
    have hcallA :
        ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
          some callCodeFromTest := by exact hcallRound
    exact Option.some.inj (hcallA.symm.trans hcall)
  subst callCodeFromTest
  have hcutCodeEq : cutCodeFromTest = cutCode := by
    have hcutA :
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.2.2.2.2 = some cutCodeFromTest := hcutRound
    have hcutB :
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.2.2.2.2 = some cutCode := by
      rw [roundDownObservation_diagnostics_eq_actual record i]
      simp only [hcut, Option.map_some]
      exact congrArg some hcutCode
    exact Option.some.inj (hcutA.symm.trans hcutB)
  subst cutCodeFromTest
  have htestRecordSome :
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test := by
    rw [hrecordInput]
    simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
      ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using htestSome
  have hcodeComparison : cutCode.2.2.1.isSome = true := by
    have hfields := congrArg
      (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
        fields.2.2.1.isSome) hcutCode
    exact hfields.symm.trans hcomparison
  have htestShape :
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some ⟨callCode.1, (ReferenceDownCompletedAmbiguityMeasurability.decodeCall
          callCode).2.sample, cutCode.2.1⟩ := by
    unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound
    simp [ReferenceDownCompletedAmbiguityMeasurability.decodeCall,
      hcallRound, hcutRound, hcutCodeEq, hpositiveGrid, hcodeComparison]
  have htestEq : test =
      ⟨callCode.1, (ReferenceDownCompletedAmbiguityMeasurability.decodeCall
        callCode).2.sample, cutCode.2.1⟩ :=
    Option.some.inj (htestRecordSome.symm.trans htestShape)
  have htestEntry :
      ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry test =
        ⟨record.input.time,
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩ := by
    rw [htestEq]
    simp [ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry,
      ReferenceDownCompletedAmbiguityMeasurability.decodeCall, hcallTime]
  have hbatchLength :
      (logged.downBatch.pending ++
        [({ time := record.input.time,
            sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
          AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))]).length =
        AffineBatchDecoder.quota p := by
    simpa only [List.length_append, List.length_singleton] using hquota
  have hjoin :
      logged.downBatch.pending ++
        [({ time := record.input.time,
            sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
          AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))] =
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h s hs z i).downBatch.pending ++
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
          rate rewards C_star C_h s hs i z).map
            ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := by
    calc
      _ = B0.pending ++
          (U k).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry ++
            [({ time := record.input.time,
                sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample } :
              AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))] := by
            rw [hpending]
      _ = B0.pending ++
          ((U k).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry ++
            [ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry test]) := by
            rw [htestEntry, List.append_assoc]
      _ = B0.pending ++
          ((U k ++ [test]).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry) := by
            rw [List.map_append]
            rfl
      _ = B0.pending ++
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownNewFirstTests
            rate rewards C_star C_h s hs i z).map
              ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry := by
            rw [← hcohort]
  refine ⟨record, callCode, loggedCode, cutCode, logged, cut,
    hrecordInput, hcall, hactualCall, hlogged, hcut, hloggedCode, hcutCode,
    hcallTime, hquota, hcomparison, hpositive, hraw, hdecodedLoggedCode,
    ?_, ?_, hbatchLength, hjoin⟩
  · simpa [B0] using hpending
  · simpa [B0] using hcompleted

end Bandits.Support.ReferenceGeneratedInheritedDownFirstCompletion

end
