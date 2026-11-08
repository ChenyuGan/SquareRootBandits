/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownLatestResetPrefix

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Take

/-!
# Actual generated DOWN completion interval and test census

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:111-157`.

The results retain the actual launch source, the same physical run, its full
receiver bank, and the original records and samples. They establish no detector,
probability, stopped-event coverage, or regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceExecutedDownBankRecurrence
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceGeneratedDownBatchBankBridge
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedDownPrefixList
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion

namespace Bandits.Support.ReferenceGeneratedDownCompletionTestInterval

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem filterMap_prefix_witness {α β : Type*} (f : α → Option β)
    (xs : List α) (q : ℕ) (hq : q < (xs.filterMap f).length) :
    ∃ before record after value,
      xs = before ++ record :: after ∧
      (before.filterMap f).length = q ∧ f record = some value := by
  induction xs generalizing q with
  | nil => simp at hq
  | cons head tail ih =>
      cases hf : f head with
      | none =>
          have hq' : q < (tail.filterMap f).length := by simpa [hf] using hq
          obtain ⟨before, record, after, value, hsplit, hlength, hrecord⟩ := ih q hq'
          refine ⟨head :: before, record, after, value, ?_, ?_, hrecord⟩
          · simp [hsplit]
          · simp [hf, hlength]
      | some value =>
          cases q with
          | zero => exact ⟨[], head, tail, value, rfl, by simp, hf⟩
          | succ q =>
              have hq' : q < (tail.filterMap f).length := by
                simpa [hf] using hq
              obtain ⟨before, record, after, value', hsplit, hlength, hrecord⟩ := ih q hq'
              refine ⟨head :: before, record, after, value', ?_, ?_, hrecord⟩
              · simp [hsplit]
              · simp [hf, hlength]

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
  cases hc : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hc]
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hc]
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).result with
      | error failure => rfl
      | ok post =>
          dsimp only
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem record_down_some_logged
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
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
            simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, hl,
              reduceCtorEq] at hd
        | ok logged =>
            refine ⟨logged, ?_⟩
            have he := congrArg Prod.fst hp
            dsimp only at he
            rw [he]
            simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, hl]
      · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hs,
          reduceCtorEq] at hd

private theorem record_logged_choice
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogged : (record.output.followers i).downInput = some logged) :
    ∃ state memory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary state memory ∧ state.status = .unoccupied ∧
      logged.status = state.status ∧ logged.downBatch = state.downBatch := by
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
    simpa only [prepared, observation, ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
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
                | ok next =>
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
      · cases hrecord : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
            prepared.follower prepared.row prepared.activation prepared.time prepared.active
            prepared.arm observation state with
        | error failure =>
            simp [ReferenceActivePhysicalStep.finishFollower,
              ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
              hrecord] at hfinish
        | ok post =>
            cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                prepared.follower prepared.row prepared.time observation state memory post with
            | error failure =>
                simp [ReferenceActivePhysicalStep.finishFollower,
                  ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                  hrecord, hrelease] at hfinish
            | ok next =>
                simp [ReferenceActivePhysicalStep.finishFollower,
                  ReferenceActivePhysicalStep.recordFollower, hconfiguration, hstatus,
                  hrecord, hrelease] at hfinish

private theorem preparedOwnObservation_eq_grid
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) :
    ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
  have hg := congrFun
    (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).2.2.2
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  change ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
    record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) at hg
  rw [hg]
  exact record.output.preparation.feedback.observations_eq _

private theorem executedTest_diagnostics
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test) :
    ∃ callCode logged cut,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
        some callCode ∧
      ReferenceFollowerDownDecoderReplay.actualDownCall i record =
        some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧ cut.rawComparison.isSome = true ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val ∧
      test.time = record.input.time ∧
      test.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
      test.sent = cut.expectedWord ∧
      AffineBatchDecoder.eligible
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 := by
  classical
  have htest0 := htest
  have hd := ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
    record i
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
            have hcomparison : cut.rawComparison.isSome = true := hpositive.2
            have hp : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                record i).val.val := by
              rw [preparedOwnObservation_eq_grid]
              exact hpositive.1
            have hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation
                i record = some callCode := hc
            obtain ⟨heq, hexpected, hactual, heligible⟩ :=
              ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
                record i callCode logged cut hcall hlogged hcut hcomparison hp
            have hcanonical := Option.some.inj (heq.symm.trans htest0)
            have hsent : test.sent = cut.expectedWord := by
              have hs := congrArg
                (fun value : ReferenceGeneratedDownBatchCalendar.ExecutedTest p => value.sent)
                hcanonical
              exact hs.symm
            have htestSample : test.sample =
                (record.input.row.2 record.input.time).2 (0, i) := by
              have hs := congrArg
                (fun value : ReferenceGeneratedDownBatchCalendar.ExecutedTest p => value.sample)
                hcanonical
              simpa using hs.symm
            have htime0 :=
              ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields record i _ hactual
            have hactual' : ReferenceFollowerDownDecoderReplay.actualDownCall i record =
                some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
              exact hactual
            rcases htime0 with ⟨htime, _hcallSample, _⟩
            exact ⟨callCode, logged, cut, rfl, hactual', hlogged, rfl, hcomparison, hp,
              by simp only [hcanonical.symm],
              htestSample, hsent, heligible⟩
          next hnegative => cases htest

private theorem logged_positive_current_eligible
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
    AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged) := by
  classical
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hgateEq := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged
  have hcomparison' :
      Option.isSome ((ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).rawComparison) = true := by
    rw [← hcutActual]
    exact hcomparison
  rw [hgateEq] at hcomparison'
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i record.input.row
      record.input.time logged := of_decide_eq_true hcomparison'
  exact (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i record.input.row
    record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
    rate logged).2 ⟨hgate.1, hgate.2.1, hpositive⟩

private theorem runOfInput_records_take
    (s : ℕ) (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s)
    (b c : ℕ) (hbc : b ≤ c) (hc : s + c ≤ p.T) :
    (ReferenceActiveHorizonMeasurability.runOfInput s c hc input).records.take b =
      (ReferenceActiveHorizonMeasurability.runOfInput s b (by omega) input).records := by
  rw [ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn s c hc input,
    ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn s b (by omega) input]
  rw [← Fin.ofFn_take_eq_take_ofFn hbc]
  apply List.ofFn_inj.mpr
  funext k
  simp [Fin.take]

/-- In a later-completion interval, every positive test through the detecting
round belongs to the one actual fresh batch. The entire test list retains its
original physical record, call diagnostics, sample and sent word. -/
theorem generated_down_completion_test_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n)) :
    let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x
    let R := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x
    let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
    let Q := AffineBatchDecoder.quota p
    let Comp := fun k : Fin (p.T - s) =>
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k)
    let P := fun k : Fin (p.T - s) =>
      ReferenceActiveHorizonMeasurability.runOfInput s k.val (by omega) Y
    let Rk := fun k : Fin (p.T - s) =>
      (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y,
        ReferenceActivePhysicalStep.step
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) Y), rfl⟩ :
        ReferenceFollowerDownDecoderReplay.Record p rate)
    let Tests := fun (a b : ℕ) =>
      ((R.records.take b).drop a).filterMap (fun record =>
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))
    (∀ k : Fin (p.T - s), k < n → ¬ Comp k) ∨
    ∃ m : Fin (p.T - s),
      ∃ hmn : m < n,
      Comp m ∧
      (∀ k : Fin (p.T - s), k < n → Comp k → k ≤ m) ∧
      (∀ k : Fin (p.T - s), m < k → k < n → ¬ Comp k) ∧
      (∀ m' : Fin (p.T - s), m' < n → Comp m' →
        (∀ k : Fin (p.T - s), k < n → Comp k → k ≤ m') → m' = m) ∧
      (let a := m.val + 1
       let alpha := s + a
       s < alpha ∧ alpha ≤ s + n.val ∧ alpha < p.T ∧
       ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
         rate rewards C_star C_h s hs i alpha (by
           omega) (by
           have hsT : s ≤ p.T := Nat.le_of_lt hs
           have hspan : s + (p.T - s) = p.T := Nat.add_sub_of_le hsT
           omega) x ∧
       ∃ stateA memoryA callCodeM loggedM cutM,
         (P ⟨a, by
           omega⟩).finalState.followers i = .ordinary stateA memoryA ∧
         stateA.downBatch.pending = [] ∧
         ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk m) =
           some callCodeM ∧
         ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk m) =
           some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeM) ∧
         ((Rk m).output.followers i).downInput = some loggedM ∧
         ((Rk m).output.followers i).down = some cutM ∧
         cutM.rawComparison.isSome = true ∧
         0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk m) i).val.val ∧
         loggedM.downBatch.pending.length + 1 = Q ∧
         (let Bm := loggedM.downBatch.pending ++
           [⟨(Rk m).input.time,
             (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeM).2.sample⟩]
          Bm.length = Q ∧ cutM.raw = AffineBatchDecoder.batchOutput Bm ∧
          stateA.downBatch.completed = loggedM.downBatch.completed ++ [Bm] ∧
          stateA.downBatch = ⟨[], loggedM.downBatch.completed ++ [Bm]⟩) ∧
         ∃ stateN memoryN callCodeN loggedN cutN tn,
           (P n).finalState.followers i = .ordinary stateN memoryN ∧
           stateN.downBatch.completed = stateA.downBatch.completed ∧
           stateN.downBatch.pending =
             (Tests a n.val).map ReferenceGeneratedDownPrefixList.stampedTest ∧
           loggedN.downBatch = stateN.downBatch ∧
           (Tests a n.val).length = Q - 1 ∧
           ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk n) =
             some callCodeN ∧
           ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk n) =
             some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN) ∧
           ((Rk n).output.followers i).downInput = some loggedN ∧
           ((Rk n).output.followers i).down = some cutN ∧
           cutN.rawComparison.isSome = true ∧
           0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (Rk n) i).val.val ∧
           loggedN.downBatch.pending.length + 1 = Q ∧
           ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 n) = some tn ∧
           (let Bn := loggedN.downBatch.pending ++
             [⟨(Rk n).input.time,
               (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩]
            ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
              rate rewards C_star C_h s hs i alpha x = Tests a n.val ++ [tn] ∧
            Tests a n.val ++ [tn] = Tests a (n.val + 1) ∧
            (Tests a (n.val + 1)).length = Q ∧
            Bn = (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
              rate rewards C_star C_h s hs i alpha x).map
                ReferenceGeneratedDownPrefixList.stampedTest ∧
            cutN.raw = AffineBatchDecoder.batchOutput Bn ∧
            (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
              rate rewards C_star C_h s hs i alpha x).Pairwise
                (fun earlier later => earlier.time.val < later.time.val) ∧
            ∀ test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                rate rewards C_star C_h s hs i alpha x,
              ∃ k : Fin (p.T - s),
                a ≤ k.val ∧ k.val ≤ n.val ∧
                ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (O.2 k) =
                  some test ∧
                test.time = (Rk k).input.time ∧
                test.sample = ((Rk k).input.row.2 (Rk k).input.time).2 (0, i) ∧
                test.sent = ReferenceActiveAffinePositiveTest.downSent (Rk k).input ∧
                ∃ callCode logged cut,
                  ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (Rk k) =
                    some callCode ∧
                  ReferenceFollowerDownDecoderReplay.actualDownCall i (Rk k) =
                    some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
                  ((Rk k).output.followers i).downInput = some logged ∧
                  ((Rk k).output.followers i).down = some cut ∧
                  cut.rawComparison.isSome = true ∧
                  0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                    (Rk k) i).val.val ∧
                  test.sent = cut.expectedWord)) := by
  classical
  dsimp only
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let fullRun := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  let observation := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  let complete := fun k : Fin (p.T - s) =>
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (observation.2 k)
  let quota := AffineBatchDecoder.quota p
  let ordinaryPrefix := fun k : Fin (p.T - s) =>
    ReferenceActiveHorizonMeasurability.runOfInput s k.val (by omega) input
  let record := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input), rfl⟩ :
      ReferenceFollowerDownDecoderReplay.Record p rate)
  let tests := fun (a b : ℕ) =>
    ((fullRun.records.take b).drop a).filterMap (fun current =>
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))
  have hlatest := ReferenceGeneratedDownLatestResetPrefix.generated_down_latest_reset_prefix
    rate rewards C_star C_h s hs x i n hcomplete
  rcases hlatest with hfirst | ⟨m, hmn, hcompm, hgreat, hnoMid, hunique, hreset⟩
  · exact Or.inl (by simpa [complete, observation] using hfirst)
  · rcases hreset with ⟨halpha, halphaN, halphaT, stateA, memoryA,
      callCodeM, loggedM, cutM, hordA, hresetA, hcallM, hactualM, hloggedM,
      hcutM, hcomparisonM, hpositiveM, hquotaM, hbatchM⟩
    rcases hbatchM with ⟨hbatchLengthM, hrawM, hcompletedM, hwholeBankM⟩
    let a := m.val + 1
    let alpha := s + a
    let indexA : Fin (p.T - s) := ⟨a, by omega⟩
    have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart input.val.1 s := input.property
    have hseed : ReferenceFollowerDecoderChronology.downBatchSeed input.val.1 s := by
      change ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x) s
      exact (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
        rate rewards C_star C_h s hs x).2.2
    let runN := ReferenceActiveHorizonMeasurability.runOfInput s n.val (by omega) input
    let runN1 := ReferenceActiveHorizonMeasurability.runOfInput s (n.val + 1) (by omega) input
    have hprefixN : fullRun.records.take n.val = runN.records := by
      simpa [fullRun, runN, input, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using
        runOfInput_records_take s input n.val (p.T - s) (by omega) (by omega)
    have hprefixN1 : fullRun.records.take (n.val + 1) = runN1.records := by
      simpa [fullRun, runN1, input, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using
        runOfInput_records_take s input (n.val + 1) (p.T - s) (by omega) (by omega)
    have hrunNLength : runN.records.length = n.val := by
      simpa [runN, ReferenceActiveHorizonMeasurability.runOfInput] using
        ReferenceActivePhysicalHorizon.run_record_count
          input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n.val
          (by omega) hmode
    have htestsRunN1 : tests a (n.val + 1) =
        (runN1.records.drop a).filterMap (fun current =>
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) := by
      simp [tests, hprefixN1]
    have hordinaryPrefix :=
      ReferenceGeneratedDownLatestResetPrefix.generated_completion_prefix_ordinary
        rate rewards C_star C_h s hs x i n hcomplete
    obtain ⟨stateN, memoryN, hstateN⟩ := hordinaryPrefix n.val (Nat.le_refl _)
    have hordinaryN : runN.finalState.followers i = .ordinary stateN memoryN := by
      simpa [runN, ordinaryPrefix, ReferenceActiveHorizonMeasurability.runOfInput] using hstateN
    have hordinaryA :
        (ReferenceActiveHorizonMeasurability.runOfInput s a (by omega) input).finalState.followers i =
          .ordinary stateA memoryA := by
      simpa [input, ordinaryPrefix, ReferenceActiveHorizonMeasurability.runOfInput] using hordA
    have hspecA := ReferenceFollowerDecoderChronology.run_downBatch_spec
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s a (by omega)
      hmode hseed i stateA memoryA hordinaryA
    have hspecN := ReferenceFollowerDecoderChronology.run_downBatch_spec
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n.val (by omega)
      hmode hseed i stateN memoryN
      (by simpa [runN, ReferenceActiveHorizonMeasurability.runOfInput] using hordinaryN)
    have htestsRun : tests a n.val =
        ((runN.records.drop a).filterMap (fun current =>
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              current.input i))) := by
      simp only [tests, ← hprefixN]
    have htestsMap : (tests a n.val).map ReferenceGeneratedDownPrefixList.stampedTest =
        ReferenceFollowerDownDecoderReplay.actualDownPositives i (runN.records.drop a) := by
      rw [htestsRun]
      simpa [runN, ReferenceActiveHorizonMeasurability.runOfInput] using
        ReferenceGeneratedDownPrefixList.run_executedTests_map_eq_actualDownPositives
          input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n.val (by omega)
          hmode i stateN memoryN
          (by simpa [runN, ReferenceActiveHorizonMeasurability.runOfInput] using hordinaryN) a
    have hsmall : (tests a n.val).length < quota := by
      by_contra hsmall
      have hge : quota ≤ (tests a n.val).length := by omega
      have hqpos := AffineBatchDecoder.quota_pos p
      have hqindex : quota - 1 <
          ((runN.records.drop a).filterMap (fun current =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                current.input i))).length := by
        rw [← htestsRun]
        omega
      obtain ⟨before, current, after, currentTest, hsplit, hbeforeCount, hcurrent⟩ :=
        filterMap_prefix_witness
          (fun current => ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              current.input i))
          (runN.records.drop a) (quota - 1) hqindex
      let jval := a + before.length
      have hjltN : jval < n.val := by
        have hdecompLength := congrArg List.length hsplit
        have hdropLength : (runN.records.drop a).length = n.val - a := by
          simp [List.length_drop, hrunNLength]
        simp only [List.length_append, List.length_cons] at hdecompLength
        omega
      have hjfull : jval < p.T - s := by omega
      let j : Fin (p.T - s) := ⟨jval, hjfull⟩
      have hjltRunN : jval < runN.records.length := by
        rw [hrunNLength]
        exact hjltN
      have hcurrentIndex :
          (runN.records.drop a).get ⟨before.length, by
            rw [hsplit]
            simp⟩ = current := by
        simp [hsplit]
      have hcurrentRecord : current = record j := by
        have hrecords :=
          ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn s n.val
            (by omega) input
        have hdropBound : before.length < (runN.records.drop a).length := by
          rw [hsplit]
          simp
        have hdropElem : (runN.records.drop a)[before.length]'hdropBound = current := by
          simpa only [List.get_eq_getElem] using hcurrentIndex
        rw [List.getElem_drop] at hdropElem
        have hgetCurrent : runN.records.get ⟨jval, hjltRunN⟩ = current := by
          simpa only [List.get_eq_getElem, jval] using hdropElem
        have hgetOfFn :
            (List.ofFn (fun k : Fin n.val =>
              (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
                ReferenceActivePhysicalStep.step
                  (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input),
                rfl⟩ : ReferenceFollowerDownDecoderReplay.Record p rate))).get
                ⟨jval, by simpa using hjltN⟩ = current := by
          have htransport := List.get_of_eq hrecords ⟨jval, hjltRunN⟩
          rw [hgetCurrent] at htransport
          exact htransport.symm
        rw [List.get_ofFn] at hgetOfFn
        simpa [record] using hgetOfFn.symm
      have htestAtJ :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              (record j).input i) = some currentTest := by
        rw [← hcurrentRecord]
        exact hcurrent
      let runJ := ReferenceActiveHorizonMeasurability.runOfInput s jval (by omega) input
      have hprefixJ : fullRun.records.take jval = runJ.records := by
        simpa [fullRun, runJ, input, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
          ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using
          runOfInput_records_take s input jval (p.T - s) (by omega) (by omega)
      have hrunJPrefix : runJ.records = runN.records.take jval := by
        calc
          runJ.records = fullRun.records.take jval := hprefixJ.symm
          _ = (fullRun.records.take n.val).take jval := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          _ = runN.records.take jval := by rw [hprefixN]
      have haLe : a ≤ n.val := by omega
      have htakeALength : (runN.records.take a).length = a := by
        rw [List.length_take, Nat.min_eq_left (by rw [hrunNLength]; exact haLe)]
      have hprefixRecords : runN.records.take jval = runN.records.take a ++ before := by
        rw [← List.take_append_drop a runN.records, hsplit]
        simp [List.take_append, jval, htakeALength]
      have hbeforeRecords : runJ.records.drop a = before := by
        rw [hrunJPrefix, hprefixRecords, List.drop_append]
        simp [htakeALength]
      have hordinaryJ : ∃ stateJ memoryJ,
          runJ.finalState.followers i = .ordinary stateJ memoryJ := by
        obtain ⟨stateJ, memoryJ, hstateJ⟩ :=
          hordinaryPrefix j.val (Nat.le_of_lt hjltN)
        exact ⟨stateJ, memoryJ, by
          simpa [runJ, ReferenceActiveHorizonMeasurability.runOfInput] using hstateJ⟩
      have hbeforeTests : tests a j.val = before.filterMap (fun current =>
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              current.input i)) := by
        unfold tests
        rw [hprefixJ, hbeforeRecords]
      have hbeforeMap : (tests a j.val).map ReferenceGeneratedDownPrefixList.stampedTest =
          ReferenceFollowerDownDecoderReplay.actualDownPositives i (runJ.records.drop a) := by
        obtain ⟨stateJ, memoryJ, hstateJ⟩ := hordinaryJ
        have hbridge := ReferenceGeneratedDownPrefixList.run_executedTests_map_eq_actualDownPositives
          input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s j.val (by omega)
          hmode i stateJ memoryJ
          (by simpa [runJ, ReferenceActiveHorizonMeasurability.runOfInput] using hstateJ) a
        have hbeforeRecordsRaw :
            (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
              input.val.2.2.1 input.val.2.2.2 s j.val (by omega) hmode).records.drop a = before := by
          simpa [runJ, ReferenceActiveHorizonMeasurability.runOfInput] using hbeforeRecords
        have hbeforeBridge :
            (before.filterMap (fun current =>
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).map
                ReferenceGeneratedDownPrefixList.stampedTest =
              ReferenceFollowerDownDecoderReplay.actualDownPositives i before := by
          rw [hbeforeRecordsRaw] at hbridge
          exact hbridge
        rw [hbeforeTests]
        calc
          _ = ReferenceFollowerDownDecoderReplay.actualDownPositives i before := hbeforeBridge
          _ = ReferenceFollowerDownDecoderReplay.actualDownPositives i (runJ.records.drop a) :=
            congrArg (ReferenceFollowerDownDecoderReplay.actualDownPositives i) hbeforeRecords.symm
      have hbeforeLength : (tests a j.val).length = quota - 1 := by
        rw [hbeforeTests, hbeforeCount]
      have hsmallJ :
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i (runJ.records.drop a)).length <
            quota := by
        rw [← hbeforeMap, List.length_map, hbeforeLength]
        have hquotaPos := AffineBatchDecoder.quota_pos p
        omega
      obtain ⟨stateJ, memoryJ, hordinaryJ⟩ :=
        hordinaryPrefix j.val (Nat.le_of_lt hjltN)
      have haj : a ≤ j.val := by
        simp [j, jval, a]
      have hjSpan : s + j.val ≤ p.T := by
        have hjn : j.val < n.val := by simpa [j] using hjltN
        omega
      have hresetJ := ReferenceExecutedDownBankRecurrence.run_interval_fresh_downBatch_identity
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s a j.val haj
        hjSpan hmode hseed i stateA memoryA
        (by simpa [ReferenceActiveHorizonMeasurability.runOfInput] using hordA)
        stateJ memoryJ (by simpa [ReferenceActiveHorizonMeasurability.runOfInput] using hordinaryJ)
        hresetA hsmallJ
      have hpriorPending :
          (stateJ.downBatch.pending).length = quota - 1 := by
        have hpending := hresetJ.1.trans hbeforeMap.symm
        rw [hpending, List.length_map, hbeforeLength]
      let jRecord := record j
      obtain ⟨callCodeJ, loggedJ, cutJ, hcallJ, hactualJ, hloggedJ, hcutJ,
        hcomparisonJ, hpositiveJ, _, _, _⟩ :=
        executedTest_diagnostics jRecord i currentTest htestAtJ
      obtain ⟨choiceJ, choiceMemoryJ, hchoiceJ, hstatusJ, hloggedStatusJ,
        hloggedBatchJ⟩ := record_logged_choice jRecord i loggedJ hloggedJ
      have hframeJ := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
        jRecord i stateJ choiceJ memoryJ choiceMemoryJ
        (by
          simpa [jRecord, record, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
            ReferenceActivePhysicalHorizon.roundInputAt,
            ReferenceActiveHorizonMeasurability.runOfInput] using hordinaryJ)
        (by simpa [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hchoiceJ)
        hresetJ.2.2.2.2
      have hloggedBank : loggedJ.downBatch = stateJ.downBatch := by
        rw [hloggedBatchJ, hframeJ.1]
      have hquotaJ : loggedJ.downBatch.pending.length + 1 = quota := by
        rw [hloggedBank, hpriorPending]
        omega
      have hquotaInput : quota ≤
          (loggedJ.downBatch.pending ++ AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i jRecord.input.row
                jRecord.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                  jRecord i) rate loggedJ)) jRecord.input.time).length := by
        simp only [List.length_append]
        have heligibleJ := logged_positive_current_eligible jRecord i loggedJ cutJ
          hloggedJ hcutJ hcomparisonJ hpositiveJ
        have hpositiveAt :
            (AffineBatchDecoder.positiveAt p
              (ActiveFollowerDownAcceptance.currentInputExtension p
                (ActiveFollowerDownAcceptance.currentRoundInput p i jRecord.input.row
                  jRecord.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                    jRecord i) rate loggedJ)) jRecord.input.time).length = 1 := by
          simp [AffineBatchDecoder.positiveAt,
            ActiveFollowerDownAcceptance.currentInputExtension, heligibleJ]
        rw [hpositiveAt]
        omega
      have hcompleteJ :=
        (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
          jRecord i).2 ⟨loggedJ, cutJ, hloggedJ, hcutJ, hcomparisonJ, hquotaInput⟩
      have hjcomp : complete j := by
        simpa [complete, observation, record, jRecord,
          ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
          ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using hcompleteJ
      have hmj : m.val < j.val := by
        simp [j, jval, a]
        omega
      have hjn : j.val < n.val := by simpa [j] using hjltN
      exact (hnoMid j (Fin.lt_def.mpr hmj) (Fin.lt_def.mpr hjn) hjcomp).elim
    have hsmallActual :
        (ReferenceFollowerDownDecoderReplay.actualDownPositives i (runN.records.drop a)).length <
          quota := by
      rw [← htestsMap, List.length_map]
      exact hsmall
    let runA := ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s a (by omega) hmode
    let runNB := ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s n.val (by omega) hmode
    have hbank := ReferenceExecutedDownBankRecurrence.run_interval_fresh_downBatch_identity
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s a n.val (by omega)
      (by omega) hmode hseed i stateA memoryA
      (by simpa [runA, ReferenceActiveHorizonMeasurability.runOfInput] using hordA)
      stateN memoryN (by simpa [runNB, runN, ReferenceActiveHorizonMeasurability.runOfInput]
        using hordinaryN) hresetA hsmallActual
    have htestsMapN :
        (tests a n.val).map ReferenceGeneratedDownPrefixList.stampedTest =
          ReferenceFollowerDownDecoderReplay.actualDownPositives i (runNB.records.drop a) := by
      simpa [tests, runNB, runN, ReferenceActiveHorizonMeasurability.runOfInput] using htestsMap
    have hpendingN : stateN.downBatch.pending =
        (tests a n.val).map ReferenceGeneratedDownPrefixList.stampedTest :=
      hbank.1.trans htestsMapN.symm
    have hloggedNdiag :=
      ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_completion_diagnostics
        rate rewards C_star C_h s hs i x n.val n.isLt hcomplete
    rcases hloggedNdiag with
      ⟨diagRecordN, callCodeN, _loggedCodeN, _cutCodeN, loggedN, cutN, hdiagInputN, hcallN,
        hactualN, hloggedN, hcutN, _hloggedCodeN, _hcutCodeN, htimeN, hquotaN,
        hcomparisonN, hpositiveN, hrawN, _hdecodedN⟩
    have hrecordN : diagRecordN = record n := by
      have hcanonical : diagRecordN =
          ⟨diagRecordN.input, ReferenceActivePhysicalStep.step diagRecordN.input, rfl⟩ := by
        cases diagRecordN with
        | mk diagInput diagOutput diagOutputEq => cases diagOutputEq; rfl
      have hinputEq : diagRecordN.input = (record n).input := by
        simpa [record] using hdiagInputN
      have hcanonicalEq :
          (⟨diagRecordN.input, ReferenceActivePhysicalStep.step diagRecordN.input, rfl⟩ :
            ReferenceFollowerDownDecoderReplay.Record p rate) = record n := by
        exact congrArg (fun roundInput : ReferenceActivePhysicalStep.RoundInput p rate =>
          (⟨roundInput, ReferenceActivePhysicalStep.step roundInput, rfl⟩ :
            ReferenceFollowerDownDecoderReplay.Record p rate)) hinputEq
      exact hcanonical.trans hcanonicalEq
    subst diagRecordN
    have hrecordOutputN : (record n).input.state =
        (ReferenceActiveHorizonMeasurability.runOfInput s n.val (by omega) input).finalState := by
      rfl
    have hchoiceN := record_logged_choice (record n) i loggedN hloggedN
    rcases hchoiceN with ⟨choiceN, choiceMemoryN, hchoiceN, hstatusN,
      hloggedStatusN, hloggedBatchN⟩
    have hframeN := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
      (record n) i stateN choiceN memoryN choiceMemoryN
      (by
        rw [hrecordOutputN]
        exact hordinaryN)
      (by simpa [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hchoiceN)
      hbank.2.2.2.2
    have hloggedBankN : loggedN.downBatch = stateN.downBatch := by
      rw [hloggedBatchN, hframeN.1]
    have hquotaByBank : (tests a n.val).length = quota - 1 := by
      have hlen := congrArg List.length hpendingN
      rw [List.length_map] at hlen
      have hquotaState : stateN.downBatch.pending.length + 1 = quota := by
        rw [← hloggedBankN]
        exact hquotaN
      omega
    have hquotaN' : loggedN.downBatch.pending.length + 1 = quota := by
      simpa [hloggedBankN] using hquotaN
    have htestNRaw :=
      ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
        (record n) i callCodeN loggedN cutN hcallN hloggedN hcutN hcomparisonN hpositiveN
    rcases htestNRaw with ⟨htestN, hsentN, hactualTestN, heligibleN⟩
    have hfieldsN := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      (record n) i _ hactualTestN
    let testN : ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
      ⟨(record n).input.time,
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample,
        cutN.expectedWord⟩
    have htestN' : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (observation.2 n) =
        some testN := by
      simpa [observation, record, testN,
        ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
        ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
        hfieldsN.2.1] using htestN
    have htestsSucc : tests a (n.val + 1) = tests a n.val ++ [testN] := by
      have hrecordsSucc :
          (fullRun.records.take (n.val + 1)).drop a =
            (fullRun.records.take n.val).drop a ++ [record n] := by
        rw [hprefixN1, hprefixN]
        have hsucc := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
          s (n.val + 1) (by omega) input
        have hprev := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
          s n.val (by omega) input
        have hsuccessor : runN1.records = runN.records ++ [record n] := by
          rw [hsucc, hprev, List.ofFn_succ', List.concat_eq_append]
          rfl
        rw [hsuccessor, List.drop_append_of_le_length (by rw [hrunNLength]; omega)]
      have hrecordTest :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              (record n).input i) = some testN := by
        simpa [observation, record,
          ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
          ReferenceDownCompletedAmbiguityMeasurability.runDownObservation] using htestN'
      have hlastTests :
          List.filterMap (fun current : ReferenceFollowerDownDecoderReplay.Record p rate =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))
            [record n] = [testN] := by
        simp [hrecordTest]
      simp only [tests, hrecordsSucc, List.filterMap_append]
      rw [hlastTests]
    have htestsLengthSucc : (tests a (n.val + 1)).length = quota := by
      rw [htestsSucc, List.length_append, List.length_singleton, hquotaByBank]
      omega
    have htestsFull :
        ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
            rate rewards C_star C_h s hs i alpha x = tests a (n.val + 1) := by
      have huncapped := ReferenceGeneratedDownPrefixList.runDownObservation_uncapped_eq_records_drop
        s (p.T - s) (by omega) input i alpha (by omega)
      have hdropSplit : fullRun.records.drop a =
          (fullRun.records.take (n.val + 1)).drop a ++ fullRun.records.drop (n.val + 1) := by
        rw [← List.take_append_drop (n.val + 1) fullRun.records, List.drop_append]
        have hlen : (fullRun.records.take (n.val + 1)).length = n.val + 1 := by
          rw [hprefixN1]
          exact ReferenceActivePhysicalHorizon.run_record_count input.val.1
            input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (n.val + 1) (by omega) hmode
        have haLen : a ≤ n.val + 1 := by omega
        rw [hlen]
        simp [Nat.sub_eq_zero_of_le haLen]
      have hprefixAll :
          (fullRun.records.drop a).filterMap (fun current =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) =
            ((fullRun.records.take (n.val + 1)).drop a).filterMap (fun current =>
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) ++
              (fullRun.records.drop (n.val + 1)).filterMap (fun current =>
                ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                  (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) := by
        rw [hdropSplit, List.filterMap_append]
      have htestsPrefix :
          tests a (n.val + 1) =
            ((List.ofFn observation.2).filterMap (fun round =>
              if alpha ≤ round.1.val then
                ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round else none)).take quota := by
        have huncappedPhys :
            ((List.ofFn observation.2).filterMap (fun round =>
              if alpha ≤ round.1.val then
                ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round else none)) =
            (fullRun.records.drop a).filterMap (fun current =>
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) := by
          simpa [observation, fullRun, input, alpha, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
            ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
            ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
            ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
            ReferenceActiveHorizonMeasurability.runOfInput] using huncapped
        rw [huncappedPhys, hprefixAll]
        have hprefixLength : quota ≤
            (((fullRun.records.take (n.val + 1)).drop a).filterMap (fun current =>
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).length := by
          simpa [tests] using htestsLengthSucc.symm.le
        have hprefixLengthEq :
            (((fullRun.records.take (n.val + 1)).drop a).filterMap (fun current =>
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).length = quota := by
          simpa [tests] using htestsLengthSucc
        rw [List.take_append_of_le_length hprefixLength]
        exact (List.take_of_length_le (by omega :
          (((fullRun.records.take (n.val + 1)).drop a).filterMap (fun current =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).length ≤ quota)).symm
      unfold ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
        ReferenceGeneratedDownBatchCalendar.observedTestsFrom
      simpa [observation] using htestsPrefix.symm
    have htestsLength :
        (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
          rate rewards C_star C_h s hs i alpha x).length = quota := by
      rw [htestsFull, htestsLengthSucc]
    have hbatchEntries :
        loggedN.downBatch.pending ++
          [⟨(record n).input.time,
            (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩] =
        (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
          rate rewards C_star C_h s hs i alpha x).map
            ReferenceGeneratedDownPrefixList.stampedTest := by
      rw [htestsFull, htestsSucc]
      have hpending' : loggedN.downBatch.pending =
          (tests a n.val).map ReferenceGeneratedDownPrefixList.stampedTest := by
        rw [hloggedBankN, hpendingN]
      rw [hpending']
      simp [testN, ReferenceGeneratedDownPrefixList.stampedTest,
        ReferenceDownCompletedAmbiguityMeasurability.decodeCall]
    have hrecordsChron :=
      ReferenceGeneratedDownPrefixList.run_executedTests_chronological
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega)
        hmode i a
    have hgeneratedTake :
        ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
          rate rewards C_star C_h s hs i alpha x =
        ((fullRun.records.drop a).filterMap (fun current =>
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).take quota := by
      have huncapped := ReferenceGeneratedDownPrefixList.runDownObservation_uncapped_eq_records_drop
        s (p.T - s) (by omega) input i alpha (by omega)
      have halphaSub : alpha - s = a := by simp [alpha]
      have huncapped' :
          ((List.ofFn observation.2).filterMap (fun round =>
            if alpha ≤ round.1.val then
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round else none)) =
          (fullRun.records.drop a).filterMap (fun current =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i)) := by
        simpa [observation, fullRun, input, alpha, halphaSub,
          ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
          ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
          ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
          ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
          ReferenceActiveHorizonMeasurability.runOfInput] using huncapped
      unfold ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
        ReferenceGeneratedDownBatchCalendar.observedTestsFrom
      simpa [observation] using congrArg (List.take quota) huncapped'
    have hchronAll :
        ((fullRun.records.drop a).filterMap (fun current =>
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation current.input i))).Pairwise
          (fun earlier later => earlier.time.val < later.time.val) := by
      simpa [fullRun, input, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
        ReferenceActiveHorizonMeasurability.runOfInput] using hrecordsChron
    have hchron :
        (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
          rate rewards C_star C_h s hs i alpha x).Pairwise
            (fun earlier later => earlier.time.val < later.time.val) := by
      rw [hgeneratedTake]
      exact hchronAll.take
    have hprovenance :
        ∀ test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
            rate rewards C_star C_h s hs i alpha x,
          ∃ k : Fin (p.T - s),
            a ≤ k.val ∧ k.val ≤ n.val ∧
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (observation.2 k) =
              some test ∧ test.time = (record k).input.time ∧
            test.sample = ((record k).input.row.2 (record k).input.time).2 (0, i) ∧
            test.sent = ReferenceActiveAffinePositiveTest.downSent (record k).input ∧
            ∃ callCode logged cut,
              ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i (record k) =
                some callCode ∧
              ReferenceFollowerDownDecoderReplay.actualDownCall i (record k) =
                some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
              ((record k).output.followers i).downInput = some logged ∧
              ((record k).output.followers i).down = some cut ∧ cut.rawComparison.isSome = true ∧
              0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (record k) i).val.val ∧
              test.sent = cut.expectedWord := by
      intro test hmem
      rw [htestsFull] at hmem
      have hmemTests : test ∈ tests a (n.val + 1) := hmem
      rw [htestsRunN1] at hmemTests
      have hmemFilter := List.mem_filterMap.mp hmemTests
      rcases hmemFilter with ⟨current, hcurrentMem, hcurrentTest⟩
      have hdropMem : current ∈ (fullRun.records.take (n.val + 1)).drop a := by
        rw [hprefixN1]
        exact hcurrentMem
      have hposition : ∃ k : Fin (n.val + 1),
          current = record ⟨k.val, by omega⟩ := by
        have hcurrentMemRun : current ∈
            (ReferenceActiveHorizonMeasurability.runOfInput s (n.val + 1) (by omega) input).records.drop a := by
          simpa [runN1] using hcurrentMem
        have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
          s (n.val + 1) (by omega) input
        rw [hrecords] at hcurrentMemRun
        obtain ⟨k, hk⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hcurrentMemRun)
        refine ⟨k, ?_⟩
        simpa [record] using hk.symm
      obtain ⟨k0, hk0⟩ := hposition
      let k : Fin (p.T - s) := ⟨k0.val, by omega⟩
      have hkVal : k.val = k0.val := rfl
      have hcurrentRecord : current = record k := by
        simpa [k] using hk0
      have hbounds : a ≤ k.val ∧ k.val ≤ n.val := by
        have htime := ReferenceActivePhysicalHorizon.run_time_values
          input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (n.val + 1)
          (by omega) hmode
        have htimeN1 :
            (runN1.records.map (fun current => current.input.time.val)) =
              ReferenceActivePhysicalHorizon.calendar s (n.val + 1) := by
          simpa [runN1, ReferenceActiveHorizonMeasurability.runOfInput] using htime
        have htimeDrop :
            ((runN1.records.drop a).map (fun current => current.input.time.val)) =
              List.range' (s + a) (n.val + 1 - a) 1 := by
          rw [List.map_drop, htimeN1]
          simp [ReferenceActivePhysicalHorizon.calendar, List.drop_range']
        have hcurrentTimeMem : current.input.time.val ∈
            (runN1.records.drop a).map (fun current => current.input.time.val) :=
          List.mem_map.mpr ⟨current, hcurrentMem, rfl⟩
        rw [htimeDrop] at hcurrentTimeMem
        have htimeLower := List.mem_range'_1.mp hcurrentTimeMem
        have htimeRecord : (record k).input.time.val = s + k.val := by
          simp [record, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
            ReferenceActivePhysicalHorizon.roundInputAt]
        have hposAfterDrop : a ≤ k.val := by
          have htimeCurrent : current.input.time.val = s + k.val := by
            rw [hcurrentRecord]
            exact htimeRecord
          omega
        exact ⟨by rw [← hkVal]; exact hposAfterDrop,
          by have := k0.isLt; omega⟩
      have hroundTest :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              current.input i) = some test := hcurrentTest
      have hroundTest' :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate (observation.2 k) =
            some test := by
        simpa [observation, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
          ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
          record, hcurrentRecord] using hroundTest
      obtain ⟨callCode, logged, cut, hcall, hactual, hlogged, hcut, hcmp, hpositive,
        htime, hsample, hsent, _heligible⟩ :=
        executedTest_diagnostics (record k) i test hroundTest'
      refine ⟨k, hbounds.1, hbounds.2, hroundTest', ?_, ?_, ?_, ?_⟩
      · simpa [hcurrentRecord] using htime
      · simpa [hcurrentRecord] using hsample
      · exact hsent.trans (ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
          (record k) i callCode logged cut hcall hlogged hcut hcmp hpositive).2.1
      · exact ⟨callCode, logged, cut, hcall, hactual, hlogged, hcut, hcmp, hpositive, hsent⟩
    have hboundary : ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
        rate rewards C_star C_h s hs i alpha (by omega) (by omega) x := by
      unfold ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
      dsimp only [alpha, a]
      have hcount : s + (m.val + 1) - s = m.val + 1 := by omega
      have hidxVal : (s + (m.val + 1)) - 1 - s = m.val := by
        have hstep : s + (m.val + 1) - 1 = s + m.val := by omega
        rw [hstep]
        omega
      let hidx : Fin (p.T - s) := ⟨(s + (m.val + 1)) - 1 - s, by
        rw [hidxVal]
        exact m.isLt⟩
      have hidxEq : hidx = m := Fin.ext hidxVal
      refine ⟨?_, ?_⟩
      · simpa [complete, observation, hidxEq] using hcompm
      · refine ⟨stateA, memoryA, ?_⟩
        simpa [hcount, input, ReferenceActiveHorizonMeasurability.runOfInput] using hordA
    refine Or.inr ⟨m, hmn, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [complete, observation] using hcompm
    · simpa [complete, observation] using hgreat
    · simpa [complete, observation] using hnoMid
    · simpa [complete, observation] using hunique
    · refine ⟨halpha, halphaN, halphaT, hboundary,
        stateA, memoryA, callCodeM, loggedM, cutM, ?_, hresetA,
        hcallM, hactualM, hloggedM, hcutM, hcomparisonM, hpositiveM, hquotaM,
        ⟨hbatchLengthM, hrawM, hcompletedM, hwholeBankM⟩,
        stateN, memoryN, callCodeN, loggedN, cutN, testN, ?_, ?_, ?_,
        hloggedBankN, ?_, hcallN, hactualN, hloggedN, hcutN, hcomparisonN,
        hpositiveN, hquotaN', htestN', ?_⟩
      · simpa [ordinaryPrefix, record, ReferenceActiveHorizonMeasurability.runOfInput] using hordA
      · simpa [ordinaryPrefix, runN, ReferenceActiveHorizonMeasurability.runOfInput] using hordinaryN
      · exact hbank.2.1
      · exact hpendingN
      · exact hquotaByBank
      · refine ⟨?_, ?_, ?_, ?_, ?_, hchron, hprovenance⟩
        · exact htestsFull.trans htestsSucc
        · exact htestsSucc.symm
        · exact htestsLengthSucc
        · exact hbatchEntries
        · simpa [record, ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hrawN

end Bandits.Support.ReferenceGeneratedDownCompletionTestInterval

end
