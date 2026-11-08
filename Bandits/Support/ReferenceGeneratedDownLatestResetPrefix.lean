/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownResetCompletionCensus

import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Actual generated DOWN latest completion and reset prefix

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:111-157`.

The exports here concern one existing generated physical run. They prove no
probability estimate, error-event coverage, stopping restriction, or regret
bound.
-/

@[expose] public section

namespace Bandits.Support.ReferenceGeneratedDownLatestResetPrefix

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceFollowerDecoderChronology
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceExecutedDownBankRecurrence
open Bandits.Support.AffineBatchDecoder

variable {p : ConstructorDimensions.Parameters}

/-- An actual completion at `n` identifies an executed test on that same
generated run. The Q-th-test decomposition then proves every incoming
follower prefix through `n` ordinary, including the detecting round's incoming
state even when its next state is a failure. -/
theorem generated_completion_prefix_ordinary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n)) :
    ∀ (k : ℕ) (hk : k ≤ n.val),
      ∃ state memory,
        (ReferenceActiveHorizonMeasurability.runOfInput s k (by omega)
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs x)).finalState.followers i =
          .ordinary state memory := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let observation := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  let record : ReferenceFollowerDownDecoderReplay.Record p rate :=
    ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega) input), rfl⟩
  have hround : observation.2 n =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i := rfl
  have hcompleteRecord := hcomplete
  rw [hround] at hcompleteRecord
  unfold ReferenceGeneratedDownBatchCalendar.completedBatchAtRound at hcompleteRecord
  rcases hcompleteRecord with
    ⟨callCode, logged, cut, hcall, hlogged, hcut, _htime, hcomparison, hpositive,
      _hquota, _hdecoded⟩
  let test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
    ⟨callCode.1, callCode.2.2.2.1, cut.2.1⟩
  have htestRecord : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test := by
    simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound, hcall, hcut,
      hpositive, hcomparison, test]
  have htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (observation.2 n) = some test := by
    simpa only [hround] using htestRecord
  have hspan : s + (p.T - s) ≤ p.T := by omega
  intro k hk
  have htest' : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
        s (p.T - s) hspan i input).2 n) =
        some test := by
    simpa [observation, ReferenceGeneratedDownBatchCalendar.generatedSourceObservation] using htest
  have hordinary := ReferenceGeneratedDownQthDecomposition.executedTest_prefix_ordinary
    s (p.T - s) hspan input i n test htest' k hk
  exact hordinary

/-- Among the actual completions before a completed round, select the greatest
one from the same generated observation. Its ordinary successor is the
physical DOWN reset produced by that very executed quota call. -/
theorem generated_down_latest_reset_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n)) :
    (∀ k : Fin (p.T - s), k < n →
      ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i x).2 k)) ∨
    ∃ m : Fin (p.T - s),
      m < n ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i x).2 m) ∧
      (∀ k : Fin (p.T - s), k < n →
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 k) → k ≤ m) ∧
      (∀ k : Fin (p.T - s), m < k → k < n →
        ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 k)) ∧
      (∀ m' : Fin (p.T - s), m' < n →
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 m') →
        (∀ k : Fin (p.T - s), k < n →
          ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 k) → k ≤ m') →
        m' = m) ∧
      (let a := m.val + 1
       let alpha := s + a
       s < alpha ∧ alpha ≤ s + n.val ∧ alpha < p.T ∧
       ∃ stateA memoryA callCode logged cut,
         (ReferenceActiveHorizonMeasurability.runOfInput s a (by omega)
           (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
             rate rewards C_star C_h s hs x)).finalState.followers i =
           .ordinary stateA memoryA ∧
         stateA.downBatch.pending = [] ∧
         ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i
           (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hs x),
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x)), rfl⟩ :
             ReferenceFollowerDownDecoderReplay.Record p rate) = some callCode ∧
         ReferenceFollowerDownDecoderReplay.actualDownCall i
           (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hs x),
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x)), rfl⟩ :
             ReferenceFollowerDownDecoderReplay.Record p rate) =
           some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) ∧
         ((⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hs x),
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x)), rfl⟩ :
             ReferenceFollowerDownDecoderReplay.Record p rate).output.followers i).downInput =
           some logged ∧
         ((⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hs x),
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x)), rfl⟩ :
             ReferenceFollowerDownDecoderReplay.Record p rate).output.followers i).down =
           some cut ∧
         cut.rawComparison.isSome = true ∧
         0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
           (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                  rate rewards C_star C_h s hs x),
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x)), rfl⟩ :
             ReferenceFollowerDownDecoderReplay.Record p rate) i).val.val ∧
         logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
         (let Bm := logged.downBatch.pending ++
           [⟨(⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                    rate rewards C_star C_h s hs x),
                ReferenceActivePhysicalStep.step
                  (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s m.val (by omega)
                    (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                      rate rewards C_star C_h s hs x)), rfl⟩ :
               ReferenceFollowerDownDecoderReplay.Record p rate).input.time,
             (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample⟩]
          Bm.length = AffineBatchDecoder.quota p ∧
          cut.raw = AffineBatchDecoder.batchOutput Bm ∧
          stateA.downBatch.completed = logged.downBatch.completed ++ [Bm] ∧
          stateA.downBatch = ⟨[], logged.downBatch.completed ++ [Bm]⟩)) := by
  classical
  let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let observation := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  let completed := fun k : Fin (p.T - s) =>
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (observation.2 k)
  let runPrefix := fun (k : ℕ) (hspan : s + k ≤ p.T) =>
    ReferenceActiveHorizonMeasurability.runOfInput s k hspan input
  let record := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input), rfl⟩ :
      ReferenceFollowerDownDecoderReplay.Record p rate)
  let quota := AffineBatchDecoder.quota p
  let earlier : Finset (Fin (p.T - s)) :=
    Finset.univ.filter fun k => k < n ∧ completed k
  have hprefixOrdinary := generated_completion_prefix_ordinary
    rate rewards C_star C_h s hs x i n hcomplete
  by_cases hearlier : earlier.Nonempty
  · let m := earlier.max' hearlier
    have hmMem : m ∈ earlier := Finset.max'_mem earlier hearlier
    have hmData : m < n ∧ completed m := by simpa [earlier] using hmMem
    have hgreat : ∀ k : Fin (p.T - s), k < n → completed k → k ≤ m := by
      intro k hkn hkcomplete
      have hkMem : k ∈ earlier := by
        simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hkn, hkcomplete⟩
      have hmax := Finset.isGreatest_max' earlier hearlier
      exact hmax.2 hkMem
    have hlater : ∀ k : Fin (p.T - s), m < k → k < n → ¬ completed k := by
      intro k hmk hkn hkcomplete
      exact (not_le_of_gt hmk) (hgreat k hkn hkcomplete)
    have hunique : ∀ m' : Fin (p.T - s), m' < n → completed m' →
        (∀ k : Fin (p.T - s), k < n → completed k → k ≤ m') → m' = m := by
      intro m' hm'n hm'complete hm'greatest
      apply le_antisymm
      · exact hgreat m' hm'n hm'complete
      · exact hm'greatest m hmData.1 hmData.2
    have hmnVal : m.val < n.val := Fin.lt_def.mp hmData.1
    obtain ⟨before, memory, hbeforeOrd⟩ := hprefixOrdinary m.val (by omega)
    obtain ⟨stateA, memoryA, hstateAOrd⟩ := hprefixOrdinary (m.val + 1) (by omega)
    have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart input.val.1 s := input.property
    have hseed : ReferenceFollowerDecoderChronology.downBatchSeed input.val.1 s := by
      change ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x) s
      exact (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
        rate rewards C_star C_h s hs x).2.2
    have hordinaryM :
        (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
          input.val.2.2.2 s m.val (by omega) hmode).finalState.followers i =
          .ordinary before memory := by
      simpa [runPrefix, ReferenceActiveHorizonMeasurability.runOfInput] using hbeforeOrd
    have hinput : (record m).input.state.followers i = .ordinary before memory := by
      change (runPrefix m.val (by omega)).finalState.followers i = .ordinary before memory
      exact hbeforeOrd
    have hsucc := ReferenceActivePhysicalHorizon.run_successor_step
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s m.val (by omega) hmode
    have hfold := ReferenceActivePhysicalHorizon.foldRound_equations
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s hmode
      (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
        input.val.2.2.2 s m.val (by omega) hmode)
      ⟨s + m.val, by omega, by omega⟩
    have hrecordNext :
        (runPrefix (m.val + 1) (by omega)).finalState = (record m).output.next := by
      change (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s (m.val + 1) (by omega) hmode).finalState = _
      rw [hsucc]
      simpa [record, runPrefix, ReferenceActiveHorizonMeasurability.runOfInput,
        ReferenceDownCompletedAmbiguityMeasurability.prefixInput] using hfold.1
    have hafter : (record m).output.next.followers i = .ordinary stateA memoryA := by
      rw [← hrecordNext]
      exact hstateAOrd
    have hbatchSpec := ReferenceFollowerDecoderChronology.run_downBatch_spec
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s m.val (by omega)
      hmode hseed i before memory hordinaryM
    have hbeforeEndpoint := hbatchSpec.1
    have hoccupiedEmpty := hbatchSpec.2
    obtain ⟨diagRecord, callCode, _loggedCode, _cutCode, logged, cut,
      hdiagInput, hcall, hactualCall, hlogged, hcut, _hloggedCode, _hcutCode,
      hcallTime, hquota, hcomparison, hpositive, hraw, _hdecoded⟩ :=
      ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_completion_diagnostics
        rate rewards C_star C_h s hs i x m.val (by omega) hmData.2
    have hdiagRecordEq : diagRecord = record m := by
      have hcanonical :
          diagRecord = ⟨diagRecord.input,
            ReferenceActivePhysicalStep.step diagRecord.input, rfl⟩ := by
        cases diagRecord with
        | mk diagInput diagOutput diagOutputEq =>
            cases diagOutputEq
            rfl
      have hinputEq : diagRecord.input = (record m).input := by
        simpa [record] using hdiagInput
      have hcanonicalEq :
          (⟨diagRecord.input,
            ReferenceActivePhysicalStep.step diagRecord.input, rfl⟩ :
              ReferenceFollowerDownDecoderReplay.Record p rate) =
          ⟨(record m).input,
            ReferenceActivePhysicalStep.step (record m).input, rfl⟩ :=
        congrArg
          (fun ri : ReferenceActivePhysicalStep.RoundInput p rate =>
            (⟨ri, ReferenceActivePhysicalStep.step ri, rfl⟩ :
              ReferenceFollowerDownDecoderReplay.Record p rate)) hinputEq
      calc
        diagRecord = ⟨diagRecord.input,
            ReferenceActivePhysicalStep.step diagRecord.input, rfl⟩ := hcanonical
        _ = ⟨(record m).input,
            ReferenceActivePhysicalStep.step (record m).input, rfl⟩ := hcanonicalEq
        _ = record m := rfl
    subst diagRecord
    have hbankFacts := ReferenceExecutedDownBankRecurrence.record_executed_down_bank_after_ordinary
      (record m) i before stateA memory memoryA (s + m.val)
      hinput hafter hbeforeEndpoint hoccupiedEmpty callCode logged cut hcall hlogged hcut
      hcomparison hpositive
    rcases hbankFacts with ⟨_hcallActual, hbank, _hexpected, _hsample, _hselected,
      _henabled, _hrounded⟩
    have hcallFields := ReferenceExecutedDownBankRecurrence.record_executed_down_call_fields
      (record m) i callCode logged cut hcall hlogged hcut hcomparison hpositive
    rcases hcallFields with ⟨_hcallActual, _htime, _hsample, _horiginalSample,
      _hselected, _henabled, _hrounded, heligible, _hexpectedWord, _hdownPositive⟩
    let decodedCall := ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode
    let trace := ActiveFollowerDownAcceptance.currentInputExtension p decodedCall.2
    have htraceEligible : AffineBatchDecoder.eligible (trace decodedCall.1) := by
      simpa [trace, ActiveFollowerDownAcceptance.currentInputExtension] using heligible
    have hdecode := AffineBatchDecoder.decodeStep_complete p trace logged.downBatch
      decodedCall.1 htraceEligible hquota
    have hcallTimeR : decodedCall.1 = (record m).input.time := by
      simpa [decodedCall, ReferenceDownCompletedAmbiguityMeasurability.decodeCall] using hcallTime
    let batch := logged.downBatch.pending ++
      [⟨(record m).input.time, decodedCall.2.sample⟩]
    have hentry : AffineBatchDecoder.entry p trace decodedCall.1 =
        ⟨(record m).input.time, decodedCall.2.sample⟩ := by
      simp [AffineBatchDecoder.entry, trace,
        ActiveFollowerDownAcceptance.currentInputExtension, hcallTimeR]
    have hwholeBank :
        stateA.downBatch = ⟨[], logged.downBatch.completed ++ [batch]⟩ := by
      calc
        stateA.downBatch = (AffineBatchDecoder.decodeStep p trace logged.downBatch
            decodedCall.1).1 := by simpa [decodedCall, trace] using hbank
        _ = ⟨[], logged.downBatch.completed ++ [batch]⟩ := by
          have hdecodeBank := congrArg Prod.fst hdecode
          rw [hdecodeBank]
          simp [batch, hentry]
    have hresetPending : stateA.downBatch.pending = [] := by
      rw [hwholeBank]
    have hbatchLength : batch.length = quota := by
      simp [batch, hquota, quota]
    have hrawBatch : cut.raw = AffineBatchDecoder.batchOutput batch := by
      simpa [batch, quota] using hraw
    have halphaBounds :
        s < s + (m.val + 1) ∧ s + (m.val + 1) ≤ s + n.val ∧ s + (m.val + 1) < p.T := by
      omega
    refine Or.inr ⟨m, hmData.1, hmData.2, hgreat, hlater, hunique, ?_⟩
    dsimp only
    refine ⟨halphaBounds.1, halphaBounds.2.1, halphaBounds.2.2,
      stateA, memoryA, callCode, logged, cut, ?_, hresetPending, ?_, ?_, ?_, ?_,
      hcomparison, hpositive, ?_, ?_⟩
    · simpa [runPrefix, ReferenceActiveHorizonMeasurability.runOfInput] using hstateAOrd
    · exact hcall
    · exact hactualCall
    · exact hlogged
    · exact hcut
    · simpa [quota] using hquota
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [batch] using hbatchLength
      · simpa [batch] using hrawBatch
      · simpa [batch] using congrArg
          (fun bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) => bank.completed)
          hwholeBank
      · simpa [batch] using hwholeBank
  · left
    intro k hkn hkcomplete
    have hkMem : k ∈ earlier := by
      simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hkn, by simpa [completed, observation] using hkcomplete⟩
    exact hearlier ⟨k, hkMem⟩

end Bandits.Support.ReferenceGeneratedDownLatestResetPrefix
