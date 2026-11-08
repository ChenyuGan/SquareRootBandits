/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownAmbiguityDetector

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Take

/-!
# Generated prefix and executed-test provenance for first collection

The generated postlaunch run is the original corrected initialization
execution continued on its complete source input and whole reward table.  The
results below align its records and executed DOWN tests with the actual first
collection window, retaining the original round, call, sample, and sent tag.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceGeneratedDownPrefixList

namespace Bandits.Support.ReferenceFirstCollectionDownGeneratedPrefix

variable {p : ConstructorDimensions.Parameters}

/-- The actual first-collection records are the prefix of the same generated
postlaunch run.  Every generated executed test in an inclusive window prefix
keeps its original indexed round and actual DOWN call, and the strict-prefix
replay is conditional only on the actual incoming ordinary follower state. -/
theorem actual_collection_down_generated_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let W := (epoch.records.drop (w + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    let Q := AffineBatchDecoder.quota p
    ∃ hs : s < p.T,
      ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
          rate rewards C_star C_h s hs,
        x.val = source ∧
        ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
          rate rewards C_star C_h s hs x =
          ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross ∧
        let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x
        let G := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
          rate rewards C_star C_h s hs x
        let K := fun k : Fin (p.T - s) =>
          ⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
              (by omega) Y,
            ReferenceActivePhysicalStep.step
              (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
                (by omega) Y), rfl⟩
        let Oi := fun (i : Fin (p.m - 1)) =>
          ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x
        let Tests := fun (i : Fin (p.m - 1)) (a b : ℕ) =>
          ((G.records.take b).drop a).filterMap (fun r =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                r.input i))
        let U := fun (i : Fin (p.m - 1)) (b : ℕ) =>
          ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hs i x b
        G.records.take count = epoch.records ∧
        ∀ nB : Fin B.length,
          ∃ N : Fin (p.T - s),
            N.val = w + nB.val ∧
            K N = B[nB.val]'nB.isLt ∧
            (K N).input.time.val = s + N.val ∧
            (G.records.take N.val).drop w = B.take nB.val ∧
            (G.records.take (N.val + 1)).drop w = B.take (nB.val + 1) ∧
            ∀ i : Fin (p.m - 1),
              (∀ test, test ∈ Tests i w (N.val + 1) →
                ∃ j : Fin (nB.val + 1),
                ∃ k : Fin (p.T - s),
                  k.val = w + j.val ∧
                  K k = B[j.val]'(by omega) ∧
                  ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                    ((Oi i).2 k) = some test ∧
                  test.time = (K k).input.time ∧
                  test.sample = ((K k).input.row.2 (K k).input.time).2 (0, i) ∧
                  test.sent = ReferenceActiveAffinePositiveTest.downSent (K k).input ∧
                  ∃ call,
                    ReferenceFollowerDownDecoderReplay.actualDownCall i (K k) = some call ∧
                    AffineBatchDecoder.eligible call.2) ∧
              ∀ (before : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                B[nB.val].input.state.followers i = .ordinary before memory →
                (Tests i w N.val).map ReferenceGeneratedDownPrefixList.stampedTest =
                    ReferenceFollowerDownDecoderReplay.actualDownPositives i
                      (B.take nB.val) ∧
                (U i N.val).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry =
                    ReferenceFollowerDownDecoderReplay.actualDownPositives i
                      (G.records.take N.val) ∧
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (B.take (nB.val + 1))).length ≤ (U i N.val).length + 1 := by
  classical
  dsimp only
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let W := (epoch.records.drop (w + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  let Q := AffineBatchDecoder.quota p
  have hwindowShort : w < count := by
    simpa [w, epoch] using hshort
  have hspanOffset : s + count ≤ p.T := by
    simpa [s] using hspan
  have hs : s < p.T := by omega
  let x : ReferenceGeneratedDownBatchCalendar.LaunchSource
      rate rewards C_star C_h s hs := ⟨source, hcross, rfl⟩
  have hx : x.val = source := rfl
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  have hcorrected : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some seed := by
    simpa [seed, x] using hseedSpec.1
  have hseed : seed = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross := by
    simp [seed, ReferenceFirstCollectionEpochAlignment.actualLaunchState, hcorrected]
  let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hs x
  let G := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  let K := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
        (by omega) Y,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
          (by omega) Y), rfl⟩ : ReferenceFollowerDownDecoderReplay.Record p rate)
  let actualInput : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s :=
    ⟨(ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross,
      (source.1.2,
        (ActualInitializationPhysicalStep.selectedRowIndex p source, rewards))),
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1⟩
  have hinput : Y = actualInput := by
    apply Subtype.ext
    simp [Y, actualInput,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput, seed, hseed, hx]
  have hGRecords : G.records = List.ofFn K := by
    simpa [G, K, ReferenceGeneratedDownBatchCalendar.generatedSourceRun] using
      (ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
        (p := p) (rate := rate) s (p.T - s) (by omega) Y)
  have hGLength : G.records.length = p.T - s := by
    simpa [G, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
      ReferenceActiveHorizonMeasurability.runOfInput] using
      (ReferenceActivePhysicalHorizon.run_record_count seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (p.T - s) (by omega) hseedSpec.2.1)
  have hRunPrefix (m : ℕ) (hm : m ≤ p.T - s) :
      (ReferenceActiveHorizonMeasurability.runOfInput
        (p := p) (rate := rate) s m (by omega) Y).records = G.records.take m := by
    have hshortRecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
      (p := p) (rate := rate) s m (by omega) Y
    calc
      _ = List.ofFn (fun k : Fin m => K ⟨k.val, by omega⟩) := by
        simpa only [K] using hshortRecords
      _ = (List.ofFn K).take m :=
        Fin.ofFn_take_eq_take_ofFn hm K
      _ = G.records.take m := by rw [← hGRecords]
  have hEpochRun : epoch =
      ReferenceActiveHorizonMeasurability.runOfInput
        (p := p) (rate := rate) s count hspan actualInput := by
    simp [s, epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceActiveHorizonMeasurability.runOfInput, actualInput]
  have hGprefix : G.records.take count = epoch.records := by
    calc
      G.records.take count =
          (ReferenceActiveHorizonMeasurability.runOfInput
            (p := p) (rate := rate) s count hspan Y).records :=
        (hRunPrefix count (by omega)).symm
      _ = (ReferenceActiveHorizonMeasurability.runOfInput
          (p := p) (rate := rate) s count hspan actualInput).records := by
        rw [hinput]
      _ = epoch.records := by rw [hEpochRun]
  have hwindowLookup (j : ℕ) (hj : j < B.length) :
      epoch.records[w + j]? = some (B[j]'hj) := by
    simpa [s, epoch, w, B] using
      (ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
        rate source rewards C_star C_h count hcross hspan hshort
        ⟨j, hj⟩).1
  have hwindowPrefix (n : ℕ) (hn : n ≤ B.length)
      (hdrop : n ≤ (epoch.records.drop w).length) :
      B.take n = (epoch.records.drop w).take n := by
    apply List.ext_getElem
    · simp only [List.length_take]
      rw [Nat.min_eq_left hn, Nat.min_eq_left hdrop]
    · intro j hjB hjE
      have hj : j < B.length :=
        Nat.lt_of_lt_of_le hjB (List.length_take_le' n B)
      have hlookup := hwindowLookup j hj
      have hvalue := (List.getElem?_eq_some_iff.mp hlookup).2
      simpa only [List.getElem_take, List.getElem_drop] using hvalue.symm
  have hGprefixAt (m : ℕ) (hm : m ≤ count) :
      G.records.take m = epoch.records.take m := by
    have h := congrArg (fun records : List (ReferenceFollowerDownDecoderReplay.Record p rate) =>
      records.take m) hGprefix
    simpa only [List.take_take, Nat.min_eq_left hm] using h
  have hGlen : count ≤ G.records.length := by
    rw [hGLength]
    omega
  have hWindowPrefixGenerated (n : ℕ) (hn : n ≤ B.length)
      (hdrop : n ≤ (epoch.records.drop w).length) :
      (G.records.take (w + n)).drop w = B.take n := by
    have hm : w + n ≤ count := by
      have hlen : epoch.records.length = count := by
        simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          (ReferenceActivePhysicalHorizon.run_record_count
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1)
      rw [List.length_drop, hlen] at hdrop
      omega
    calc
      (G.records.take (w + n)).drop w =
          (epoch.records.take (w + n)).drop w :=
        congrArg (List.drop w) (hGprefixAt (w + n) hm)
      _ = (epoch.records.drop w).take n := by
        rw [List.drop_take]
        congr 1
        omega
      _ = B.take n := (hwindowPrefix n hn hdrop).symm
  have hGRecordsAt (k : Fin (p.T - s)) :
      G.records[k.val]'(by
        rw [hGLength]
        exact k.isLt) = K k := by
    have hk : k.val < G.records.length := by rw [hGLength]; exact k.isLt
    have h := List.getElem_of_eq hGRecords hk
    simpa only [List.getElem_ofFn] using h
  let Oi (i : Fin (p.m - 1)) :=
    ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
  let Tests (i : Fin (p.m - 1)) (a b : ℕ) :=
    ((G.records.take b).drop a).filterMap (fun r =>
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i))
  let U (i : Fin (p.m - 1)) (b : ℕ) :=
    ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i x b
  refine ⟨hs, x, rfl, ?_, ?_, ?_⟩
  · simpa [seed] using hseed
  · exact hGprefix
  · intro nB
    have hlookup := hwindowLookup nB.val nB.isLt
    have hwindowBound := (List.getElem?_eq_some_iff.mp hlookup).1
    have hwindowValue := (List.getElem?_eq_some_iff.mp hlookup).2
    have hlen : epoch.records.length = count := by
      simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        (ReferenceActivePhysicalHorizon.run_record_count
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).1)
    have hwindowBoundCount : w + nB.val < count := by
      omega
    let N : Fin (p.T - s) := ⟨w + nB.val, by omega⟩
    have hNcount : N.val ≤ count := by
      simpa [N] using Nat.le_of_lt hwindowBoundCount
    have hNsuccCount : N.val + 1 ≤ count := by
      simpa [N] using Nat.succ_le_of_lt hwindowBoundCount
    have hdropBound : nB.val + 1 ≤ (epoch.records.drop w).length := by
      rw [List.length_drop, hlen]
      omega
    have hstrictPrefix := hWindowPrefixGenerated nB.val (Nat.le_of_lt nB.isLt)
      (by omega : nB.val ≤ (epoch.records.drop w).length)
    have hnBsucc : nB.val + 1 ≤ B.length := Nat.succ_le_of_lt nB.isLt
    have hinclusivePrefix := hWindowPrefixGenerated (nB.val + 1) hnBsucc hdropBound
    have hKwindow : K N = B[nB.val]'nB.isLt := by
      have hGtoEpoch := List.getElem_of_eq hGprefix
        (by
          rw [List.length_take, Nat.min_eq_left hGlen]
          exact hwindowBoundCount)
      calc
        K N = G.records[N.val]'(by
            simp [G, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
              ReferenceActiveHorizonMeasurability.runOfInput,
              ReferenceActivePhysicalHorizon.run_record_count]) :=
          (hGRecordsAt N).symm
        _ = epoch.records[w + nB.val]'hwindowBound := by
          simpa [N] using hGtoEpoch
        _ = B[nB.val]'nB.isLt := hwindowValue
    have hKtime : (K N).input.time.val = s + N.val := by
      have htime := (ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
        rate source rewards C_star C_h count hcross hspan hshort nB).2.1
      have htime' : B[nB.val].input.time.val + 1 = s + w + 1 + nB.val := by
        simpa [s, epoch, w, B] using htime
      rw [hKwindow]
      simp only [N]
      omega
    refine ⟨N, rfl, hKwindow, hKtime, hstrictPrefix, hinclusivePrefix, ?_⟩
    intro i
    constructor
    · intro test htest
      obtain ⟨record, hrecordMem, htestExec⟩ := List.mem_filterMap.mp htest
      obtain ⟨q, hq, hqrecord⟩ := List.mem_iff_getElem.mp hrecordMem
      have hNsuccLen : N.val + 1 ≤ G.records.length := le_trans hNsuccCount hGlen
      have hsegmentLength : ((G.records.take (N.val + 1)).drop w).length = nB.val + 1 := by
        rw [List.length_drop, List.length_take, Nat.min_eq_left hNsuccLen]
        simp only [N]
        omega
      have hqle : q ≤ nB.val := by
        rw [hsegmentLength] at hq
        omega
      have hqBound : q < nB.val + 1 := by omega
      let j : Fin (nB.val + 1) := ⟨q, hqBound⟩
      have hkBound : w + q < p.T - s := by
        have hNlt := N.isLt
        simp only [N] at hNlt
        omega
      let k : Fin (p.T - s) := ⟨w + q, hkBound⟩
      have hNsuccLeG : N.val + 1 ≤ G.records.length := hNsuccLen
      have hrecordIndex : w + q < G.records.length := by
        have hqIndex : w + q < N.val + 1 := by
          simp only [N]
          omega
        exact Nat.lt_of_lt_of_le hqIndex hNsuccLeG
      have hrecordG : record = G.records[w + q]'hrecordIndex := by
        calc
          record = ((G.records.take (N.val + 1)).drop w)[q]'hq := hqrecord.symm
          _ = G.records[w + q]'hrecordIndex := by
            simp [List.getElem_drop, List.getElem_take]
      have hprefixAt := hGprefixAt (N.val + 1) hNsuccCount
      have hqIndex : w + q < N.val + 1 := by
        simp only [N]
        omega
      have hGtoEpoch := List.getElem_of_eq hprefixAt
        (by
          rw [List.length_take, Nat.min_eq_left hNsuccLeG]
          exact hqIndex)
      have hrecordEpoch : record = epoch.records[w + q]'(by omega) := by
        calc
          record = G.records[w + q]'hrecordIndex := hrecordG
          _ = epoch.records[w + q]'(by omega) := by
            simpa only [List.getElem_take] using hGtoEpoch
      have hqWindow : q < B.length := by omega
      have hwindowAt : epoch.records[w + q]? = some (B[q]'hqWindow) :=
        hwindowLookup q hqWindow
      have hrecordWindow : record = B[q]'(by omega) := by
        calc
          record = epoch.records[w + q]'(by omega) := hrecordEpoch
          _ = B[q]'(by omega) := (List.getElem?_eq_some_iff.mp hwindowAt).2
      have hKN : K k = record := by
        calc
          K k = G.records[k.val]'(by
              simp [G, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
                ReferenceActiveHorizonMeasurability.runOfInput,
                ReferenceActivePhysicalHorizon.run_record_count]) :=
            (hGRecordsAt k).symm
          _ = record := by simpa [k] using hrecordG.symm
      have hKWindow : K k = B[j.val]'(by omega) := by
        simpa [j] using hKN.trans hrecordWindow
      have hround : (Oi i).2 k =
          ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
            (K k).input i := by
        rfl
      have htestOnK : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation (K k).input i) =
            some test := by
        rw [hKN]
        exact htestExec
      have htestObserved :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate ((Oi i).2 k) = some test := by
        rw [hround]
        exact htestOnK
      obtain ⟨call, hcall, hEligible, htimeCall, hsampleCall, htime, hsample, hsent⟩ :=
        ReferenceGeneratedDownPrefixList.executedTestOfRound_some_actual
          (K k) i test htestOnK
      refine ⟨j, k, ?_, hKWindow, htestObserved, htime, hsample, hsent, ?_⟩
      · rfl
      · exact ⟨call, hcall, hEligible⟩
    · intro before memory hordinary
      have hwindowEndpoints :=
        ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
          rate source rewards C_star C_h count hcross hspan hshort nB
      have hordinaryActual :
          (ReferenceActivePhysicalHorizon.run
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s (w + nB.val) (by omega)
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1).finalState.followers i =
            .ordinary before memory := by
        rw [← hwindowEndpoints.1]
        exact hordinary
      have hordinaryGenerated :
          (ReferenceActiveHorizonMeasurability.runOfInput
            (p := p) (rate := rate) s N.val (by omega) Y).finalState.followers i =
            .ordinary before memory := by
        rw [hinput]
        simpa [N, ReferenceActiveHorizonMeasurability.runOfInput, actualInput] using
          hordinaryActual
      have hstrictMap :=
        ReferenceGeneratedDownPrefixList.run_executedTests_map_eq_actualDownPositives
          (p := p) (rate := rate)
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          s N.val (by omega)
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate source rewards C_star C_h hcross).1 i before memory
          hordinaryActual w
      have hactualRunRecords :
          (ReferenceActivePhysicalHorizon.run
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s N.val (by omega)
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1).records =
            G.records.take N.val := by
        calc
          _ = (ReferenceActiveHorizonMeasurability.runOfInput
              (p := p) (rate := rate) s N.val (by omega) actualInput).records := rfl
          _ = (ReferenceActiveHorizonMeasurability.runOfInput
              (p := p) (rate := rate) s N.val (by omega) Y).records := by rw [hinput]
          _ = G.records.take N.val := hRunPrefix N.val (by omega)
      have hstrictOutput :
          (Tests i w N.val).map ReferenceGeneratedDownPrefixList.stampedTest =
            ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take nB.val) := by
        have hm := hstrictMap
        rw [hactualRunRecords] at hm
        change
          (List.filterMap (fun r =>
            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i))
            ((G.records.take N.val).drop w)).map
              ReferenceGeneratedDownPrefixList.stampedTest =
            ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (B.take nB.val)
        rw [← hstrictPrefix]
        simpa using hm
      have hUmap :=
        ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_tests_map_eq_actualDownPositives
          rate rewards C_star C_h s hs i x N.val (by omega) before memory hordinaryGenerated
      have hUoutput :
          (U i N.val).map ReferenceGeneratedInheritedDownCompletion.inheritedTestEntry =
            ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (G.records.take N.val) := by
        have hrunRecords := hRunPrefix N.val (by omega)
        rw [hrunRecords] at hUmap
        simpa [U] using hUmap
      have hactualPositivesAppend (records later : List (ReferenceFollowerDownDecoderReplay.Record p rate)) :
          ReferenceFollowerDownDecoderReplay.actualDownPositives i (records ++ later) =
            ReferenceFollowerDownDecoderReplay.actualDownPositives i records ++
              ReferenceFollowerDownDecoderReplay.actualDownPositives i later := by
        simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
          ReferenceFollowerDownDecoderReplay.actualDownCalls,
          ReferenceFollowerDownDecoderReplay.positiveCallEntries,
          List.filterMap_append, List.flatMap_append]
      have hsegmentLeFull :
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take nB.val)).length ≤
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (G.records.take N.val)).length := by
        have hsplit : G.records.take N.val =
            (G.records.take N.val).take w ++ (G.records.take N.val).drop w :=
          (List.take_append_drop w (G.records.take N.val)).symm
        have hpositiveSplit := calc
          ReferenceFollowerDownDecoderReplay.actualDownPositives i (G.records.take N.val) =
              ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((G.records.take N.val).take w ++ (G.records.take N.val).drop w) :=
            congrArg (ReferenceFollowerDownDecoderReplay.actualDownPositives i) hsplit
          _ = ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((G.records.take N.val).take w) ++
              ReferenceFollowerDownDecoderReplay.actualDownPositives i
                ((G.records.take N.val).drop w) := hactualPositivesAppend _ _
        calc
          _ = (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              ((G.records.take N.val).drop w)).length := by
            rw [← hstrictPrefix]
          _ ≤ (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (G.records.take N.val)).length := by
            rw [hpositiveSplit]
            simp only [List.length_append]
            omega
      have hsegmentLeU :
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take nB.val)).length ≤
            (U i N.val).length := by
        calc
          _ ≤ (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (G.records.take N.val)).length := hsegmentLeFull
          _ = (U i N.val).length := by rw [← hUoutput]; simp
      have hpositiveTakeOne (records : List (ReferenceFollowerDownDecoderReplay.Record p rate))
          (record : ReferenceFollowerDownDecoderReplay.Record p rate) :
          (ReferenceFollowerDownDecoderReplay.actualDownPositives i (records ++ [record])).length ≤
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i records).length + 1 := by
        cases hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i record with
        | none =>
            simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
              ReferenceFollowerDownDecoderReplay.positiveCallEntries,
              ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall,
              List.filterMap_append]
        | some call =>
            by_cases hpositive : AffineBatchDecoder.eligible call.2
            · simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
                ReferenceFollowerDownDecoderReplay.positiveCallEntries,
                ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall, hpositive,
                List.filterMap_append, AffineBatchDecoder.positiveAt,
                ActiveFollowerDownAcceptance.currentInputExtension]
            · simp [ReferenceFollowerDownDecoderReplay.actualDownPositives,
                ReferenceFollowerDownDecoderReplay.positiveCallEntries,
                ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall, hpositive,
                List.filterMap_append, AffineBatchDecoder.positiveAt,
                ActiveFollowerDownAcceptance.currentInputExtension]
      have htakeSucc : B.take (nB.val + 1) =
          B.take nB.val ++ [B[nB.val]'nB.isLt] := by
        exact (List.take_concat_get' B nB.val nB.isLt).symm
      refine ⟨hstrictOutput, hUoutput, ?_⟩
      calc
        (ReferenceFollowerDownDecoderReplay.actualDownPositives i
            (B.take (nB.val + 1))).length =
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (B.take nB.val ++ [B[nB.val]'nB.isLt])).length := by rw [htakeSucc]
        _ ≤ (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (B.take nB.val)).length + 1 := hpositiveTakeOne _ _
        _ ≤ (U i N.val).length + 1 := Nat.add_le_add_right hsegmentLeU 1

end Bandits.Support.ReferenceFirstCollectionDownGeneratedPrefix

end
