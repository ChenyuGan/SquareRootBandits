/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation

import Mathlib.Tactic

/-!
# Actual all-arm weights on the first collection window

This module connects the original zero-origin numerical prefix to the actual
first collection readout. It retains the physical record and the option-valued
payload, cell, and prefix witnesses.

Sources: `06_interruptions.tex:376-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceFirstCollectionWeightEnvelope

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem execute_disabled_registers
    (Q : RecordedQueueRun.Parameters) (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K)
    (hdisabled : ∀ c ∈ rounds, c.enabled = false) (a : Fin p.K) :
    (RecordedQueueRun.execute Q rounds state).registers a = state.registers a := by
  induction rounds generalizing state with
  | nil => rfl
  | cons c tail ih =>
      have hstep := RecordedQueueRun.step_disabled_preserves Q state c
        (hdisabled c List.mem_cons_self) a
      simpa only [RecordedQueueRun.execute] using
        (ih (RecordedQueueRun.step Q state c)
          (fun d hd => hdisabled d (List.mem_cons_of_mem c hd))).trans hstep.1

private theorem run_registers_eq_take_of_disabled_tail
    (Q : RecordedQueueRun.Parameters) (L : List (RecordedQueueRun.RoundInput p.K))
    (n : ℕ)
    (hdisabled : ∀ c ∈ L.drop n, c.enabled = false) (a : Fin p.K) :
    (RecordedQueueRun.run Q L).registers a =
      (RecordedQueueRun.run Q (L.take n)).registers a := by
  have hfactor : RecordedQueueRun.run Q L =
      RecordedQueueRun.execute Q (L.drop n) (RecordedQueueRun.run Q (L.take n)) := by
    calc
      RecordedQueueRun.run Q L =
          RecordedQueueRun.execute Q (L.take n ++ L.drop n)
            (RecordedQueueRun.initialState p.K) := by
        change RecordedQueueRun.execute Q L (RecordedQueueRun.initialState p.K) = _
        exact congrArg (fun xs => RecordedQueueRun.execute Q xs
          (RecordedQueueRun.initialState p.K)) (List.take_append_drop n L).symm
      _ = RecordedQueueRun.execute Q (L.drop n)
            (RecordedQueueRun.execute Q (L.take n)
              (RecordedQueueRun.initialState p.K)) :=
        RecordedEpisodeStability.execute_append Q (L.take n) (L.drop n)
          (RecordedQueueRun.initialState p.K)
      _ = RecordedQueueRun.execute Q (L.drop n)
            (RecordedQueueRun.run Q (L.take n)) := rfl
  calc
    (RecordedQueueRun.run Q L).registers a =
        (RecordedQueueRun.execute Q (L.drop n)
          (RecordedQueueRun.run Q (L.take n))).registers a := by rw [hfactor]
    _ = (RecordedQueueRun.run Q (L.take n)).registers a :=
      execute_disabled_registers Q (L.drop n)
        (RecordedQueueRun.run Q (L.take n)) hdisabled a

private theorem stopped_prefix_envelope
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (n : ℕ) (hn : n ≤ ReplayWeightStability.episodeHorizon rate.eta.val)
    (hdisabled : ∀ c ∈ L.drop n, c.enabled = false) :
    ∀ a : Fin p.K,
      0 < RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) a ∧
      1 ≤ RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) a ∧
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) a ≤ 2 := by
  intro a
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hcap : Q.eta ≤ 1 / 64 := by
    dsimp [Q, ReferenceFirstLaunchNumericalCell.queueParameters]
    have hM : (1 : ℝ) ≤ (p.m : ℝ) := by
      exact_mod_cast (Nat.le_trans (by decide) p.two_le_m)
    have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
      have hmk : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
      exact_mod_cast (Nat.le_trans (by decide) hmk)
    have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
      exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
    have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
    have hdenLower : (1024 : ℝ) ≤
        1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by
      calc
        (1024 : ℝ) = 1024 * 1 * 1 * 1 := by ring
        _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
            (CanonicalRecordingRates.L_stab p : ℝ) := by gcongr
    have hmul : rate.eta.val *
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
      (le_div_iff₀ hden).mp rate.sourceCap
    have hsmall : rate.eta.val * 1024 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hdenLower (le_of_lt rate.eta.property)
      nlinarith
    change rate.eta.val ≤ 1 / 64
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    nlinarith
  have hH := RecordedEpisodeStability.execute_source_weight_envelope Q
    (RecordedQueueRun.initialState p.K) (L.take n) a (by
      have htake : (L.take n).length ≤ n := List.length_take_le _ _
      exact htake.trans hn)
  have hreg := run_registers_eq_take_of_disabled_tail Q L n hdisabled a
  have hweight : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q L) a =
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (L.take n)) a := by
    rw [RecordedQueueRun.scoreWeight, RecordedQueueRun.scoreWeight, hreg]
  have hstart : RecordedQueueRun.scoreWeight Q
      (RecordedQueueRun.initialState p.K) a = 1 := by
    simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      Bandits.Support.ScoreWeights.scoreWeight]
  have hlower := hH.1
  have hupper := hH.2.1
  rw [hstart] at hlower hupper
  have hupper' : RecordedQueueRun.scoreWeight Q
      (RecordedQueueRun.run Q (L.take n)) a < 2 := by
    simpa only [RecordedQueueRun.run, mul_one] using hupper
  rw [hweight]
  exact ⟨lt_of_lt_of_le zero_lt_one hlower, hlower, le_of_lt hupper'⟩

private theorem actual_record_index
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt = r ∧
      t.val = ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h + k.val := by
  classical
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  by_cases hs : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h ≤ t.val
  · simp only [hs] at hr
    have hget := List.getElem?_eq_some_iff.mp hr
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let k : Fin R.length := ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h, hget.1⟩
    refine ⟨k, ?_, ?_⟩
    · simpa only [k, R] using hget.2
    · dsimp only [k]
      omega
  · simp only [hs] at hr
    cases hr

private theorem mapM_some_slots {α : Type*} (L : List α) :
    (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.mapM_cons, ih]

private theorem actual_past_cells_source_prefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    ∃ (whole : List (RecordedQueueRun.RoundInput p.K))
      (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = whole.map some ∧
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t source = some (whole.take k.val) ∧
      t.val = ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h + k.val ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h t.val source = some (whole.take k.val) ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt = r := by
  classical
  obtain ⟨k, hrecord, htime⟩ := actual_record_index
    (rate := rate) rewards C_star C_h source t r hr
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hR := ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h source hlaunch
      have hRlen : R.length = 0 := by
        dsimp only [R]
        exact congrArg List.length hR.1
      have hk : k.val < R.length := k.isLt
      omega
  | some active =>
      have hcells :=
        ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
          rate rewards C_star C_h source
      simp only [hlaunch] at hcells
      obtain ⟨whole, hlen, hmap, hprefix, _hphases⟩ := hcells
      have hlaunchBy :
          ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
            rate rewards C_star C_h t.val source := by
        refine ⟨?_, ?_⟩
        · exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
            rate source rewards C_star C_h).1 (by rw [hlaunch]; rfl)
        · rw [htime]
          exact Nat.le_add_right _ _
      have hcut : t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h = k.val := by rw [htime]; omega
      have hslots : ReferenceFirstCollectionCurrentRetainedGate.pastSlots
          rate rewards C_star C_h t source =
            (R.take k.val).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) := by
        apply List.ext_getElem
        · simp only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
            List.length_map, List.length_range, List.length_take]
          rw [hcut, Nat.min_eq_left k.isLt.le]
        · intro j hj hj'
          have hjk : j < k.val := by
            have := hj'
            simp only [List.length_map, List.length_take] at this
            omega
          have hjR : j < R.length := lt_trans hjk k.isLt
          simp only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
            List.getElem_map, List.getElem_range,
            List.getElem_map, List.getElem_take]
          rw [List.getElem?_eq_getElem hjR]
          rfl
      have hmapTake := congrArg (fun xs => xs.take k.val) hmap
      have hmapTake' : (R.take k.val).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
            (whole.take k.val).map some := by
        simpa only [List.map_take] using hmapTake
      have hslots' : ReferenceFirstCollectionCurrentRetainedGate.pastSlots
          rate rewards C_star C_h t source = (whole.take k.val).map some :=
        hslots.trans hmapTake'
      have hpast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t source = some (whole.take k.val) := by
        simp only [ReferenceFirstCollectionCurrentRetainedGate.pastCells?, hlaunchBy,
          ite_true, hslots']
        induction whole.take k.val with
        | nil => rfl
        | cons c cs ih => simp only [List.map_cons, List.mapM_cons, ih, id_eq]; rfl
      have hprefixInputs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h t.val source = some (whole.take k.val) := by
        simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
          hlaunchBy, ite_true]
        change (((R.take (t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)).map
            (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id) = _
        rw [hcut, hmapTake']
        exact mapM_some_slots _
      exact ⟨whole, k, hmap, hpast, htime, hprefixInputs, hrecord⟩

private theorem actual_cell0_source_value
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (whole : List (RecordedQueueRun.RoundInput p.K))
    (hmap : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = whole.map some)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt) =
      some (whole[k.val]'(by
        have hlen := congrArg List.length hmap
        simp only [List.length_map] at hlen
        omega)) := by
  have hw : k.val < whole.length := by
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  have h := congrArg (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[k.val]?) hmap
  simp only [List.getElem?_map, List.getElem?_eq_getElem k.isLt,
    List.getElem?_eq_getElem hw] at h
  exact Option.some.inj h

private theorem actual_prefix_stopped_score_vector
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (whole : List (RecordedQueueRun.RoundInput p.K))
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (htime : t.val = ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h t.val source = some (whole.take k.val)) :
    ∃ (sourceWord : List (RecordedQueueRun.RoundInput p.K)),
      sourceWord.take k.val = whole.take k.val ∧
      ∀ a : Fin p.K,
        RecordedQueueRun.scoreWeight
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (whole.take k.val)) a =
          (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate sourceWord i
              (min k.val (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) sourceWord))).1) a := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hno := ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h source hlaunch
      have hk : k.val <
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).length := k.isLt
      simp only [hno.1] at hk
      omega
  | some active =>
      have hrestore :=
        ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
          rate rewards C_star C_h source
      simp only [hlaunch] at hrestore
      obtain ⟨sourceWord, hlen, hprefixes, _hterminal, _hunique,
        _hinstallations, _hlaterOperations, hweights⟩ := hrestore
      have hklen : k.val ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).length := k.isLt.le
      have hprefixAt := hprefixes k.val hklen
      have hprefixAt' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h t.val source = some (sourceWord.take k.val) := by
        rw [htime]
        exact hprefixAt
      have hsame : sourceWord.take k.val = whole.take k.val :=
        Option.some.inj (hprefixAt'.symm.trans hprefix)
      have hkWord : k.val ≤ sourceWord.length := by omega
      have hweightsAt := hweights k.val hkWord
      have hscore := hweightsAt.2.1
      refine ⟨sourceWord, hsame, ?_⟩
      intro a
      rw [← hsame]
      exact congrFun hscore a

private theorem prepare_collection_at_cutoff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (u : Fin p.T) (hu : u.val + 1 = ledger.cutoff) :
    (prepare x).coordinator = .collection payload ledger
      (collectionClock payload ledger saved u) u
      (CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x payload ledger (collectionClock payload ledger saved u) u)) := by
  have hrange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    constructor <;> have := u.isLt <;> omega
  have hval : ledger.cutoff - 1 = u.val := by omega
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have heq : cutoff = u := Fin.ext hval
  simp only [ReferenceActivePhysicalStep.prepare, dispatch, hstate, dite_eq_left hrange,
    CoordinatorRoundDispatch.dispatch]
  change DispatchCut.collection payload ledger (collectionClock payload ledger saved cutoff)
    cutoff (CoordinatorRoundDispatch.dispatchCollection
      (collectionInput x payload ledger (collectionClock payload ledger saved cutoff) cutoff)) = _
  rw [heq]

private theorem actual_empty_collection_later_chosen
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .collection payload ledger saved)
    (hempty : ledger.pending = ∅) :
    laterChosen (completeSuffixRecords rate source rewards C_star C_h)[k.val].input = true := by
  by_cases hf : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.time.val + 1 < ledger.freezeAt
  · obtain ⟨u, hu, _core, _started, _hstart, _instruction, _hassignment,
      _, _, _, _, _consistent, _output, _hlocal, _, _clockData, _installation, _selected,
      _, _, _, _, hdispatch, _⟩ :=
      ReferenceCompleteEmptyCollectionCorrectedChoiceDomains.complete_empty_corrected_choice_domains
        rate rewards C_star C_h source k payload ledger saved hstate hempty hf
    simp only [laterChosen, prepare_collection_at_cutoff
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input payload ledger saved
      hstate u hu, hdispatch]
  · obtain ⟨u, hu, _core, _, _started, _hstart, _instruction, _hassignment,
      _htime, _hrenewal, _output, _hlocal, _, _, _, _, _, _, _, _, _, _mass,
      _sampled, _, _, _, _selection, hdispatch, _⟩ :=
      ReferenceCompleteEmptyCollectionRenewalChoiceDomains.complete_empty_collection_renewal_choice_domains
        rate rewards C_star C_h source k payload ledger saved hstate hempty (by omega)
    simp only [laterChosen, prepare_collection_at_cutoff
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input payload ledger saved
      hstate u hu, hdispatch]

private theorem collection_window_no_later
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) (hw : w < records.length)
    (j : Fin (collectionWindow records w).length) (hj : 0 < j.val) :
    laterChosen (collectionWindow records w)[j.val].input = false := by
  have hhead : (records.drop w).take 1 = [records[w]] := by
    rw [List.drop_eq_getElem_cons hw]
    rfl
  let tail := (records.drop (w + 1)).takeWhile (fun r => !laterChosen r.input)
  have hwindow : collectionWindow records w = records[w] :: tail := by
    simp only [collectionWindow, hhead, List.singleton_append, tail]
  have hindex : j.val - 1 < tail.length := by
    have := j.isLt
    have hlen := congrArg List.length hwindow
    simp only [List.length_cons] at hlen
    omega
  have hrecord : (collectionWindow records w)[j.val] = tail[j.val - 1] := by
    simp only [hwindow]
    simp only [List.getElem_cons, Nat.ne_of_gt hj, dite_false]
  rw [hrecord]
  have hmem := List.getElem_mem hindex
  have htest := List.mem_takeWhile_imp hmem
  cases he : laterChosen tail[j.val - 1].input <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true]

/-- The initialized first stream covers the whole actual collection window.
Stopping at its first empty ledger cannot omit another collection date. -/
private theorem initialized_stream_covers_window
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (firstLiveWindow (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records).length < count)
    (hfull : completeSuffixRecords rate source rewards C_star C_h =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hs).records)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hshort) :
    d.stream.ell = d.stream.window.length := by
  classical
  let R := completeSuffixRecords rate source rewards C_star C_h
  let w := (firstLiveWindow R).length
  have hwindow : d.stream.window = collectionWindow R w := by
    rw [d.stream.windowIsActual]
    change collectionWindow _ _ = collectionWindow R w
    rw [← hfull]
  have hR : R = (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records := hfull
  have hw : w < R.length := by
    have hlen : R.length = count := by
      rw [hR]
      exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hwcount : w < count := by simpa only [w, hR] using hshort
    omega
  by_contra hne
  have hlt : d.stream.ell < d.stream.window.length :=
    lt_of_le_of_ne d.stream.withinWindow hne
  have hempty : d.ledger.pending = ∅ := by
    cases hout : d.outcome with
    | exhausted hp heq _ _ _ => exact False.elim (hne heq)
    | empty data => exact data.pendingEmpty
  let next := d.stream.window[d.stream.ell]'hlt
  have hnext := (d.stream.alignment ⟨d.stream.ell, hlt⟩).1
  have hprev := (d.stream.alignment
    ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).1
  have hrecord : d.stream.window[d.last.val]'(lt_of_lt_of_le d.last.isLt d.stream.withinWindow) =
      d.record := (List.getElem?_eq_some_iff.mp d.recordAt).2
  rw [hrecord, ← hfull] at hprev
  rw [← hfull] at hnext
  change R[w + d.stream.ell]? = some next at hnext
  change R[w + d.last.val]? = some d.record at hprev
  have hk : w + d.stream.ell < R.length := (List.getElem?_eq_some_iff.mp hnext).1
  have hp : w + d.last.val < R.length := (List.getElem?_eq_some_iff.mp hprev).1
  have hnextEq : R[w + d.stream.ell] = next := (List.getElem?_eq_some_iff.mp hnext).2
  have hprevEq : R[w + d.last.val] = d.record := (List.getElem?_eq_some_iff.mp hprev).2
  have hlast : d.last.val + 1 = d.stream.ell := d.lastIsLast
  have hi : w + d.last.val + 1 < R.length := by omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h source (w + d.last.val) hi
  have hindex : w + d.last.val + 1 = w + d.stream.ell := by
    have := d.lastIsLast
    omega
  change (R[w + d.last.val + 1]).input.state = (R[w + d.last.val]).output.next at hadj
  simp only [hindex] at hadj
  have hadjNext : next.input.state = d.record.output.next :=
    (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      r.input.state) hnextEq).symm.trans
        (hadj.trans (congrArg (fun r => r.output.next) hprevEq))
  have hstate : next.input.state.coordinator =
      .collection d.stream.payload d.ledger d.stream.saved := by
    rw [hadjNext, d.actualNextCoordinator]
  have hlater := actual_empty_collection_later_chosen rewards C_star C_h source
    ⟨w + d.stream.ell, hk⟩ d.stream.payload d.ledger d.stream.saved
    (by
      change (R[w + d.stream.ell]).input.state.coordinator = _
      exact (congrArg (fun r => r.input.state.coordinator) hnextEq).trans hstate) hempty
  have hnotLater := collection_window_no_later R w hw
    ⟨d.stream.ell, by rw [← hwindow]; exact hlt⟩
    (lt_of_lt_of_le Nat.zero_lt_one d.stream.positiveLength)
  have hnot : laterChosen next.input = false := by
    simpa only [← hwindow, next] using hnotLater
  have hyes : laterChosen next.input = true := by
    change laterChosen (R[w + d.stream.ell]).input = true at hlater
    exact (congrArg (fun r => laterChosen r.input) hnextEq).symm.trans hlater
  rw [hnot] at hyes
  cases hyes

private theorem collection_readout_call_eq_choice
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some call)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
      some ⟨call.payload, call.preLedger, call.started, call.weights⟩ := by
  classical
  have hp : record.output.preparation = prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcut : ReferenceCollectionSegmentExtraction.choiceOfCut
      record.output.preparation.coordinator = some call := by
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    simp only [← hp] at hchoice
    split at hchoice
    · cases hchoice
    · exact hchoice
  have hdom := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
    (show (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome = true by
      rw [hread]; rfl)
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall
  rw [ite_eq_left hdom.1]
  cases hcoord : record.output.preparation.coordinator with
  | first outcome => cases outcome <;> simp [hcoord] at hdom
  | invalidCollectionCutoff => simp [hcoord] at hdom
  | dagger => simp [hcoord] at hdom
  | live r q base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
          have hpos : 0 < r.payload.sigma.val := by simpa only [hcoord] using hdom.2
          simp only [hcoord, ReferenceCollectionSegmentExtraction.choiceOfCut] at hcut
          cases Option.some.inj hcut
          simp only [ite_eq_left hpos]
      | clockFailure => simp [hcoord] at hdom
      | initializerFailure => simp [hcoord] at hdom
      | localFailure => simp [hcoord] at hdom
      | continuingChosen => simp [hcoord] at hdom
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simp only [hcoord, ReferenceCollectionSegmentExtraction.choiceOfCut] at hcut
          cases Option.some.inj hcut
          rfl
      | clockFailure => simp [hcoord] at hdom
      | localFailure => simp [hcoord] at hdom
      | coreFailure => simp [hcoord] at hdom
      | laterReconstructionFailure => simp [hcoord] at hdom
      | laterPrefixFailure => simp [hcoord] at hdom
      | laterOrientationFailure => simp [hcoord] at hdom
      | laterChoiceFailure => simp [hcoord] at hdom
      | laterChosen => simp [hcoord] at hdom

private theorem grid_boundary_le_start_add_horizon (sigma : Fin p.T) :
    FollowerCutoffScan.gridBoundary p rate.eta.val sigma ≤
      sigma.val + 1 + ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) = sigma.val + 1 :=
    Nat.mod_add_div _ _
  have hround : H * ((sigma.val + 1) / H + 1) ≤ sigma.val + 1 + H := by
    rw [Nat.mul_succ]
    omega
  exact (Nat.min_le_right _ _).trans hround

private theorem initialized_stream_payload_facts
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (firstLiveWindow (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records).length < count)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hc hs hshort) :
    out.payload.anchor = (fun _ => 1) ∧
      out.payload.sigma.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h ∧
      (firstLiveWindow (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hs).records).length ≤
          ReplayWeightStability.episodeHorizon rate.eta.val := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let start := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  let E := ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
    source rewards C_star C_h hc count hs
  let w := (firstLiveWindow E.records).length
  have hw : w < count := hshort
  obtain ⟨execution⟩ := out.cutoffExecution
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hcut : E.records[w]'(by omega) = out.cutoff.cut :=
    (List.getElem?_eq_some_iff.mp out.cutoff.cutIndex).2
  have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start seed.activeAtStart
    count hs ⟨w, hw⟩
  have hcutActual : out.cutoff.cut =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
        (by omega) seed.activeAtStart := hcut.symm.trans hat
  have hcoord : (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start w
      (by omega) seed.activeAtStart).finalState.coordinator =
        .live execution.live execution.owned execution.base := by
    exact (congrArg (fun r => r.input.state.coordinator) hcutActual).symm.trans
      execution.actualLive
  have henv := ReferenceFirstLiveWeightEnvelope.run_first_live_weight_envelope
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hs seed.activeAtStart seed.coordinatorFirst w hw.le (le_refl w)
  rw [hcoord] at henv
  have hpayload : out.payload = execution.live.payload :=
    out.payloadMatchesCutoff.trans execution.payloadIsLive
  have hanchor : out.payload.anchor = (fun _ => 1) := by
    funext a
    rw [hpayload]
    exact henv.1 a
  have hsigma : out.payload.sigma.val = start := by
    rw [out.payloadMatchesCutoff]
    exact out.cutoffContext.2.1
  have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) start initial := by
    have hf : initial.coordinator = .first := seed.coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt, hf]
  have hclock := (ReferenceRunClockPreservation.run_clockAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hs
    seed.activeAtStart hseed).2.1 w hw.le
  simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclock
  obtain ⟨_, hvalid, hclockSigma, _, hgrid, _, hbefore, _⟩ := hclock
  have hboundary : execution.live.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val out.payload.sigma := by
    rw [hgrid, hvalid.1, hclockSigma, ← hpayload]
    rfl
  have hbound := grid_boundary_le_start_add_horizon (rate := rate) out.payload.sigma
  rw [hboundary] at hbefore
  rw [hsigma] at hbound
  refine ⟨hanchor, hsigma, ?_⟩
  change w ≤ ReplayWeightStability.episodeHorizon rate.eta.val
  omega

private theorem actual_choice_enabled_eq
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hc count hs).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hc count hs).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hc count hs).records).length).length)
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hcall : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hc count hs).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate z rewards C_star C_h hc count hs).records).length)[n].input = some call) :
    let record := (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hc count hs).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hc count hs).records).length)[n]
    call.preLedger.freezeAt =
      FollowerCutoffScan.gridBoundary p rate.eta.val call.payload.sigma ∧
    ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time =
      decide (record.input.time.val + 1 < call.preLedger.freezeAt) := by
  obtain ⟨hcontext, _, _, _, henabled, _⟩ :=
    ReferenceFirstCollectionEnabledPrefix.actual_first_collection_enabled_history_prefix
      rate z rewards C_star C_h count hc hs hshort n call hcall
  obtain ⟨cut, suffix, reg, owned, base, c0, initializer, seg,
    _, _, _, _, _, _, _, _, _, _, _, _, _, hgrid, _, _, _, _,
    hpay, hctx, hdate⟩ := hcontext
  have hfreeze : call.preLedger.freezeAt = initializer.freezeAt :=
    congrArg (fun ctx => ctx.2.2.2.1) hctx
  refine ⟨?_, ?_⟩
  · rw [hfreeze, hgrid, ← hpay]
  · rw [henabled, hdate]
    simp only [Nat.add_left_comm, Nat.add_comm]

private theorem actual_first_collection_data
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (firstLiveWindow (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records).length < count)
    (hfull : completeSuffixRecords rate source rewards C_star C_h =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hs).records) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    let w := (firstLiveWindow R).length
    let B := collectionWindow R w
    let s := physicalStart rate source rewards C_star C_h
    ∃ P : Payload rate,
      P.anchor = (fun _ => 1) ∧ P.sigma.val = s ∧
      w ≤ ReplayWeightStability.episodeHorizon rate.eta.val ∧
      ∀ (j : ℕ) (hj : j < B.length),
        ∃ (c : RecordedQueueRun.RoundInput p.K)
          (call : ReferenceCollectionSegmentExtraction.Choice rate),
          call.payload = P ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate B[j] = some c ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 B[j] = some c ∧
          ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 B[j] =
            some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
          c.rate = P.rate ∧
          c.enabled = decide (B[j].input.time.val + 1 <
            FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma) ∧
          B[j].input.time.val = s + w + j ∧ R[w + j]? = some B[j] := by
  classical
  intro R w B s
  obtain ⟨_seed, _hstart, d, head, initializer, valid, D,
    _hhead, _hpay, _hinit, _hchecked, hDlen, _hzero, hcells⟩ :=
    ReferenceFirstPhasesNumericalObservationIdentification.actual_first_collection_numerical_observation_identity
      rate source rewards C_star C_h hc count hs hshort
  have hcover := initialized_stream_covers_window rewards C_star C_h source hc count hs
    hshort hfull d
  let out := d.stream
  have hwindow : out.window = B := by
    rw [out.windowIsActual]
    change collectionWindow _ _ = B
    rw [← hfull]
  have hactualWindow : ReferenceFirstCollectionReadyStream.actualWindow (rate := rate)
      source rewards C_star C_h hc count hs = B := by
    rw [← out.windowIsActual]
    exact hwindow
  have hell : out.ell = B.length := hcover.trans (congrArg List.length hwindow)
  obtain ⟨hanchor, hsigma, hw⟩ := initialized_stream_payload_facts
    rewards C_star C_h source hc count hs hshort out
  have hsigma' : out.payload.sigma.val = s := hsigma
  have hw' : w ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    simpa only [w, R, hfull] using hw
  refine ⟨out.payload, hanchor, hsigma', hw', ?_⟩
  intro j hj
  let n : Fin out.ell := ⟨j, by omega⟩
  obtain ⟨call, _validCall, hchoice, hpayload, _hcontext, _hsourceCell,
    _hrows, _hselected, _hrewards, htime, henabled, _hreward, hrate,
    _hphysical, hread, hlive⟩ := hcells n
  have hDlength : D.length = B.length := hDlen.trans hell
  have hjD : j < D.length := by rw [hDlength]; exact hj
  have hjWindow : j < d.stream.window.length := by
    change j < out.window.length
    rw [hwindow]
    exact hj
  let c := D[j]'hjD
  have hwindowD : d.stream.window = B := hwindow
  have hrecord : d.stream.window[j]'hjWindow = B[j] := List.getElem_of_eq hwindowD _
  have hchoiceB : ReferenceCollectionSegmentExtraction.choice B[j].input = some call := by
    simpa only [n, hrecord] using hchoice
  have hreadB : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 B[j] = some c := by
    simpa only [n, hrecord, c] using hread
  have hliveB : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 B[j] = none := by
    simpa only [n, hrecord] using hlive
  have hcellB : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate B[j] = some c := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveB, hreadB]
    rfl
  have hcallB := collection_readout_call_eq_choice B[j] call c hchoiceB hreadB
  let jE : Fin (ReferenceFirstCollectionReadyStream.actualWindow (rate := rate)
      source rewards C_star C_h hc count hs).length := ⟨j, by rw [hactualWindow]; exact hj⟩
  have hchoiceE : ReferenceCollectionSegmentExtraction.choice
      (ReferenceFirstCollectionReadyStream.actualWindow (rate := rate)
        source rewards C_star C_h hc count hs)[jE.val].input = some call := by
    simpa only [jE, hactualWindow] using hchoiceB
  have hactive := actual_choice_enabled_eq (rate := rate)
    rewards C_star C_h source count hc hs hshort jE call hchoiceE
  have hwindowNative : collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hc count hs).records
      (firstLiveWindow (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hc count hs).records).length = B := hactualWindow
  have hrecordNative : (collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hc count hs).records
      (firstLiveWindow (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hc count hs).records).length)[jE] = B[j] := by
    simp only [Fin.getElem_fin]
    exact List.getElem_of_eq hwindowNative _
  have hactiveB : ReferenceActivePhysicalStep.collectionEnabled call.preLedger B[j].input.time =
      decide (B[j].input.time.val + 1 < call.preLedger.freezeAt) := by
    exact (congrArg
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time =
          decide (record.input.time.val + 1 < call.preLedger.freezeAt)) hrecordNative).mp hactive.2
  have hfreeze : call.preLedger.freezeAt =
      FollowerCutoffScan.gridBoundary p rate.eta.val out.payload.sigma := by
    rw [hactive.1, hpayload]
  have henabledB : c.enabled = decide (B[j].input.time.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val out.payload.sigma) := by
    have he : c.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger B[j].input.time := by
      simpa only [n, hrecord, c] using henabled
    rw [he, hactiveB, hfreeze]
  have htimeB : B[j].input.time.val = s + w + j := by
    simpa only [n, hrecord, ← hfull, s, w, R, physicalStart,
      generatedBoundary, generatedInput] using htime
  have hindex := (out.alignment ⟨j, by omega⟩).1
  have hindexB : R[w + j]? = some B[j] := by
    simpa only [← hfull, out, hrecord, R, w] using hindex
  exact ⟨c, call, hpayload, hcellB, hreadB, hcallB, hrate,
    henabledB, htimeB, hindexB⟩

/-- An actual collection readout at a real date keeps its exact zero-origin
source prefix and its post-choice call in one existential witness. This
intermediate result is deterministic and does not identify the analytical
prefix with an acquired history. -/
public theorem actual_collection_readout_source_prefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c) :
    ∃ (whole L : List (RecordedQueueRun.RoundInput p.K))
      (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = whole.map some ∧
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t source = some L ∧
      L = whole.take k.val ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt = r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
        some ⟨payload, ledger, started, weights⟩ ∧
      c.rate = payload.rate ∧
      c.enabled = decide (r.input.time.val + 1 < started.clock.g) ∧
      ∃ j : Fin whole.length, j.val = k.val ∧ c = whole[j.val]'j.isLt ∧
      ∃ sourceWord : List (RecordedQueueRun.RoundInput p.K),
        sourceWord.take k.val = L ∧
        ∀ a : Fin p.K,
          RecordedQueueRun.scoreWeight
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) a =
            (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
                rate sourceWord i
                (min k.val (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) sourceWord))).1) a := by
  classical
  obtain ⟨whole, k, hmap, hpast, htime, hprefix, hrecord⟩ := actual_past_cells_source_prefix
    (rate := rate) rewards C_star C_h source t r hr
  obtain ⟨sourceWord, hsame, hscore⟩ := actual_prefix_stopped_score_vector
    (rate := rate) rewards C_star C_h source t whole k htime hprefix
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt
  have hread' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record =
      some c := by simpa only [record, hrecord] using hread
  have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    cases h : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none => rfl
    | some d =>
        have hdisjoint := ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 record ⟨by rw [h]; rfl, by rw [hread']; rfl⟩
        exact False.elim hdisjoint
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone, hread']
  obtain ⟨payload, ledger, started, weights, _hbranch, hcall, hrate,
      henabled, _hoperations⟩ :=
    ReferenceCollectionOldEpisodeOperationPreservation.complete_suffix_collectionReadout_operation_frames
      (rate := rate) rewards C_star C_h source k c hread'
  have hcall' : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
      some ⟨payload, ledger, started, weights⟩ := by
    simpa only [hrecord] using hcall
  have hcell0' : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simpa only [record, hrecord] using hcell0
  have hcellSource := actual_cell0_source_value
    (rate := rate) rewards C_star C_h source whole hmap k
  have hw : k.val < whole.length := by
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  have hcellSource' : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r =
      some (whole[k.val]'hw) := by
    simpa only [hrecord] using hcellSource
  have hcellEq : c = whole[k.val]'hw := Option.some.inj (hcell0'.symm.trans hcellSource')
  let j : Fin whole.length := ⟨k.val, hw⟩
  have hcellEq' : c = whole[j.val]'j.isLt := by simpa only [j] using hcellEq
  have henabled' : c.enabled = decide (r.input.time.val + 1 < started.clock.g) := by
    simpa only [hrecord] using henabled
  refine ⟨whole, whole.take k.val, k, payload, ledger, started, weights,
    hmap, hpast, rfl, hrecord, hcell0', hcall', hrate, henabled',
    j, rfl, hcellEq',
    sourceWord, hsame, ?_⟩
  intro a
  exact hscore a

/-- Every actual first-collection date has its literal collection call and
zero-origin numerical prefix. The old unit anchor and canonical rates are
retained, and the STOPPED score vector is within the all-arm factor-two band.
The physical collection length is unrestricted. The final identity retains
the first detecting post-update through `firstOverflowPrefix`. -/
public theorem actual_first_collection_weight_envelope
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hmem : r ∈ collectionWindow (completeSuffixRecords rate source rewards C_star C_h)
      (firstLiveWindow (completeSuffixRecords rate source rewards C_star C_h)).length) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (call : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t source = some L ∧
      L.length = t.val - physicalStart rate source rewards C_star C_h ∧
      r.input.time = t ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
        some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
      call.payload.anchor = (fun _ => 1) ∧
      c.rate = call.payload.rate ∧
      call.payload.rate = CanonicalRecordingRates.xi p rate.eta.val call.payload.anchor ∧
      c.enabled = decide (t.val + 1 < call.started.clock.g) ∧
      (∀ a : Fin p.K,
        0 < call.payload.anchor a ∧
        0 < RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ∧
        call.payload.anchor a ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ∧
        RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ≤ 2 * call.payload.anchor a) ∧
      ∃ sourceWord : List (RecordedQueueRun.RoundInput p.K),
        sourceWord.take L.length = L ∧
        ∀ a : Fin p.K,
          RecordedQueueRun.scoreWeight (queueParameters rate)
            (RecordedQueueRun.run (queueParameters rate) L) a =
          AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate sourceWord a
              (min L.length (UnstoppedRecordedQueueComparison.firstOverflowPrefix
                (queueParameters rate) sourceWord))).1 := by
  classical
  let R := completeSuffixRecords rate source rewards C_star C_h
  let s := physicalStart rate source rewards C_star C_h
  let w := (firstLiveWindow R).length
  let B := collectionWindow R w
  change r ∈ B at hmem
  obtain ⟨whole, k, hmap, hpast, htime, hprefix, hrecord⟩ := actual_past_cells_source_prefix
    (rate := rate) rewards C_star C_h source t r hr
  have hwle : w ≤ R.length := (List.takeWhile_prefix _).length_le
  have hwshort : w < R.length := by
    by_contra hnot
    have heq : w = R.length := by omega
    have hnil : B = [] := by
      simp only [B, collectionWindow, heq, List.drop_length, List.take_nil,
        List.drop_eq_nil_of_le (Nat.le_succ _), List.takeWhile_nil, List.nil_append]
    rw [hnil] at hmem
    cases hmem
  have hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
    apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mp
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h with
    | none =>
        have hnil := (ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
          rate rewards C_star C_h source hlaunch).1
        have hk := k.isLt
        have hzero := congrArg List.length hnil
        simp only [List.length_nil] at hzero
        omega
    | some active => rfl
  let count := p.T - s
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h source
  have hfull : R = (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h source hc
  have hlen : R.length = count := by
    rw [hfull]
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : (firstLiveWindow (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hs).records).length < count := by
    rw [← hfull]
    exact lt_of_lt_of_eq hwshort hlen
  obtain ⟨P, hanchor, hsigma, hwH, hcells⟩ := actual_first_collection_data
    (rate := rate) rewards C_star C_h source hc count hs hshort hfull
  change P.sigma.val = s at hsigma
  change w ≤ ReplayWeightStability.episodeHorizon rate.eta.val at hwH
  change ∀ (i : ℕ) (hi : i < B.length),
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (call : ReferenceCollectionSegmentExtraction.Choice rate),
      call.payload = P ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate B[i] = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 B[i] = some c ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 B[i] =
        some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
      c.rate = P.rate ∧
      c.enabled = decide (B[i].input.time.val + 1 <
        FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma) ∧
      B[i].input.time.val = s + w + i ∧ R[w + i]? = some B[i] at hcells
  obtain ⟨j, hj, hBj⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨c, call, hpay, hcell, hread, hcall, hrate, _henabled, hdate, _hindex⟩ := hcells j hj
  have hreadR : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
    simpa only [hBj] using hread
  have hcallR : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
      some ⟨call.payload, call.preLedger, call.started, call.weights⟩ := by
    simpa only [hBj] using hcall
  have hcellR : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simpa only [hBj] using hcell
  have hlookup : R[k.val]? = some r := by
    rw [List.getElem?_eq_getElem k.isLt]
    exact congrArg some hrecord
  have hrecordTime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate source rewards C_star C_h k.val r hlookup
  have hrtime : r.input.time = t := Fin.ext (hrecordTime.trans htime.symm)
  have hdateR : r.input.time.val = s + w + j := by simpa only [hBj] using hdate
  change r.input.time.val = s + k.val at hrecordTime
  have hkdate : k.val = w + j := by omega
  let L := whole.take k.val
  have hwholeLength : whole.length = R.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map] at h
    exact h.symm
  have hLlen : L.length = k.val := by
    simp only [L, List.length_take]
    exact Nat.min_eq_left (by rw [hwholeLength]; exact k.isLt.le)
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hgrid : FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ≤ s + 1 + H := by
    simpa only [hsigma] using grid_boundary_le_start_add_horizon (rate := rate) P.sigma
  have hdisabled : ∀ d ∈ L.drop H, d.enabled = false := by
    intro d hd
    obtain ⟨q, hq, heq⟩ := List.mem_iff_getElem.mp hd
    have hqk : H + q < k.val := by
      have hlength : (L.drop H).length = k.val - H := by rw [List.length_drop, hLlen]
      rw [hlength] at hq
      omega
    have hqR : H + q < R.length := lt_trans hqk k.isLt
    have hqWhole : H + q < whole.length := by rw [hwholeLength]; exact hqR
    have hwholeD : whole[H + q]'hqWhole = d := by
      simpa only [L, List.getElem_drop, List.getElem_take] using heq
    have hwn : w ≤ H + q := by omega
    have hn : H + q - w < B.length := by omega
    obtain ⟨cell, _choice, _hpay, hcellB, _hreadB, _hcallB, _hrateB,
      henabledB, hdateB, hindexB⟩ := hcells (H + q - w) hn
    have hi : w + (H + q - w) = H + q := Nat.add_sub_of_le hwn
    have hindex' : R[H + q]? = some B[H + q - w] := by
      simpa only [hi] using hindexB
    have hrecordB : R[H + q]'hqR = B[H + q - w] :=
      (List.getElem?_eq_some_iff.mp hindex').2
    have hsource := actual_cell0_source_value
      (rate := rate) rewards C_star C_h source whole hmap ⟨H + q, hqR⟩
    have hsourceB : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate B[H + q - w] =
        some (whole[H + q]'hqWhole) := by
      change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (R[H + q]'hqR) =
        some (whole[H + q]'hqWhole) at hsource
      exact (congrArg (fun record => ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record)
        hrecordB).symm.trans hsource
    have hcellWhole : cell = whole[H + q]'hqWhole :=
      Option.some.inj (hcellB.symm.trans hsourceB)
    have hcellDisabled : cell.enabled = false := by
      rw [henabledB, hdateB]
      exact decide_eq_false (by omega)
    exact (congrArg RecordedQueueRun.RoundInput.enabled
      (hcellWhole.trans hwholeD)).symm.trans hcellDisabled
  have hband := stopped_prefix_envelope rate L H (le_refl H) hdisabled
  obtain ⟨sourceWord, hsame, hscore⟩ := actual_prefix_stopped_score_vector
    (rate := rate) rewards C_star C_h source t whole k htime hprefix
  obtain ⟨payload, ledger, started, weights, _out, hactualCall, _hpost,
      _hrecording, _he, heClock, hactualRate, _hreward, _hgate⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hreadR
  have htuple := Option.some.inj (hactualCall.symm.trans hcallR)
  have hpayload : payload = call.payload := congrArg Sigma.fst htuple
  have hstarted : started = call.started := congrArg (fun x => x.2.2.1) htuple
  have hrateCall : c.rate = call.payload.rate := by rw [← hpayload]; exact hactualRate
  have heClock' : c.enabled = decide (t.val + 1 < call.started.clock.g) := by
    simpa only [hrtime, hstarted] using heClock
  have hanchorCall : call.payload.anchor = (fun _ => 1) :=
    (congrArg (fun P : Payload rate => P.anchor) hpay).trans hanchor
  refine ⟨L, c, call, hpast, ?_, hrtime, hcellR, hreadR, hcallR, hanchorCall,
    hrateCall, rfl, heClock', ?_, sourceWord, ?_, ?_⟩
  · rw [hLlen, htime]
    omega
  · intro a
    have ha := congrFun hanchorCall a
    rw [ha, mul_one]
    exact ⟨zero_lt_one, hband a⟩
  · rw [hLlen]
    exact hsame
  · intro a
    rw [hLlen]
    exact hscore a

end Bandits.Support.ReferenceFirstCollectionWeightEnvelope

end
