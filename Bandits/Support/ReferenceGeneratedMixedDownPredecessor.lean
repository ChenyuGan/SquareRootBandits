/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchDetectorMass
public import Bandits.Support.ReferenceGeneratedPrelaunchDownLaunchCohortHistory

import Lean.Elab.Tactic.Omega

/-!
# Same-birth mixed DOWN predecessors

Deterministic events on the original source, with all inherited candidate
flags retained. Level zero is the actual birth. Positive levels combine the
literal prelaunch and inherited postlaunch detectors.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-153`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:60-112,127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.

These are internal event results. Probability recurrence and iteration belong
to the subsequent mixed at-birth tail consumer.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedMixedDownPredecessor

open ConstructorDimensions BootstrapDimensions MeasureTheory ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open ReferenceGeneratedPrelaunchDownCurrentPair
open ReferenceGeneratedPrelaunchDownCohortInterval
open ReferenceGeneratedPrelaunchDownOccurrenceTail
open ReferenceGeneratedPrelaunchDownOccurrencePredecessor
open ReferenceGeneratedInheritedDownCompletion
open ReferenceGeneratedInheritedDownCohort
open ReferenceGeneratedInheritedDownPrefixMarker
open ReferenceGeneratedInheritedDownPostlaunchOccurrence
open ReferenceGeneratedDownBatchCalendar
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The actual mixed detector, with the operational quota guard. -/
def mixedDownDetector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  if hq : 1 ≤ q then
    if hqQ : q ≤ AffineBatchDecoder.quota p then
      prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q ∪
        inheritedDownPostlaunchDetector rate rewards C_star C_h i alpha k q
          hAlpha w hq hqQ control0
    else ∅
  else {z | birthAt rate rewards C_star C_h z i alpha hAlpha k}

/-- Both actual unhashed occurrence unions, before the current hash equation. -/
def mixedDownOccurrenceUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | ∃ r : Fin p.T,
    prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} ∪
      inheritedDownPostlaunchOccurrenceUnion rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0

@[simp] theorem mixedDownDetector_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p) :
    mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 0 =
      {z | birthAt rate rewards C_star C_h z i alpha hAlpha k} := by
  simp only [mixedDownDetector, dite_eq_right (show ¬ 1 ≤ 0 by omega)]

theorem mixedDownDetector_positive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 q =
      prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q ∪
        inheritedDownPostlaunchDetector rate rewards C_star C_h i alpha k q
          hAlpha w hq hqQ control0 := by
  simp only [mixedDownDetector, dite_eq_left hq, dite_eq_left hqQ]

private theorem prelaunch_tests_succ
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨r.val + 1, hnext⟩ =
      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
        (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hstep :=
            ReferenceGeneratedPrelaunchDownActiveBridge.source_prelaunch_down_active_successor
              rate rewards C_star C_h z i r hnext
          rw [hpref] at hstep
          exact hstep.2.2.2.1
      | inr inactive =>
          have hstep :=
            ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_inactive_successor
              rate rewards C_star C_h z i r hnext
          rw [hpref] at hstep
          rcases hstep with ⟨hcurrent, htests, hnextData⟩
          cases hn : source_prelaunch_down_prefix rate rewards C_star C_h z i
              ⟨r.val + 1, hnext⟩ with
          | inl nextBranch =>
              cases nextBranch with
              | inl nextActive =>
                  rw [hn] at hnextData
                  simpa only [hcurrent, htests, Option.toList_none, List.append_nil]
                    using hnextData.1
              | inr nextInactive =>
                  rw [hn] at hnextData
                  simpa only [hcurrent, htests, Option.toList_none, List.append_nil]
                    using hnextData.1
          | inr nextStopped =>
              rw [hn] at hnextData
              simpa only [hcurrent, htests, Option.toList_none, List.append_nil]
                using hnextData.1
  | inr stopped =>
      have hstop :=
        ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_stopped_to_terminal
          rate rewards C_star C_h z i r
      rw [hpref] at hstop
      obtain ⟨_, _, _, hcurrent, hfuture⟩ := hstop
      obtain ⟨_, _, _, htests, _, _⟩ := hfuture ⟨r.val + 1, hnext⟩ (by simp)
      simpa only [hcurrent, Option.toList_none, List.append_nil] using htests

private theorem prelaunch_current_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T) (test : ExecutedTest p)
    (hcurrent : source_prelaunch_down_current_test rate rewards C_star C_h z i r = some test) :
    test.time = r ∧
      test.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i) := by
  have hA : A_r rate rewards C_star C_h z i r := by
    simp only [A_r, hcurrent, Option.isSome_some]
  have heq := current_test_eq_some_of_selected_positive rate rewards C_star C_h z i r
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rfl hA
  have ht := Option.some.inj (hcurrent.symm.trans heq)
  exact ⟨congrArg ExecutedTest.time ht, congrArg ExecutedTest.sample ht⟩

private theorem prelaunch_tests_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hzero : 0 < p.T) :
    source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨0, hzero⟩ = [] := by
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨0, hzero⟩ with
  | inl branch =>
      cases branch with
      | inl active => simp [source_prelaunch_down_prefix_tests, hpref]
      | inr inactive => simp only [source_prelaunch_down_prefix_tests, hpref]
  | inr stopped =>
      have hidx : (roundBlockIndex p ⟨0, hzero⟩).val = 0 := by
        simp [roundBlockIndex]
      have heq : stopped.val.1 = ReferenceInitializationRun.initial p := by
        simpa only [hidx, ReferenceInitializationRun.run_zero] using stopped.property.2.1
      have hnone : stopped.val.1.crossing = none := by rw [heq]; rfl
      exact (stopped.property.1 hnone).elim

/-- The final retained prelaunch test is an actual current call at its real
round, even when arbitrary zero-test rounds follow it. -/
private theorem prelaunch_last_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ∀ n (hn : n < p.T),
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨n, hn⟩).length > 0 →
      ∃ (r : Fin p.T) (test : ExecutedTest p), r.val < n ∧
        source_prelaunch_down_current_test rate rewards C_star C_h z i r = some test ∧
        source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨n, hn⟩ =
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++ [test] := by
  intro n
  induction n with
  | zero =>
      intro hn hpos
      rw [prelaunch_tests_zero rate rewards C_star C_h i z hn] at hpos
      simp only [List.length_nil, Nat.lt_irrefl] at hpos
  | succ n ih =>
      intro hn hpos
      let r : Fin p.T := ⟨n, by omega⟩
      have hstep := prelaunch_tests_succ rate rewards C_star C_h i z r hn
      cases hcurrent : source_prelaunch_down_current_test rate rewards C_star C_h z i r with
      | none =>
          simp only [hcurrent, Option.toList_none, List.append_nil] at hstep
          rw [hstep] at hpos
          obtain ⟨u, test, hut, hcur, hlist⟩ := ih (by omega) hpos
          exact ⟨u, test, by omega, hcur, hstep.trans hlist⟩
      | some test =>
          exact ⟨r, test, by dsimp [r]; omega, hcurrent, by
            simpa only [hcurrent, Option.toList_some] using hstep⟩

/-- Extract the actual birth and the entire same-birth launch interval from
L at the SAME original source. The boundary option, rather than a terminal
projection alone, identifies the birth parameter. -/
private theorem launch_birth_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T) (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s.val s.isLt)
    (hk : (generatedInheritedInitialFollower rate rewards C_star C_h
      s.val s.isLt x i).downBatch.completed.length = k)
    (hboundary : sourcePrelaunchDownCohortBoundary rate rewards C_star C_h x.val i k = some alpha) :
    birthAt rate rewards C_star C_h x.val i alpha hAlpha k ∧
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s =
      sourcePrelaunchDownTests rate rewards C_star C_h x.val i) ∧
    (∀ test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i,
      alpha ≤ test.time.val ∧ test.time.val < s.val) ∧
    (∀ u, alpha ≤ u → ∀ hu : u ≤ s.val,
      ∃ a stateU,
        sourcePrelaunchDownActualCohort rate rewards C_star C_h x.val i u
          (hu.trans s.isLt.le) = some (a, stateU) ∧
        stateU.downBatch.completed.length = k ∧
        bankBirth a stateU.downBatch = some alpha ∧
        ∀ w,
          source_prelaunch_down_current_cohort_flags rate rewards C_star C_h x.val i
            ⟨u, hu.trans_lt s.isLt⟩ w =
          ((generatedInheritedDownOldFirstTests rate rewards C_star C_h
            s.val s.isLt x i).filter (fun test => test.time.val < u)).map
              (sourcePrelaunchDownCandidateFlag w)) := by
  have hStop : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h x.val)).completed < p.T := by
    change ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed < p.T
    rw [x.property.2]
    exact s.isLt
  have hhistory :=
    ((ReferenceGeneratedPrelaunchDownLaunchCohortHistory.source_launch_down_historical_cohort
      rate rewards C_star C_h x.val i).2 x.property.1).1 hStop
  simp only [sourceReferenceInput, x.property.2] at hhistory
  obtain ⟨y, _hy, _hlaunch, _hfollower, _hseed, _hfailure, _hnew, _hshort,
    _hpending, a, _ha, _hcases, _hactual, htests, beta, hBeta, _hBetaS,
    _hbank, hbirth, _hunique, hboundaryBeta, hOld, _hforced⟩ :=
      hhistory
  have hbeta : beta = alpha := by
    have hb := hboundaryBeta
    change sourcePrelaunchDownCohortBoundary rate rewards C_star C_h x.val i
      (generatedInheritedInitialFollower rate rewards C_star C_h
        s.val s.isLt x i).downBatch.completed.length = some beta at hb
    rw [hk, hboundary] at hb
    exact (Option.some.inj hb).symm
  subst beta
  have hOldEq :
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h x.val i s.val s.isLt.le).drop
        (AffineBatchDecoder.quota p *
          (generatedInheritedInitialFollower rate rewards C_star C_h
            s.val s.isLt x i).downBatch.completed.length) =
      generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i := by
    rw [htests]
    rfl
  dsimp only [generatedInheritedInitialFollower] at hOldEq
  change _ ∧ _ ∧ _ at hOld
  rw [hOldEq] at hOld
  refine ⟨?_, ?_, hOld.2.2.1, ?_⟩
  · change birthAt rate rewards C_star C_h x.val i alpha hAlpha
      (generatedInheritedInitialFollower rate rewards C_star C_h
        s.val s.isLt x i).downBatch.completed.length at hbirth
    rwa [hk] at hbirth
  · rw [← sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h x.val i
      s.val s.isLt.le s.isLt]
    exact htests
  · intro u hau hus
    obtain ⟨stateU, hactualU, hcompleted, hbankU, _hpendingU, hflagsU⟩ :=
      hOld.2.2.2 u hau hus
    refine ⟨a, stateU, hactualU, ?_, hbankU, ?_⟩
    · change stateU.downBatch.completed =
        (generatedInheritedInitialFollower rate rewards C_star C_h
          s.val s.isLt x i).downBatch.completed at hcompleted
      rw [hcompleted, hk]
    · intro w
      have hflags := hflagsU w
      simpa only [dite_eq_left (hus.trans_lt s.isLt)] using hflags

private theorem past_indicator_of_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) (har : alpha ≤ r.val)
    (hbirth : birthAt rate rewards C_star C_h z i alpha hAlpha k)
    (hA : A_r rate rewards C_star C_h z i r)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hactual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i r.val r.isLt.le =
      some (a, state))
    (hk : state.downBatch.completed.length = k)
    (hb : bankBirth a state.downBatch = some alpha)
    (hlen : state.downBatch.pending.length = q - 1)
    (hflags : List.Forall (fun flags => flags.1 ∧ flags.2)
      (source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i r w)) :
    source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k q hAlpha r w := by
  refine ⟨hq, hqQ, har, hbirth, ?_⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have heq := sourcePrelaunchDownActualCohort_of_active
            rate rewards C_star C_h z i r.val r.isLt.le r.isLt active hpref
          have hpair := Option.some.inj (heq.symm.trans hactual)
          have ha := (Prod.mk.inj hpair).1
          have hs := (Prod.mk.inj hpair).2
          change active.val.2.2.2.downBatch.completed.length = k ∧ _
          rw [ha, hs]
          exact ⟨hk, hb, hlen, hflags⟩
      | inr inactive =>
          simp only [A_r, source_prelaunch_down_current_test, hpref,
            Option.isSome_none, Bool.false_eq_true] at hA
  | inr stopped =>
      simp only [A_r, source_prelaunch_down_current_test, hpref,
        Option.isSome_none, Bool.false_eq_true] at hA

private theorem prelaunch_tests_extend
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T) :
    ∀ n (hn : r.val + n < p.T),
      ∃ tail, source_prelaunch_down_prefix_tests rate rewards C_star C_h z i
          ⟨r.val + n, hn⟩ =
        source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++ tail := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact ⟨[], by simp only [Nat.add_zero, List.append_nil]⟩
  | succ n ih =>
      intro hn
      obtain ⟨tail, htail⟩ := ih (by omega)
      let u : Fin p.T := ⟨r.val + n, by omega⟩
      have hstep := prelaunch_tests_succ rate rewards C_star C_h i z u (by dsimp [u]; omega)
      refine ⟨tail ++ (source_prelaunch_down_current_test rate rewards C_star C_h z i u).toList, ?_⟩
      have hfin : (⟨u.val + 1, by dsimp [u]; omega⟩ : Fin p.T) =
          ⟨r.val + (n + 1), hn⟩ := Fin.ext (by dsimp [u]; omega)
      rw [← hfin, hstep, htail, List.append_assoc]

private theorem prelaunch_occurrence_rank
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r) :
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).length =
      AffineBatchDecoder.quota p * k + (q - 1) := by
  rcases hOcc.1 with ⟨_, _, _, _, hmatch⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref] at hmatch
          obtain ⟨hk, _, hlen, _⟩ := hmatch
          have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
          rw [hpref] at hcensus
          have hlength := congrArg List.length hcensus.1
          rw [List.length_map, AffineBatchDecoder.length_collected _ hcensus.2.2.1,
            hk, hlen, Nat.mul_comm] at hlength
          exact hlength
      | inr inactive => simp only [hpref] at hmatch
  | inr stopped => simp only [hpref] at hmatch

private theorem prelaunch_current_before_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s.val s.isLt)
    (r : Fin p.T) (hA : A_r rate rewards C_star C_h x.val i r) :
    r.val < s.val := by
  obtain ⟨hnone, _⟩ := (A_r_iff rate rewards C_star C_h x.val i r).mp hA
  by_contra hnot
  have hsr : s.val ≤ r.val := by omega
  let input := sourceReferenceInput rate rewards C_star C_h x.val
  let b := ReferenceInitializationRun.output input
  have hElapsed : ReferenceInitializationRun.elapsed p b.completed = s.val := x.property.2
  have hmul : b.completed * B_boot p ≤ r.val := by
    dsimp only [ReferenceInitializationRun.elapsed] at hElapsed
    have hsT := s.isLt
    omega
  have hindex : b.completed ≤ (roundBlockIndex p r).val := by
    change b.completed ≤ r.val / B_boot p
    exact (Nat.le_div_iff_mul_le (B_boot_pos p)).mpr hmul
  have hown : ReferenceInitializationRun.run input b.completed = b :=
    ReferenceInitializationPrefixInvariance.run_at_completed input (n_boot p) le_rfl
  have hcross : (ReferenceInitializationRun.run input b.completed).crossing.isSome = true := by
    rw [hown]
    exact x.property.1
  have hstop := ReferenceInitializationRun.run_stops_at_crossing input b.completed
    ((roundBlockIndex p r).val - b.completed) hcross
  rw [Nat.add_sub_of_le hindex, hown] at hstop
  have hnone' : (ReferenceInitializationRun.run input (roundBlockIndex p r).val).crossing = none := hnone
  rw [hstop] at hnone'
  have hc : b.crossing.isSome = true := x.property.1
  rw [hnone'] at hc
  cases hc

/-- The last inherited prelaunch test is a same-birth hashed occurrence.
Every supplied condition here is extracted from an actual postlaunch event;
no such history condition is an input to the public event inclusions. -/
private theorem old_last_hashed_occurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s.val s.isLt)
    (hk : (generatedInheritedInitialFollower rate rewards C_star C_h
      s.val s.isLt x i).downBatch.completed.length = k)
    (hboundary : sourcePrelaunchDownCohortBoundary rate rewards C_star C_h x.val i k = some alpha)
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (hlen : (generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i).length = q)
    (hgood : ∀ test ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i,
      test.sent ≠ some w ∧ AffineChannelLaw.affineHash test.sample w = 1) :
    ∃ r : Fin p.T,
      prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w x.val r := by
  obtain ⟨hbirth, htests, htimes, hinterval⟩ :=
    launch_birth_interval rate rewards C_star C_h i alpha k hAlpha s x hk hboundary
  let Old := generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i
  let Qk := AffineBatchDecoder.quota p * k
  have hOld : Old =
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s).drop Qk := by
    dsimp only [Old, generatedInheritedDownOldFirstTests, Qk]
    rw [hk, htests]
  have hpositive : 0 < (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s).length := by
    have hdrop := congrArg List.length hOld
    simp only [List.length_drop] at hdrop
    change Old.length = q at hlen
    omega
  obtain ⟨r, test, hrs, hcurrent, hsplit⟩ :=
    prelaunch_last_current rate rewards C_star C_h i x.val s.val s.isLt hpositive
  change source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s =
    source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i r ++ [test] at hsplit
  have hsplitLength := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons, List.length_nil] at hsplitLength
  have hdropLength :
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s).length - Qk = q := by
    rw [← List.length_drop, ← hOld]
    exact hlen
  have htotal :
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i s).length = Qk + q := by
    omega
  have hbefore : Qk ≤
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i r).length := by
    change Old.length = q at hlen
    omega
  have hOldSplit : Old =
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i r).drop Qk ++ [test] := by
    rw [hOld, hsplit, List.drop_append_of_le_length hbefore]
  have hmem : test ∈ Old := by
    rw [hOldSplit]
    exact List.mem_append_right _ (List.mem_singleton_self test)
  obtain ⟨htime, hsample⟩ := prelaunch_current_time rate rewards C_star C_h i x.val r test hcurrent
  have har : alpha ≤ r.val := by simpa only [htime] using (htimes test hmem).1
  obtain ⟨a, state, hactual, hcompleted, hbank, hflags⟩ := hinterval r.val har hrs.le
  have hA : A_r rate rewards C_star C_h x.val i r := by
    simp only [A_r, hcurrent, Option.isSome_some]
  have hpending : state.downBatch.pending.length = q - 1 := by
    cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h x.val i r with
    | inl branch =>
        cases branch with
        | inl active =>
            have heq := sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h x.val i
              r.val r.isLt.le r.isLt active hpref
            have hs := (Prod.mk.inj (Option.some.inj (heq.symm.trans hactual))).2
            have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h x.val i r
            rw [hpref] at hcensus
            have hp := congrArg List.length hcensus.2.1
            simp only [hs, hcompleted, List.length_drop, List.length_map] at hp
            dsimp only [Qk] at htotal
            omega
        | inr inactive =>
            simp only [A_r, source_prelaunch_down_current_test, hpref,
              Option.isSome_none, Bool.false_eq_true] at hA
    | inr stopped =>
        simp only [A_r, source_prelaunch_down_current_test, hpref,
          Option.isSome_none, Bool.false_eq_true] at hA
  have hflagAll : List.Forall (fun flags => flags.1 ∧ flags.2)
      (source_prelaunch_down_current_cohort_flags rate rewards C_star C_h x.val i r w) := by
    rw [hflags w, List.forall_iff_forall_mem]
    intro flags hflagsMem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hflagsMem
    exact hgood t (List.mem_of_mem_filter ht)
  refine ⟨r, ⟨?_, hA⟩, ?_⟩
  · exact past_indicator_of_actual rate rewards C_star C_h i alpha k q hAlpha w
      x.val r hq hqQ har hbirth hA a state hactual hcompleted hbank hpending hflagAll
  · change AffineChannelLaw.affineHash
      (((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2 r).2 (0, i)) w = 1
    rw [← hsample]
    exact (hgood test hmem).2

private theorem record_called_down_selected
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut)
    (hcomparison : cut.rawComparison.isSome = true) :
    ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time := by
  have hdiag : ReferenceActiveAffinePositiveTest.downDiagnosticCall
      (record.output.followers i) = true := by
    simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hcut, hcomparison]
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i] at hdiag
  change ReferenceActiveAffinePositiveTest.downDiagnosticCall
    (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) = true at hdiag
  rw [ReferenceActiveAffinePositiveTest.finishFollower_down_call,
    ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix] at hdiag
  cases hc : (record.output.preparation.followers.followers i).configuration with
  | dagger => simp only [ReferenceActiveAffinePositiveTest.downPrefixGate, hc, Bool.false_eq_true] at hdiag
  | ordinary state memory =>
      simp only [ReferenceActiveAffinePositiveTest.downPrefixGate, hc, decide_eq_true_eq] at hdiag
      have hselected := hdiag.2.1
      rw [(record.output.preparation.follower_alignment i).1,
        (record.output.preparation.follower_alignment i).2.1,
        (record.output.preparation.follower_alignment i).2.2.1] at hselected
      exact hselected

private theorem new_test_selector_sample
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s.val s.isLt)
    (test : ExecutedTest p)
    (hmem : test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownNewFirstTests
      rate rewards C_star C_h s.val s.isLt i x) :
    ReferenceSelectedAffinePairLaw.selector p test.time x.val =
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val,
        some ((0, i) : ContinuousLearningRows.Channel p)) ∧
    test.sample = ((x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
      test.time).2 (0, i) := by
  obtain ⟨_n, record, hrecord, _hrecordTime, htime, hsample, _htest,
    _call, cut, _hcall, hcut, _hcallTime, _hcallSample, _hsent,
    _hexpected, _hpositive, hcomparison⟩ :=
      generated_inherited_down_new_test_physical (rate := rate)
        rewards C_star C_h s.val s.isLt x i test hmem
  have hselected := record_called_down_selected rate record i cut hcut hcomparison
  have hrecords := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s.val (p.T - s.val) (by omega)
    (generatedSourceRunInput rate rewards C_star C_h s.val s.isLt x)
  change record ∈ (ReferenceActiveHorizonMeasurability.runOfInput
    s.val (p.T - s.val) (by omega)
    (generatedSourceRunInput rate rewards C_star C_h s.val s.isLt x)).records at hrecord
  rw [hrecords] at hrecord
  obtain ⟨u, hu⟩ := List.mem_ofFn.mp hrecord
  have hrow : record.input.row =
      x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) := by
    rw [← hu]
    rfl
  rw [hrow, ← htime] at hselected
  refine ⟨?_, hsample⟩
  apply (ReferenceSelectedAffinePairLaw.selector_eq_iff p
    (ActualInitializationPhysicalStep.selectedRowIndex p x.val) test.time (0, i) x.val).mpr
  refine ⟨rfl, ?_⟩
  simp only [ReferenceSelectedAffinePairLaw.selectedChannel,
    ReferenceSelectedAffinePairLaw.channelFromDraws, hselected.1, ite_true, hselected.2]

/-- Backwards census of the cumulative postlaunch prefix. A missing current
call adds no test and does not clear the inherited flags. -/
private theorem postlaunch_last_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (s : Fin p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s.val s.isLt) :
    ∀ n (hn : n ≤ p.T - s.val),
      inheritedDownPrefix (rate := rate) rewards C_star C_h s.val s.isLt i x n =
          generatedInheritedDownOldFirstTests rate rewards C_star C_h s.val s.isLt x i ∨
      ∃ (u : ℕ) (hu : u < n) (test : ExecutedTest p),
        executedTestOfRound rate
          ((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2
            ⟨u, by omega⟩) = some test ∧
        inheritedDownPrefix (rate := rate) rewards C_star C_h s.val s.isLt i x n =
          inheritedDownPrefix (rate := rate) rewards C_star C_h s.val s.isLt i x u ++ [test] := by
  intro n
  induction n with
  | zero =>
      intro _hn
      exact Or.inl (inheritedDownPrefix_zero (rate := rate) rewards C_star C_h s.val s.isLt i x)
  | succ n ih =>
      intro hn
      have hstep := inheritedDownPrefix_succ (rate := rate) rewards C_star C_h s.val s.isLt
        i x n (by omega)
      cases hcurrent : executedTestOfRound rate
          ((generatedSourceObservation rate rewards C_star C_h s.val s.isLt i x).2
            ⟨n, by omega⟩) with
      | none =>
          simp only [hcurrent, Option.toList_none, List.append_nil] at hstep
          rcases ih (by omega) with hold | ⟨u, hu, test, htest, hsplit⟩
          · exact Or.inl (hstep.trans hold)
          · exact Or.inr ⟨u, by omega, test, htest, hstep.trans hsplit⟩
      | some test =>
          exact Or.inr ⟨n, by omega, test, hcurrent, by
            simpa only [hcurrent, Option.toList_some] using hstep⟩

/-- Every actual postlaunch q-th occurrence has its same-source mixed
predecessor. No launch, birth, history, flags, or predecessor is a root input. -/
theorem inheritedDownPostlaunchOccurrence_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (δ : Lambda p alpha)
    (hOcc : z ∈ inheritedDownPostlaunchOccurrence rate rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ) :
    z ∈ mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1) := by
  rcases hOcc with ⟨hselector, x, hx, hAlphaS, hk, hboundary, hlen, hgood,
    _current, _hcurrent, _hsent⟩
  subst z
  have hbirth := (launch_birth_interval rate rewards C_star C_h i alpha k hAlpha
    δ.1.2.1 x hk hboundary).1
  by_cases hone : q = 1
  · have hzero : q - 1 = 0 := by omega
    rw [hzero, mixedDownDetector_zero]
    exact hbirth
  have hprev : 1 ≤ q - 1 := by omega
  have hprevQ : q - 1 ≤ AffineBatchDecoder.quota p := by omega
  rw [mixedDownDetector_positive rate rewards C_star C_h i alpha k (q - 1)
    hAlpha w hprev hprevQ control0]
  rcases postlaunch_last_current rate rewards C_star C_h i δ.1.2.1 x
      (δ.1.2.2.val - δ.1.2.1.val) (by omega) with hold | ⟨u, hu, test, hcurrent, hsplit⟩
  · left
    have hOldLength :
        (generatedInheritedDownOldFirstTests rate rewards C_star C_h
          δ.1.2.1.val δ.1.2.1.isLt x i).length = q - 1 := by
      rw [← hold]
      exact hlen
    have hOldGood : ∀ t ∈ generatedInheritedDownOldFirstTests rate rewards C_star C_h
        δ.1.2.1.val δ.1.2.1.isLt x i,
        t.sent ≠ some w ∧ AffineChannelLaw.affineHash t.sample w = 1 := by
      rw [← hold]
      exact hgood
    obtain ⟨r, hhit⟩ := old_last_hashed_occurrence rate rewards C_star C_h i alpha k
      (q - 1) hAlpha w δ.1.2.1 x hk hboundary hprev hprevQ hOldLength hOldGood
    have hlevel : q - 1 = (q - 2) + 1 := by omega
    rw [hlevel, prelaunchDownDetector_succ]
    exact ⟨r, by simpa only [← hlevel] using hhit⟩
  · right
    have hlength :
        (inheritedDownPrefix (rate := rate) rewards C_star C_h
          δ.1.2.1.val δ.1.2.1.isLt i x u).length = (q - 1) - 1 := by
      rw [hsplit, List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    have htestGood : test.sent ≠ some w ∧ AffineChannelLaw.affineHash test.sample w = 1 :=
      hgood test (hsplit ▸ List.mem_append_right _ (List.mem_singleton_self test))
    have hpastGood : ∀ t ∈ inheritedDownPrefix (rate := rate) rewards C_star C_h
        δ.1.2.1.val δ.1.2.1.isLt i x u,
        t.sent ≠ some w ∧ AffineChannelLaw.affineHash t.sample w = 1 := by
      intro t ht
      apply hgood t
      rw [hsplit]
      exact List.mem_append_left _ ht
    have hnew := inheritedDownPrefix_current_mem (rate := rate) rewards C_star C_h
      δ.1.2.1.val δ.1.2.1.isLt i x u (q - 1) (by omega) hprev hprevQ hlength test hcurrent
    obtain ⟨hsel, hsample⟩ := new_test_selector_sample rate rewards C_star C_h i δ.1.2.1 x test hnew
    let r : Fin p.T := ⟨δ.1.2.1.val + u, by omega⟩
    have htime : test.time = r := Fin.ext
      (inheritedDownCurrentTest_time (rate := rate) rewards C_star C_h
        δ.1.2.1.val δ.1.2.1.isLt i x ⟨u, by omega⟩ test hcurrent)
    have hrow : ActualInitializationPhysicalStep.selectedRowIndex p x.val = δ.1.1 := by
      exact congrArg Prod.fst hselector
    have hselr : ReferenceSelectedAffinePairLaw.selector p r x.val =
        (δ.1.1, some ((0, i) : ContinuousLearningRows.Channel p)) := by
      simpa only [htime, hrow] using hsel
    have hsampleR : test.sample = ((x.val.1.2 δ.1.1).2 r).2 (0, i) := by
      simpa only [htime, hrow] using hsample
    let ε : Lambda p alpha := ⟨(δ.1.1, δ.1.2.1, r), hAlphaS, by dsimp [r]; omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨ε, ?_, ?_⟩
    · refine ⟨hselr, x, rfl, hAlphaS, hk, hboundary, ?_, ?_, test, ?_, htestGood.1⟩
      · simpa only [ε, r, Nat.add_sub_cancel_left] using hlength
      · simpa only [ε, r, Nat.add_sub_cancel_left] using hpastGood
      · simpa only [ε, r, Nat.add_sub_cancel_left] using hcurrent
    · change AffineChannelLaw.affineHash (((x.val.1.2 δ.1.1).2 r).2 (0, i)) w = 1
      rw [← hsampleR]
      exact htestGood.2

/-- The postlaunch unhashed union is contained in the same mixed preceding
level, including the actual birth at level zero. -/
theorem inheritedDownPostlaunchOccurrenceUnion_subset_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    inheritedDownPostlaunchOccurrenceUnion rate rewards C_star C_h
        i alpha k q hAlpha w hq hqQ control0 ⊆
      mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1) := by
  intro z hz
  obtain ⟨δ, hOcc⟩ := Set.mem_iUnion.mp hz
  exact inheritedDownPostlaunchOccurrence_previous rate rewards C_star C_h
    i alpha k q hAlpha w hq hqQ control0 z δ hOcc

/-- The full mixed unhashed occurrence union has an actual mixed predecessor.
All history and launch inputs are produced inside the two event proofs. -/
theorem mixedDownOccurrenceUnion_subset_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    mixedDownOccurrenceUnion rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 ⊆
      mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1) := by
  intro z hz
  rcases hz with ⟨r, hpre⟩ | hpost
  · have hprevious := prelaunch_occurrence_previous rate rewards C_star C_h
      i alpha k q hAlpha w z r hq hpre
    by_cases hone : q = 1
    · have hzero : q - 1 = 0 := by omega
      rw [hzero, mixedDownDetector_zero]
      rwa [hzero, prelaunchDownDetector_zero] at hprevious
    · have hprev : 1 ≤ q - 1 := by omega
      have hprevQ : q - 1 ≤ AffineBatchDecoder.quota p := by omega
      rw [mixedDownDetector_positive rate rewards C_star C_h i alpha k (q - 1)
        hAlpha w hprev hprevQ control0]
      exact Or.inl hprevious
  · exact inheritedDownPostlaunchOccurrenceUnion_subset_previous rate rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 hpost

/-- The same q-th test cannot occur in both phases. A prelaunch occurrence
has already increased the actual census past `Q*k+q-1` before launch. The
inherited postlaunch occurrence still has at most `q-1` old tests. -/
theorem prelaunch_postlaunch_occurrence_disjoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Disjoint
      {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ r : Fin p.T,
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r}
      (inheritedDownPostlaunchOccurrenceUnion rate rewards C_star C_h
        i alpha k q hAlpha w hq hqQ control0) := by
  apply Set.disjoint_left.mpr
  intro z hpre hpost
  obtain ⟨r, hpre⟩ := hpre
  obtain ⟨δ, hpost⟩ := Set.mem_iUnion.mp hpost
  rcases hpost with ⟨_hselector, x, hx, _hAlphaS, hk, hboundary, hlen, _hgood,
    _test, _hcurrent, _hsent⟩
  subst z
  have hrs := prelaunch_current_before_launch rate rewards C_star C_h i δ.1.2.1 x r hpre.2
  have hnext : r.val + 1 < p.T := by omega
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  obtain ⟨test, hcurrent, _htime, _hsent⟩ :=
    current_test_wrong_word rate rewards C_star C_h x.val i r w hpre.2
  have hstep : source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i rn =
      source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i r ++ [test] := by
    simpa only [hcurrent, Option.toList_some] using
      prelaunch_tests_succ rate rewards C_star C_h i x.val r hnext
  obtain ⟨tail, htail⟩ := prelaunch_tests_extend rate rewards C_star C_h i x.val rn
    (δ.1.2.1.val - rn.val) (by dsimp [rn]; omega)
  have hfin : (⟨rn.val + (δ.1.2.1.val - rn.val), by dsimp [rn]; omega⟩ : Fin p.T) =
      δ.1.2.1 := Fin.ext (by dsimp [rn]; omega)
  rw [hfin, hstep] at htail
  have hlengthFull := congrArg List.length htail
  simp only [List.length_append, List.length_cons, List.length_nil] at hlengthFull
  have hrank := prelaunch_occurrence_rank rate rewards C_star C_h
    i alpha k q hAlpha w x.val r hpre
  obtain ⟨_hbirth, htests, _htimes, _hinterval⟩ :=
    launch_birth_interval rate rewards C_star C_h i alpha k hAlpha δ.1.2.1 x hk hboundary
  have hOldLength :
      (generatedInheritedDownOldFirstTests rate rewards C_star C_h
        δ.1.2.1.val δ.1.2.1.isLt x i).length =
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h x.val i δ.1.2.1).length -
        AffineBatchDecoder.quota p * k := by
    simp only [generatedInheritedDownOldFirstTests, List.length_drop, hk, ← htests]
  change
    (generatedInheritedDownOldFirstTests rate rewards C_star C_h δ.1.2.1.val
        δ.1.2.1.isLt x i ++
      generatedInheritedDownTests rate rewards C_star C_h δ.1.2.1.val
        δ.1.2.1.isLt i x (δ.1.2.2.val - δ.1.2.1.val)).length = q - 1 at hlen
  rw [List.length_append] at hlen
  omega

/-- Hashed phase disjointness follows by dropping only the current hash
condition from each side of the actual unhashed disjointness theorem. -/
theorem prelaunch_postlaunch_detector_disjoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Disjoint
      (prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q)
      (inheritedDownPostlaunchDetector rate rewards C_star C_h
        i alpha k q hAlpha w hq hqQ control0) := by
  have hdisjoint := prelaunch_postlaunch_occurrence_disjoint rate rewards C_star C_h
    i alpha k q hAlpha w hq hqQ control0
  apply hdisjoint.mono
  · intro z hz
    have hlevel : q = (q - 1) + 1 := by omega
    rw [hlevel, prelaunchDownDetector_succ] at hz
    obtain ⟨r, hhit⟩ := hz
    exact ⟨r, by simpa only [← hlevel] using hhit.1⟩
  · intro z hz
    obtain ⟨δ, hhit⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨δ, hhit.1⟩

/-- Positive prelaunch levels beyond quota are empty by the literal
past-indicator quota check. -/
theorem prelaunchDownDetector_eq_empty_of_quota_lt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hquota : AffineBatchDecoder.quota p < q) :
    prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q = ∅ := by
  have hq : 1 ≤ q := by omega
  have hlevel : q = (q - 1) + 1 := by omega
  rw [hlevel, prelaunchDownDetector_succ]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨r, hhit⟩
  have hbound := hhit.1.1.2.1
  omega

/-- The total mixed family uses the same quota endpoint as both constituent
positive-level events. There is no additional operational branch. -/
theorem mixedDownDetector_eq_empty_of_quota_lt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hquota : AffineBatchDecoder.quota p < q) :
    mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 q = ∅ := by
  have hq : 1 ≤ q := by omega
  have hnot : ¬ q ≤ AffineBatchDecoder.quota p := by omega
  simp only [mixedDownDetector, dite_eq_left hq, dite_eq_right hnot]

/-- Every level is Borel on the WHOLE original source carrier. -/
theorem measurableSet_mixedDownDetector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ) :
    MeasurableSet (mixedDownDetector rate rewards C_star C_h i alpha k hAlpha w control0 q) := by
  by_cases hq : 1 ≤ q
  · by_cases hqQ : q ≤ AffineBatchDecoder.quota p
    · rw [mixedDownDetector_positive rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0]
      exact (ReferenceGeneratedPrelaunchDownDetectorMass.measurableSet_prelaunchDownDetector
        rate rewards C_star C_h i alpha k hAlpha w q).union
        (measurableSet_inheritedDownPostlaunchDetector
          rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0)
    · rw [mixedDownDetector_eq_empty_of_quota_lt rate rewards C_star C_h i alpha k q
        hAlpha w control0 (by omega)]
      exact MeasurableSet.empty
  · have hzero : q = 0 := by omega
    rw [hzero, mixedDownDetector_zero]
    exact ReferenceGeneratedPrelaunchDownPastFactor.measurableSet_birthAt
      rate rewards C_star C_h i alpha hAlpha k

/-- Both actual unhashed phase events, and hence their union, are Borel. -/
theorem measurableSet_mixedDownOccurrenceUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet
      (mixedDownOccurrenceUnion rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0) := by
  exact (ReferenceGeneratedPrelaunchDownDetectorMass.measurableSet_prelaunchDownOccurrenceUnion
    rate rewards C_star C_h i alpha k q hAlpha w).union
    (measurableSet_inheritedDownPostlaunchOccurrenceUnion
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0)

end Bandits.Support.ReferenceGeneratedMixedDownPredecessor
