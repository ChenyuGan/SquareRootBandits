/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
public import Bandits.Support.ReferenceGeneratedInheritedDownCohort
public import Bandits.Support.ReferenceGeneratedDownFreshSourceTail

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fin.Tuple.Take

/-!
# Actual inherited DOWN prefixes and measurable pair-remainder marker

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-153`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:60-112,127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.

This module keeps the initialized pending equations and appends only the
positive tests in the actual postlaunch calendar prefix. It reconstructs the
current physical input and a measurable marker for every removed DOWN pair.
The one-round half identity and source event composition belong to the next
module; no tail or manuscript closure is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceGeneratedInheritedDownCohort
open Bandits.Support.ReferenceGeneratedDownPrefixEvent
open Bandits.Support.ReferenceGeneratedAffineHashHalf

namespace Bandits.Support.ReferenceGeneratedInheritedDownPrefixMarker

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev Pair (p : Parameters) := ReferenceSelectedAffinePairLaw.Pair p
abbrev PairRemainder (p : Parameters) (j : Fin (M p)) (r : Fin p.T)
    (i : Fin (p.m - 1)) :=
  ReferenceSelectedAffinePairLaw.Remainder p j r (0, i)
abbrev LaunchSource {p : Parameters} {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) :=
  ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs

variable {p : Parameters} {rate : RateInput p}

/-- The literal inherited list at calendar offset `n`: the initialized old
pending equations followed by exactly the positive tests in `[s,s+n)`. -/
def inheritedDownPrefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs) (n : ℕ) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
      rate rewards C_star C_h s hs x i ++
    ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
      rate rewards C_star C_h s hs i x n

/-- The offset-zero list is the already initialized old pending bank. -/
theorem inheritedDownPrefix_zero
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs) :
    inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x 0 =
      ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
        rate rewards C_star C_h s hs x i := by
  simp [inheritedDownPrefix,
    ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests]

/-- Initialization retains exactly the old pending entries, with no reset. -/
theorem inheritedDownPrefix_zero_pending
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs) :
    (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x 0).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry =
      (generatedInheritedInitialFollower rate rewards C_star C_h s hs x i).downBatch.pending := by
  rw [inheritedDownPrefix_zero]
  exact (generated_inherited_down_old_pending (rate := rate) rewards C_star C_h s hs x i).1

/-- Advancing the actual observation calendar appends exactly its current
executed test, if present. The `Option` branch is retained as `[].` -/
theorem inheritedDownPrefix_succ
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (n : ℕ) (hn : s + n < p.T) :
    inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x (n + 1) =
      inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n ++
        (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 ⟨n, by omega⟩)).toList := by
  let code := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  have hn' : n < p.T - s := by omega
  have hlen : n < (List.ofFn code.2).length := by
    simp only [List.length_ofFn]
    exact hn'
  have hstep : (List.ofFn code.2)[n]'(by simpa using hn') = code.2 ⟨n, hn'⟩ := by
    simp
  unfold inheritedDownPrefix
  simp only [ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests]
  rw [← List.take_concat_get' (List.ofFn code.2) n hlen,
    List.filterMap_append]
  rw [hstep]
  cases hcurrent : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (code.2 ⟨n, hn'⟩) <;> simp [hcurrent, code]

theorem inheritedDownCurrentTest_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (test : ExecutedTest p)
    (htest : executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 n) = some test) :
    test.time.val = s + n.val := by
  let input := ReferenceDownCompletedAmbiguityMeasurability.prefixInput s n.val (by omega)
    (generatedSourceRunInput rate rewards C_star C_h s hs x)
  let round := ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation input i
  change executedTestOfRound rate round = some test at htest
  cases hcall : round.2.2.1 with
  | none => simp [executedTestOfRound, hcall] at htest
  | some call =>
    have htime : call.1 = input.time := by
      change ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation input i =
        some call at hcall
      unfold ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation at hcall
      cases hreg : ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters input i with
      | none => simp [hreg] at hcall
      | some registers =>
        simp only [hreg, Option.map_some, Option.some.injEq] at hcall
        exact (congrArg Prod.fst hcall).symm
    cases hcut : round.2.2.2.2.2 with
    | none => simp [executedTestOfRound, hcall, hcut] at htest
    | some cut =>
      have hexpanded := htest
      simp only [executedTestOfRound, hcall, hcut, Option.ite_some_none_eq_some] at hexpanded
      have heq := congrArg ExecutedTest.time hexpanded.2
      rw [← heq, htime]
      rfl

/-- Offset bounds include the terminal prefix `n = T - s`. Every actual
prefix is strictly chronological, and all its equations precede `s + n`. -/
theorem inheritedDownPrefix_chronological
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (n : ℕ) (hn : n ≤ p.T - s) :
    (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n).Pairwise
        (fun a b => a.time.val < b.time.val) ∧
      ∀ test ∈ inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n,
        test.time.val < s + n := by
  induction n with
  | zero =>
    rw [inheritedDownPrefix_zero]
    obtain ⟨_, _, _, hold⟩ := generated_inherited_down_old_test_birth
      (rate := rate) rewards C_star C_h s hs x i
    exact ⟨(ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_tests_pairwise
      rate rewards C_star C_h x.val i).sublist (List.drop_sublist _ _),
      fun test hmem => by simpa only [Nat.add_zero] using (hold test hmem).2.1⟩
  | succ n ih =>
    obtain ⟨hpair, hbefore⟩ := ih (by omega)
    rw [inheritedDownPrefix_succ (rate := rate) rewards C_star C_h s hs i x n (by omega)]
    cases hcurrent : executedTestOfRound rate
        ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 ⟨n, by omega⟩) with
    | none =>
      simp only [Option.toList_none, List.append_nil]
      exact ⟨hpair, fun test hmem => by have := hbefore test hmem; omega⟩
    | some current =>
      have htime := inheritedDownCurrentTest_time (rate := rate) rewards C_star C_h s hs i x
        ⟨n, by omega⟩ current hcurrent
      change current.time.val = s + n at htime
      simp only [Option.toList_some]
      refine ⟨List.pairwise_append.mpr ⟨hpair, by simp, ?_⟩, ?_⟩
      · intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst b
        rw [htime]
        exact hbefore a ha
      · intro test hmem
        rcases List.mem_append.mp hmem with hold | hnew
        · have := hbefore test hold; omega
        · simp only [List.mem_singleton] at hnew
          subst test
          omega

/-- If the current calendar test is positive, the actual inherited prefix
through this test is the first `q` equations of the actual inherited cohort.
The quota subtraction is the initialized pending length, so the old equations
remain in their original positions. -/
theorem inheritedDownPrefix_current_take
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (n q : ℕ) (hn : s + n < p.T) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (hlen : (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n).length = q - 1)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hcurrent : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 ⟨n, by omega⟩) = some test) :
    inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n ++ [test] =
      (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
        rate rewards C_star C_h s hs i x).take q := by
  let Old := ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
    rate rewards C_star C_h s hs x i
  let U := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i x (n + 1)
  let full := ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
    rate rewards C_star C_h s hs i x (p.T - s)
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs x i).downBatch
  let tail := ((List.ofFn (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x).2).drop (n + 1)).filterMap
      (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate)
  have hsuccessor : inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n ++ [test] =
      inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x (n + 1) := by
    rw [inheritedDownPrefix_succ (rate := rate) rewards C_star C_h s hs i x n hn,
      hcurrent]
    rfl
  have hprefixValue : inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x
      (n + 1) = Old ++ U := rfl
  have hprefixLength : (Old ++ U).length = q := by
    calc
      (Old ++ U).length =
          (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x (n + 1)).length := by
            rw [hprefixValue]
      _ = (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n ++ [test]).length := by
            rw [← hsuccessor]
      _ = q := by simp [hlen]; omega
  have hOldLength : Old.length = B0.pending.length := by
    simpa [Old, B0] using
      (ReferenceGeneratedInheritedDownCohort.generated_inherited_down_old_pending
        (rate := rate) rewards C_star C_h s hs x i).2
  have hfullSplit : full = U ++ tail := by
    let code := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
    let rounds := List.ofFn code.2
    have hsplit : rounds.filterMap (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) =
        (rounds.take (n + 1)).filterMap
            (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) ++
          (rounds.drop (n + 1)).filterMap
            (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) := by
      conv_lhs => rw [← List.take_append_drop (n + 1) rounds]
      rw [List.filterMap_append]
    change ((List.ofFn
      (ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2).take (p.T - s)).filterMap
          (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) = _
    rw [List.take_of_length_le (by simp)]
    simpa [rounds, code, U, tail,
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests] using hsplit
  have hUle : U.length ≤ AffineBatchDecoder.quota p - B0.pending.length := by
    rw [List.length_append] at hprefixLength
    rw [hOldLength] at hprefixLength
    omega
  have htakeU : (full.take (AffineBatchDecoder.quota p - B0.pending.length)).take U.length = U := by
    calc
      (full.take (AffineBatchDecoder.quota p - B0.pending.length)).take U.length =
          full.take U.length := by
            rw [List.take_take, Nat.min_eq_left hUle]
      _ = U := by
        rw [hfullSplit, List.take_append]
        simp
  have hCohort :
      ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
        rate rewards C_star C_h s hs i x =
        Old ++ full.take (AffineBatchDecoder.quota p - B0.pending.length) := rfl
  have hOldLe : Old.length ≤ q := by
    rw [hOldLength]
    rw [List.length_append] at hprefixLength
    omega
  have hdiff : q - Old.length = U.length := by
    rw [List.length_append] at hprefixLength
    omega
  have htakeCohort :
      (Old ++ full.take (AffineBatchDecoder.quota p - B0.pending.length)).take q = Old ++ U := by
    rw [List.take_append]
    rw [List.take_of_length_le hOldLe]
    rw [hdiff]
    rw [htakeU]
  calc
    inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n ++ [test] =
        inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x (n + 1) := hsuccessor
    _ = Old ++ U := hprefixValue
    _ = (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
        rate rewards C_star C_h s hs i x).take q := by
          rw [hCohort]
          exact htakeCohort.symm

/-- A current positive test below quota belongs to the actual new part of
the first inherited cohort; no eventual completion is required. -/
theorem inheritedDownPrefix_current_mem
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (n q : ℕ) (hn : s + n < p.T) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (hlen : (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n).length = q - 1)
    (test : ExecutedTest p)
    (hcurrent : executedTestOfRound rate
      ((generatedSourceObservation rate rewards C_star C_h s hs i x).2 ⟨n, by omega⟩) = some test) :
    test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownNewFirstTests
      rate rewards C_star C_h s hs i x := by
  have htake := inheritedDownPrefix_current_take (rate := rate) rewards C_star C_h
    s hs i x n q hn hq hqQ hlen test hcurrent
  have hmem : test ∈ generatedInheritedDownFirstCohortTests rate rewards C_star C_h s hs i x :=
    List.mem_of_mem_take (htake ▸ List.mem_append_right _ (List.mem_singleton_self test))
  rcases List.mem_append.mp hmem with hold | hnew
  · obtain ⟨_, _, _, hbirth⟩ := generated_inherited_down_old_test_birth
      (rate := rate) rewards C_star C_h s hs x i
    have hbefore := (hbirth test hold).2.1
    have htime := inheritedDownCurrentTest_time (rate := rate) rewards C_star C_h s hs i x
      ⟨n, by omega⟩ test hcurrent
    omega
  · exact hnew

/-- At the terminal offset the projection contains the whole actual calendar. -/
theorem inheritedDownPrefix_terminal
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs) :
    inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x (p.T - s) =
      generatedInheritedDownOldFirstTests rate rewards C_star C_h s hs x i ++
        (List.ofFn (generatedSourceObservation rate rewards C_star C_h s hs i x).2).filterMap
          (executedTestOfRound rate) := by
  unfold inheritedDownPrefix generatedInheritedDownTests
  rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]

/-- The actual physical DOWN input at the current round, produced from the
same crossing branch and original source rather than supplied as a trace. -/
def inheritedDownCurrentInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : ContinuousLearningRows.Channel p))) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
    rewards C_star C_h j r (0, i) s hsr control0
      ⟨x.1, ⟨hselector, x.2.1, x.2.2⟩⟩

/-- The concrete current record runs the existing physical step on the
produced source input. -/
def inheritedDownCurrentRecord
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : ContinuousLearningRows.Channel p))) :
    ReferenceFollowerDownDecoderReplay.Record p rate :=
  ⟨inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
      control0 i x hselector,
    ReferenceActivePhysicalStep.step
      (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
        control0 i x hselector), rfl⟩

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- Reconstruct the source's actual current input from E's original `[s,r)`
run. The current selected index follows from the produced DOWN selector. -/
theorem inheritedDownCurrentInput_eq_sourcePrefixInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : ContinuousLearningRows.Channel p))) :
    inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
      control0 i x hselector =
    ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
        rate rewards C_star C_h s (by omega) x) := by
  let hs : s < p.T := by omega
  let branch : {z : SourceInput p // z ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
        rewards C_star C_h j r (0, i) s} :=
    ⟨x.1, ⟨hselector, x.2.1, x.2.2⟩⟩
  let retained0 := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  let actualControl : ContinuousLearningRows.TimeControl p :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r x.1).1
  let retainedActual := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h j r (0, i) s hsr actualControl branch
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j := by
    have h := congrArg Prod.fst hselector
    change ActualInitializationPhysicalStep.selectedRowIndex p x.1 = j at h
    exact h
  have hsplitSelected : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 retained0.1) = j := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p j r control0 retained0.1 retained0.2.1
  have hrem : retained0.1 = retainedActual.1 := by
    rw [ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val,
      ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val]
  have hstate := ReferenceGeneratedDownPrefixEvent.retainedPrefixFinalState_eq_of_remainder_eq
    rate rewards C_star C_h j r s hsr control0 actualControl retained0 retainedActual hrem
      (r.val - s) (by omega)
  have hrunInput := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput_eq_source
    rate rewards C_star C_h j r s hs hsr x hselected retainedActual
    (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val
      (rate := rate) rewards C_star C_h j r (0, i) s hsr actualControl branch)
  have hbranchState := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_state
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  have hstateSource :
      (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
        control0 i x hselector).state =
      (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x)).finalState := by
    calc
      _ = (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
          rate rewards C_star C_h j r control0 retained0.1 retained0.2.1 s
          (r.val - s) hsr retained0.2.2 (by omega)).finalState := by
            simpa [inheritedDownCurrentInput, branch] using hbranchState
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput
              rate rewards C_star C_h j r s hsr control0 retained0)).finalState := by
              simp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor,
                ReferenceActiveHorizonMeasurability.runOfInput,
                ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput,
                ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed]
              rw [hsplitSelected]
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput
              rate rewards C_star C_h j r s hsr actualControl retainedActual)).finalState := hstate
      _ = (ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega)
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
              rate rewards C_star C_h s hs x)).finalState := by rw [hrunInput]
  have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  have hsourceSelected :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1 = j := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hselected
  apply roundInput_ext hstateSource
  · simpa [inheritedDownCurrentInput, branch,
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using hfields.1
  · calc
      (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
        control0 i x hselector).selected =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1 := by
            simpa [inheritedDownCurrentInput, branch] using hfields.2.1
      _ = j := hsourceSelected
      _ = (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
          (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs x)).selected := by
              simpa [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
                ReferenceActivePhysicalHorizon.roundInputAt,
                ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using hselected.symm
  · calc
      (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
        control0 i x hselector).time = r := by
          simpa [inheritedDownCurrentInput, branch] using hfields.2.2.1
      _ = (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s)
          (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs x)).time := by
              apply Fin.ext
              simp only [ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
                ReferenceActivePhysicalHorizon.roundInputAt]
              omega
  · simpa [inheritedDownCurrentInput, branch,
      ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput] using hfields.2.2.2

/-- The actual calendar test at the current offset is exactly the test in
the source's physical observation at round `r`. -/
theorem inheritedDownCurrentTest_eq_sourcePrefixTest
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : ContinuousLearningRows.Channel p))) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s (by omega) i x).2 ⟨r.val - s, by omega⟩) =
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
          control0 i x hselector) i) := by
  rw [inheritedDownCurrentInput_eq_sourcePrefixInput
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselector]
  rfl

/-- The actual source selector produces the physical selected follower. -/
theorem inheritedDownCurrent_senderIndex
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 = (j, some (0, i))) :
    ReferenceActivePhysicalStep.upSenderIndex (inheritedDownCurrentInput (rate := rate)
      rewards C_star C_h j r s hsr control0 i x hselector) = i :=
  ReferenceGeneratedDownPrefixPositiveHalf.generatedCurrentDown_senderIndex
    (rate := rate) rewards C_star C_h j r i s hsr control0
      ⟨x.1, hselector, x.2.1, x.2.2⟩

/-- Existence of the actual current calendar test is equivalent to the
physical positive diagnostic and its exact option-valued sent word. -/
theorem inheritedDownCurrentPositiveSent_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hselector : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : ContinuousLearningRows.Channel p)))
    (w : Candidate p) :
    (∃ test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s (by omega) i x).2 ⟨r.val - s, by omega⟩) = some test ∧
        test.sent ≠ some w) ↔
    ReferenceActiveAffinePositiveTest.downPositive
        (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
          control0 i x hselector) = true ∧
      ReferenceActiveAffinePositiveTest.downSent
        (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
          control0 i x hselector) ≠ some w := by
  let record := inheritedDownCurrentRecord (rate := rate) rewards C_star C_h j r s hsr
    control0 i x hselector
  have hsender : ReferenceActivePhysicalStep.upSenderIndex record.input = i :=
    inheritedDownCurrent_senderIndex (rate := rate) rewards C_star C_h j r s hsr
      control0 i x hselector
  have hiff := ReferenceGeneratedDownPrefixPositiveHalf.executedTestOfRound_iff_downPositive
    (rate := rate) record i hsender
  have hsource := inheritedDownCurrentTest_eq_sourcePrefixTest
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselector
  constructor
  · rintro ⟨test, htest, hsent⟩
    rw [hsource] at htest
    have htestRecord :
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
            some test := by
      simpa [record, inheritedDownCurrentRecord] using htest
    let round := ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i
    let diagnostic := round.2.2.2
    cases hcallCode : round.2.2.1 with
    | none =>
        simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
          round, hcallCode] at htestRecord
    | some callCode =>
      cases hcutCode : diagnostic.2.2 with
      | none =>
          simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
            round, diagnostic, hcallCode, hcutCode] at htestRecord
      | some cutFields =>
        let condition :=
          0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
            cutFields.2.2.1.isSome
        have hcondition : condition := by
          have htestExpanded := htestRecord
          simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
            round, diagnostic, hcallCode, hcutCode] at htestExpanded
          exact htestExpanded.1
        have hdiagnostics :=
          ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
            record i
        have hcutDiagnostic := hcutCode
        change (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.2.2.2.2 = some cutFields at hcutDiagnostic
        rw [hdiagnostics] at hcutDiagnostic
        have hcutWitness : ∃ cut,
            (record.output.followers i).down = some cut ∧
              ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutFields := by
          cases hdown : (record.output.followers i).down with
          | none => simp [hdown] at hcutDiagnostic
          | some cut =>
              have hc : ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutFields := by
                simpa [hdown] using hcutDiagnostic
              exact ⟨cut, rfl, hc⟩
        obtain ⟨cut, hactualCut, hcutFields⟩ := hcutWitness
        have hcomparison : cut.rawComparison.isSome = true := by
          have hproj := congrArg
            (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
              fields.2.2.1.isSome) hcutFields
          have hproj' : cut.rawComparison.isSome = cutFields.2.2.1.isSome := by
            simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hproj
          rw [hproj']
          exact hcondition.2
        have hpositive :
            0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
          have hgrid :
              0 < (ActualInitializationPhysicalStep.observationOfGrid p
                (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val := by
            simpa [round, ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using
              hcondition.1
          have hown : ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
              ActualInitializationPhysicalStep.observationOfGrid p
                (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
            have hgrid' := congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
              record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            change ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
              record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) at hgrid'
            rw [hgrid']
            exact record.output.preparation.feedback.observations_eq _
          rw [hown]
          exact hgrid
        have hdiagnosticCall : ReferenceActiveAffinePositiveTest.downDiagnosticCall
            (record.output.followers i) = true := by
          simp [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hactualCut, hcomparison]
        have hownBool : decide (0 <
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) = true := by
          exact decide_eq_true hpositive
        have hpositiveRecord : ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
          have heq := ReferenceActiveAffinePositiveTest.record_downPositive record
          rw [hsender, hdiagnosticCall, hownBool] at heq
          exact heq
        have hcanonical := hiff.mpr hpositiveRecord
        have htestEq : test =
            ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
              ReferenceActiveAffinePositiveTest.downSent record.input⟩ := by
          exact Option.some.inj (htestRecord.symm.trans hcanonical)
        have hsentRecord : ReferenceActiveAffinePositiveTest.downSent record.input ≠ some w := by
          intro hword
          apply hsent
          have hsentTest : test.sent =
              ReferenceActiveAffinePositiveTest.downSent record.input := by
            simpa using congrArg
              ReferenceGeneratedDownBatchCalendar.ExecutedTest.sent htestEq
          exact hsentTest.trans hword
        have hpositiveCurrent :
            ReferenceActiveAffinePositiveTest.downPositive
              (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
                control0 i x hselector) = true := by
          simpa [record, inheritedDownCurrentRecord] using hpositiveRecord
        have hsentCurrent :
            ReferenceActiveAffinePositiveTest.downSent
              (inheritedDownCurrentInput (rate := rate) rewards C_star C_h j r s hsr
                control0 i x hselector) ≠ some w := by
          simpa [record, inheritedDownCurrentRecord] using hsentRecord
        exact ⟨hpositiveCurrent, hsentCurrent⟩
  · rintro ⟨hpositive, hsent⟩
    have hpositiveRecord : ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
      simpa [record, inheritedDownCurrentRecord] using hpositive
    have hsentRecord : ReferenceActiveAffinePositiveTest.downSent record.input ≠ some w := by
      simpa [record, inheritedDownCurrentRecord] using hsent
    have hcanonical := hiff.mpr hpositiveRecord
    let test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
      ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
        ReferenceActiveAffinePositiveTest.downSent record.input⟩
    refine ⟨test, ?_, ?_⟩
    · rw [hsource]
      simpa [test, record, inheritedDownCurrentRecord] using hcanonical
    · simpa [test] using hsentRecord

/-- Literal inherited marker: the actual initialization bank, its actual old
cohort boundary, and every equation in `Old ++ U_n` pass the candidate. -/
def inheritedDownMarker
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (w : Candidate p)
    (s : ℕ) (hs : s < p.T) (i : Fin (p.m - 1))
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs) (n : ℕ) : Prop :=
  alpha ≤ s ∧
    (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch.completed.length = k ∧
    ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
      rate rewards C_star C_h x.1 i k = some alpha ∧
    (inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n).length = q - 1 ∧
    ∀ test ∈ inheritedDownPrefix (rate := rate) rewards C_star C_h s hs i x n,
      ReferenceGeneratedDownBatchCalendar.ExecutedTest.good w test

/-- Restore an old pending entry with its original time/sample and absent sent word. -/
def inheritedDownOldEntryTest
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :
    ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
  ⟨entry.time, entry.sample, none⟩

/-- Boundary projection shared by the actual initialization output and its
countable marker code. -/
def inheritedDownBoundaryCode
    (_i : Fin (p.m - 1)) (k : ℕ)
    (activation : Option (ReferencePrelaunchFollower.Activation p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Option ℕ :=
  if k = 0 then activation.map (fun a => a.val - 1)
  else (bank.completed[k - 1]?.bind List.getLast?).map (fun entry => entry.time.val + 1)

/-- The marker initialization boundary, expressed through the actual terminal
boundary and decoded initial follower bank. -/
def inheritedDownBoundaryFromInitial
    (i : Fin (p.m - 1)) (k : ℕ)
    (out : ReferenceInitializationRun.Boundary p)
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Option ℕ :=
  inheritedDownBoundaryCode i k
    (out.activation (ActualReferenceInitializationBlock.refFollower i)) bank

/-- The countable code predicate used to measure the inherited marker on the
actual retained interval. Old tests are reconstructed from B0.pending; new
tests are projected from E's real run observation. -/
def inheritedDownMarkerCode
    (alpha k q s n : ℕ) (w : Candidate p) (i : Fin (p.m - 1))
    (activation : Option (ReferencePrelaunchFollower.Activation p))
    (bankCode : FollowerDownMeasurability.DecoderBatchCode p)
    (observation : ReferenceDownCompletedAmbiguityMeasurability.RunDownObservationCode
      p rate n) : Prop :=
  let bank := FollowerDownMeasurability.decoderBatchOfCode bankCode
  let Old := bank.pending.map inheritedDownOldEntryTest
  let New := (List.ofFn observation.2).filterMap
    (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate)
  let boundary := inheritedDownBoundaryCode i k activation bank
  alpha ≤ s
    ∧ bank.completed.length = k
    ∧ boundary = some alpha
    ∧ (Old ++ New).length = q - 1
    ∧ ∀ test ∈ Old ++ New,
      ReferenceGeneratedDownBatchCalendar.ExecutedTest.good w test

theorem inheritedDownOld_eq_pendingTests
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource (rate := rate) rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) :
    ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
        rate rewards C_star C_h s hs x i =
      ((ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
        rate rewards C_star C_h s hs x i).downBatch.pending.map inheritedDownOldEntryTest) := by
  let Old := ReferenceGeneratedInheritedDownCohort.generatedInheritedDownOldFirstTests
    rate rewards C_star C_h s hs x i
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs x i).downBatch
  have hpending := ReferenceGeneratedInheritedDownCohort.generated_inherited_down_old_pending
    (rate := rate) rewards C_star C_h s hs x i
  obtain ⟨alpha, _, _, hsent⟩ :=
    ReferenceGeneratedInheritedDownCohort.generated_inherited_down_old_test_birth
      (rate := rate) rewards C_star C_h s hs x i
  have hrestoreMap : Old.map (fun test => inheritedDownOldEntryTest
      (ReferenceGeneratedPrelaunchDownCohort.testEntry test)) = Old.map id := by
    apply List.map_congr_left
    intro test hmem
    have hnone : test.sent = none := (hsent test hmem).2.2.2
    cases test with
    | mk time sample sent =>
      change (⟨time, sample, none⟩ : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) =
        ⟨time, sample, sent⟩
      have hsentNone : sent = none := by simpa using hnone
      exact congrArg (fun v => (⟨time, sample, v⟩ :
        ReferenceGeneratedDownBatchCalendar.ExecutedTest p)) hsentNone.symm
  have hrestore : Old.map (fun test => inheritedDownOldEntryTest
      (ReferenceGeneratedPrelaunchDownCohort.testEntry test)) = Old := by
    simpa using hrestoreMap
  calc
    Old = Old.map (fun test => inheritedDownOldEntryTest
        (ReferenceGeneratedPrelaunchDownCohort.testEntry test)) := by
          simpa using hrestore.symm
    _ = (Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry).map
        inheritedDownOldEntryTest := by rw [List.map_map]; rfl
    _ = B0.pending.map inheritedDownOldEntryTest := by
      rw [show Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = B0.pending from
        by simpa [Old, B0] using hpending.1]

/-- Restore the source represented by E's original control remainder and its
actual launch certificate. -/
def inheritedDownRetainedLaunchSource
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0) :
    LaunchSource (rate := rate) rewards C_star C_h s (by omega) := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = j := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p j r control0 x.1 x.2.1
  have hstart : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r source).2 ∈
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h j r s control0 := by
    simpa [source, ReferenceGeneratedActivePrefixFactor.splitSource] using x.2.2
  have hlaunch := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
    rate rewards C_star C_h j r control0 source hselected s hsr).mp hstart
  exact ⟨source, hlaunch.1, hlaunch.2⟩

/-- The literal Old++U marker is exactly the countable code predicate on E's
actual retained subtype. The short observation and D's full observation agree
on every physical offset before r. -/
private theorem inheritedDownMarker_retained_iff_code
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (w : Candidate p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0) :
    inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s
      (by omega) i (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h
        j r s hsr control0 x) (r.val - s) ↔
      inheritedDownMarkerCode (rate := rate) alpha k q s (r.val - s) w i
        ((ReferenceInitializationRun.output
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards (ReferencePrelaunchCarriedMeasurability.sourceCoordinates
              (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1)))).activation
          (ActualReferenceInitializationBlock.refFollower i))
        (ReferenceInitializationMeasurability.downBatchCode
          ((ReferenceInitializationRun.ordinary
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
              rewards (ReferencePrelaunchCarriedMeasurability.sourceCoordinates
                (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1)))
            (ReferenceInitializationRun.output
              (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
                rewards (ReferencePrelaunchCarriedMeasurability.sourceCoordinates
                  (ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1))))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch))
        (ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
          rate rewards C_star C_h j r s hsr control0 i x) := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1
  let launch := inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h
    j r s hsr control0 x
  let initialOutput := ReferenceInitializationRun.output
    (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates source))
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s (by omega) launch i).downBatch
  let bankCode := ReferenceInitializationMeasurability.downBatchCode
    ((ReferenceInitializationRun.ordinary
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
        (ReferencePrelaunchCarriedMeasurability.sourceCoordinates source))
      initialOutput (ActualReferenceInitializationBlock.refFollower i)).downBatch)
  let bank := FollowerDownMeasurability.decoderBatchOfCode bankCode
  let observation := ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
    rate rewards C_star C_h j r s hsr control0 i x
  let input := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput
    rate rewards C_star C_h j r s hsr control0 x
  let sourceInput := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s (by omega) launch
  let shortCode := ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
    (p := p) (rate := rate) s (r.val - s) (by omega) i input
  let fullCode := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s (by omega) i launch
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = j := by
    dsimp [source, launch]
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p j r control0 x.1 x.2.1
  let actualControl := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r launch.1).1
  let retainedActual : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr actualControl :=
    ⟨x.1, ReferenceGeneratedDownPrefixEvent.retainedAtControl_mem rate rewards C_star C_h j r s
      hsr control0 actualControl x⟩
  have hrem : retainedActual.1 =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r launch.1).2 := by
    dsimp [retainedActual, launch, inheritedDownRetainedLaunchSource]
    exact (congrArg Prod.snd
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).apply_symm_apply
        (control0, x.1))).symm
  have hinput := ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput_eq_source
    rate rewards C_star C_h j r s (by omega) hsr launch hselected retainedActual hrem
  have hobsEq := ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation_eq_of_remainder_eq
    rate rewards C_star C_h j r s hsr control0 actualControl i x retainedActual
      (by rfl)
  have hround : ∀ t : Fin (r.val - s), shortCode.2 t =
      fullCode.2 ⟨t.val, by omega⟩ := by
    intro t
    change (ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
      rate rewards C_star C_h j r s hsr control0 i x).2 t = fullCode.2 ⟨t.val, by omega⟩
    rw [hobsEq]
    change (ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
      (p := p) (rate := rate) s (r.val - s) (by omega) i
      (ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput rate rewards C_star C_h j r s
        hsr actualControl retainedActual)).2 t = fullCode.2 ⟨t.val, by omega⟩
    rw [hinput]
    simp only [ReferenceDownCompletedAmbiguityMeasurability.runDownObservation,
      ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput]
    rfl
  have hobsPrefix : List.ofFn shortCode.2 =
      (List.ofFn fullCode.2).take (r.val - s) := by
    have hfun : shortCode.2 =
        fun t : Fin (r.val - s) => fullCode.2 ⟨t.val, by omega⟩ := funext hround
    rw [hfun]
    exact Fin.ofFn_take_eq_take_ofFn
      (n := p.T - s) (Nat.sub_le_sub_right (Nat.le_of_lt r.isLt) s) fullCode.2
  have hbankCode : bank = B0 := by
    dsimp [bank, bankCode, B0, initialOutput]
    rw [ReferencePrelaunchCarriedMeasurability.downBatchCode_eq_decoderBatchCode]
    exact FollowerDownMeasurability.decoderBatchOfCode_code _
  have hdecodeCode : FollowerDownMeasurability.decoderBatchOfCode bankCode = B0 := by
    simpa [bank] using hbankCode
  have hlaunchSource : launch.1 = source := by rfl
  have hOld := inheritedDownOld_eq_pendingTests (rate := rate) rewards C_star C_h s
    (by omega) launch i
  have hboundary :
      inheritedDownBoundaryFromInitial (p := p) i k initialOutput B0 =
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h source i k := by
    change inheritedDownBoundaryFromInitial i k
        (ReferenceInitializationRun.output
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
            (ReferencePrelaunchCarriedMeasurability.sourceCoordinates source))) B0 = _
    rw [ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput]
    dsimp [inheritedDownBoundaryFromInitial,
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary,
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower]
    rfl
  have hnew :
      ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
          rate rewards C_star C_h s (by omega) i launch (r.val - s) =
        (List.ofFn shortCode.2).filterMap
          (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) := by
    change ((List.ofFn fullCode.2).take (r.val - s)).filterMap
        (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate) =
      (List.ofFn shortCode.2).filterMap
        (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate)
    rw [hobsPrefix]
  have hboundaryCode : inheritedDownBoundaryCode i k
      (initialOutput.activation (ActualReferenceInitializationBlock.refFollower i)) B0 =
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h source i k := by
    simpa [inheritedDownBoundaryFromInitial] using hboundary
  change inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s
      (by omega) i launch (r.val - s) ↔ _
  simp [inheritedDownMarker, inheritedDownPrefix, inheritedDownMarkerCode,
    bankCode, initialOutput, source, B0, shortCode, input,
    ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation,
    hdecodeCode, hOld, hnew, hboundaryCode, hlaunchSource]

private theorem inheritedDownOptionSingleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α)
      LaterAssignmentStartMeasurability.optionMeasurableSpace := by
  constructor
  intro value
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({value} : Set (Option α)) = e ⁻¹' {e value} := by
    ext other
    exact ⟨congrArg _, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e value with
  | inl item =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton item).inl_image (β := PUnit)
  | inr item =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton item).inr_image (α := α)

/-- The actual inherited marker is Borel on E's retained launch subtype.
M0's terminal activation and bank code, together with E's measurable run
observation, determine the countable marker code. -/
private theorem measurableSet_inheritedDownMarkerRetained
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (w : Candidate p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) :
    MeasurableSet {x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 |
      inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s
        (by omega) i (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h
          j r s hsr control0 x) (r.val - s)} := by
  let : MeasurableSpace
      (List (Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p))) :=
    ReferenceInitializationMeasurability.listCountableMeasurableSpace _
  let : MeasurableSpace
      (List (List (Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p)))) :=
    ReferenceInitializationMeasurability.listCountableMeasurableSpace _
  let : MeasurableSingletonClass
      (List (Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p))) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSingletonClass
      (List (List (Fin p.T × AffineChannelLaw.Sample (AffineBatchDecoder.width p)))) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSpace (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option Bool) := LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :=
    CoordinatorUpMeasurability.rawDecoderOutputMeasurableSpace (AffineBatchDecoder.width p)
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace
      (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSingletonClass
      (FollowerDownMeasurability.FollowerStateCode p rate) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSingletonClass
      (Option (FollowerDownMeasurability.FollowerStateCode p rate)) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSingletonClass
      (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCallCode p)) :=
    inheritedDownOptionSingleton
  let : MeasurableSingletonClass (Option Bool) := inheritedDownOptionSingleton
  let : MeasurableSingletonClass
      (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSingletonClass (Option DeclaredFollowerLocalRound.RoundFailure) :=
    inheritedDownOptionSingleton
  let : MeasurableSingletonClass
      (Option (ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p)) :=
    inheritedDownOptionSingleton
  let source := fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
    ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1
  have hsource : Measurable source := by
    change Measurable (fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
        rate rewards C_star C_h j r s hsr control0 =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm
        (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hcoordinates : Measurable
      (fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
        rate rewards C_star C_h j r s hsr control0 =>
        ReferencePrelaunchCarriedMeasurability.sourceCoordinates (source x)) :=
    ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates.comp hsource
  let out := fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
    ReferenceInitializationRun.output
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
        (ReferencePrelaunchCarriedMeasurability.sourceCoordinates (source x)))
  let bankCode := fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
    ReferenceInitializationMeasurability.downBatchCode
      ((ReferenceInitializationRun.ordinary
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
          (ReferencePrelaunchCarriedMeasurability.sourceCoordinates (source x)))
        (out x) (ActualReferenceInitializationBlock.refFollower i)).downBatch)
  let activation := fun x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 =>
    (out x).activation (ActualReferenceInitializationBlock.refFollower i)
  let observation := ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
    rate rewards C_star C_h j r s hsr control0 i
  have hout : Measurable out :=
    Measurable.comp
      (ReferenceInitializationMeasurability.measurable_output p C_star C_h rate.eta rewards)
      hcoordinates
  have hbankCode : Measurable bankCode :=
    Measurable.comp
      (ReferenceInitializationMeasurability.measurable_output_downBatchCode p C_star C_h
        rate.eta rewards (ActualReferenceInitializationBlock.refFollower i)) hcoordinates
  have hactivation : Measurable activation := by
    exact Measurable.comp
      (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
        b.activation (ActualReferenceInitializationBlock.refFollower i))) hout
  have hinput : Measurable (ReferenceGeneratedDownPrefixEvent.retainedPrefixRunInput
      rate rewards C_star C_h j r s hsr control0) :=
    ReferenceGeneratedDownPrefixEvent.measurable_retainedPrefixRunInput
      rate rewards C_star C_h j r s hsr control0
  have hobs : Measurable observation := by
    exact Measurable.comp
      (ReferenceDownCompletedAmbiguityMeasurability.measurable_runDownObservation
        s (r.val - s) (by omega) i) hinput
  let key := fun x => (activation x, bankCode x, observation x)
  have hkey : Measurable key := hactivation.prodMk (hbankCode.prodMk hobs)
  have heq :
      {x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
          rate rewards C_star C_h j r s hsr control0 |
        inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s
          (by omega) i (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h
            j r s hsr control0 x) (r.val - s)} =
        key ⁻¹' {v | inheritedDownMarkerCode (rate := rate) alpha k q s
          (r.val - s) w i v.1 v.2.1 v.2.2} := by
    ext x
    simpa [key, activation, out, bankCode, observation] using
      (inheritedDownMarker_retained_iff_code (rate := rate) rewards C_star C_h alpha k q w
        j r s hsr control0 i x)
  rw [heq]
  exact hkey (Set.to_countable _).measurableSet

/-- The selector, initialized launch, and retained original control
remainder for the inherited DOWN marker. -/
def inheritedDownLaunchRemainder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (_hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) : Set (PairRemainder p j r i) :=
  ReferenceGeneratedAffineHashHalf.generatedLaunchRemainderSet
    (rate := rate) rewards C_star C_h j r (0, i) s control0

abbrev InheritedDownRemainderLaunch
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :=
  {v : PairRemainder p j r i //
    v ∈ inheritedDownLaunchRemainder rate rewards C_star C_h j r s
      hsr control0 i}

/-- The canonical launch retained in the actual DOWN pair remainder. Its
measurable space is inherited from the admitted fixed-pair remainder. -/
def inheritedDownRemainderRetainedLaunch
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (v : InheritedDownRemainderLaunch rate rewards C_star C_h j r s
      hsr control0 i) :
    ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0 :=
  ⟨ReferenceGeneratedAffineHashHalf.retainedControlProjection
      (p := p) (q := j) (t := r) (c := (0, i)) v.1,
    v.2.2⟩

theorem measurable_inheritedDownRemainderRetainedLaunch
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :
    Measurable (inheritedDownRemainderRetainedLaunch rate rewards C_star C_h
      j r s hsr control0 i) := by
  apply Measurable.subtype_mk
  exact ReferenceGeneratedAffineHashHalf.measurable_retainedControlProjection.comp
    measurable_subtype_coe

/-- The concrete inherited-prefix cylinder in the original pair remainder.
It records J/selector, the complete public/private past cell, initialization's
existing pending bank and boundary, and every good test in the actual `Old ++ U_n`
prefix. The current round's physical positivity and sent word remain in Z's
generated event. -/
def inheritedDownMarkerRemainder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (_hAlpha : alpha ≤ p.T)
    (w : Candidate p) (_hq : 1 ≤ q) (_hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p ×
      GeneratedBootstrapRoundLaw.Past p r)) (_hCell : MeasurableSet Cell)
    (i : Fin (p.m - 1)) : Set (PairRemainder p j r i) := by
  let L := InheritedDownRemainderLaunch rate rewards C_star C_h j r s hsr
    control0 i
  let source := fun v : L =>
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (default, v.1)
  let retained := inheritedDownRemainderRetainedLaunch rate rewards C_star C_h
    j r s hsr control0 i
  let good := {v : L | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r
      (source v) ∈ Cell ∧
    inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
      (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
        control0 (retained v)) (r.val - s)}
  exact Subtype.val '' good

/-- Membership in the concrete remainder cylinder. -/
theorem inheritedDownMarkerRemainder_mem_iff
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p ×
      GeneratedBootstrapRoundLaw.Past p r)) (hCell : MeasurableSet Cell)
    (i : Fin (p.m - 1)) (v : PairRemainder p j r i) :
    v ∈ inheritedDownMarkerRemainder rate rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i ↔
    ∃ hlaunch : v ∈ inheritedDownLaunchRemainder rate rewards C_star C_h j r s hsr
      control0 i,
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm
          (default, v)) ∈ Cell ∧
        inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
          (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
            control0
            (inheritedDownRemainderRetainedLaunch rate rewards C_star C_h j r s
              hsr control0 i ⟨v, hlaunch⟩)) (r.val - s) := by
  classical
  simp only [inheritedDownMarkerRemainder, Set.mem_image, Subtype.exists]
  constructor
  · rintro ⟨a, hlaunch, hgood, ha⟩
    subst a
    exact ⟨hlaunch, hgood.1, hgood.2⟩
  · rintro ⟨hlaunch, hcell, hmarker⟩
    exact ⟨v, hlaunch, ⟨hcell, hmarker⟩, rfl⟩

/-- The inherited-prefix cylinder is Borel in the actual original pair
remainder, using the retained initialization output and E's whole `[s,r)`
observation code. -/
theorem measurableSet_inheritedDownMarkerRemainder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p ×
      GeneratedBootstrapRoundLaw.Past p r)) (hCell : MeasurableSet Cell)
    (i : Fin (p.m - 1)) :
    MeasurableSet (inheritedDownMarkerRemainder rate rewards C_star C_h alpha k q
      hAlpha w hq hqQ j r s hsr control0 Cell hCell i) := by
  classical
  let L := InheritedDownRemainderLaunch rate rewards C_star C_h j r s hsr
    control0 i
  let source := fun v : L =>
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (default, v.1)
  let retained := inheritedDownRemainderRetainedLaunch rate rewards C_star C_h
    j r s hsr control0 i
  have hlaunch : MeasurableSet
      (inheritedDownLaunchRemainder rate rewards C_star C_h j r s hsr
        control0 i) := by
    change MeasurableSet (ReferenceSelectedAffinePairLaw.remainderSelectorEvent p j r
        (0, i) ∩
      ReferenceGeneratedAffineHashHalf.retainedControlProjection (p := p) (q := j)
          (t := r) (c := (0, i)) ⁻¹'
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h j r s control0)
    exact (ReferenceSelectedAffinePairLaw.measurableSet_remainderSelectorEvent p j r (0, i)).inter
      ((ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
      rate rewards C_star C_h j r s (by omega) control0).preimage
        (ReferenceGeneratedAffineHashHalf.measurable_retainedControlProjection
          (p := p) (q := j) (t := r) (c := (0, i))))
  have hsource : Measurable source := by
    change Measurable (fun v : L =>
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (default, v.1))
    exact (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  let hcellSet : Set L := {v |
    ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r (source v) ∈ Cell}
  have hcellMeasurable : MeasurableSet hcellSet := by
    change MeasurableSet ((ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r ∘ source) ⁻¹'
      Cell)
    exact (ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView r).comp hsource hCell
  let retainedSet : Set L := {v |
    inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
      (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
        control0 (retained v)) (r.val - s)}
  have hretainedSet : MeasurableSet retainedSet := by
    change MeasurableSet (retained ⁻¹' {x |
      inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
        (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
          control0 x) (r.val - s)})
    exact (measurableSet_inheritedDownMarkerRetained (rate := rate) rewards C_star C_h alpha k q w
      j r s hsr control0 i).preimage
        (measurable_inheritedDownRemainderRetainedLaunch (rate := rate) rewards C_star C_h
          j r s hsr control0 i)
  let good := hcellSet ∩ retainedSet
  have hgood : MeasurableSet good := hcellMeasurable.inter hretainedSet
  have hEmbedding : MeasurableEmbedding (Subtype.val : L → PairRemainder p j r i) :=
    MeasurableEmbedding.subtype_coe hlaunch
  have hImage : MeasurableSet (Subtype.val '' good) := hEmbedding.measurableSet_image.mpr hgood
  have heq : inheritedDownMarkerRemainder (rate := rate) rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i = Subtype.val '' good := by
    rfl
  rw [heq]
  exact hImage

private theorem inheritedDownMarker_retained_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (w : Candidate p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 control : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control0)
    (y : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h j r s hsr control)
    (hxy : x.1 = y.1) :
    inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
        (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
          control0 x) (r.val - s) ↔
      inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
        (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
          control y) (r.val - s) := by
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource j r control0 x.1
  let source1 := ReferenceGeneratedActivePrefixFactor.splitSource j r control y.1
  let out (source : SourceInput p) := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let ordinary (source : SourceInput p) (f : ActiveRoundActions.Follower p.m) :
      ReferencePrelaunchFollower.State p rate.eta :=
    ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (out source) f
  have hfacts0 := ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
    rate rewards C_star C_h j r s hsr control0 x.1 x.2.1 x.2.2
  have hfacts1 := ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
    rate rewards C_star C_h j r s hsr control y.1 y.2.1 y.2.2
  have hindex : ActualInitializationPhysicalStep.selectedRowIndex p source0 = j := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p j r control0 x.1 x.2.1
  have hreplace : source1 = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p r source0 control := by
    have h := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p j r source0 control hindex
    simpa [source0, source1, ReferenceGeneratedActivePrefixFactor.splitSource,
      hxy] using h
  have hstop := ReferenceInitializationControlRemainder.stopped_observation_replaceSourceControl
    rate rewards C_star C_h r source0 control s (by omega)
  have hstop' : ReferenceInitializationControlRemainder.stoppedObservation
      rate rewards C_star C_h source0 s =
        ReferenceInitializationControlRemainder.stoppedObservation
          rate rewards C_star C_h source1 s := by
    rw [hreplace]
    exact hstop.2
  have hcrossed0 : ReferenceInitializationControlRemainder.stoppedCrossedBy
      rate rewards C_star C_h source0 s := by
    refine ⟨hfacts0.1, ?_⟩
    rw [hfacts0.2]
  have hcrossed1 : ReferenceInitializationControlRemainder.stoppedCrossedBy
      rate rewards C_star C_h source1 s := by
    refine ⟨hfacts1.1, ?_⟩
    rw [hfacts1.2]
  have hpayload : (out source0, fun f => ordinary source0 f) =
      (out source1, fun f => ordinary source1 f) := by
    simpa [ReferenceInitializationControlRemainder.stoppedObservation,
      hcrossed0, hcrossed1, out, ordinary] using hstop'
  have houtEq : out source0 = out source1 := congrArg Prod.fst hpayload
  have hordinaryEq : (fun f => ordinary source0 f) = (fun f => ordinary source1 f) :=
    congrArg Prod.snd hpayload
  have hobs := ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation_eq_of_remainder_eq
    rate rewards C_star C_h j r s hsr control0 control i x y hxy
  have hleft := inheritedDownMarker_retained_iff_code (rate := rate) rewards C_star C_h
    alpha k q w j r s hsr control0 i x
  have hright := inheritedDownMarker_retained_iff_code (rate := rate) rewards C_star C_h
    alpha k q w j r s hsr control i y
  simp only [ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput]
    at hleft hright
  have hbank := congrFun hordinaryEq (ActualReferenceInitializationBlock.refFollower i)
  change ordinary source0 _ = ordinary source1 _ at hbank
  have hcode :
      inheritedDownMarkerCode (rate := rate) alpha k q s (r.val - s) w i
        ((out source0).activation (ActualReferenceInitializationBlock.refFollower i))
        (ReferenceInitializationMeasurability.downBatchCode
          ((ordinary source0 (ActualReferenceInitializationBlock.refFollower i)).downBatch))
        (ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
          rate rewards C_star C_h j r s hsr control0 i x) ↔
      inheritedDownMarkerCode (rate := rate) alpha k q s (r.val - s) w i
        ((out source1).activation (ActualReferenceInitializationBlock.refFollower i))
        (ReferenceInitializationMeasurability.downBatchCode
          ((ordinary source1 (ActualReferenceInitializationBlock.refFollower i)).downBatch))
        (ReferenceGeneratedDownPrefixEvent.retainedPrefixObservation
          rate rewards C_star C_h j r s hsr control i y) := by
    rw [houtEq, hbank, hobs]
  exact hleft.trans (hcode.trans hright.symm)

/-- Reconstruct the inherited marker from the original pair remainder.
Every removed DOWN pair gives the same old bank, launch boundary, and
`[s,r)` observation marker as the canonical pair used to define the Borel
remainder cylinder. -/
theorem inheritedDownMarker_pair_reconstruct
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (w : Candidate p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (a : Pair p) (v : PairRemainder p j r i)
    (hv : v ∈ inheritedDownLaunchRemainder rate rewards C_star C_h j r s hsr control0 i)
    (x : LaunchSource (rate := rate) rewards C_star C_h s (by omega))
    (hx : x.1 = (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (a, v)) :
    inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i x
        (r.val - s) ↔
      inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s (by omega) i
        (inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h j r s hsr
          control0 (inheritedDownRemainderRetainedLaunch rate rewards C_star C_h j r s
            hsr control0 i ⟨v, hv⟩)) (r.val - s) := by
  let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (a, v)
  let branch : {source : SourceInput p // source ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
        rewards C_star C_h j r (0, i) s} :=
    ⟨z, (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 a v).2 hv⟩
  let launch : LaunchSource (rate := rate) rewards C_star C_h s (by omega) :=
    ⟨z, branch.2.2.1, branch.2.2.2⟩
  have hx' : x = launch := Subtype.ext hx
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = j := by
    have h := congrArg Prod.fst branch.2.1
    change ActualInitializationPhysicalStep.selectedRowIndex p z = j at h
    exact h
  let control := (z.1.2 j).2 r
  let atBase := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  let atSource := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h j r s hsr control z hselected launch.2.1 launch.2.2
  let canonical := inheritedDownRemainderRetainedLaunch rate rewards C_star C_h
    j r s hsr control0 i ⟨v, hv⟩
  have hbaseSource : atBase.1 = atSource.1 := by
    rw [ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val,
      ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val]
  have hbaseCanonical : atBase = canonical := by
    apply Subtype.ext
    rw [ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val]
    exact ReferenceGeneratedAffineHashHalf.fixedControlSplit_pair_remainder (a := a) v
  have hindependent := inheritedDownMarker_retained_control_independent
    (rate := rate) rewards C_star C_h alpha k q w j r s hsr control0 control i
    atBase atSource hbaseSource
  have hsource : inheritedDownRetainedLaunchSource (rate := rate) rewards C_star C_h
      j r s hsr control atSource = launch := by
    apply Subtype.ext
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm
      (control, atSource.1) = z
    rw [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val]
    have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r z =
        (control, (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r z).2) := by
      apply Prod.ext <;> rfl
    rw [← hsplit]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p j r).symm_apply_apply z
  rw [hbaseCanonical, hsource] at hindependent
  simpa only [hx'] using hindependent.symm

/-- Full source reconstruction for every removed DOWN pair. The baseline
retained control serves only to code the marker; the launch on the right is
at the original source with its actual current control. Positivity is absent. -/
theorem inheritedDownMarkerRemainder_pair_iff
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1))
    (a : Pair p) (v : PairRemainder p j r i) :
    v ∈ inheritedDownMarkerRemainder rate rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i ↔
    let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (a, v)
    ReferenceSelectedAffinePairLaw.selector p r z = (j, some (0, i)) ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ Cell ∧
      ∃ x : LaunchSource (rate := rate) rewards C_star C_h s (by omega),
        x.val = z ∧ inheritedDownMarker (rate := rate) rewards C_star C_h alpha k q w s
          (by omega) i x (r.val - s) := by
  let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (a, v)
  have hp := ReferenceGeneratedPrelaunchDownCurrentPair.same_ids_past_of_pair_replacement
    j r i v a default
  have hview : ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z =
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)).symm (default, v)) :=
    Prod.ext hp.1 hp.2
  rw [inheritedDownMarkerRemainder_mem_iff]
  constructor
  · rintro ⟨hv, hcell, hmarker⟩
    have hb := (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 a v).mpr hv
    let x : LaunchSource (rate := rate) rewards C_star C_h s (by omega) :=
      ⟨z, hb.2.1, hb.2.2⟩
    refine ⟨hb.1, hview.symm ▸ hcell, x, rfl, ?_⟩
    exact (inheritedDownMarker_pair_reconstruct (rate := rate) rewards C_star C_h
      alpha k q w j r s hsr control0 i a v hv x rfl).mpr hmarker
  · rintro ⟨hselector, hcell, x, hx, hmarker⟩
    have hb : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
        rewards C_star C_h j r (0, i) s :=
      ⟨hselector, by simpa only [hx] using x.property.1,
        by simpa only [hx] using x.property.2⟩
    have hv := (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 a v).mp hb
    refine ⟨hv, hview ▸ hcell, ?_⟩
    exact (inheritedDownMarker_pair_reconstruct (rate := rate) rewards C_star C_h
      alpha k q w j r s hsr control0 i a v hv x hx).mp hmarker

end Bandits.Support.ReferenceGeneratedInheritedDownPrefixMarker

end
