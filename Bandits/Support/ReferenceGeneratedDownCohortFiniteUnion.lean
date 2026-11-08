/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedMixedDownAtBirthTail
public import Bandits.Support.ReferenceGeneratedDownFreshAllLaunchTail

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# Joint mixed and fresh DOWN cohort finite union

This module bounds one literal union of the actual mixed DOWN detector over
all bounded physical births and the actual generated fresh-reset event over
all earlier launch strata. Its base-mass join uses their source-level
disjointness, so it pays no phase or birth-count factor. The result is an
internal source-probability estimate, not either manuscript error event.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-155`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion

variable {p : ConstructorDimensions.Parameters}

variable
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev Candidate (p : ConstructorDimensions.Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev SourceLaw (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.sourceInputLaw p

private theorem filterMap_length_le {α β : Type*}
    (l : List α) (f : α → Option β) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases hf : f a <;> simp [hf, ih] <;> omega

private theorem boundaryPrelaunchDownTests_length_le
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (i : Fin (p.m - 1)) :
    (ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i).length ≤
      ReferenceInitializationRun.elapsed p b.completed := by
  classical
  let f := ActualReferenceInitializationBlock.refFollower i
  by_cases hforced : b.forcedFailure f
  · simp [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests, f, hforced]
  · cases hactivation : b.activation f with
    | none =>
        simp [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
          f, hforced, hactivation]
    | some a =>
        simp only [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
          f, hforced, hactivation]
        change ((List.ofFn (fun u : Fin
          (ReferenceInitializationRun.elapsed p b.completed) => u)).filterMap
            (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
              (ReferencePrelaunchFollower.calendar
                (ReferenceInitializationRun.elapsed_le_T p b.completed) u)
              (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u))).length ≤ _
        calc
          _ ≤ (List.ofFn (fun u : Fin
              (ReferenceInitializationRun.elapsed p b.completed) => u)).length :=
                filterMap_length_le _ _
          _ = ReferenceInitializationRun.elapsed p b.completed := by simp

private theorem completed_quota_le_test_count
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (hmap : tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
      AffineBatchDecoder.collected bank)
    (hquota : ∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) :
    AffineBatchDecoder.quota p * bank.completed.length ≤ tests.length := by
  have hcollected := AffineBatchDecoder.length_collected bank hquota
  have hmapLength : tests.length = (AffineBatchDecoder.collected bank).length := by
    have h := congrArg List.length hmap
    simpa only [List.length_map] using h
  calc
    AffineBatchDecoder.quota p * bank.completed.length ≤
        bank.completed.length * AffineBatchDecoder.quota p + bank.pending.length := by
          rw [Nat.mul_comm]
          exact Nat.le_add_right _ _
    _ = (AffineBatchDecoder.collected bank).length := hcollected.symm
    _ = tests.length := hmapLength.symm

/-- Every actual birth ordinal is bounded by the physical boundary. For a
strict prefix this comes from the real `Fin alpha` filterMap census; at `T` it
comes from the actual terminal output census, including the forced initial
bank branch. -/
theorem birthAt_ordinal_le
    (i : Fin (p.m - 1)) (alpha k : ℕ) (hAlpha : alpha ≤ p.T)
    (z : SourceInput p)
    (hbirth : ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k) :
    k ≤ alpha := by
  classical
  by_cases hlt : alpha < p.T
  · let r : Fin p.T := ⟨alpha, hlt⟩
    have hbirth' := hbirth
    cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i ⟨alpha, hlt⟩ with
    | inl branch =>
        cases branch with
        | inl active =>
            simp only [Set.mem_setOf_eq,
              ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hbirth'
            rcases hbirth' with ⟨hcompleted, _, _⟩
            have hcensus := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_census
              rate rewards C_star C_h z i r
            have hprefR : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
                rate rewards C_star C_h z i r = .inl (.inl active) := by
              simpa only [r] using hpref
            rw [hprefR] at hcensus
            rcases hcensus with ⟨hmap, _, hquota, _⟩
            let bank := active.val.2.2.2.downBatch
            have htestsBound :
                (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
                  rate rewards C_star C_h z i r).length ≤ alpha := by
              rw [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests, hprefR]
              exact (filterMap_length_le _ _).trans (by simp [r])
            have hcount := completed_quota_le_test_count bank
              (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
                rate rewards C_star C_h z i r)
              (by simpa only [bank] using hmap) (by simpa only [bank] using hquota)
            have hcount' : AffineBatchDecoder.quota p * k ≤
                (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
                  rate rewards C_star C_h z i r).length := by
              simpa only [bank, hcompleted] using hcount
            have hQ : 1 ≤ AffineBatchDecoder.quota p :=
              Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)
            have hkQ : k ≤ AffineBatchDecoder.quota p * k := by
              calc
                k = 1 * k := by omega
                _ ≤ AffineBatchDecoder.quota p * k := Nat.mul_le_mul_right k hQ
            exact hkQ.trans (hcount'.trans htestsBound)
        | inr _ =>
            simp only [Set.mem_setOf_eq,
              ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hbirth'
    | inr stopped =>
        simp only [Set.mem_setOf_eq,
          ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hbirth'
        rcases hbirth' with ⟨a, _, hcompleted, _, _⟩
        have hcensus := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_census
          rate rewards C_star C_h z i r
        have hprefR : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z i r = .inr stopped := by
          simpa only [r] using hpref
        rw [hprefR] at hcensus
        rcases hcensus with ⟨hmap, _, hquota, _⟩
        let bank := stopped.val.2.downBatch
        have hElapsed : ReferenceInitializationRun.elapsed p stopped.val.1.completed ≤ alpha := by
          rw [stopped.property.2.1]
          exact (ReferenceInitializationRun.elapsed_mono p
            (ReferenceInitializationPrefixInvariance.run_completed_le
              (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
                rate rewards C_star C_h z) (BootstrapDimensions.roundBlockIndex
                  p r).val)).trans
            (GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
              (s := BootstrapDimensions.roundBlockIndex p r) (t := r)
              (BootstrapDimensions.round_mem_quotient_block p r))
        have htestsBound :
            (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
              rate rewards C_star C_h z i r).length ≤ alpha := by
          rw [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests, hprefR]
          exact (boundaryPrelaunchDownTests_length_le
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
              rate rewards C_star C_h z) stopped.val.1 i).trans hElapsed
        have hcount := completed_quota_le_test_count bank
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
            rate rewards C_star C_h z i r)
          (by simpa only [bank] using hmap) (by simpa only [bank] using hquota)
        have hcount' : AffineBatchDecoder.quota p * k ≤
            (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
              rate rewards C_star C_h z i r).length := by
          simpa only [bank, hcompleted] using hcount
        have hQ : 1 ≤ AffineBatchDecoder.quota p :=
          Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)
        have hkQ : k ≤ AffineBatchDecoder.quota p * k := by
          calc
            k = 1 * k := by omega
            _ ≤ AffineBatchDecoder.quota p * k := Nat.mul_le_mul_right k hQ
        exact hkQ.trans (hcount'.trans htestsBound)
  · have halpha : alpha = p.T := by omega
    subst alpha
    simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
      dif_neg (Nat.not_lt.mpr le_rfl)] at hbirth
    rcases hbirth with ⟨a, _, hcompleted, _, _⟩
    let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
      rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    let bank := (ReferenceInitializationRun.ordinary x b f).downBatch
    let tests := ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
      rate rewards C_star C_h z i
    have hcensus := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
      rate rewards C_star C_h z i
    rcases hcensus with ⟨hmap, _, hcompletedBatches, _⟩
    have hquota : ∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p := by
      intro batch hmem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
      have hlen := (hcompletedBatches j hj).2
      change (ReferenceInitializationRun.ordinary x b f).downBatch.completed[j].length =
        AffineBatchDecoder.quota p at hlen
      change (ReferenceInitializationRun.ordinary x b f).downBatch.completed[j] = batch at hget
      rw [hget] at hlen
      exact hlen
    have htestsBound : tests.length ≤ p.T := by
      change (ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
        x b i).length ≤ p.T
      exact (boundaryPrelaunchDownTests_length_le x b i).trans
        (ReferenceInitializationRun.elapsed_le_T p b.completed)
    have hcount := completed_quota_le_test_count bank tests
      (by simpa only [tests, bank, x, b, f,
        ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using hmap) hquota
    have hcount' : AffineBatchDecoder.quota p * k ≤ tests.length := by
      change (ReferenceInitializationRun.ordinary x b f).downBatch.completed.length = k at hcompleted
      rw [hcompleted] at hcount
      exact hcount
    have hQ : 1 ≤ AffineBatchDecoder.quota p :=
      Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)
    have hkQ : k ≤ AffineBatchDecoder.quota p * k := by
      calc
        k = 1 * k := by omega
        _ ≤ AffineBatchDecoder.quota p * k := Nat.mul_le_mul_right k hQ
    exact hkQ.trans (hcount'.trans htestsBound)

/-- At a fixed source and boundary, the completed-bank readout in `birthAt`
determines its ordinal. This includes the stopped existential-activation
branch, which retains the same ordinary bank. -/
theorem birthAt_pairwiseDisjoint
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T) :
    Pairwise (Function.onFun Disjoint
      (fun k : Fin (alpha + 1) =>
        {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k.val})) := by
  classical
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro z hk hl
  have hEq : k.val = l.val := by
    by_cases hlt : alpha < p.T
    · let r : Fin p.T := ⟨alpha, hlt⟩
      have hk' := hk
      have hl' := hl
      cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i ⟨alpha, hlt⟩ with
      | inl branch =>
          cases branch with
          | inl active =>
              simp only [Set.mem_setOf_eq,
                ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hk' hl'
              exact hk'.1.symm.trans hl'.1
          | inr _ =>
              simp only [Set.mem_setOf_eq,
                ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hk'
      | inr stopped =>
          simp only [Set.mem_setOf_eq,
            ReferenceGeneratedPrelaunchDownPrefix.birthAt, dif_pos hlt, hpref] at hk' hl'
          rcases hk' with ⟨_, _, hlenK, _, _⟩
          rcases hl' with ⟨_, _, hlenL, _, _⟩
          exact hlenK.symm.trans hlenL
    · have halpha : alpha = p.T := by omega
      subst alpha
      simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
        dif_neg (Nat.not_lt.mpr le_rfl)] at hk hl
      rcases hk with ⟨_, _, hlenK, _, _⟩
      rcases hl with ⟨_, _, hlenL, _, _⟩
      exact hlenK.symm.trans hlenL
  exact hkl (Fin.ext hEq)

/-- A mixed hashed detector can occur only on its actual level-zero birth.
This follows by removing the current hash equation, using the mixed
occurrence-to-previous inclusion, and iterating down to `mixedDownDetector_zero`.
-/
theorem mixedDownDetector_subset_birthAt
    (i : Fin (p.m - 1)) (alpha k : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) :
    {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha k hAlpha w control0 q} ⊆
    {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k} := by
  induction q with
  | zero =>
      intro z hz
      rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_zero
        rate rewards C_star C_h i alpha k hAlpha w control0] at hz
      exact hz
  | succ q ih =>
      by_cases hquota : q + 1 ≤ AffineBatchDecoder.quota p
      · intro z hz
        have hpositive := ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
          rate rewards C_star C_h i alpha k (q + 1) hAlpha w (by omega) hquota control0
        rw [hpositive] at hz
        have hUnhashed :
            z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
              rate rewards C_star C_h i alpha k (q + 1) hAlpha w (by omega) hquota control0 := by
          rcases hz with hpre | hpost
          · rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector_succ
              rate rewards C_star C_h i alpha k q hAlpha w] at hpre
            obtain ⟨r, hpre⟩ := hpre
            exact Or.inl ⟨r, hpre.1⟩
          · obtain ⟨δ, hpost⟩ := Set.mem_iUnion.mp hpost
            exact Or.inr (Set.mem_iUnion.mpr ⟨δ, hpost.1⟩)
        have hprevious := ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion_subset_previous
          rate rewards C_star C_h i alpha k (q + 1) hAlpha w (by omega) hquota control0
          hUnhashed
        exact ih hprevious
      · intro z hz
        rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_eq_empty_of_quota_lt
          rate rewards C_star C_h i alpha k (q + 1) hAlpha w control0 (by omega)] at hz
        exact hz.elim

/-- The unrestricted countable birth union is exactly its census-bounded
finite union. No ordinal is removed merely because it is a natural number. -/
theorem birthAt_iUnion_nat_eq_iUnion_fin
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T) :
    (⋃ k : ℕ, {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k}) =
      ⋃ k : Fin (alpha + 1),
        {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k.val} := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    have hbound := birthAt_ordinal_le rate rewards C_star C_h i alpha k hAlpha z hk
    exact ⟨⟨k, Nat.lt_succ_of_le hbound⟩, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.val, hk⟩

/-- The unrestricted detector union also reduces to the actual finite birth
census, by detector-to-birth inclusion followed by the ordinal bound. -/
theorem mixedDownDetector_iUnion_nat_eq_iUnion_fin
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) :
    (⋃ k : ℕ, {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha k hAlpha w control0 q}) =
      ⋃ k : Fin (alpha + 1),
        {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k.val hAlpha w control0 q} := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    have hbirth := mixedDownDetector_subset_birthAt rate rewards C_star C_h i alpha k
      hAlpha w control0 q hk
    have hbound := birthAt_ordinal_le rate rewards C_star C_h i alpha k hAlpha z hbirth
    exact ⟨⟨k, Nat.lt_succ_of_le hbound⟩, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.val, hk⟩

def mixedDownDetectorAllOrdinals
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) : Set (SourceInput p) :=
  ⋃ k : ℕ, {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
    rate rewards C_star C_h i alpha k hAlpha w control0 q}

def birthAtAllOrdinals
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T) : Set (SourceInput p) :=
  ⋃ k : ℕ, {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
    rate rewards C_star C_h z i alpha hAlpha k}

private theorem mixedDownDetector_finite_ordinal_geometric_bound
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) :
    SourceLaw p (⋃ k : Fin (alpha + 1),
      {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
        rate rewards C_star C_h i alpha k.val hAlpha w control0 q}) ≤
      ((1 : ENNReal) / 2) ^ q * SourceLaw p
        (⋃ k : Fin (alpha + 1),
          {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k.val}) := by
  classical
  let μ := SourceLaw p
  let D := fun k : Fin (alpha + 1) =>
    {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha k.val hAlpha w control0 q}
  let B := fun k : Fin (alpha + 1) =>
    {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k.val}
  have hdisjB : Pairwise (Function.onFun Disjoint B) := by
    simpa only [B] using birthAt_pairwiseDisjoint rate rewards C_star C_h i alpha hAlpha
  have hdisjD : Pairwise (Function.onFun Disjoint D) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hzk hzl
    have hbk := mixedDownDetector_subset_birthAt rate rewards C_star C_h i alpha k.val
      hAlpha w control0 q hzk
    have hbl := mixedDownDetector_subset_birthAt rate rewards C_star C_h i alpha l.val
      hAlpha w control0 q hzl
    exact (Set.disjoint_left.mp (hdisjB hkl)) hbk hbl
  have hmeasD : ∀ k, MeasurableSet (D k) := by
    intro k
    exact ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha k.val hAlpha w control0 q
  have hmeasB : ∀ k, MeasurableSet (B k) := by
    intro k
    change MeasurableSet {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k.val}
    rw [← ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_zero
      rate rewards C_star C_h i alpha k.val hAlpha w control0]
    exact ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha k.val hAlpha w control0 0
  have hDmeasure : μ (⋃ k : Fin (alpha + 1), D k) ≤
      ((1 : ENNReal) / 2) ^ q * μ (⋃ k : Fin (alpha + 1), B k) := by
    calc
      μ (⋃ k : Fin (alpha + 1), D k) =
          ∑ k : Fin (alpha + 1), μ (D k) := by
        rw [measure_iUnion hdisjD hmeasD, tsum_fintype]
      _ ≤ ∑ k : Fin (alpha + 1),
          ((1 : ENNReal) / 2) ^ q * μ (B k) := by
        apply Finset.sum_le_sum
        intro k _
        exact ReferenceGeneratedMixedDownAtBirthTail.mixedDownDetector_source_geometric_bound
          rate rewards C_star C_h i alpha k.val hAlpha w control0 q
      _ = ((1 : ENNReal) / 2) ^ q *
          ∑ k : Fin (alpha + 1), μ (B k) := by rw [Finset.mul_sum]
      _ = ((1 : ENNReal) / 2) ^ q * μ (⋃ k : Fin (alpha + 1), B k) := by
        rw [measure_iUnion hdisjB hmeasB, tsum_fintype]
  simpa only [D, B] using hDmeasure

/-- The full mixed detector over every physical birth has the geometric bound
relative to the union of those actual birth strata. -/
theorem mixedDownAllOrdinal_geometric_bound
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) :
    SourceLaw p (mixedDownDetectorAllOrdinals rate rewards C_star C_h i alpha hAlpha
      w control0 q) ≤
      ((1 : ENNReal) / 2) ^ q *
        SourceLaw p (birthAtAllOrdinals rate rewards C_star C_h i alpha hAlpha) := by
  rw [mixedDownDetectorAllOrdinals,
    mixedDownDetector_iUnion_nat_eq_iUnion_fin rate rewards C_star C_h i alpha hAlpha w control0 q,
    birthAtAllOrdinals,
    birthAt_iUnion_nat_eq_iUnion_fin rate rewards C_star C_h i alpha hAlpha]
  exact mixedDownDetector_finite_ordinal_geometric_bound
    rate rewards C_star C_h i alpha hAlpha w control0 q

/-- The relative all-ordinal estimate also holds for real measure on the
finite original source probability space. -/
theorem mixedDownAllOrdinal_measureReal_geometric_bound
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (q : ℕ) :
    (SourceLaw p).real
        (mixedDownDetectorAllOrdinals rate rewards C_star C_h i alpha hAlpha w control0 q) ≤
      ((1 : ℝ) / 2) ^ q * (SourceLaw p).real
        (birthAtAllOrdinals rate rewards C_star C_h i alpha hAlpha) := by
  have h := mixedDownAllOrdinal_geometric_bound rate rewards C_star C_h i alpha hAlpha
    w control0 q
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hreal

/-- A positive mixed detector at the terminal boundary is empty. The
prelaunch branch would require a physical round at or after `T`; the inherited
branch would require a launch start at or after `T`. The level-zero birth is
not covered by this result. -/
theorem mixedDownDetector_terminal_eq_empty
    (i : Fin (p.m - 1)) (k : ℕ) (w : Candidate p)
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ)
    (hq : 1 ≤ q) :
    ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i p.T k le_rfl w control0 q = ∅ := by
  by_cases hquota : q ≤ AffineBatchDecoder.quota p
  · rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
      rate rewards C_star C_h i p.T k q le_rfl w hq hquota control0]
    have hpre : ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
        rate rewards C_star C_h i p.T k le_rfl w q = ∅ := by
      cases q with
      | zero => omega
      | succ n =>
          rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector_succ
            rate rewards C_star C_h i p.T k n le_rfl w]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          obtain ⟨r, hocc⟩ := hz
          have hstart := hocc.1.1.2.2.1
          omega
    have hpost : ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
        (rate := rate) rewards C_star C_h i p.T k q le_rfl w hq hquota control0 = ∅ := by
      unfold ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨δ, _⟩ := Set.mem_iUnion.mp hz
      have hstart : p.T ≤ δ.1.2.1.val := δ.2.1
      omega
    rw [hpre, hpost]
    simp
  · rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_eq_empty_of_quota_lt
      rate rewards C_star C_h i p.T k q le_rfl w control0 (by omega)]

/-- The literal joint event: for each receiver, physical start, and candidate,
take the finite union over its actual prelaunch birth ordinals and join that
with the generated fresh-reset event over all actual earlier launch strata.
`control0` is supplied to the mixed detector; the fresh event itself does not
depend on it. -/
def downCohortUnionEvent
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ) :
    Set (SourceInput p) :=
  ⋃ i : Fin (p.m - 1), ⋃ alpha : Fin p.T, ⋃ w : Candidate p,
    (⋃ k : Fin (alpha.val + 1),
      {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
        rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q}) ∪
      ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
        (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q

private theorem no_birthAt_after_actual_launch
    (i : Fin (p.m - 1)) (s alpha k : ℕ) (hs : s < p.T)
    (hsa : s < alpha) (halpha : alpha < p.T)
    (z : SourceInput p)
    (launch : ReferenceGeneratedDownQthCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (hsource : launch.val = z) :
    ¬ ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha (Nat.le_of_lt halpha) k := by
  classical
  subst z
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h launch.val
  let r : Fin p.T := ⟨alpha, halpha⟩
  have hElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed = s := by
    simpa only [x, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using
      launch.property.2
  have hCross : (ReferenceInitializationRun.output x).crossing.isSome = true := by
    simpa only [x, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using
      launch.property.1
  have hCompletedMul : (ReferenceInitializationRun.output x).completed *
      BootstrapDimensions.B_boot p = s := by
    dsimp only [ReferenceInitializationRun.elapsed] at hElapsed
    omega
  have hCompletedLe : (ReferenceInitializationRun.output x).completed ≤
      (BootstrapDimensions.roundBlockIndex p r).val := by
    apply (Nat.le_div_iff_mul_le (BootstrapDimensions.B_boot_pos p)).2
    rw [hCompletedMul]
    exact Nat.le_of_lt hsa
  have hRunAtOutputCompleted := ReferenceInitializationPrefixInvariance.run_at_completed
    x (BootstrapDimensions.n_boot p) le_rfl
  change ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed =
    ReferenceInitializationRun.output x at hRunAtOutputCompleted
  have hCrossAtOutputCompleted :
      (ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed).crossing.isSome =
        true := by
    rw [hRunAtOutputCompleted]
    exact hCross
  have hStop := ReferenceInitializationRun.run_stops_at_crossing x
    (ReferenceInitializationRun.output x).completed
    ((BootstrapDimensions.roundBlockIndex p r).val -
      (ReferenceInitializationRun.output x).completed) hCrossAtOutputCompleted
  have hRunAtRound : ReferenceInitializationRun.run x
      (BootstrapDimensions.roundBlockIndex p r).val =
        ReferenceInitializationRun.output x := by
    rw [Nat.add_sub_of_le hCompletedLe] at hStop
    exact hStop.trans hRunAtOutputCompleted
  have hCrossAtRound :
      (ReferenceInitializationRun.run x
        (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = true := by
    rw [hRunAtRound]
    exact hCross
  have hOutputAtRound := ReferenceInitializationRun.output_eq_of_crossing x
    (BootstrapDimensions.roundBlockIndex p r).val
    (BootstrapDimensions.roundBlockIndex p r).isLt.le hCrossAtRound
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h launch.val i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hnone := active.val.1.property.2.1
          have hfalse : (ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = false := by
            rw [← active.val.1.property.2.2]
            simp [hnone]
          simp only [hfalse, Bool.false_eq_true] at hCrossAtRound
      | inr inactive =>
          have hnone := inactive.val.1.property.2.1
          have hfalse : (ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = false := by
            rw [← inactive.val.1.property.2.2]
            simp [hnone]
          simp only [hfalse, Bool.false_eq_true] at hCrossAtRound
  | inr stopped =>
      have hboundary : stopped.val.1 = ReferenceInitializationRun.output x := by
        calc
          stopped.val.1 = ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val :=
                stopped.property.2.1
          _ = ReferenceInitializationRun.output x := hOutputAtRound.symm
      have hlate : ReferenceInitializationRun.elapsed p stopped.val.1.completed < alpha := by
        rw [hboundary, hElapsed]
        exact hsa
      exact ReferenceGeneratedPrelaunchDownBirthBounds.source_prelaunch_down_stopped_prefix_no_late_birthAt
        rate rewards C_star C_h launch.val i r stopped hpref hlate k

private theorem birthUnion_disjoint_freshBase
    (i : Fin (p.m - 1)) (alpha : Fin p.T) (w : Candidate p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Disjoint
      (⋃ k : Fin (alpha.val + 1),
        {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha.val alpha.isLt.le k.val})
      (ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
        (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0) := by
  apply Set.disjoint_left.mpr
  intro z hbirth hfresh
  obtain ⟨k, hbirth⟩ := Set.mem_iUnion.mp hbirth
  have hfresh' := hfresh
  simp only [ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent,
    Set.mem_setOf_eq] at hfresh'
  obtain ⟨s, hs, hsa, hsource⟩ := hfresh'
  have hsource' := hsource
  simp only [ReferenceGeneratedDownFreshSourceTail.generatedDownFreshSourceEvent,
    Set.mem_setOf_eq] at hsource'
  obtain ⟨launch, hsourceEq, _⟩ := hsource'
  exact no_birthAt_after_actual_launch rate rewards C_star C_h i s alpha.val k hs hsa
    alpha.isLt z launch hsourceEq hbirth

private theorem downCohortUnion_stratum_measure_le
    (i : Fin (p.m - 1)) (alpha : Fin p.T) (w : Candidate p)
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p) :
    SourceLaw p
        ((⋃ k : Fin (alpha.val + 1),
          {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q}) ∪
          ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
            (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q) ≤
      ((1 : ENNReal) / 2) ^ q := by
  let μ := SourceLaw p
  let B := ⋃ k : Fin (alpha.val + 1),
    {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha.val alpha.isLt.le k.val}
  let D := ⋃ k : Fin (alpha.val + 1),
    {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q}
  let F0 := ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
    (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0
  let Fq := ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
    (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro k
    rw [← ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_zero
      rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0]
    exact ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 0
  have hF0meas : MeasurableSet F0 := by
    exact ReferenceGeneratedDownFreshAllLaunchTail.measurableSet_generatedDownFreshAllLaunchSourceEvent
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0 (by omega) control0
  have hdisj : Disjoint B F0 := by
    simpa only [B, F0] using birthUnion_disjoint_freshBase rate rewards C_star C_h
      i alpha w control0
  have hbase : μ B + μ F0 ≤ 1 := by
    calc
      μ B + μ F0 = μ (B ∪ F0) := by rw [← measure_union hdisj hF0meas]
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hD : μ D ≤ ((1 : ENNReal) / 2) ^ q * μ B := by
    simpa only [μ, D, B] using mixedDownDetector_finite_ordinal_geometric_bound
      rate rewards C_star C_h i alpha.val alpha.isLt.le w control0 q
  have hF : μ Fq ≤ ((1 : ENNReal) / 2) ^ q * μ F0 := by
    simpa only [μ, Fq, F0] using
      ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent_measure_le_geometric
        (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q hqQ control0
  calc
    μ (D ∪ Fq) ≤ μ D + μ Fq := measure_union_le D Fq
    _ ≤ ((1 : ENNReal) / 2) ^ q * μ B +
        ((1 : ENNReal) / 2) ^ q * μ F0 := add_le_add hD hF
    _ = ((1 : ENNReal) / 2) ^ q * (μ B + μ F0) := by rw [mul_add]
    _ ≤ ((1 : ENNReal) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((1 : ENNReal) / 2) ^ q := by simp

/-- The literal finite union is Borel for every level through the actual
decoder quota. -/
theorem measurableSet_downCohortUnionEvent
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet (downCohortUnionEvent rate rewards C_star C_h control0 q) := by
  classical
  unfold downCohortUnionEvent
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro alpha
  apply MeasurableSet.iUnion
  intro w
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro k
    exact ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q
  · exact ReferenceGeneratedDownFreshAllLaunchTail.measurableSet_generatedDownFreshAllLaunchSourceEvent
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q hqQ control0

/-- The joint finite union pays only the candidate, receiver, and physical
start counts. Its per-cell estimate uses the disjoint actual birth/reset base. -/
theorem downCohortUnionEvent_measure_le_geometric
    (control0 : ContinuousLearningRows.TimeControl p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p) :
    SourceLaw p (downCohortUnionEvent rate rewards C_star C_h control0 q) ≤
      (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) * ((1 : ENNReal) / 2) ^ q := by
  classical
  let μ := SourceLaw p
  calc
    μ (downCohortUnionEvent rate rewards C_star C_h control0 q) ≤
        ∑ i : Fin (p.m - 1), μ (⋃ alpha : Fin p.T, ⋃ w : Candidate p,
          (⋃ k : Fin (alpha.val + 1),
            {z : SourceInput p | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
              rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q}) ∪
          ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
            (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q) := by
      apply measure_iUnion_fintype_le
    _ ≤ ∑ i : Fin (p.m - 1), ∑ alpha : Fin p.T, ∑ w : Candidate p,
        ((1 : ENNReal) / 2) ^ q := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro alpha _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro w _
      exact downCohortUnion_stratum_measure_le rate rewards C_star C_h i alpha w
        control0 q hqQ
    _ = (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) * ((1 : ENNReal) / 2) ^ q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, mul_assoc]

/-- At the actual decoder quota, converting the finite-source measure to real
measure and applying the source's exact quota arithmetic gives the joint
`1/(4N²)` bound. -/
theorem downCohortUnionEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (SourceLaw p).real
        (downCohortUnionEvent rate rewards C_star C_h control0
          (AffineBatchDecoder.quota p)) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  have h := downCohortUnionEvent_measure_le_geometric rate rewards C_star C_h
    control0 (AffineBatchDecoder.quota p) le_rfl
  have hreal := ENNReal.toReal_mono (by finiteness) h
  have hquota := ReferenceSuppressedDownTail.quota_union_factor_le p
  calc
    (SourceLaw p).real
        (downCohortUnionEvent rate rewards C_star C_h control0
          (AffineBatchDecoder.quota p)) ≤
        (((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
          (2 : ℝ) ^ AffineBatchDecoder.width p) * ((1 : ℝ) / 2) ^
            AffineBatchDecoder.quota p := by
      simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        ENNReal.toReal_natCast] using hreal
    _ = ((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
          2 ^ AffineBatchDecoder.width p *
          ((2 : ℝ) ^ AffineBatchDecoder.quota p)⁻¹ := by
      have hpow : ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p =
          ((2 : ℝ) ^ AffineBatchDecoder.quota p)⁻¹ := by
        rw [one_div_pow]
        simp only [one_div]
      rw [hpow]
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := hquota

end Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion

end
