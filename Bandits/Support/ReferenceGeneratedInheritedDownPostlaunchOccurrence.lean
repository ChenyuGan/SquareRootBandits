/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownSourceHalf

import Lean.Elab.Tactic.Omega

/-!
# Actual postlaunch inherited DOWN occurrences

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-138`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.

The events below keep the actual initialization bank and cohort boundary,
the cumulative old-plus-new physical prefix, and the executed current test.
The finite index only selects a row, launch round, and current round. It does
not encode another execution or reset the inherited prefix when a decoder
bank is cleared.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceGeneratedInheritedDownCohort
open Bandits.Support.ReferenceGeneratedInheritedDownPrefixMarker
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
open Bandits.Support.ReferenceSelectedAffinePairLaw
open Bandits.Support.ReferenceGeneratedInheritedDownSourceHalf

namespace Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchOccurrence

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev LaunchSource {p : Parameters} {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) :=
  ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs

/-- The finite stratum index records `(j,s,r)` with the actual boundary and
round order. It is only an event index. -/
abbrev Lambda (p : Parameters) (alpha : ℕ) :=
  {δ : Fin (M p) × Fin p.T × Fin p.T //
    alpha ≤ δ.2.1.val ∧ δ.2.1.val ≤ δ.2.2.val}

variable {p : Parameters}

/-- The literal actual postlaunch inherited-cohort occurrence. Every earlier
test, including the inherited bank, retains its original sent option and
sample equation. The current test is the actual positive physical call. -/
def inheritedDownPostlaunchOccurrence
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (_hAlpha : alpha ≤ p.T) (w : Candidate p) (_hq : 1 ≤ q)
    (_hqQ : q ≤ AffineBatchDecoder.quota p)
    (_control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) : Set (SourceInput p) :=
  {z |
    ReferenceSelectedAffinePairLaw.selector p δ.1.2.2 z =
        (δ.1.1, some ((0, i) : Channel p)) ∧
      ∃ x : LaunchSource (rate := rate) rewards C_star C_h δ.1.2.1.val
          (by omega),
        x.1 = z ∧
        alpha ≤ δ.1.2.1.val ∧
        (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
          rate rewards C_star C_h δ.1.2.1.val (by omega) x i).downBatch.completed.length = k ∧
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
          rate rewards C_star C_h z i k = some alpha ∧
        (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
          (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
          (δ.1.2.2.val - δ.1.2.1.val)).length = q - 1 ∧
        (∀ t ∈ ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
            (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
            (δ.1.2.2.val - δ.1.2.1.val),
          t.sent ≠ some w ∧ AffineChannelLaw.affineHash t.sample w = 1) ∧
        ∃ test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h δ.1.2.1.val (by omega) i x).2
              ⟨δ.1.2.2.val - δ.1.2.1.val, by omega⟩) = some test ∧
          test.sent ≠ some w}

/-- Add the exact original-source hash equation for `(j,r,DOWN,i)`. -/
def inheritedDownPostlaunchHashedOccurrence
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) : Set (SourceInput p) :=
  {z | z ∈ inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ ∧
    AffineChannelLaw.affineHash (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) w = 1}

/-- The finite union of the hashed actual postlaunch occurrences. -/
def inheritedDownPostlaunchDetector
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  ⋃ δ : Lambda p alpha,
    inheritedDownPostlaunchHashedOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ

/-- The corresponding finite union before imposing the original hash equation. -/
def inheritedDownPostlaunchOccurrenceUnion
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  ⋃ δ : Lambda p alpha,
    inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ

/-- Exact identification of one literal postlaunch occurrence with H's
original-source event, using the whole source carrier and a universal past
cell. -/
theorem inheritedDownPostlaunchOccurrence_eq_sourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) :
    inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
        i alpha k q hAlpha w hq hqQ control0 δ =
      ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
        (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
        δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ
        MeasurableSet.univ i := by
  ext z
  constructor
  · intro h
    rcases h with ⟨hselector, x, hx, hboundaryStart, hcompleted, hboundary,
      hlength, hgoodPrefix, test, hcurrent, hsent⟩
    refine ⟨hselector, Set.mem_univ _, x, hx, ?_, test, hcurrent, hsent⟩
    refine ⟨hboundaryStart, hcompleted, ?_, hlength, ?_⟩
    · simpa [hx] using hboundary
    · intro t ht
      exact hgoodPrefix t ht
  · intro h
    rcases h with ⟨hselector, _hcell, x, hx, hmarker, test, hcurrent, hsent⟩
    rcases hmarker with ⟨hboundaryStart, hcompleted, hboundary, hlength, hgoodPrefix⟩
    refine ⟨hselector, x, hx, hboundaryStart, hcompleted, ?_, hlength, ?_,
      test, hcurrent, hsent⟩
    · simpa [hx] using hboundary
    · intro t ht
      exact hgoodPrefix t ht

/-- Exact identification of the hashed event with H's original-pair event. -/
theorem inheritedDownPostlaunchHashedOccurrence_eq_hashOneSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) :
    inheritedDownPostlaunchHashedOccurrence (rate := rate) rewards C_star C_h
        i alpha k q hAlpha w hq hqQ control0 δ =
      ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
        (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
        δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ
        MeasurableSet.univ i := by
  ext z
  change (z ∈ inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ ∧
      AffineChannelLaw.affineHash (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) w = 1) ↔
    (z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
      δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ
      MeasurableSet.univ i ∧
      AffineChannelLaw.affineHash (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) w = 1)
  rw [inheritedDownPostlaunchOccurrence_eq_sourceEvent]

/-- Every occurrence has its actual current test, at the selected physical
round, as the last member of the first `q` cohort equations. -/
theorem inheritedDownPostlaunchOccurrence_current_take
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) (δ : Lambda p alpha)
    (hO : z ∈ inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ) :
    ∃ (x : LaunchSource (rate := rate) rewards C_star C_h δ.1.2.1.val
        (by omega)) (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
      x.1 = z ∧
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h δ.1.2.1.val (by omega) i x).2
          ⟨δ.1.2.2.val - δ.1.2.1.val, by omega⟩) = some test ∧
      test.time = δ.1.2.2 ∧
      ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
          (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
          (δ.1.2.2.val - δ.1.2.1.val) ++ [test] =
        (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h δ.1.2.1.val (by omega) i x).take q := by
  rcases hO with ⟨_hselector, x, hx, _hboundaryStart, _hcompleted, _hboundary,
    hlength, _hgoodPrefix, test, hcurrent, _hsent⟩
  have htimeVal := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentTest_time
    (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
    ⟨δ.1.2.2.val - δ.1.2.1.val, by omega⟩ test hcurrent
  have htime : test.time = δ.1.2.2 := Fin.ext (by
    calc
      test.time.val = δ.1.2.1.val + (δ.1.2.2.val - δ.1.2.1.val) := htimeVal
      _ = δ.1.2.2.val := by omega)
  have htake := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_current_take
    (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
    (δ.1.2.2.val - δ.1.2.1.val) q (by omega) hq hqQ hlength test hcurrent
  exact ⟨x, test, hx, hcurrent, htime, htake⟩

/-- A hashed occurrence carries the actual good current test and its original
sample, sent word, first-cohort membership, and take identity. -/
theorem inheritedDownPostlaunchHashedOccurrence_current_test
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) (δ : Lambda p alpha)
    (hHit : z ∈ inheritedDownPostlaunchHashedOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ) :
    ∃ (x : LaunchSource (rate := rate) rewards C_star C_h δ.1.2.1.val
        (by omega)) (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
      ReferenceSelectedAffinePairLaw.selector p δ.1.2.2 z =
        (δ.1.1, some ((0, i) : Channel p)) ∧
      x.1 = z ∧
      ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarker
        (rate := rate) rewards C_star C_h alpha k q w δ.1.2.1.val
        (by omega) i x (δ.1.2.2.val - δ.1.2.1.val) ∧
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h δ.1.2.1.val (by omega) i x).2
          ⟨δ.1.2.2.val - δ.1.2.1.val, by omega⟩) = some test ∧
      test.time = δ.1.2.2 ∧
      test.sample = (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) ∧
      test.sent = ReferenceActiveAffinePositiveTest.downSent
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput
          δ.1.2.1.val (δ.1.2.2.val - δ.1.2.1.val) (by omega)
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h δ.1.2.1.val (by omega) x)) ∧
      ReferenceGeneratedDownBatchCalendar.ExecutedTest.good w test ∧
      test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownNewFirstTests
        rate rewards C_star C_h δ.1.2.1.val (by omega) i x ∧
      ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
          (rate := rate) rewards C_star C_h δ.1.2.1.val (by omega) i x
          (δ.1.2.2.val - δ.1.2.1.val) ++ [test] =
        (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h δ.1.2.1.val (by omega) i x).take q := by
  have hsource : z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
      δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i := by
    rw [← inheritedDownPostlaunchHashedOccurrence_eq_hashOneSourceEvent
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ]
    exact hHit
  exact ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent_current_test
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i z hsource

/-- Two unhashed occurrences for the same source input have the same
row, launch time, and current round. -/
theorem inheritedDownPostlaunchOccurrence_unique
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) (δ ε : Lambda p alpha)
    (hδ : z ∈ inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ)
    (hε : z ∈ inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 ε) : δ = ε := by
  rcases δ with ⟨⟨j₁, s₁, r₁⟩, hδIndex⟩
  rcases ε with ⟨⟨j₂, s₂, r₂⟩, hεIndex⟩
  have hselector₁ : ReferenceSelectedAffinePairLaw.selector p r₁ z =
      (j₁, some ((0, i) : Channel p)) := by
    change (ReferenceSelectedAffinePairLaw.selector p r₁ z =
      (j₁, some ((0, i) : Channel p)) ∧ _) at hδ
    exact hδ.1
  have hselector₂ : ReferenceSelectedAffinePairLaw.selector p r₂ z =
      (j₂, some ((0, i) : Channel p)) := by
    change (ReferenceSelectedAffinePairLaw.selector p r₂ z =
      (j₂, some ((0, i) : Channel p)) ∧ _) at hε
    exact hε.1
  have hj : j₁ = j₂ := by
    have hrow₁ := congrArg Prod.fst hselector₁
    have hrow₂ := congrArg Prod.fst hselector₂
    rw [ReferenceSelectedAffinePairLaw.selector_rowIndex] at hrow₁ hrow₂
    exact hrow₁.symm.trans hrow₂
  have hTake₁ := inheritedDownPostlaunchOccurrence_current_take
    (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 z
    ⟨⟨j₁, s₁, r₁⟩, hδIndex⟩ hδ
  have hTake₂ := inheritedDownPostlaunchOccurrence_current_take
    (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 z
    ⟨⟨j₂, s₂, r₂⟩, hεIndex⟩ hε
  rcases hTake₁ with ⟨x₁, t₁, hx₁, _hcurrent₁, htime₁, htake₁⟩
  rcases hTake₂ with ⟨x₂, t₂, hx₂, _hcurrent₂, htime₂, htake₂⟩
  have hsVal : s₁.val = s₂.val := by
    have hElapsed₁ := x₁.property.2
    have hElapsed₂ := x₂.property.2
    rw [hx₁] at hElapsed₁
    rw [hx₂] at hElapsed₂
    exact hElapsed₁.symm.trans hElapsed₂
  have hs : s₁ = s₂ := Fin.ext hsVal
  subst j₂
  subst s₂
  have hx : x₁ = x₂ := by
    apply Subtype.ext
    exact hx₁.trans hx₂.symm
  subst x₂
  have hlists :
      ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
          (rate := rate) rewards C_star C_h s₁.val s₁.isLt i x₁
          (r₁.val - s₁.val) ++ [t₁] =
        ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
          (rate := rate) rewards C_star C_h s₁.val s₁.isLt i x₁
          (r₂.val - s₁.val) ++ [t₂] := htake₁.trans htake₂.symm
  have hlast := congrArg List.getLast? hlists
  have htest : t₁ = t₂ := by
    simp only [List.getLast?_append_cons, List.getLast?_singleton] at hlast
    exact Option.some.inj hlast
  have hr : r₁ = r₂ := by
    calc
      r₁ = t₁.time := htime₁.symm
      _ = t₂.time := congrArg ReferenceGeneratedDownBatchCalendar.ExecutedTest.time htest
      _ = r₂ := htime₂
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hr

/-- The literal occurrence is Borel in the original source law, by its exact
equality with H's measurable physical source event. -/
theorem measurableSet_inheritedDownPostlaunchOccurrence
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) :
    MeasurableSet (inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ) := by
  rw [inheritedDownPostlaunchOccurrence_eq_sourceEvent]
  exact ReferenceGeneratedInheritedDownSourceHalf.measurableSet_inheritedDownSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i

/-- The hashed literal occurrence is Borel in the original source law. -/
theorem measurableSet_inheritedDownPostlaunchHashedOccurrence
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (δ : Lambda p alpha) :
    MeasurableSet (inheritedDownPostlaunchHashedOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ) := by
  rw [inheritedDownPostlaunchHashedOccurrence_eq_hashOneSourceEvent]
  exact ReferenceGeneratedInheritedDownSourceHalf.measurableSet_inheritedDownHashOneSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i

/-- A finite union of the hashed occurrence strata remains Borel. -/
theorem measurableSet_inheritedDownPostlaunchDetector
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (inheritedDownPostlaunchDetector (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0) := by
  classical
  change MeasurableSet (⋃ δ : Lambda p alpha,
    inheritedDownPostlaunchHashedOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ)
  exact MeasurableSet.iUnion (fun δ =>
    measurableSet_inheritedDownPostlaunchHashedOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ)

/-- The finite unhashed occurrence union remains Borel. -/
theorem measurableSet_inheritedDownPostlaunchOccurrenceUnion
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (inheritedDownPostlaunchOccurrenceUnion (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0) := by
  classical
  change MeasurableSet (⋃ δ : Lambda p alpha,
    inheritedDownPostlaunchOccurrence (rate := rate) rewards C_star C_h
      i alpha k q hAlpha w hq hqQ control0 δ)
  exact MeasurableSet.iUnion (fun δ =>
    measurableSet_inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ)

end Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchOccurrence

end
