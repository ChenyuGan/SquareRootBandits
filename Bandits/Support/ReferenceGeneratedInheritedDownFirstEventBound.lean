/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownDetectorContainment
public import Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion
public import Mathlib.MeasureTheory.Measure.Real

/-!
# First inherited wrong DOWN completion inside the joint cohort union

This module defines the restricted source event for an actual nonterminal
launch whose first suffix completion contains an ordinary wrong unique DOWN
acceptance diagnostic. The inherited detector theorem places that same saved
diagnostic in the mixed DOWN detector, and the joint cohort union bounds its
source-input measure.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-155`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The event does not cover later completions, absent or terminal launches,
prelaunch false acceptance, or fixed-awaited ambiguity. It is a restricted
physical projection, not the full source false-event predicate or a claim
about complete decoding probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceGeneratedInheritedDownFirstEventBound

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The actual first completed suffix batch at a nonterminal launch has a
saved DOWN diagnostic accepted as a unique wrong ordinary word. -/
def inheritedFirstWrongEvent :
    Set (ReferenceGeneratedDownCohortFiniteUnion.SourceInput p) :=
  {z | ∃ (s : ℕ) (hs : s < p.T)
      (x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s hs)
      (i : Fin (p.m - 1)) (n : Fin (p.T - s)),
        x.val = z ∧
        (ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 n) ∧
          ∀ l (hl : l < n.val),
            ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
              ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                rate rewards C_star C_h s hs i x).2
                ⟨l, lt_trans hl n.isLt⟩)) ∧
        ∃ cut,
          ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut}

/-- Every event witness is contained in the existing joint DOWN cohort union
at the decoder quota. The launch, first completion, saved cut, raw word,
boundary, completed-bank ordinal, and source are those of the same witness. -/
theorem inheritedFirstWrongEvent_subset_downCohortUnion
    (control0 : ContinuousLearningRows.TimeControl p) :
    inheritedFirstWrongEvent rate rewards C_star C_h ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  intro z hz
  rcases hz with
    ⟨s, hs, x, i, n, hx, ⟨⟨hcomplete, hnoEarlier⟩,
      ⟨savedCut, hsavedCut, hsavedWrong⟩⟩⟩
  subst z
  have hdet :=
    ReferenceGeneratedInheritedDownDetectorContainment.generated_inherited_wrong_completion_detector
      rate rewards C_star C_h s hs x i n control0 ⟨hcomplete, hnoEarlier⟩
      ⟨savedCut, hsavedCut, hsavedWrong⟩
  dsimp only at hdet
  rcases hdet with
    ⟨cut, word, alpha, hAlpha, hcut, _, _, hAlphaS, hbirth, _, _, _, hmixed⟩
  have hcutEq : cut = savedCut :=
    Option.some.inj (hcut.symm.trans hsavedCut)
  let B0 :=
    (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch
  change ReferenceGeneratedPrelaunchDownPrefix.birthAt
    rate rewards C_star C_h x.val i alpha hAlpha B0.completed.length at hbirth
  have hOrdinal :=
    ReferenceGeneratedDownCohortFiniteUnion.birthAt_ordinal_le
      rate rewards C_star C_h i alpha B0.completed.length hAlpha x.val hbirth
  have hAlphaLt : alpha < p.T := Nat.lt_of_le_of_lt hAlphaS hs
  let alphaFin : Fin p.T := ⟨alpha, hAlphaLt⟩
  let ordinalFin : Fin (alpha + 1) :=
    ⟨B0.completed.length, Nat.lt_succ_of_le hOrdinal⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine Set.mem_iUnion.mpr ⟨alphaFin, ?_⟩
  refine Set.mem_iUnion.mpr ⟨word, ?_⟩
  apply Set.mem_union_left
  refine Set.mem_iUnion.mpr ⟨ordinalFin, ?_⟩
  exact hmixed

/-- The original source-input law bound follows by monotonicity from the
existing geometric estimate for the joint cohort union at the decoder quota.
No measurability premise for the restricted physical event is used. -/
theorem inheritedFirstWrongEvent_measure_le_geometric
    (control0 : ContinuousLearningRows.TimeControl p) :
    ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p
        (inheritedFirstWrongEvent rate rewards C_star C_h) ≤
      (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) *
        ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p := by
  calc
    ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p
        (inheritedFirstWrongEvent rate rewards C_star C_h) ≤
      ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
      measure_mono (inheritedFirstWrongEvent_subset_downCohortUnion
        rate rewards C_star C_h control0)
    _ ≤ (((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) *
        ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p :=
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measure_le_geometric
        rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) le_rfl

/-- The real measure of the restricted actual first-inherited event is at
most the existing joint quota bound. -/
theorem inheritedFirstWrongEvent_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p).real
        (inheritedFirstWrongEvent rate rewards C_star C_h) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  calc
    (ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p).real
        (inheritedFirstWrongEvent rate rewards C_star C_h) ≤
      (ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p).real
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) :=
      measureReal_mono (inheritedFirstWrongEvent_subset_downCohortUnion
        rate rewards C_star C_h control0) (by finiteness)
    _ ≤ 1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) :=
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent_measureReal_quota_bound
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceGeneratedInheritedDownFirstEventBound

end
