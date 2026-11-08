/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedMixedDownPredecessor

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# Fixed-birth mixed DOWN source tail

The literal mixed detector combines the prelaunch and inherited postlaunch
DOWN events for the same birth, word, rewards, and original source. Its
positive-level half-mass identity follows by adding the two phase identities
over their actual disjoint events. The resulting recurrence iterates from the
literal birth event, retaining its mass on the whole original source carrier.

These are internal fixed-birth source-measure estimates. They are not a
batch-start conditional law, a union over births or words, an all-DOWN failure
bound, or closure of a manuscript theorem.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-155`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceGeneratedMixedDownAtBirthTail

variable {p : ConstructorDimensions.Parameters}

variable
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (i : Fin (p.m - 1))
  (alpha k : ℕ)
  (hAlpha : alpha ≤ p.T)
  (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
  (control0 : ContinuousLearningRows.TimeControl p)

variable
  (a : Fin p.T)
  (ha : a.val ≤ alpha)
  (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
  (hCell : MeasurableSet Cell)

include a ha Cell hCell in
/-- Intersecting the actual mixed detector with a measurable strict-past
cell preserves measurability on the original source space. -/
theorem measurableSet_mixedDownDetector_local (q : ℕ) :
    MeasurableSet
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} := by
  have _ha : a.val ≤ alpha := ha
  have hCellSource : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell} :=
    hCell.preimage (ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView a)
  exact hCellSource.inter
    (ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha k hAlpha w control0 q)

include a ha Cell hCell in
/-- Intersecting the literal mixed occurrence union with a measurable
strict-past cell preserves measurability on the original source space. -/
theorem measurableSet_mixedDownOccurrence_local
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    MeasurableSet
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
          rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
  have _ha : a.val ≤ alpha := ha
  have hCellSource : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell} :=
    hCell.preimage (ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView a)
  exact hCellSource.inter
    (ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownOccurrenceUnion
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0)

include a ha Cell hCell in
/-- The positive mixed detector has exactly half the mass of the two actual
unhashed occurrence unions, localized to the same original strict-past cell.
The prelaunch and inherited postlaunch pieces are added using the genuine
unhashed and hashed cross-phase disjointness results. -/
theorem mixedDownDetector_source_mass_half
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} =
    (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
          rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
  classical
  let B : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell}
  let preDetector := ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
    rate rewards C_star C_h i alpha k hAlpha w q
  let postDetector := ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
    (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
  let preOccurrence : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {z | ∃ r : Fin p.T,
      ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownOccurrence
        rate rewards C_star C_h i alpha k q hAlpha w z r}
  let postOccurrence :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0

  have hB : MeasurableSet B := by
    exact hCell.preimage
      (ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView a)
  have hPreDetector : MeasurableSet preDetector :=
    ReferenceGeneratedPrelaunchDownDetectorMass.measurableSet_prelaunchDownDetector
      rate rewards C_star C_h i alpha k hAlpha w q
  have hPostDetector : MeasurableSet postDetector :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.measurableSet_inheritedDownPostlaunchDetector
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
  have hPreOccurrence : MeasurableSet preOccurrence :=
    ReferenceGeneratedPrelaunchDownDetectorMass.measurableSet_prelaunchDownOccurrenceUnion
      rate rewards C_star C_h i alpha k q hAlpha w
  have hPostOccurrence : MeasurableSet postOccurrence :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.measurableSet_inheritedDownPostlaunchOccurrenceUnion
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0

  have hPreDetectorCell : MeasurableSet (B ∩ preDetector) := hB.inter hPreDetector
  have hPostDetectorCell : MeasurableSet (B ∩ postDetector) := hB.inter hPostDetector
  have hPreOccurrenceCell : MeasurableSet (B ∩ preOccurrence) := hB.inter hPreOccurrence
  have hPostOccurrenceCell : MeasurableSet (B ∩ postOccurrence) := hB.inter hPostOccurrence
  have hDetectorCellsMeasurable :
      MeasurableSet (B ∩ preDetector) ∧ MeasurableSet (B ∩ postDetector) :=
    ⟨hPreDetectorCell, hPostDetectorCell⟩
  have hOccurrenceCellsMeasurable :
      MeasurableSet (B ∩ preOccurrence) ∧ MeasurableSet (B ∩ postOccurrence) :=
    ⟨hPreOccurrenceCell, hPostOccurrenceCell⟩

  have hPreHalf :
      BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ preDetector) =
        (1 : ENNReal) / 2 *
          BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ preOccurrence) := by
    simpa only [Set.inter_def, Set.mem_ofPred_eq, B, preDetector, preOccurrence] using
      (ReferenceGeneratedPrelaunchDownDetectorMass.prelaunchDownDetector_source_mass_half
        rate rewards C_star C_h i alpha k q hAlpha w a ha Cell hCell hq)
  have hPostHalf :
      BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ postDetector) =
        (1 : ENNReal) / 2 *
          BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ postOccurrence) := by
    simpa only [Set.inter_def, Set.mem_ofPred_eq, B, postDetector, postOccurrence,
      ReferenceGeneratedInheritedDownPostlaunchDetectorMass.inheritedDownPostlaunchPastCell] using
      (ReferenceGeneratedInheritedDownPostlaunchDetectorMass.inheritedDownPostlaunchDetector_source_mass_half
        rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
        a ha Cell hCell)

  have hDetectorDisjoint : Disjoint (B ∩ preDetector) (B ∩ postDetector) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (Set.disjoint_left.mp
      (ReferenceGeneratedMixedDownPredecessor.prelaunch_postlaunch_detector_disjoint
        rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0)) hz.2 hz'.2
  have hOccurrenceDisjoint : Disjoint (B ∩ preOccurrence) (B ∩ postOccurrence) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (Set.disjoint_left.mp
      (ReferenceGeneratedMixedDownPredecessor.prelaunch_postlaunch_occurrence_disjoint
        rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0)) hz.2 hz'.2

  have hDetectorUnion :
      {z | z ∈ B ∧ z ∈
        ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} =
        (B ∩ preDetector) ∪ (B ∩ postDetector) := by
    rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hz, hpre | hpost⟩
      · exact Or.inl ⟨hz, hpre⟩
      · exact Or.inr ⟨hz, hpost⟩
    · rintro (⟨hz, hpre⟩ | ⟨hz, hpost⟩)
      · exact ⟨hz, Or.inl hpre⟩
      · exact ⟨hz, Or.inr hpost⟩
  have hOccurrenceUnion :
      {z | z ∈ B ∧ z ∈
        ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
          rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
        (B ∩ preOccurrence) ∪ (B ∩ postOccurrence) := by
    change B ∩ (preOccurrence ∪ postOccurrence) =
      (B ∩ preOccurrence) ∪ (B ∩ postOccurrence)
    exact Set.inter_union_distrib_left B preOccurrence postOccurrence

  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha k hAlpha w control0 q} =
        BootstrapPrivateRoundStreams.sourceInputLaw p
          ((B ∩ preDetector) ∪ (B ∩ postDetector)) := by rw [hDetectorUnion]
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ preDetector) +
          BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ postDetector) :=
      measure_union hDetectorDisjoint hDetectorCellsMeasurable.2
    _ = (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
            (B ∩ preOccurrence) +
          (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
            (B ∩ postOccurrence) := by rw [hPreHalf, hPostHalf]
    _ = (1 : ENNReal) / 2 *
          (BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ preOccurrence) +
            BootstrapPrivateRoundStreams.sourceInputLaw p (B ∩ postOccurrence)) := by
      rw [← mul_add]
    _ = (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          ((B ∩ preOccurrence) ∪ (B ∩ postOccurrence)) := by
      rw [← measure_union hOccurrenceDisjoint hOccurrenceCellsMeasurable.2]
    _ = (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈
            ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
              rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
      rw [← hOccurrenceUnion]
    _ = (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
              rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
      rfl

include a ha Cell hCell in
/-- The full mixed recurrence is applied to the occurrence-to-previous
inclusion, inside `measure_mono`; it never iterates either phase alone. -/
theorem mixedDownDetector_local_recurrence
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
    (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1)} := by
  have hMassHalf := mixedDownDetector_source_mass_half
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell q hq hqQ
  have hOccurrenceSubset :=
    ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion_subset_previous
      rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
  have hIntersectionSubset :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
            rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} ⊆
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1)} := by
    rintro z ⟨hCellZ, hOccurrence⟩
    exact ⟨hCellZ, hOccurrenceSubset hOccurrence⟩
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha k hAlpha w control0 q} =
        (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownOccurrenceUnion
              rate rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := hMassHalf
    _ ≤ (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
              rate rewards C_star C_h i alpha k hAlpha w control0 (q - 1)} :=
      mul_le_mul_of_nonneg_left (measure_mono hIntersectionSubset) zero_le

include a ha Cell hCell in
/-- Every mixed detector level is bounded by the same geometric factor times
the actual same-birth mass inside the original past cell. Level zero is
rewritten to the literal `birthAt` event, including zero-mass cells. -/
theorem mixedDownDetector_local_geometric_bound
    (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
    ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k} := by
  induction q with
  | zero =>
      rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_zero,
        pow_zero, one_mul]
      exact le_rfl
  | succ q ih =>
      by_cases hquota : q + 1 ≤ AffineBatchDecoder.quota p
      · have hstep := mixedDownDetector_local_recurrence
          rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell
          (q + 1) (Nat.succ_pos q) hquota
        calc
          BootstrapPrivateRoundStreams.sourceInputLaw p
              {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
                  rate rewards C_star C_h i alpha k hAlpha w control0 (q + 1)} ≤
              (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
                {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                  z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
                    rate rewards C_star C_h i alpha k hAlpha w control0 q} := hstep
          _ ≤ (1 : ENNReal) / 2 *
                (((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
                  {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                    ReferenceGeneratedPrelaunchDownPrefix.birthAt
                      rate rewards C_star C_h z i alpha hAlpha k}) :=
            mul_le_mul_of_nonneg_left ih zero_le
          _ = ((1 : ENNReal) / 2) ^ (q + 1) *
                BootstrapPrivateRoundStreams.sourceInputLaw p
                  {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                    ReferenceGeneratedPrelaunchDownPrefix.birthAt
                      rate rewards C_star C_h z i alpha hAlpha k} := by
            rw [pow_succ]
            ac_rfl
      · have hEmpty :
            ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
              rate rewards C_star C_h i alpha k hAlpha w control0 (q + 1) = ∅ :=
          ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_eq_empty_of_quota_lt
            rate rewards C_star C_h i alpha k (q + 1) hAlpha w control0 (by omega)
        rw [hEmpty]
        simp only [Set.mem_empty_iff_false, and_false, Set.ofPred_false, measure_empty]
        exact zero_le

include a ha Cell hCell in
/-- The localized geometric estimate also holds for real measure. The
original source probability is finite, so `toReal` preserves the bound. -/
theorem mixedDownDetector_local_measureReal_geometric_bound
    (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
    ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k} := by
  have hENN := mixedDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell q
  have hReal := ENNReal.toReal_mono (by finiteness) hENN
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hReal

include a ha Cell hCell in
/-- A localized mixed tail is at most the geometric factor, since the actual
birth cell is an event under the original probability measure. -/
theorem mixedDownDetector_local_geometric_bound_le_one
    (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
    ((1 : ENNReal) / 2) ^ q := by
  have hBirth := mixedDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell q
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
        ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ReferenceGeneratedPrelaunchDownPrefix.birthAt
              rate rewards C_star C_h z i alpha hAlpha k} := hBirth
    _ ≤ ((1 : ENNReal) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (prob_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ReferenceGeneratedPrelaunchDownPrefix.birthAt
              rate rewards C_star C_h z i alpha hAlpha k})) zero_le
    _ = ((1 : ENNReal) / 2) ^ q := by simp

include a ha Cell hCell in
/-- The localized real-measure tail is at most the geometric factor. -/
theorem mixedDownDetector_local_measureReal_geometric_bound_le_one
    (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
    ((1 : ℝ) / 2) ^ q := by
  have hBirth := mixedDownDetector_local_measureReal_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell q
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
        ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ReferenceGeneratedPrelaunchDownPrefix.birthAt
              rate rewards C_star C_h z i alpha hAlpha k} := hBirth
    _ ≤ ((1 : ℝ) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ReferenceGeneratedPrelaunchDownPrefix.birthAt
              rate rewards C_star C_h z i alpha hAlpha k}))
        (pow_nonneg (div_nonneg zero_le_one zero_le_two) q)
    _ = ((1 : ℝ) / 2) ^ q := by simp

include a ha Cell hCell in
/-- In particular, the fixed-cell estimate at the decoder quota retains the
actual birth mass inside the cell. -/
theorem mixedDownDetector_local_quota_geometric_bound :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0
            (AffineBatchDecoder.quota p)} ≤
    ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p *
      BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k} := by
  exact mixedDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell
      (AffineBatchDecoder.quota p)

include a ha Cell hCell in
/-- The localized quota event is bounded by `2⁻Q`, including zero-mass
birth cells, with `Q` equal to the actual decoder quota. -/
theorem mixedDownDetector_local_quota_tail_le_one :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0
            (AffineBatchDecoder.quota p)} ≤
    ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p := by
  exact mixedDownDetector_local_geometric_bound_le_one
    rate rewards C_star C_h i alpha k hAlpha w control0 a ha Cell hCell
      (AffineBatchDecoder.quota p)

/-- The full-source estimate is the local result at the genuine strict-past
index `a = 0`, whose `Fin p.T` proof uses `p.one_le_T`. -/
theorem mixedDownDetector_source_geometric_bound
    (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
      ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k} := by
  let a0 : Fin p.T :=
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one p.one_le_T⟩
  have hLocal := mixedDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a0 (Nat.zero_le alpha)
      Set.univ MeasurableSet.univ q
  simpa only [Set.mem_univ, true_and] using hLocal

/-- The full-source real-measure estimate retains the actual birth mass. -/
theorem mixedDownDetector_source_measureReal_geometric_bound
    (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
      ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k} := by
  let a0 : Fin p.T :=
    ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one p.one_le_T⟩
  have hLocal := mixedDownDetector_local_measureReal_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a0 (Nat.zero_le alpha)
      Set.univ MeasurableSet.univ q
  simpa only [Set.mem_univ, true_and] using hLocal

/-- The unlocalized mixed DOWN probability is at most `2⁻q`, because the
actual same-birth event has source probability at most one. -/
theorem mixedDownDetector_source_geometric_bound_le_one
    (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
      ((1 : ENNReal) / 2) ^ q := by
  have hBirth := mixedDownDetector_source_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 q
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
        ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k} := hBirth
    _ ≤ ((1 : ENNReal) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (prob_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k})) zero_le
    _ = ((1 : ENNReal) / 2) ^ q := by simp

/-- The unlocalized real-measure mixed DOWN probability is at most `2⁻q`. -/
theorem mixedDownDetector_source_measureReal_geometric_bound_le_one
    (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
      ((1 : ℝ) / 2) ^ q := by
  have hBirth := mixedDownDetector_source_measureReal_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 q
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0 q} ≤
        ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k} := hBirth
    _ ≤ ((1 : ℝ) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k}))
        (pow_nonneg (div_nonneg zero_le_one zero_le_two) q)
    _ = ((1 : ℝ) / 2) ^ q := by simp

/-- The global all-Q tail at the actual decoder quota, with the real-valued
source measure and no normalization by the probability of a birth. -/
theorem mixedDownDetector_source_quota_tail_le_one :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0
            (AffineBatchDecoder.quota p)} ≤
      ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p := by
  exact mixedDownDetector_source_geometric_bound_le_one
    rate rewards C_star C_h i alpha k hAlpha w control0
      (AffineBatchDecoder.quota p)

theorem mixedDownDetector_source_measureReal_quota_tail_le_one :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha k hAlpha w control0
            (AffineBatchDecoder.quota p)} ≤
      ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p := by
  exact mixedDownDetector_source_measureReal_geometric_bound_le_one
    rate rewards C_star C_h i alpha k hAlpha w control0
      (AffineBatchDecoder.quota p)

end Bandits.Support.ReferenceGeneratedMixedDownAtBirthTail

end
