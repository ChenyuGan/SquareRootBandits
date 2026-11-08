/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownDetectorMass
public import Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrencePredecessor

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# Fixed-birth prelaunch DOWN source recurrence

The localized recurrence combines the original-source detector half-mass
identity with the actual previous-detector inclusion. Its iteration is rooted
at the literal empty-bank birth event, so the geometric bound retains the
birth mass. The unlocalized results specialize the same test cell to the
entire original source space.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-164`,
and `05_binary_transport.tex:20-42` in `sources/zip4/manuscript/`.

These are internal source-measure estimates. They do not assert a mixed
launch tail, a union over births or words, a conditional expectation on a
manuscript history, or closure of a manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
open Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceRecurrence

variable {p : ConstructorDimensions.Parameters}

/-- One positive detector level has at most half the preceding detector mass
inside the same measurable original-past cell. The occurrence-to-previous
inclusion is applied inside `measure_mono`; all birth, word, reward, source,
and past-view parameters remain fixed. -/
theorem prelaunchDownDetector_local_recurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) (hq : 1 ≤ q) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w (q - 1)} := by
  have hMassHalf :=
    ReferenceGeneratedPrelaunchDownDetectorMass.prelaunchDownDetector_source_mass_half
      rate rewards C_star C_h i alpha k q hAlpha w a ha Cell hCell hq
  have hOccurrenceSubset :=
    ReferenceGeneratedPrelaunchDownOccurrencePredecessor.prelaunch_occurrence_exists_subset_previous
      rate rewards C_star C_h i alpha k q hAlpha w hq
  have hIntersectionSubset :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          ∃ r : Fin p.T,
            ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownOccurrence
              rate rewards C_star C_h i alpha k q hAlpha w z r} ⊆
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w (q - 1)} := by
    rintro z ⟨hCellZ, hOccurrence⟩
    exact ⟨hCellZ, hOccurrenceSubset hOccurrence⟩
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w q} =
        (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ∃ r : Fin p.T,
              ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownOccurrence
                rate rewards C_star C_h i alpha k q hAlpha w z r} := hMassHalf
    _ ≤ (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
              rate rewards C_star C_h i alpha k hAlpha w (q - 1)} :=
      mul_le_mul_of_nonneg_left (measure_mono hIntersectionSubset) zero_le

/-- Every localized level is bounded by its actual birth mass times the
geometric factor. At level zero the detector is exactly the literal birth
event; it is not replaced by the whole source space. -/
theorem prelaunchDownDetector_local_geometric_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0} := by
  induction q with
  | zero =>
      simp only [pow_zero, one_mul]
      exact le_rfl
  | succ q ih =>
      have hstep := prelaunchDownDetector_local_recurrence
        rate rewards C_star C_h i alpha k (q + 1) hAlpha w a ha Cell hCell
          (Nat.succ_pos q)
      calc
        BootstrapPrivateRoundStreams.sourceInputLaw p
            {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
              z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
                rate rewards C_star C_h i alpha k hAlpha w (q + 1)} ≤
            (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
              {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
                  rate rewards C_star C_h i alpha k hAlpha w q} := hstep
        _ ≤ (1 : ENNReal) / 2 *
              (((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
                {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                  z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
                    rate rewards C_star C_h i alpha k hAlpha w 0}) :=
          mul_le_mul_of_nonneg_left ih zero_le
        _ = ((1 : ENNReal) / 2) ^ (q + 1) *
              BootstrapPrivateRoundStreams.sourceInputLaw p
                {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
                  z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
                    rate rewards C_star C_h i alpha k hAlpha w 0} := by
          rw [pow_succ]
          ac_rfl

/-- The localized geometric estimate also holds for the real-valued measure,
using finiteness of the actual source probability measure. -/
theorem prelaunchDownDetector_local_measureReal_geometric_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0} := by
  have hENN := prelaunchDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w a ha Cell hCell q
  have hReal := ENNReal.toReal_mono (by finiteness) hENN
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hReal

/-- With a terminal birth index `alpha = T`, every positive detector level is
empty by the indicator's actual calendar bound. -/
theorem prelaunchDownDetector_empty_of_terminal_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hTerminal : alpha = p.T) (hq : 0 < q) :
    ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
      rate rewards C_star C_h i alpha k hAlpha w q = ∅ := by
  cases q with
  | zero => omega
  | succ q =>
      rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector_succ]
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro r hhit
      rcases hhit with ⟨⟨hIndicator, _⟩, _⟩
      rcases hIndicator with ⟨_, _, hClock, _, _⟩
      omega

/-- Levels above the actual quota are empty because the existing predictable
indicator includes its literal `q ≤ quota` guard. -/
theorem prelaunchDownDetector_empty_of_quota_lt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : AffineBatchDecoder.quota p < q) :
    ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
      rate rewards C_star C_h i alpha k hAlpha w q = ∅ := by
  cases q with
  | zero => omega
  | succ q =>
      rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector_succ]
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro r hhit
      rcases hhit with ⟨⟨hIndicator, _⟩, _⟩
      rcases hIndicator with ⟨_, hQuota, _, _, _⟩
      omega

/-- On the original full-source law, every fixed-birth detector level is
bounded by the same geometric factor times the actual birth mass. The cell is
the whole original public-ID/strict-past carrier at `a = 0`. -/
theorem prelaunchDownDetector_source_geometric_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w 0} := by
  let a : Fin p.T := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one p.one_le_T⟩
  have hLocal := prelaunchDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w a (Nat.zero_le _) Set.univ
      MeasurableSet.univ q
  simpa only [Set.mem_univ, true_and] using hLocal

/-- The original-source detector mass is also at most the geometric factor,
since the actual birth event has mass at most one under `sourceInputLaw`. -/
theorem prelaunchDownDetector_source_geometric_bound_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (q : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ENNReal) / 2) ^ q := by
  have hBirth := prelaunchDownDetector_source_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w q
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
        ((1 : ENNReal) / 2) ^ q * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0} := hBirth
    _ ≤ ((1 : ENNReal) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (prob_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0}))
        zero_le
    _ = ((1 : ENNReal) / 2) ^ q := by simp

/-- The unlocalized birth-mass estimate in real measure. -/
theorem prelaunchDownDetector_source_measureReal_geometric_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w 0} := by
  have hENN := prelaunchDownDetector_source_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w q
  have hReal := ENNReal.toReal_mono (by finiteness) hENN
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hReal

/-- The original-source real measure is at most `2⁻q`, using the actual
probability law and its real-measure bound on the birth event. -/
theorem prelaunchDownDetector_source_measureReal_geometric_bound_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (q : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
      ((1 : ℝ) / 2) ^ q := by
  have hBirth := prelaunchDownDetector_source_measureReal_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w q
  calc
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
          rate rewards C_star C_h i alpha k hAlpha w q} ≤
        ((1 : ℝ) / 2) ^ q * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0} := hBirth
    _ ≤ ((1 : ℝ) / 2) ^ q * 1 :=
      mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
          (s := {z | z ∈ ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector
            rate rewards C_star C_h i alpha k hAlpha w 0}))
        (pow_nonneg (div_nonneg zero_le_one zero_le_two) q)
    _ = ((1 : ℝ) / 2) ^ q := by simp

end Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceRecurrence

end
