/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownFreshSourceTail

import Lean.Elab.Tactic.Omega

/-!
# Original-source fresh-reset DOWN all-launch tail

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-153`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The event is the finite union of the actual generated-source reset events at
all births strictly after the computed launch. Distinct birth strata are
disjoint because the same original source has one computed completed elapsed
index. Its zero event remains the union of actual resets, and its recurrence
does not pay a launch-time multiplicity factor. This is an internal tail
consumer; it does not provide full decoder-event coverage or a conditional
batch-history theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ReferenceGeneratedDownFreshSourceTail

namespace Bandits.Support.ReferenceGeneratedDownFreshAllLaunchTail

abbrev Parameters := Bandits.Support.ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ReferenceGeneratedDownFreshSourceTail.RateInput
abbrev SourceInput := Bandits.Support.BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  Bandits.Support.ReferenceGeneratedDownFreshSourceTail.Candidate p

variable {p : Parameters} {rate : RateInput p}

/-- The actual fresh-reset event on the launch stratum indexed by `s : Fin alpha`.
The in-horizon proof is derived from `s < alpha < T`. -/
def generatedDownFreshAllLaunchSourceStratum
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) (s : Fin alpha) : Set (SourceInput p) :=
  Bandits.Support.ReferenceGeneratedDownFreshSourceTail.generatedDownFreshSourceEvent
    (rate := rate) rewards C_star C_h s.val (Nat.lt_trans s.isLt halphaT) i alpha s.isLt
    halphaT candidate q

/-- Union of the original-source fresh-reset events over all actual launch
strata `s < alpha`. The `q = 0` fiber is the union of the real reset events. -/
def generatedDownFreshAllLaunchSourceEvent
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) : Set (SourceInput p) :=
  {source | ∃ s : ℕ, ∃ hs : s < p.T, ∃ hsa : s < alpha,
    source ∈ Bandits.Support.ReferenceGeneratedDownFreshSourceTail.generatedDownFreshSourceEvent
      (rate := rate) rewards C_star C_h s hs i alpha hsa halphaT candidate q}

/-- The literal existential event is exactly the finite union indexed by `Fin alpha`.
The bound `s < T` for each stratum is derived from `s < alpha < T`. -/
theorem generatedDownFreshAllLaunchSourceEvent_eq_iUnion_fin
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) :
    generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha halphaT
        candidate q =
      ⋃ s : Fin alpha,
        generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i alpha
          halphaT candidate q s := by
  ext source
  simp only [generatedDownFreshAllLaunchSourceEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
    generatedDownFreshAllLaunchSourceStratum]
  constructor
  · rintro ⟨s, hs, hsa, hmem⟩
    exact ⟨⟨s, hsa⟩, hmem⟩
  · rintro ⟨s, hmem⟩
    exact ⟨s.val, Nat.lt_trans s.isLt halphaT, s.isLt, hmem⟩

/-- With no postlaunch birth index, the all-launch event is empty. -/
theorem generatedDownFreshAllLaunchSourceEvent_eq_empty_zero
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (halphaT : 0 < p.T)
    (candidate : Candidate p) (q : ℕ) :
    generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i 0 halphaT
        candidate q = ∅ := by
  ext source
  simp [generatedDownFreshAllLaunchSourceEvent]

/-- Distinct all-launch strata are disjoint because D's `LaunchSource` subtype
records the same original source's computed `elapsed(output.completed)`. -/
theorem generatedDownFreshAllLaunchSourceStratum_pairwiseDisjoint
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun s : Fin alpha => generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards
        C_star C_h i alpha halphaT candidate q s)) := by
  classical
  intro s t hst
  change Disjoint
    (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i alpha halphaT
      candidate q s)
    (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i alpha halphaT
      candidate q t)
  rw [Set.disjoint_left]
  intro source hsourceS hsourceT
  rcases hsourceS with ⟨xs, hxs, _hdownS⟩
  rcases hsourceT with ⟨xt, hxt, _hdownT⟩
  have htimeS := xs.property.2
  have htimeT := xt.property.2
  rw [hxs] at htimeS
  rw [hxt] at htimeT
  have hval : s.val = t.val := htimeS.symm.trans htimeT
  exact hst (Fin.ext hval)

/-- Measurability of every all-launch event up to the actual decoder quota. -/
theorem measurableSet_generatedDownFreshAllLaunchSourceEvent
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) (hqQ : q ≤ Bandits.Support.AffineBatchDecoder.quota p)
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p) :
    MeasurableSet (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i
      alpha halphaT candidate q) := by
  rw [generatedDownFreshAllLaunchSourceEvent_eq_iUnion_fin (rate := rate) rewards C_star C_h i
    alpha halphaT candidate q]
  apply MeasurableSet.iUnion
  intro s
  exact measurableSet_generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s.val
    (Nat.lt_trans s.isLt halphaT) i alpha s.isLt halphaT candidate q hqQ control0

/-- The all-launch source event satisfies the half recurrence. Both finite-union
measure equalities use the actual pairwise-disjoint launch strata. -/
theorem generatedDownFreshAllLaunchSourceEvent_recurrence
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ Bandits.Support.AffineBatchDecoder.quota p)
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p) :
    Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
          halphaT candidate q) ≤
      ((1 : ℝ≥0∞) / 2) *
        Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
            halphaT candidate (q - 1)) := by
  classical
  let μ := Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
  have hqPrevQ : q - 1 ≤ Bandits.Support.AffineBatchDecoder.quota p := by omega
  have hEqQ := generatedDownFreshAllLaunchSourceEvent_eq_iUnion_fin (rate := rate) rewards
    C_star C_h i alpha halphaT candidate q
  have hEqPrev := generatedDownFreshAllLaunchSourceEvent_eq_iUnion_fin (rate := rate) rewards
    C_star C_h i alpha halphaT candidate (q - 1)
  have hdisjQ := generatedDownFreshAllLaunchSourceStratum_pairwiseDisjoint (rate := rate) rewards
    C_star C_h i alpha halphaT candidate q
  have hdisjPrev := generatedDownFreshAllLaunchSourceStratum_pairwiseDisjoint (rate := rate)
    rewards C_star C_h i alpha halphaT candidate (q - 1)
  have hmeasQ : ∀ s : Fin alpha,
      MeasurableSet (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i
        alpha halphaT candidate q s) := by
    intro s
    exact measurableSet_generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s.val
      (Nat.lt_trans s.isLt halphaT) i alpha s.isLt halphaT candidate q hqQ control0
  have hmeasPrev : ∀ s : Fin alpha,
      MeasurableSet (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i
        alpha halphaT candidate (q - 1) s) := by
    intro s
    exact measurableSet_generatedDownFreshSourceEvent (rate := rate) rewards C_star C_h s.val
      (Nat.lt_trans s.isLt halphaT) i alpha s.isLt halphaT candidate (q - 1) hqPrevQ control0
  calc
    μ (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha halphaT
        candidate q) =
        ∑ s : Fin alpha, μ (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star
          C_h i alpha halphaT candidate q s) := by
      rw [hEqQ, measure_iUnion hdisjQ hmeasQ, tsum_fintype]
    _ ≤ ∑ s : Fin alpha, ((1 : ℝ≥0∞) / 2) *
          μ (generatedDownFreshAllLaunchSourceStratum (rate := rate) rewards C_star C_h i alpha
            halphaT candidate (q - 1) s) := by
      apply Finset.sum_le_sum
      intro s _hs
      exact generatedDownFreshSourceEvent_recurrence (rate := rate) rewards C_star C_h s.val
        (Nat.lt_trans s.isLt halphaT) i alpha s.isLt halphaT candidate q hq hqQ control0
    _ = ((1 : ℝ≥0∞) / 2) *
          μ (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
            halphaT candidate (q - 1)) := by
      rw [← Finset.mul_sum, hEqPrev, measure_iUnion hdisjPrev hmeasPrev, tsum_fintype]

/-- The all-launch event has the geometric tail, with its actual reset union as
the base event. The induction includes the endpoint `q = quota`. -/
theorem generatedDownFreshAllLaunchSourceEvent_measure_le_geometric
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ)
    (hqQ : q ≤ Bandits.Support.AffineBatchDecoder.quota p)
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p) :
    Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
          halphaT candidate q) ≤
      ((1 : ℝ≥0∞) / 2) ^ q *
        Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
            halphaT candidate 0) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hprev : q ≤ Bandits.Support.AffineBatchDecoder.quota p := by omega
      have hrec := generatedDownFreshAllLaunchSourceEvent_recurrence (rate := rate) rewards C_star
        C_h i alpha halphaT candidate (q + 1) (by omega) hqQ control0
      have hbound := ih hprev
      calc
        _ ≤ ((1 : ℝ≥0∞) / 2) *
              Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
                (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i
                  alpha halphaT candidate q) := by simpa using hrec
        _ ≤ ((1 : ℝ≥0∞) / 2) *
              (((1 : ℝ≥0∞) / 2) ^ q *
                Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
                  (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i
                    alpha halphaT candidate 0)) := by gcongr
        _ = ((1 : ℝ≥0∞) / 2) ^ (q + 1) *
              Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
                (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i
                  alpha halphaT candidate 0) := by
          rw [pow_succ]
          ac_rfl

/-- Unconditional ENNReal tail bound for the actual all-launch reset union. -/
theorem generatedDownFreshAllLaunchSourceEvent_measure_le_geometric_unconditional
    (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha : ℕ) (halphaT : alpha < p.T)
    (candidate : Candidate p) (q : ℕ)
    (hqQ : q ≤ Bandits.Support.AffineBatchDecoder.quota p)
    (control0 : Bandits.Support.ContinuousLearningRows.TimeControl p) :
    Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha
          halphaT candidate q) ≤ ((1 : ℝ≥0∞) / 2) ^ q := by
  let μ := Bandits.Support.BootstrapPrivateRoundStreams.sourceInputLaw p
  have hreset : μ (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i
      alpha halphaT candidate 0) ≤ 1 := by
    calc
      μ (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha halphaT
          candidate 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    μ (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha halphaT
        candidate q) ≤ ((1 : ℝ≥0∞) / 2) ^ q * μ
          (generatedDownFreshAllLaunchSourceEvent (rate := rate) rewards C_star C_h i alpha halphaT
            candidate 0) :=
      generatedDownFreshAllLaunchSourceEvent_measure_le_geometric (rate := rate) rewards C_star C_h i
        alpha halphaT candidate q hqQ control0
    _ ≤ ((1 : ℝ≥0∞) / 2) ^ q := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hreset
          (by positivity : (0 : ℝ≥0∞) ≤ ((1 : ℝ≥0∞) / 2) ^ q)

end Bandits.Support.ReferenceGeneratedDownFreshAllLaunchTail

end
