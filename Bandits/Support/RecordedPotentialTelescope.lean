/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedPotentialStep

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cumulative potential comparison for the recorded queue run

This file telescopes the actual product-set normalizer along the existing
zero-initialized `RecordedQueueRun`. The sums range over every supplied
calendar round, including disabled and post-overflow inputs.

## Main results

* `initial_scoreWeight_eq_one` and `initial_normalizer_eq_choose` identify the
  exact initial potential from the actual powerset-card support.
* `servedEstimate_cumulative_comparison` proves the finite-run cumulative
  served-estimate comparison with one initial combinatorial cost.

## Source

`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174` defines the score
update and weights; `:182-215` retains the first overflow update; and
`:393-427` gives the cumulative served-estimate comparison.

These are fully proved internal results. The round inputs are explicit
deterministic traces; this module does not assert a conditional recording law,
queue-drift estimate, reward comparison, or learning-lemma closure.
-/

public section

open scoped BigOperators

namespace Bandits.Support.RecordedPotentialTelescope

open RecordedQueueRun ProductSetLaw RecordedPotentialStep

variable {K m : ℕ}

/-- The existing zero run starts with unit score weight on every arm. -/
theorem initial_scoreWeight_eq_one (p : Parameters) (i : Fin K) :
    RecordedQueueRun.scoreWeight p (RecordedQueueRun.initialState K) i = 1 := by
  simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
    ScoreWeights.scoreWeight]

/-- The initial normalizer is the cardinality of the actual `m`-set support. -/
theorem initial_normalizer_eq_choose (p : Parameters) :
    ProductSetLaw.normalizer m
      (RecordedQueueRun.scoreWeight p (RecordedQueueRun.initialState K)) =
      (Nat.choose K m : ℝ) := by
  classical
  rw [ProductSetLaw.normalizer_eq_support_sum]
  calc
    (∑ S ∈ ProductSetLaw.support K m,
        ProductSetLaw.setWeight
          (RecordedQueueRun.scoreWeight p (RecordedQueueRun.initialState K)) S) =
        ∑ S ∈ ProductSetLaw.support K m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      unfold ProductSetLaw.setWeight
      apply Finset.prod_eq_one
      intro i hi
      exact initial_scoreWeight_eq_one p i
    _ = ((ProductSetLaw.support K m).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (Nat.choose K m : ℝ) := by
      simp only [ProductSetLaw.support, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]

/-- Positivity of the source's combinatorial initial normalizer. -/
theorem choose_pos_real (hmK : m < K) : 0 < (Nat.choose K m : ℝ) := by
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt hmK)

private noncomputable def prefixNormalizer (p : Parameters) (rounds : List (RoundInput K))
    (m : ℕ) (n : ℕ) : ℝ :=
  ProductSetLaw.normalizer m
    (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p (rounds.take n)))

private noncomputable def servedSetTerm (p : Parameters) (rounds : List (RoundInput K))
    (S : ProductSet K m) (t : ℕ) (ht : t < rounds.length) : ℝ :=
  ∑ i ∈ S.1,
    RecordedPotentialStep.servedEstimate p
      (RecordedQueueRun.run p (rounds.take t)) (rounds[t]'ht) i

private noncomputable def servedSetTotal (p : Parameters) (rounds : List (RoundInput K))
    (S : ProductSet K m) (n : ℕ) (hn : n ≤ rounds.length) : ℝ :=
  ∑ t : Fin n,
    servedSetTerm p rounds S t.val (Nat.lt_of_lt_of_le t.isLt hn)

private theorem prefixNormalizer_pos (p : Parameters) (rounds : List (RoundInput K))
    (hm : 2 ≤ m) (hmK : m < K) (n : ℕ) :
    0 < prefixNormalizer p rounds m n := by
  unfold prefixNormalizer
  apply ProductSetLaw.normalizer_pos
  · omega
  · exact hmK
  · intro i
    exact RecordedPotentialStep.scoreWeight_pos p _ i

private theorem prefix_setWeight_eq_exp_servedSetTotal (p : Parameters)
    (rounds : List (RoundInput K)) (S : ProductSet K m) (n : ℕ)
    (hn : n ≤ rounds.length) :
    ProductSetLaw.setWeight
        (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p (rounds.take n))) S.1 =
      Real.exp (RecordedPotentialStep.potentialLambda p *
        servedSetTotal p rounds S n hn) := by
  induction n with
  | zero =>
      simp [servedSetTotal, ProductSetLaw.setWeight,
        RecordedQueueRun.scoreWeight, RecordedQueueRun.run,
        RecordedQueueRun.execute, RecordedQueueRun.initialState,
        ScoreWeights.scoreWeight]
  | succ n ih =>
      have hlt : n < rounds.length := by omega
      have hsum :
        servedSetTotal p rounds S (n + 1) hn =
            servedSetTotal p rounds S n (by omega) + servedSetTerm p rounds S n hlt := by
        dsimp [servedSetTotal]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
      rw [RecordedPotentialStep.run_take_succ_eq_step p rounds n hlt,
        RecordedPotentialStep.step_setWeight_eq_mul_exp]
      rw [ih (by omega), hsum, mul_add, Real.exp_add]
      simp only [servedSetTerm]

private theorem prefix_normalizer_ratio_prod (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K) (n : ℕ) :
    (∏ t ∈ Finset.range n,
      prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t) =
      prefixNormalizer p rounds m n / prefixNormalizer p rounds m 0 := by
  induction n with
  | zero =>
      exact (div_self (prefixNormalizer_pos p rounds hm hmK 0).ne').symm
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn0 : prefixNormalizer p rounds m n ≠ 0 :=
        (prefixNormalizer_pos p rounds hm hmK n).ne'
      have h00 : prefixNormalizer p rounds m 0 ≠ 0 :=
        (prefixNormalizer_pos p rounds hm hmK 0).ne'
      field_simp [hn0, h00]

private theorem prefix_log_normalizer_ratios_sum (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K) (n : ℕ) :
    (∑ t : Fin n, Real.log
      (prefixNormalizer p rounds m (t.val + 1) / prefixNormalizer p rounds m t.val)) =
      Real.log (prefixNormalizer p rounds m n / prefixNormalizer p rounds m 0) := by
  have hprod := prefix_normalizer_ratio_prod p rounds hm hmK n
  have hlogprod :
      Real.log (∏ t ∈ Finset.range n,
        prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t) =
        ∑ t ∈ Finset.range n, Real.log
          (prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t) := by
    apply Real.log_prod
    intro t ht
    exact (div_pos
      (prefixNormalizer_pos p rounds hm hmK (t + 1))
      (prefixNormalizer_pos p rounds hm hmK t)).ne'
  calc
    (∑ t : Fin n, Real.log
        (prefixNormalizer p rounds m (t.val + 1) / prefixNormalizer p rounds m t.val)) =
        ∑ t ∈ Finset.range n, Real.log
          (prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t) :=
      Fin.sum_univ_eq_sum_range
        (fun t : ℕ => Real.log
          (prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t)) n
    _ = Real.log (∏ t ∈ Finset.range n,
        prefixNormalizer p rounds m (t + 1) / prefixNormalizer p rounds m t) := hlogprod.symm
    _ = Real.log (prefixNormalizer p rounds m n / prefixNormalizer p rounds m 0) := by
      rw [hprod]

private theorem terminal_atom_le_normalizer (p : Parameters)
    (rounds : List (RoundInput K)) (S : ProductSet K m) :
    ProductSetLaw.setWeight
        (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p rounds)) S.1 ≤
      ProductSetLaw.normalizer m
        (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p rounds)) := by
  rw [ProductSetLaw.normalizer_eq_support_sum]
  apply Finset.single_le_sum
  · intro T hT
    exact (ProductSetLaw.setWeight_pos _
      (fun i => RecordedPotentialStep.scoreWeight_pos p (RecordedQueueRun.run p rounds) i)
      T).le
  · exact S.2

private theorem terminal_log_ratio_lower (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K)
    (S : ProductSet K m) :
    RecordedPotentialStep.potentialLambda p *
        servedSetTotal p rounds S rounds.length (Nat.le_refl _) -
        Real.log (Nat.choose K m : ℝ) ≤
      Real.log (prefixNormalizer p rounds m rounds.length / prefixNormalizer p rounds m 0) := by
  have hterminalProduct :=
    prefix_setWeight_eq_exp_servedSetTotal p rounds S rounds.length (Nat.le_refl _)
  have hterminalRun :
      RecordedQueueRun.run p (rounds.take rounds.length) = RecordedQueueRun.run p rounds := by
    simp
  rw [hterminalRun] at hterminalProduct
  have hatom := terminal_atom_le_normalizer p rounds S
  have hatomPos : 0 < ProductSetLaw.setWeight
      (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p rounds)) S.1 :=
    ProductSetLaw.setWeight_pos _
      (fun i => RecordedPotentialStep.scoreWeight_pos p (RecordedQueueRun.run p rounds) i)
      S.1
  have hlogAtom := Real.log_le_log hatomPos hatom
  rw [hterminalProduct, Real.log_exp] at hlogAtom
  have hinit : prefixNormalizer p rounds m 0 = (Nat.choose K m : ℝ) := by
    simp [prefixNormalizer, initial_normalizer_eq_choose,
      RecordedQueueRun.run, RecordedQueueRun.execute]
  have hterminalNormalizer :
      prefixNormalizer p rounds m rounds.length =
        ProductSetLaw.normalizer m
          (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p rounds)) := by
    simp [prefixNormalizer]
  have hfinalPos : 0 < ProductSetLaw.normalizer m
      (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p rounds)) := by
    simpa [prefixNormalizer] using
      prefixNormalizer_pos p rounds hm hmK rounds.length
  have hchoosePos := choose_pos_real (K := K) (m := m) hmK
  rw [hterminalNormalizer, hinit, Real.log_div
    hfinalPos.ne' hchoosePos.ne']
  nlinarith only [hlogAtom]

/-- The actual cumulative served-estimate comparison along one finite run.

The indexed sum visits every element of `rounds`, even when an input is
disabled or follows overflow. `run_take_succ_eq_step` retains the transition
which first sets overflow. The normalizer is initialized once at the all-one
weights, so the bound pays one `log (choose K m)` term for the whole run.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:393-427`. -/
theorem servedEstimate_cumulative_comparison (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K)
    (hsmall : 4 * (m : ℝ) * p.eta ≤ 1) (S : ProductSet K m) :
    (∑ t : Fin rounds.length,
      (∑ i ∈ S.1,
        RecordedPotentialStep.servedEstimate p
          (RecordedQueueRun.run p (rounds.take t.val)) (rounds[t.val]'t.isLt) i -
       ∑ i,
        ProductSetLaw.theta m
            (RecordedQueueRun.scoreWeight p
              (RecordedQueueRun.run p (rounds.take t.val))) i *
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) (rounds[t.val]'t.isLt) i)) ≤
      Real.log (Nat.choose K m : ℝ) / RecordedPotentialStep.potentialLambda p +
        16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p * rounds.length := by
  let A : ℝ := ∑ t : Fin rounds.length,
    ∑ i ∈ S.1,
      RecordedPotentialStep.servedEstimate p
        (RecordedQueueRun.run p (rounds.take t.val)) (rounds[t.val]'t.isLt) i
  let B : ℝ := ∑ t : Fin rounds.length,
    ∑ i,
      ProductSetLaw.theta m
          (RecordedQueueRun.scoreWeight p
            (RecordedQueueRun.run p (rounds.take t.val))) i *
        RecordedPotentialStep.servedEstimate p
          (RecordedQueueRun.run p (rounds.take t.val)) (rounds[t.val]'t.isLt) i
  have hterminal :
      RecordedPotentialStep.potentialLambda p * A -
          Real.log (Nat.choose K m : ℝ) ≤
        Real.log (prefixNormalizer p rounds m rounds.length / prefixNormalizer p rounds m 0) := by
    simpa [A, servedSetTotal, servedSetTerm] using
      terminal_log_ratio_lower p rounds hm hmK S
  have hstep (t : Fin rounds.length) :
      Real.log (prefixNormalizer p rounds m (t.val + 1) /
          prefixNormalizer p rounds m t.val) ≤
        RecordedPotentialStep.potentialLambda p *
            (∑ i,
              ProductSetLaw.theta m
                  (RecordedQueueRun.scoreWeight p
                    (RecordedQueueRun.run p (rounds.take t.val))) i *
                RecordedPotentialStep.servedEstimate p
                  (RecordedQueueRun.run p (rounds.take t.val))
                  (rounds[t.val]'t.isLt) i) +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2 := by
    simpa [prefixNormalizer] using
      RecordedPotentialStep.run_prefix_log_normalizer_le_coarse p rounds t.val t.isLt
        hm hmK hsmall
  have hupper :
      Real.log (prefixNormalizer p rounds m rounds.length / prefixNormalizer p rounds m 0) ≤
        RecordedPotentialStep.potentialLambda p * B +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2 *
            rounds.length := by
    calc
      Real.log (prefixNormalizer p rounds m rounds.length / prefixNormalizer p rounds m 0) =
          ∑ t : Fin rounds.length, Real.log
            (prefixNormalizer p rounds m (t.val + 1) / prefixNormalizer p rounds m t.val) :=
        (prefix_log_normalizer_ratios_sum p rounds hm hmK rounds.length).symm
      _ ≤ ∑ t : Fin rounds.length,
          (RecordedPotentialStep.potentialLambda p *
              (∑ i,
                ProductSetLaw.theta m
                    (RecordedQueueRun.scoreWeight p
                      (RecordedQueueRun.run p (rounds.take t.val))) i *
                  RecordedPotentialStep.servedEstimate p
                    (RecordedQueueRun.run p (rounds.take t.val))
                    (rounds[t.val]'t.isLt) i) +
            16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2) :=
        Finset.sum_le_sum (fun t _ => hstep t)
      _ = RecordedPotentialStep.potentialLambda p * B +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2 *
            rounds.length := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hcompare :
      RecordedPotentialStep.potentialLambda p * (A - B) ≤
        Real.log (Nat.choose K m : ℝ) +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2 *
            rounds.length := by
    nlinarith only [hterminal, hupper]
  have hpotentialPos := RecordedPotentialStep.potentialLambda_pos p
  have hrhs :
      Real.log (Nat.choose K m : ℝ) / RecordedPotentialStep.potentialLambda p +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p * rounds.length =
        (Real.log (Nat.choose K m : ℝ) +
          16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p ^ 2 *
            rounds.length) / RecordedPotentialStep.potentialLambda p := by
    field_simp [hpotentialPos.ne']
  have hfinal : A - B ≤
      Real.log (Nat.choose K m : ℝ) / RecordedPotentialStep.potentialLambda p +
        16 * (m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda p * rounds.length := by
    rw [hrhs, le_div_iff₀ hpotentialPos]
    nlinarith only [hcompare]
  rw [Finset.sum_sub_distrib]
  simpa [A, B] using hfinal

end Bandits.Support.RecordedPotentialTelescope

end
