/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ProductSetDistribution
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.RecordedEpisodeStability
public import Bandits.Support.RecordedQueueRun
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-anchor slow-law refresh for recorded queue steps

This module compares the manuscript's existing canonical slow-set marginal
before and after one actual `RecordedQueueRun.step`. It constructs its residual
mass from those two marginals and defines the refresh transition on the
existing `(m - 1)`-set carrier. Sources:
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37,96-104,176-187,219-243`.

These are fixed-step internal laws. They do not define an adaptive conditional
slow-set marginal, the physical schedule, or a continuous sampler coupling.
-/

public section

open scoped BigOperators

namespace Bandits.Support.RecordedSlowRefresh

variable {K : ℕ}

open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ProductSetLaw
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ScoreWeights

/-- The source proposal hazard `h = 4 m eta` for a fixed constructor and
recorded queue parameter. Source: `04_slow_fast_learner.tex:176-177`. -/
@[expose] def hazard (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) : ℝ :=
  4 * (p.m : ℝ) * q.eta

theorem hazard_pos (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) : 0 < hazard p q := by
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)))
    q.eta_pos

/-- The manuscript learning-rate cap itself implies the hazard bound; the
hazard bound is not an input to any refresh construction. -/
theorem hazard_le_quarter (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    hazard p q ≤ 1 / 4 := by
  have hm : (0 : ℝ) < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hKnat := ConstructorDimensions.K_pos p
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
  have hLnat := CanonicalRecordingRates.L_stab_ge_one p
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast hLnat
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
    one_le_mul_of_one_le_of_one_le hK hL
  have hme_nonneg : 0 ≤ (p.m : ℝ) * q.eta := mul_nonneg hm.le q.eta_pos.le
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hcap_mul : q.eta *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp hcap
  have hscaled : 16 * ((p.m : ℝ) * q.eta) ≤
      1024 * ((p.m : ℝ) * q.eta) *
        ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) := by
    have hmul : (p.m : ℝ) * q.eta ≤
        ((p.m : ℝ) * q.eta) * ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) := by
      calc
        (p.m : ℝ) * q.eta = ((p.m : ℝ) * q.eta) * 1 := by ring
        _ ≤ ((p.m : ℝ) * q.eta) *
            ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
          mul_le_mul_of_nonneg_left hKL hme_nonneg
    have hmul_nonneg : 0 ≤ ((p.m : ℝ) * q.eta) *
        ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
      mul_nonneg hme_nonneg (mul_nonneg (by positivity) (by positivity))
    calc
      16 * ((p.m : ℝ) * q.eta) ≤
          16 * (((p.m : ℝ) * q.eta) *
            ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ ≤ 1024 * ((p.m : ℝ) * q.eta) *
          ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 1024)
              hmul_nonneg)
  have hscaled_cap : 1024 * ((p.m : ℝ) * q.eta) *
      ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 := by
    calc
      1024 * ((p.m : ℝ) * q.eta) *
          ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) =
        q.eta * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by ring
      _ ≤ 1 := hcap_mul
  have h16 : 16 * (p.m : ℝ) * q.eta ≤ 1 := by nlinarith [hscaled, hscaled_cap]
  unfold hazard
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  nlinarith [h16]

/-- Positivity of the actual recorded score weight, derived from the positive
source score base. -/
theorem scoreWeight_pos (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (i : Fin K) :
    0 < RecordedQueueRun.scoreWeight q state i := by
  exact ScoreWeights.scoreWeight_pos
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr q.D_pos)) _

/-- Actual score monotonicity of `RecordedQueueRun.step`, including all its
enabled, disabled, and overflow branches. -/
theorem step_scoreWeight_mono (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) :
    RecordedQueueRun.scoreWeight q state i ≤
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i := by
  have hscore :
      ((RecordedQueueRun.step q state round).registers i).1 =
        (state.registers i).1 +
          RecordedQueueRun.recordService (4 * q.n) (state.registers i)
            (RecordedQueueRun.acceptedRecord q state round i) := by
    change (QueueReplay.transition (4 * q.n) (state.registers i)
      (RecordedQueueRun.acceptedRecord q state round i)).1 = _
    exact RecordedQueueRun.transition_score_eq_add_recordService _ _ _
  change ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) (state.registers i).1 ≤ _
  exact ScoreWeights.sourceWeight_mono (Nat.cast_pos.mpr q.D_pos)
    (by rw [hscore]; exact Nat.le_add_right _ _)

/-- The one-coordinate weight envelope obtained from the actual step's source
logarithmic weight-increment lemma. -/
theorem step_scoreWeight_exp_envelope (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (i : Fin p.K) :
    RecordedQueueRun.scoreWeight q state i ≤
        RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i ∧
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i ≤
        Real.exp (4 * q.eta) * RecordedQueueRun.scoreWeight q state i := by
  refine ⟨step_scoreWeight_mono q state round i, ?_⟩
  have hratio_pos : 0 <
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i /
        RecordedQueueRun.scoreWeight q state i :=
    div_pos (scoreWeight_pos q (RecordedQueueRun.step q state round) i)
      (scoreWeight_pos q state i)
  have hlog := RecordedEpisodeStability.step_source_weight_log_le q state round i
  have hratio :
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i /
        RecordedQueueRun.scoreWeight q state i ≤ Real.exp (4 * q.eta) := by
    calc
      _ = Real.exp (Real.log
          (RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i /
            RecordedQueueRun.scoreWeight q state i)) := (Real.exp_log hratio_pos).symm
      _ ≤ Real.exp (4 * q.eta) := Real.exp_le_exp.mpr hlog
  exact (div_le_iff₀ (scoreWeight_pos q state i)).mp hratio

/-- The actual product weight on every supported `m`-set grows by at most
`exp (4 m eta)` in one recorded queue step. -/
theorem step_setWeight_le (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ProductSetLaw.setWeight
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S.1 ≤
      Real.exp (4 * (p.m : ℝ) * q.eta) *
        ProductSetLaw.setWeight (fun i => RecordedQueueRun.scoreWeight q state i) S.1 := by
  have hprod := Finset.prod_le_prod₀
    (s := S.1)
    (fun i hi => (scoreWeight_pos q (RecordedQueueRun.step q state round) i).le)
    (fun i hi => (step_scoreWeight_exp_envelope p q state round i).2)
  have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
  have hexp : Real.exp (4 * q.eta) ^ p.m =
      Real.exp (4 * (p.m : ℝ) * q.eta) := by
    calc
      Real.exp (4 * q.eta) ^ p.m =
          Real.exp ((p.m : ℝ) * (4 * q.eta)) :=
        (Real.exp_nat_mul (4 * q.eta) p.m).symm
      _ = Real.exp (4 * (p.m : ℝ) * q.eta) := by congr 1; ring
  change (∏ i ∈ S.1,
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) ≤ _
  calc
    (∏ i ∈ S.1,
        RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) ≤
        ∏ i ∈ S.1,
          (Real.exp (4 * q.eta) * RecordedQueueRun.scoreWeight q state i) := hprod
    _ = Real.exp (4 * q.eta) ^ S.1.card *
          ProductSetLaw.setWeight (fun i => RecordedQueueRun.scoreWeight q state i) S.1 := by
      simp [ProductSetLaw.setWeight, Finset.prod_mul_distrib]
    _ = Real.exp (4 * (p.m : ℝ) * q.eta) *
          ProductSetLaw.setWeight (fun i => RecordedQueueRun.scoreWeight q state i) S.1 := by
      rw [hcard, hexp]

/-- The actual partition function after one step is at most the source
`exp (4 m eta)` multiple of its pre-step value. -/
theorem step_normalizer_le (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) :
    ProductSetLaw.normalizer p.m
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) ≤
      Real.exp (4 * (p.m : ℝ) * q.eta) *
        ProductSetLaw.normalizer p.m (fun i => RecordedQueueRun.scoreWeight q state i) := by
  rw [ProductSetLaw.normalizer_eq_support_sum, ProductSetLaw.normalizer_eq_support_sum]
  calc
    (∑ S ∈ ProductSetLaw.support p.K p.m,
        ProductSetLaw.setWeight
          (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S) ≤
      ∑ S ∈ ProductSetLaw.support p.K p.m,
        Real.exp (4 * (p.m : ℝ) * q.eta) *
          ProductSetLaw.setWeight (fun i => RecordedQueueRun.scoreWeight q state i) S := by
      apply Finset.sum_le_sum
      intro S hS
      exact step_setWeight_le p q state round ⟨S, hS⟩
    _ = Real.exp (4 * (p.m : ℝ) * q.eta) *
        ∑ S ∈ ProductSetLaw.support p.K p.m,
          ProductSetLaw.setWeight (fun i => RecordedQueueRun.scoreWeight q state i) S := by
      rw [Finset.mul_sum]

/-- Every actual product-set atom after a step dominates its pre-step atom by
the exponential inverse partition-growth factor. -/
theorem step_Q_exp_domination (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Real.exp (-(4 * (p.m : ℝ) * q.eta)) *
        ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q state i) S ≤
      ProductSetLaw.Q p.m
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S := by
  let w : Fin p.K → ℝ := fun i => RecordedQueueRun.scoreWeight q state i
  let w' : Fin p.K → ℝ := fun i =>
    RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i
  have hw : ∀ i, 0 < w i := fun i => scoreWeight_pos q state i
  have hw' : ∀ i, 0 < w' i := fun i =>
    scoreWeight_pos q (RecordedQueueRun.step q state round) i
  have hZ : ProductSetLaw.normalizer p.m w' ≤
      Real.exp (4 * (p.m : ℝ) * q.eta) * ProductSetLaw.normalizer p.m w := by
    simpa [w, w'] using step_normalizer_le p q state round
  have hZpos : 0 < ProductSetLaw.normalizer p.m w :=
    ProductSetLaw.normalizer_pos w (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
      p.m_lt_K hw
  have hZ'pos : 0 < ProductSetLaw.normalizer p.m w' :=
    ProductSetLaw.normalizer_pos w' (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
      p.m_lt_K hw'
  have hA_le : ProductSetLaw.setWeight w S.1 ≤ ProductSetLaw.setWeight w' S.1 := by
    exact Finset.prod_le_prod₀
      (fun i hi => (scoreWeight_pos q state i).le)
      (fun i hi => (step_scoreWeight_exp_envelope p q state round i).1)
  have hdiv : ProductSetLaw.setWeight w S.1 /
        (Real.exp (4 * (p.m : ℝ) * q.eta) * ProductSetLaw.normalizer p.m w) ≤
      ProductSetLaw.setWeight w' S.1 / ProductSetLaw.normalizer p.m w' := by
    exact div_le_div₀ (ProductSetLaw.setWeight_pos w' hw' S.1).le hA_le hZ'pos hZ
  have hident : ProductSetLaw.Q p.m w S *
      Real.exp (-(4 * (p.m : ℝ) * q.eta)) =
        ProductSetLaw.setWeight w S.1 /
          (Real.exp (4 * (p.m : ℝ) * q.eta) * ProductSetLaw.normalizer p.m w) := by
    rw [ProductSetLaw.Q]
    change (ProductSetLaw.setWeight w S.1 / ProductSetLaw.normalizer p.m w) *
        Real.exp (-(4 * (p.m : ℝ) * q.eta)) = _
    rw [Real.exp_neg]
    field_simp [hZpos.ne', Real.exp_ne_zero]
  change Real.exp (-(4 * (p.m : ℝ) * q.eta)) * ProductSetLaw.Q p.m w S ≤
    ProductSetLaw.Q p.m w' S
  rw [mul_comm, hident, ProductSetLaw.Q]
  exact hdiv

/-- One-step product-set domination at the exact source hazard. The estimate
`1 - h ≤ exp (-h)` is proved from Mathlib's pinned `one_sub_le_exp_neg`. -/
theorem step_Q_domination (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (1 - hazard p q) *
        ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q state i) S ≤
      ProductSetLaw.Q p.m
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S := by
  have hlinear : 1 - hazard p q ≤ Real.exp (-(hazard p q)) :=
    Real.one_sub_le_exp_neg (hazard p q)
  have hQ := step_Q_exp_domination p q state round S
  change (1 - hazard p q) * _ ≤ _
  calc
    (1 - hazard p q) *
        ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q state i) S ≤
      Real.exp (-(hazard p q)) *
        ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q state i) S :=
      mul_le_mul_of_nonneg_right hlinear
        (ProductSetLaw.Q_pos _ (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
          (fun i => scoreWeight_pos q state i) S).le
    _ ≤ ProductSetLaw.Q p.m
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S := by
      simpa [hazard] using hQ

/-- The actual logical slow-set marginal of a recorded queue state, expressed
through the already accepted canonical orientation law. -/
@[expose] noncomputable def recordedSlowMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) : ℝ :=
  CanonicalOrientedSetLaw.slowMarginal
    (fun i => RecordedQueueRun.scoreWeight q state i) anchor
    p.two_le_m p.m_lt_K (fun i => scoreWeight_pos q state i)
    hanchor U

/-- The same canonical law as an actual PMF on the existing slow-set carrier. -/
@[expose] noncomputable def recordedSlowPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i) :
    PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
  CanonicalOrientedSetLaw.slowSetPMF
    (fun i => RecordedQueueRun.scoreWeight q state i) anchor
    p.two_le_m p.m_lt_K (fun i => scoreWeight_pos q state i) hanchor

/-- Every actual recorded queue step dominates the fixed-anchor slow marginal
by the source hazard. In particular, enabled non-overflowed steps include the
first overflow update retained by `RecordedQueueRun.step`. The comparison sums
the same anchor orientation probabilities on the existing canonical law. -/
theorem step_slowMarginal_domination
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    (1 - hazard p q) * recordedSlowMass p q state anchor hanchor U ≤
      recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U := by
  unfold recordedSlowMass CanonicalOrientedSetLaw.slowMarginal
    FiniteOrientationDisintegration.slowMarginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hnow := CanonicalOrientedSetLaw.orientedJointMass_eq_Q_mul_orientationProbability
    (fun i => RecordedQueueRun.scoreWeight q state i) anchor p.two_le_m p.m_lt_K
    (fun i => scoreWeight_pos q state i) hanchor U j
  have hnext := CanonicalOrientedSetLaw.orientedJointMass_eq_Q_mul_orientationProbability
    (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i)
    anchor p.two_le_m p.m_lt_K
    (fun i => scoreWeight_pos q (RecordedQueueRun.step q state round) i) hanchor U j
  rw [hnow, hnext]
  let S : ProductSetLaw.ProductSet p.K p.m := ⟨insert j.1 U.1, by
    rcases Finset.mem_sdiff.mp j.2 with ⟨hjI, hjU⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset hjI (Finset.subset_univ _),
        (Finset.card_insert_of_notMem hjU).trans (CanonicalOrientedSetLaw.slowSet_card p.two_le_m U)⟩⟩
  have halpha : 0 <
      FiniteOrientationDisintegration.orientationProbability anchor
        (insert j.1 U.1) (Finset.insert_nonempty _ _)
        (fun i hi => hanchor i)
        ⟨j.1, Finset.mem_insert_self _ _⟩ :=
    FiniteOrientationDisintegration.orientationProbability_pos anchor
      (insert j.1 U.1) (Finset.insert_nonempty _ _)
      (fun i hi => hanchor i) ⟨j.1, Finset.mem_insert_self _ _⟩
  have hQ' :
      (1 - hazard p q) *
          ProductSetLaw.Q p.m
            (fun i => RecordedQueueRun.scoreWeight q state i) S ≤
        ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S := by
    exact step_Q_domination p q state round S
  calc
    (1 - hazard p q) *
        (ProductSetLaw.Q p.m
          (fun i => RecordedQueueRun.scoreWeight q state i) S *
          FiniteOrientationDisintegration.orientationProbability anchor
            (insert j.1 U.1) (Finset.insert_nonempty _ _)
            (fun i hi => hanchor i)
            ⟨j.1, Finset.mem_insert_self _ _⟩) =
      ((1 - hazard p q) * ProductSetLaw.Q p.m
        (fun i => RecordedQueueRun.scoreWeight q state i) S) *
          FiniteOrientationDisintegration.orientationProbability anchor
            (insert j.1 U.1) (Finset.insert_nonempty _ _)
            (fun i hi => hanchor i)
            ⟨j.1, Finset.mem_insert_self _ _⟩ := by ring
    _ ≤ ProductSetLaw.Q p.m
        (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) S *
          FiniteOrientationDisintegration.orientationProbability anchor
            (insert j.1 U.1) (Finset.insert_nonempty _ _)
            (fun i hi => hanchor i)
            ⟨j.1, Finset.mem_insert_self _ _⟩ :=
      mul_le_mul_of_nonneg_right hQ' halpha.le

/-- The existing canonical slow marginal is normalized on its supported
carrier for every actual recorded score vector. -/
theorem recordedSlowMass_sum_eq_one (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
      recordedSlowMass p q state anchor hanchor U) = 1 := by
  simpa [recordedSlowMass] using
    (CanonicalOrientedSetLaw.slowMarginal_sum_eq_one
      (fun i => RecordedQueueRun.scoreWeight q state i) anchor
      p.two_le_m p.m_lt_K (fun i => scoreWeight_pos q state i) hanchor)

/-- Positivity of the recorded slow marginal follows from the existing
canonical oriented-set law. -/
theorem recordedSlowMass_pos (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    0 < recordedSlowMass p q state anchor hanchor U := by
  exact CanonicalOrientedSetLaw.slowMarginal_pos
    (fun i => RecordedQueueRun.scoreWeight q state i) anchor
    p.two_le_m p.m_lt_K (fun i => scoreWeight_pos q state i) hanchor U

/-- The literal residual refresh mass on the existing canonical slow-set
carrier: `rho(U) = (p_next(U) - (1-h) p_now(U))/h`. -/
@[expose] noncomputable def residualMass
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) : ℝ :=
  (recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U -
    (1 - hazard p q) * recordedSlowMass p q state anchor hanchor U) /
      hazard p q

theorem residualMass_nonneg (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    0 ≤ residualMass p q state round anchor hanchor U := by
  rw [residualMass]
  apply div_nonneg
  · exact sub_nonneg.mpr
      (step_slowMarginal_domination p q state round anchor hanchor U)
  · exact (hazard_pos p q).le

/-- The residual is pointwise characterized by the affine identity whose
normalization makes the refresh mixture exactly the next canonical law. -/
theorem residualMass_characterization (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    hazard p q * residualMass p q state round anchor hanchor U +
        (1 - hazard p q) * recordedSlowMass p q state anchor hanchor U =
      recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U := by
  rw [residualMass]
  have hh := hazard_pos p q
  field_simp [ne_of_gt hh]
  ring

/-- The residual masses sum to one; no normalization premise is assumed. -/
theorem residualMass_sum_eq_one (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
      residualMass p q state round anchor hanchor U) = 1 := by
  unfold residualMass
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [recordedSlowMass_sum_eq_one p q (RecordedQueueRun.step q state round) anchor hanchor,
    recordedSlowMass_sum_eq_one p q state anchor hanchor]
  have hh := hazard_pos p q
  field_simp [ne_of_gt hh]
  ring

/-- The residual law as a PMF on the original supported `(m - 1)`-set type. -/
@[expose] noncomputable def residualPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) := by
  classical
  exact PMF.ofFintype
    (fun U => ENNReal.ofReal (residualMass p q state round anchor hanchor U)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
      · rw [residualMass_sum_eq_one]
        simp
      · intro U hU
        exact residualMass_nonneg p q state round anchor hanchor U)

theorem residualPMF_apply (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    residualPMF p q state round anchor hanchor U =
      ENNReal.ofReal (residualMass p q state round anchor hanchor U) := by
  simp [residualPMF]

/-- The source refresh proposal probability is zero after a pre-state overflow
or on a disabled round. It depends only on the pre-state, so an enabled update
that first sets overflow retains its proposal. -/
@[expose] def proposalProbability (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) : ℝ :=
  if state.overflow = false ∧ round.enabled = true then hazard p q else 0

theorem proposalProbability_active (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (hnotOverflow : state.overflow = false) (henabled : round.enabled = true) :
    proposalProbability p q state round = hazard p q := by
  simp [proposalProbability, hnotOverflow, henabled]

theorem proposalProbability_zero_of_disabled (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (hdisabled : round.enabled = false) :
    proposalProbability p q state round = 0 := by
  simp [proposalProbability, hdisabled]

theorem proposalProbability_zero_of_overflow (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (hoverflow : state.overflow = true) :
    proposalProbability p q state round = 0 := by
  simp [proposalProbability, hoverflow]

theorem proposalProbability_nonneg (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) :
    0 ≤ proposalProbability p q state round := by
  by_cases hactive : state.overflow = false ∧ round.enabled = true
  · rw [proposalProbability_active p q state round hactive.1 hactive.2]
    exact (hazard_pos p q).le
  · simp [proposalProbability, hactive]

theorem proposalProbability_le_one (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    proposalProbability p q state round ≤ 1 := by
  by_cases hactive : state.overflow = false ∧ round.enabled = true
  · rw [proposalProbability_active p q state round hactive.1 hactive.2]
    exact le_trans (hazard_le_quarter p q hcap) (by norm_num)
  · simp [proposalProbability, hactive]

/-- The Bernoulli proposal PMF, with its normalization proved from the
probability interval. -/
@[expose] noncomputable def bernoulliProposalPMF (probability : ℝ)
    (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1) : PMF Bool := by
  classical
  refine PMF.ofFintype
    (fun proposal => if proposal then ENNReal.ofReal probability
      else ENNReal.ofReal (1 - probability)) ?_
  have hfalse : 0 ≤ 1 - probability := by linarith
  simp
  rw [← ENNReal.ofReal_add hprobability_nonneg hfalse]
  rw [show probability + (1 - probability) = 1 by ring, ENNReal.ofReal_one]

/-- A generic one-step Bernoulli proposal and fresh-law refresh kernel. The
coin is `true` with probability `probability`; `false` retains `current`. -/
@[expose] noncomputable def refreshKernel {α : Type*} [Fintype α]
    (probability : ℝ) (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1) (rho : PMF α) (current : α) : PMF α := by
  classical
  exact (bernoulliProposalPMF probability hprobability_nonneg hprobability_le_one).bind
    (fun proposal => if proposal then rho else PMF.pure current)

theorem refreshKernel_apply {α : Type*} [Fintype α] [DecidableEq α]
    (probability : ℝ) (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1) (rho : PMF α) (current next : α) :
    refreshKernel probability hprobability_nonneg hprobability_le_one rho current next =
      (if next = current then ENNReal.ofReal (1 - probability) else 0) +
        ENNReal.ofReal probability * rho next := by
  classical
  simp [refreshKernel, bernoulliProposalPMF, PMF.bind_apply, PMF.ofFintype_apply,
    PMF.pure_apply]
  ac_rfl

theorem refreshKernel_zero {α : Type*} [Fintype α] [DecidableEq α]
    (rho : PMF α) (current : α) :
    refreshKernel 0 (by norm_num) (by norm_num) rho current = PMF.pure current := by
  classical
  ext next
  rw [refreshKernel_apply]
  simp

/-- Pointwise law of a current PMF passed through the Bernoulli refresh
kernel. This is the explicit `(1-h) μ + h rho` identity. -/
theorem refreshKernel_bind_apply {α : Type*} [Fintype α] [DecidableEq α]
    (probability : ℝ) (hprobability_nonneg : 0 ≤ probability)
    (hprobability_le_one : probability ≤ 1) (rho μ : PMF α) (next : α) :
    μ.bind (fun current =>
      refreshKernel probability hprobability_nonneg hprobability_le_one rho current) next =
      ENNReal.ofReal (1 - probability) * μ next +
        ENNReal.ofReal probability * rho next := by
  classical
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [refreshKernel_apply, mul_add]
  rw [Finset.sum_add_distrib]
  have hμ : (∑ current : α, μ current) = 1 := by
    simpa using μ.tsum_coe
  have hretain :
      (∑ current : α,
        μ current * (if next = current then ENNReal.ofReal (1 - probability) else 0)) =
        ENNReal.ofReal (1 - probability) * μ next := by
    simp [mul_comm]
  have hfresh :
      (∑ current : α,
        μ current * (ENNReal.ofReal probability * rho next)) =
        ENNReal.ofReal probability * rho next := by
    calc
      _ = (∑ current : α, μ current) *
          (ENNReal.ofReal probability * rho next) := by rw [Finset.sum_mul]
      _ = ENNReal.ofReal probability * rho next := by rw [hμ]; simp
  rw [hretain, hfresh]

theorem recordedSlowPMF_apply (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    recordedSlowPMF p q state anchor hanchor U =
      ENNReal.ofReal (recordedSlowMass p q state anchor hanchor U) := by
  simpa [recordedSlowPMF, recordedSlowMass] using
    (CanonicalOrientedSetLaw.slowSetPMF_apply
      (fun i => RecordedQueueRun.scoreWeight q state i) anchor
      p.two_le_m p.m_lt_K (fun i => scoreWeight_pos q state i) hanchor U)

/-- Disabled and post-overflow steps preserve the actual score-weight vector.
This reads the existing `RecordedQueueRun.step` exceptional paths directly. -/
theorem step_scoreWeights_eq_of_inactive (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (hinactive : round.enabled = false ∨ state.overflow = true) :
    (fun i => RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state round) i) =
      (fun i => RecordedQueueRun.scoreWeight q state i) := by
  funext i
  rcases hinactive with hdisabled | hoverflow
  · have hstep := RecordedQueueRun.step_disabled_preserves q state round hdisabled i
    change ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ))
      ((RecordedQueueRun.step q state round).registers i).1 =
        ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) (state.registers i).1
    rw [hstep.1]
  · have hstep := RecordedQueueRun.step_after_overflow_preserves q state round hoverflow i
    change ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ))
      ((RecordedQueueRun.step q state round).registers i).1 =
        ScoreWeights.scoreWeight (1 + 1 / (q.D : ℝ)) (state.registers i).1
    rw [hstep.1]

theorem recordedSlowMass_step_eq_of_inactive (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (hinactive : round.enabled = false ∨ state.overflow = true)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U =
      recordedSlowMass p q state anchor hanchor U := by
  have hweight := step_scoreWeights_eq_of_inactive p q state round hinactive
  unfold recordedSlowMass
  simp only [hweight]

theorem recordedSlowPMF_step_eq_of_inactive (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (hinactive : round.enabled = false ∨ state.overflow = true) :
    recordedSlowPMF p q (RecordedQueueRun.step q state round) anchor hanchor =
      recordedSlowPMF p q state anchor hanchor := by
  have hweight := step_scoreWeights_eq_of_inactive p q state round hinactive
  unfold recordedSlowPMF
  simp only [hweight]

/-- In an inactive round the literal residual is the current slow law; its
proposal probability is separately zero, so no refresh is performed. -/
theorem residualMass_eq_current_of_inactive (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (hinactive : round.enabled = false ∨ state.overflow = true)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    residualMass p q state round anchor hanchor U =
      recordedSlowMass p q state anchor hanchor U := by
  rw [residualMass,
    recordedSlowMass_step_eq_of_inactive p q state round anchor hanchor hinactive U]
  have hh := hazard_pos p q
  field_simp [ne_of_gt hh]
  ring

/-- The recorded refresh kernel uses the source hazard only on enabled rounds
whose pre-state has not overflowed. -/
@[expose] noncomputable def recordedRefreshKernel
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) := by
  classical
  exact refreshKernel (proposalProbability p q state round)
    (proposalProbability_nonneg p q state round)
    (proposalProbability_le_one p q state round hcap)
    (residualPMF p q state round anchor hanchor) U

theorem recordedRefreshKernel_apply (p : ConstructorDimensions.Parameters)
    (q : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K) (anchor : Fin p.K → ℝ)
    (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (U V : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    recordedRefreshKernel p q state round anchor hanchor hcap U V =
      (if V = U then ENNReal.ofReal
        (1 - proposalProbability p q state round) else 0) +
        ENNReal.ofReal (proposalProbability p q state round) *
          residualPMF p q state round anchor hanchor V := by
  classical
  simpa [recordedRefreshKernel] using
    (refreshKernel_apply (proposalProbability p q state round)
      (proposalProbability_nonneg p q state round)
      (proposalProbability_le_one p q state round hcap)
      (residualPMF p q state round anchor hanchor) U V)

theorem recordedRefreshKernel_eq_pure_of_inactive
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (hinactive : round.enabled = false ∨ state.overflow = true)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    recordedRefreshKernel p q state round anchor hanchor hcap U = PMF.pure U := by
  have hzero : proposalProbability p q state round = 0 := by
    rcases hinactive with hdisabled | hoverflow
    · exact proposalProbability_zero_of_disabled p q state round hdisabled
    · exact proposalProbability_zero_of_overflow p q state round hoverflow
  unfold recordedRefreshKernel
  simp only [hzero]
  exact refreshKernel_zero (residualPMF p q state round anchor hanchor) U

/-- On an enabled update from a clear pre-state, including the update that
first sets overflow, the actual queue step retains its records and the refresh
probability remains `h`. No successor-overflow test suppresses that proposal. -/
theorem first_overflow_update_is_retained_and_proposed
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (henabled : round.enabled = true) (hnotOverflow : state.overflow = false)
    (hfirstOverflow : (RecordedQueueRun.step q state round).overflow = true) :
    proposalProbability p q state round = hazard p q ∧
      (∀ i, RecordedQueueRun.acceptedRecord q state round i =
        (true, RecordedQueueRun.quantizedArrival q round i)) ∧
      ∀ i, (RecordedQueueRun.step q state round).registers i =
        QueueReplay.transition (4 * q.n) (state.registers i)
          (RecordedQueueRun.acceptedRecord q state round i) := by
  refine ⟨proposalProbability_active p q state round hnotOverflow henabled, ?_⟩
  constructor
  · intro i
    simp [RecordedQueueRun.acceptedRecord, hnotOverflow, henabled]
  · exact (RecordedQueueRun.step_retains_first_overflow_update q state round
      hnotOverflow hfirstOverflow).2

/-- An enabled, pre-overflowed actual queue step satisfies the fixed-anchor
slow-law domination estimate. The first overflowing successor remains in
scope because the update comparison does not inspect its successor flag. -/
theorem enabled_preOverflow_slowMarginal_domination
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (henabled : round.enabled = true) (hnotOverflow : state.overflow = false)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    proposalProbability p q state round = hazard p q ∧
      (1 - hazard p q) * recordedSlowMass p q state anchor hanchor U ≤
        recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U := by
  exact ⟨proposalProbability_active p q state round hnotOverflow henabled,
    step_slowMarginal_domination p q state round anchor hanchor U⟩

/-- On an active round, the Bernoulli refresh kernel averaged against the
actual current slow-set PMF is exactly the actual next slow-set PMF. -/
theorem active_step_refresh_law
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    :
    (recordedSlowPMF p q state anchor hanchor).bind
      (fun U => refreshKernel (hazard p q) (hazard_pos p q).le
        (le_trans (hazard_le_quarter p q hcap) (by norm_num))
        (residualPMF p q state round anchor hanchor) U) =
      recordedSlowPMF p q (RecordedQueueRun.step q state round) anchor hanchor := by
  classical
  apply PMF.ext
  intro U
  rw [refreshKernel_bind_apply]
  rw [recordedSlowPMF_apply, residualPMF_apply, recordedSlowPMF_apply]
  have hh : 0 ≤ 1 - hazard p q := by
    have hquarter := hazard_le_quarter p q hcap
    linarith
  have hnow : 0 ≤ recordedSlowMass p q state anchor hanchor U :=
    (recordedSlowMass_pos p q state anchor hanchor U).le
  have hrho : 0 ≤ residualMass p q state round anchor hanchor U :=
    residualMass_nonneg p q state round anchor hanchor U
  have hterm₁ : 0 ≤ (1 - hazard p q) *
      recordedSlowMass p q state anchor hanchor U := mul_nonneg hh hnow
  have hterm₂ : 0 ≤ hazard p q *
      residualMass p q state round anchor hanchor U :=
    mul_nonneg (hazard_pos p q).le hrho
  rw [← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_mul (hazard_pos p q).le]
  rw [← ENNReal.ofReal_add hterm₁ hterm₂]
  have hreal :
      (1 - hazard p q) * recordedSlowMass p q state anchor hanchor U +
          hazard p q * residualMass p q state round anchor hanchor U =
        recordedSlowMass p q (RecordedQueueRun.step q state round) anchor hanchor U := by
    rw [add_comm]
    exact residualMass_characterization p q state round anchor hanchor U
  rw [hreal]

/-- The complete refresh law for every actual step. Enabled rounds with a clear
pre-state use the residual proposal; disabled and post-overflow rounds use the
zero-proposal identity kernel and preserve the actual law. -/
theorem recorded_step_refresh_law
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    (recordedSlowPMF p q state anchor hanchor).bind
      (fun U => recordedRefreshKernel p q state round anchor hanchor hcap U) =
      recordedSlowPMF p q (RecordedQueueRun.step q state round) anchor hanchor := by
  classical
  by_cases hactive : state.overflow = false ∧ round.enabled = true
  · have hprob := proposalProbability_active p q state round hactive.1 hactive.2
    have hkernel :
        (fun U => recordedRefreshKernel p q state round anchor hanchor hcap U) =
          (fun U => refreshKernel (hazard p q) (hazard_pos p q).le
            (le_trans (hazard_le_quarter p q hcap) (by norm_num))
            (residualPMF p q state round anchor hanchor) U) := by
      funext U
      simp [recordedRefreshKernel, hprob]
    rw [hkernel]
    exact active_step_refresh_law p q state round anchor hanchor hcap
  · have hinactive : round.enabled = false ∨ state.overflow = true := by
      rcases not_and_or.mp hactive with hstate | hround
      · right
        cases hs : state.overflow with
        | false => exact (hstate hs).elim
        | true => rfl
      · left
        cases hr : round.enabled with
        | false => rfl
        | true => exact (hround hr).elim
    have hkernel :
        (fun U => recordedRefreshKernel p q state round anchor hanchor hcap U) =
          (fun U => PMF.pure U) := by
      funext U
      exact recordedRefreshKernel_eq_pure_of_inactive p q state round anchor hanchor
        hcap hinactive U
    rw [hkernel, PMF.bind_pure]
    exact (recordedSlowPMF_step_eq_of_inactive p q state round anchor hanchor hinactive).symm

/-- Appending a suffix after a finite run is the same as executing that suffix
from the run's final state. -/
theorem execute_append (q : RecordedQueueRun.Parameters)
    (rounds suffix : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) :
    RecordedQueueRun.execute q (rounds ++ suffix) state =
      RecordedQueueRun.execute q suffix (RecordedQueueRun.execute q rounds state) := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih (RecordedQueueRun.step q state round)

/-- A finite run extended by one actual round is exactly its actual next step. -/
theorem run_append_singleton (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K)) (round : RecordedQueueRun.RoundInput K) :
    RecordedQueueRun.run q (rounds ++ [round]) =
      RecordedQueueRun.step q (RecordedQueueRun.run q rounds) round := by
  change RecordedQueueRun.execute q (rounds ++ [round])
      (RecordedQueueRun.initialState K) = _
  rw [execute_append]
  simp [RecordedQueueRun.execute, RecordedQueueRun.run]

/-- Finite-prefix specialization of fixed-step slow-law domination, expressed
using the actual `run` and its one-round extension. -/
theorem run_append_singleton_slowMarginal_domination
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    (1 - hazard p q) *
        recordedSlowMass p q (RecordedQueueRun.run q rounds) anchor hanchor U ≤
      recordedSlowMass p q (RecordedQueueRun.run q (rounds ++ [round])) anchor hanchor U := by
  rw [run_append_singleton]
  exact step_slowMarginal_domination p q (RecordedQueueRun.run q rounds) round
    anchor hanchor U

/-- Finite-prefix specialization of the exact PMF refresh identity. -/
theorem run_append_singleton_refresh_law
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    (recordedSlowPMF p q (RecordedQueueRun.run q rounds) anchor hanchor).bind
      (fun U => recordedRefreshKernel p q (RecordedQueueRun.run q rounds) round
        anchor hanchor hcap U) =
      recordedSlowPMF p q (RecordedQueueRun.run q (rounds ++ [round])) anchor hanchor := by
  rw [run_append_singleton]
  exact recorded_step_refresh_law p q (RecordedQueueRun.run q rounds) round
    anchor hanchor hcap





end Bandits.Support.RecordedSlowRefresh

end
