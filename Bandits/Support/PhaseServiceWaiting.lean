/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Process.Filtration

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite-horizon parallel-service waiting bound

The source is `sources/zip4/manuscript/05_binary_transport.tex:180-240`.
The round index `t : ℕ` below denotes manuscript round `t + 1`. Thus its
predictable quantities use `F_(t+1)` and its binary service observation is
measurable at the end-of-round history `F_(t+2)`. This module proves the
generic conditional-service waiting bound, its source exponential-process
argument, and the resulting unconditional phase-charge moment and expectation
bounds. It does not establish that any particular protocol has the service,
quota, stopping, or nesting premises, or provide a conditional estimate at a
random phase start with respect to its stopped σ-algebra.
-/

@[expose] public section

namespace Bandits.Support.PhaseServiceWaiting

open MeasureTheory
open scoped BigOperators MeasureTheory

/-- A finite-valued stopping time for the pre-round filtration. -/
def IsPreRoundStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›) (τ : Ω → ℕ) : Prop :=
  ∀ n, MeasurableSet[ℱ n] {ω | τ ω ≤ n}

/-- The source constant `1 - exp(-1)` in the exponential process. -/
noncomputable def kappa : ℝ := 1 - Real.exp (-1)

/-- The predictable indicator that task `i` is unresolved at the start of
source round `t + 1`. -/
noncomputable def J {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ) (ω : Ω) : ℝ :=
  Set.indicator {ω | i ∈ P t ω} (fun _ => (1 : ℝ)) ω

/-- The source binary observation, represented as a real-valued zero-one
random variable so that its conditional expectation is the ordinary real
conditional expectation from Mathlib. -/
def observation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (X : Fin d → ℕ → Ω → Bool) (i : Fin d) (t : ℕ) (ω : Ω) : ℝ :=
  if X i t ω then 1 else 0

/-- The literal source count through the first `v` rounds. -/
noncomputable def N {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (i : Fin d) (v : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.range v, if i ∈ P t ω ∧ X i t ω then 1 else 0

/-- The literal predictable service charge for task `i` through the first
`v` rounds. -/
noncomputable def G {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (i : Fin d) (v : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range v, J P i t ω * w t ω

/-- The source phase-active indicator. The phase indices `sigma` and `theta`
are manuscript round numbers, and `P` is empty outside `[sigma, theta)`. -/
noncomputable def A {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Set.indicator {ω | sigma ω ≤ t + 1 ∧ t + 1 < theta ω ∧ (P t ω).Nonempty}
    (w t) ω

/-- The literal total phase charge through the first `v` rounds. -/
noncomputable def totalCharge {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ) (v : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range v, A P sigma theta w t ω

/-- The maximum task charge, defined only for a positive finite task count. -/
noncomputable def maxTaskCharge {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (hd : 0 < d) (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (v : ℕ) (ω : Ω) : ℝ :=
  Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩)
    (fun i => G P w i v ω)

/-- The source nonnegative exponential process, using the literal `G` and
`N` sums above. -/
noncomputable def Z {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (i : Fin d) (v : ℕ) (ω : Ω) : ℝ :=
  Real.exp (kappa * a * G P w i v ω - (N P X i v ω : ℝ))

@[simp]
theorem J_of_mem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ) (ω : Ω)
    (h : i ∈ P t ω) : J P i t ω = 1 := by
  simp [J, h]

@[simp]
theorem J_of_not_mem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ) (ω : Ω)
    (h : i ∉ P t ω) : J P i t ω = 0 := by
  simp [J, h]

/-- The unresolved-task indicator is pointwise zero or one. -/
theorem J_mem_unit_interval {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ) (ω : Ω) :
    J P i t ω ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : i ∈ P t ω <;> simp [J, h]

/-- Predictability of each unresolved-task indicator follows from
pre-round measurability of the task set. -/
theorem J_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (ℱ : MeasureTheory.Filtration ℕ m)
    {d : ℕ} (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ)
    (hP : MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω}) :
    StronglyMeasurable[ℱ (t + 1)] (J P i t) := by
  unfold J
  exact stronglyMeasurable_const.indicator hP

/-- Multiplying `J` by a function is the indicator of that function on the
unresolved-task event. -/
theorem J_mul_eq_indicator {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (i : Fin d) (t : ℕ) (f : Ω → ℝ) :
    (fun ω => J P i t ω * f ω) = ({ω | i ∈ P t ω}.indicator f) := by
  funext ω
  by_cases h : i ∈ P t ω <;> simp [J, h]

/-- The phase-active charge is predictable from the two stopping rules, the
pre-round task-set measurability, and the predictable weight. -/
theorem A_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (ℱ : MeasureTheory.Filtration ℕ m)
    {d T : ℕ} (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (t : ℕ) (ht : t < T) :
    StronglyMeasurable[ℱ (t + 1)] (A P sigma theta w t) := by
  have hne : MeasurableSet[ℱ (t + 1)] {ω | (P t ω).Nonempty} := by
    have heq : {ω | (P t ω).Nonempty} = ⋃ i : Fin d, {ω | i ∈ P t ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.Nonempty]
    rw [heq]
    exact MeasurableSet.iUnion fun i => hP i t ht
  have hthetaLt : MeasurableSet[ℱ (t + 1)] {ω | t + 1 < theta ω} := by
    have h := (htheta (t + 1)).compl
    convert h using 1
    ext ω
    simp
  have hphase : MeasurableSet[ℱ (t + 1)]
      {ω | sigma ω ≤ t + 1 ∧ t + 1 < theta ω ∧ (P t ω).Nonempty} := by
    convert ((hsigma (t + 1)).inter hthetaLt).inter hne using 1
    ext ω
    simp [and_assoc]
  unfold A
  exact (hw t ht).indicator hphase

@[simp]
theorem N_succ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (i : Fin d) (v : ℕ) (ω : Ω) :
    N P X i (v + 1) ω = N P X i v ω +
      if i ∈ P v ω ∧ X i v ω then 1 else 0 := by
  change (∑ t ∈ Finset.range (v + 1),
      if i ∈ P t ω ∧ X i t ω then 1 else 0) = _
  rw [Finset.sum_range_succ]
  rfl

/-- Casting the natural processed-observation count to `ℝ` recovers exactly
the source sum of the predictable indicator times the binary observation. -/
theorem N_cast_eq_source_sum {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (i : Fin d) (v : ℕ) (ω : Ω) :
    (N P X i v ω : ℝ) =
      ∑ t ∈ Finset.range v, J P i t ω * observation X i t ω := by
  induction v with
  | zero => simp [N]
  | succ v ih =>
      rw [N_succ, Nat.cast_add, ih, Finset.sum_range_succ]
      by_cases hm : i ∈ P v ω
      · cases hx : X i v ω
        · simp [hm, hx, observation]
        · simp [hm, hx, observation]
      · simp [hm, observation]

@[simp]
theorem G_succ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (i : Fin d) (v : ℕ) (ω : Ω) :
    G P w i (v + 1) ω = G P w i v ω + J P i v ω * w v ω := by
  simp [G, Finset.sum_range_succ]

/-- The predictable charge is nonnegative and bounded by `T K` on every
prefix of the source horizon. -/
theorem G_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {d T K : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (hw : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (i : Fin d) (v : ℕ) (hv : v ≤ T) (ω : Ω) :
    G P w i v ω ∈ Set.Icc (0 : ℝ) ((T : ℝ) * (K : ℝ)) := by
  have hnonneg : ∀ t ∈ Finset.range v, 0 ≤ J P i t ω * w t ω := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    exact mul_nonneg (J_mem_unit_interval P i t ω).1
      (hw t (lt_of_lt_of_le ht' hv) ω).1
  have hterm_le : ∀ t ∈ Finset.range v, J P i t ω * w t ω ≤ (K : ℝ) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hJ := J_mem_unit_interval P i t ω
    have hw' := hw t (lt_of_lt_of_le ht' hv) ω
    calc
      J P i t ω * w t ω ≤ 1 * w t ω :=
        mul_le_mul_of_nonneg_right hJ.2 hw'.1
      _ = w t ω := one_mul _
      _ ≤ (K : ℝ) := hw'.2
  constructor
  · exact Finset.sum_nonneg hnonneg
  · calc
      G P w i v ω ≤ ∑ t ∈ Finset.range v, (K : ℝ) :=
        Finset.sum_le_sum hterm_le
      _ = (v : ℝ) * (K : ℝ) := by simp
      _ ≤ (T : ℝ) * (K : ℝ) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (Nat.cast_nonneg K)

/-- Measurability of the literal predictable task charge at the pre-round
history following its last included round. -/
theorem G_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {d T : ℕ}
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (i : Fin d) (v : ℕ) (hv : v ≤ T) :
    StronglyMeasurable[ℱ (v + 1)] (G P w i v) := by
  unfold G
  apply Finset.stronglyMeasurable_fun_sum
  intro t ht
  have htrange := Finset.mem_range.mp ht
  have hlt : t < T := lt_of_lt_of_le htrange hv
  have hJ := (J_stronglyMeasurable ℱ P i t (hP i t hlt)).mono
    (ℱ.mono (by omega : t + 1 ≤ v + 1))
  have hw' := (hw t hlt).mono (ℱ.mono (by omega : t + 1 ≤ v + 1))
  exact hJ.mul hw'

/-- The literal exponential process is measurable at the end of its current
prefix, since its observation history ends at `F_(v+1)`. -/
theorem Z_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {d T : ℕ}
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hX : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (i : Fin d) (v : ℕ) (hv : v ≤ T) :
    StronglyMeasurable[ℱ (v + 1)] (Z P X w a i v) := by
  have hG : StronglyMeasurable[ℱ (v + 1)] (G P w i v) := by
    unfold G
    apply Finset.stronglyMeasurable_fun_sum
    intro t ht
    have htrange := Finset.mem_range.mp ht
    have hlt : t < T := lt_of_lt_of_le htrange hv
    have hJ := (J_stronglyMeasurable ℱ P i t (hP i t hlt)).mono
      (ℱ.mono (by omega : t + 1 ≤ v + 1))
    have hw' := (hw t hlt).mono (ℱ.mono (by omega : t + 1 ≤ v + 1))
    exact hJ.mul hw'
  have hNsrc : StronglyMeasurable[ℱ (v + 1)]
      (fun ω => ∑ t ∈ Finset.range v,
        J P i t ω * observation X i t ω) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro t ht
    have htrange := Finset.mem_range.mp ht
    have hlt : t < T := lt_of_lt_of_le htrange hv
    have hJ := (J_stronglyMeasurable ℱ P i t (hP i t hlt)).mono
      (ℱ.mono (by omega : t + 1 ≤ v + 1))
    have hX' := (hX i t hlt).mono (ℱ.mono (by omega : t + 2 ≤ v + 1))
    exact hJ.mul hX'
  have hN : StronglyMeasurable[ℱ (v + 1)]
      (fun ω => (N P X i v ω : ℝ)) := by
    have heq : (fun ω => (N P X i v ω : ℝ)) =
        (fun ω => ∑ t ∈ Finset.range v,
          J P i t ω * observation X i t ω) := by
      funext ω
      exact N_cast_eq_source_sum P X i v ω
    rw [heq]
    exact hNsrc
  have harg : StronglyMeasurable[ℱ (v + 1)]
      (fun ω => kappa * a * G P w i v ω - (N P X i v ω : ℝ)) :=
    (stronglyMeasurable_const.mul hG).sub hN
  unfold Z
  exact Real.continuous_exp.comp_stronglyMeasurable harg

/-- Positivity of the source exponential constant. -/
theorem kappa_pos : 0 < kappa := by
  unfold kappa
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

/-- The source exponential constant is at most one. -/
theorem kappa_le_one : kappa ≤ 1 := by
  unfold kappa
  have h := Real.exp_pos (-1)
  linarith

/-- A pathwise integrability bound for the source exponential process. -/
theorem Z_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {d T K : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hw : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (i : Fin d) (v : ℕ) (hv : v ≤ T) (ω : Ω) :
    Z P X w a i v ω ∈ Set.Icc (0 : ℝ) (Real.exp (a * (T : ℝ) * (K : ℝ))) := by
  have hG := G_mem_Icc P w hw i v hv ω
  have hNnonneg : 0 ≤ (N P X i v ω : ℝ) := Nat.cast_nonneg _
  have hexpArg :
      kappa * a * G P w i v ω - (N P X i v ω : ℝ) ≤
        a * (T : ℝ) * (K : ℝ) := by
    have hmul : kappa * a * G P w i v ω ≤ a * G P w i v ω := by
      calc
        kappa * a * G P w i v ω = kappa * (a * G P w i v ω) := by ring
        _ ≤ 1 * (a * G P w i v ω) :=
          mul_le_mul_of_nonneg_right kappa_le_one (mul_nonneg ha.le hG.1)
        _ = a * G P w i v ω := one_mul _
    have hGupper : a * G P w i v ω ≤ a * ((T : ℝ) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hG.2 ha.le
    nlinarith [hmul, hGupper, hNnonneg]
  constructor
  · exact (Real.exp_pos _).le
  · change Real.exp (kappa * a * G P w i v ω - (N P X i v ω : ℝ)) ≤ _
    exact Real.exp_le_exp.mpr hexpArg

/-- The source exponential process is integrable at every bounded horizon
prefix. -/
theorem Z_integrable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (i : Fin d) (v : ℕ) (hv : v ≤ T) : Integrable (Z P X w a i v) μ := by
  have hsm := (Z_stronglyMeasurable ℱ P X w a hP hw_meas hX_meas i v hv).mono
    (ℱ.le (v + 1))
  apply Integrable.of_mem_Icc 0 (Real.exp (a * (T : ℝ) * (K : ℝ))) hsm.aemeasurable
  exact ae_of_all μ fun ω => Z_mem_Icc P X w a ha hw_bound i v hv ω

@[simp]
theorem totalCharge_succ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ) (v : ℕ) (ω : Ω) :
    totalCharge P sigma theta w (v + 1) ω =
      totalCharge P sigma theta w v ω + A P sigma theta w v ω := by
  simp [totalCharge, Finset.sum_range_succ]

/-- If a task set is empty outside the phase interval, the source phase charge
at one round is exactly the predictable weight when the unresolved set is
nonempty. -/
theorem A_eq_ite_nonempty {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ)
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (t : ℕ) (ht : t < T) (ω : Ω) :
    A P sigma theta w t ω =
      if (P t ω).Nonempty then w t ω else 0 := by
  by_cases hne : (P t ω).Nonempty
  · simp [A, hne, hphase t ht ω hne]
  · simp [A, hne]

/-- Under within-phase nested unresolved sets, the total phase charge is the
maximum of the literal task charges. The nesting premise applies only when
the earlier index is at or after `sigma` and the later index is before
`theta`. The phase-support premise includes the terminal failure round because
its source condition is `t + 1 < theta`. -/
theorem totalCharge_eq_maxTaskCharge {Ω : Type*} [MeasurableSpace Ω]
    {d T : ℕ} (hd : 0 < d)
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ)
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_nonneg : ∀ t, t < T → ∀ ω, 0 ≤ w t ω)
    (ω : Ω) :
    totalCharge P sigma theta w T ω = maxTaskCharge hd P w T ω := by
  classical
  let active : Finset ℕ := (Finset.range T).filter fun t => (P t ω).Nonempty
  have hFinNonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
  have hAeq : ∀ t, t < T →
      A P sigma theta w t ω = if (P t ω).Nonempty then w t ω else 0 := by
    intro t ht
    exact A_eq_ite_nonempty P sigma theta w hphase t ht ω
  change totalCharge P sigma theta w T ω =
    Finset.univ.sup' hFinNonempty (fun i => G P w i T ω)
  by_cases hactive : active.Nonempty
  · let last := active.max' hactive
    have hlast_mem : last ∈ active := Finset.max'_mem active hactive
    have hlast_lt : last < T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hlast_mem).1
    have hlast_nonempty : (P last ω).Nonempty :=
      (Finset.mem_filter.mp hlast_mem).2
    obtain ⟨i, hi_last⟩ := hlast_nonempty
    have hactive_iff : ∀ t, t < T →
        ((P t ω).Nonempty ↔ i ∈ P t ω) := by
      intro t ht
      constructor
      · intro htne
        have ht_mem : t ∈ active := by
          simp [active, ht, htne]
        have ht_le : t ≤ last := Finset.le_max' active t ht_mem
        have hphase_t := hphase t ht ω htne
        have hphase_last := hphase last hlast_lt ω ⟨i, hi_last⟩
        exact hnested t last ht_le hlast_lt ω hphase_t.1 hphase_last.2 hi_last
      · intro hmem
        exact ⟨i, hmem⟩
    have hterm_i : ∀ t, t < T →
        A P sigma theta w t ω = J P i t ω * w t ω := by
      intro t ht
      rw [hAeq t ht]
      by_cases hmem : i ∈ P t ω
      · have hne : (P t ω).Nonempty := hactive_iff t ht |>.2 hmem
        simp [hne, J_of_mem P i t ω hmem]
      · have hne : ¬(P t ω).Nonempty := by
          intro hne
          exact hmem (hactive_iff t ht |>.1 hne)
        simp [hne, J_of_not_mem P i t ω hmem]
    have htotal_i : totalCharge P sigma theta w T ω = G P w i T ω := by
      change (∑ t ∈ Finset.range T, A P sigma theta w t ω) = _
      apply Finset.sum_congr rfl
      intro t ht
      exact hterm_i t (Finset.mem_range.mp ht)
    have htask_le : ∀ j, G P w j T ω ≤ totalCharge P sigma theta w T ω := by
      intro j
      change (∑ t ∈ Finset.range T, J P j t ω * w t ω) ≤ _
      apply Finset.sum_le_sum
      intro t ht
      have htlt := Finset.mem_range.mp ht
      rw [hAeq t htlt]
      by_cases hne : (P t ω).Nonempty
      · by_cases hmem : j ∈ P t ω
        · simp [hne, J_of_mem P j t ω hmem]
        · rw [J_of_not_mem P j t ω hmem]
          simp [hne]
          exact hw_nonneg t htlt ω
      · have hnot : j ∉ P t ω := by
          intro hj
          exact hne ⟨j, hj⟩
        rw [J_of_not_mem P j t ω hnot]
        simp [hne]
    have hsup_le :
        Finset.univ.sup' hFinNonempty (fun j => G P w j T ω) ≤
          totalCharge P sigma theta w T ω :=
      Finset.sup'_le hFinNonempty _ fun j _ => htask_le j
    have htotal_le_sup : totalCharge P sigma theta w T ω ≤
        Finset.univ.sup' hFinNonempty (fun j => G P w j T ω) := by
      rw [htotal_i]
      exact Finset.le_sup' (f := fun j => G P w j T ω)
        (Finset.mem_univ i)
    exact le_antisymm htotal_le_sup hsup_le
  · have hnever : ∀ t, t < T → ¬(P t ω).Nonempty := by
      intro t ht hne
      exact hactive ⟨t, by simp [active, ht, hne]⟩
    have htotal_zero : totalCharge P sigma theta w T ω = 0 := by
      change (∑ t ∈ Finset.range T, A P sigma theta w t ω) = 0
      apply Finset.sum_eq_zero
      intro t ht
      rw [hAeq t (Finset.mem_range.mp ht)]
      simp [hnever t (Finset.mem_range.mp ht)]
    have htask_zero : ∀ i, G P w i T ω = 0 := by
      intro i
      change (∑ t ∈ Finset.range T, J P i t ω * w t ω) = 0
      apply Finset.sum_eq_zero
      intro t ht
      have hnot : i ∉ P t ω := by
        intro hi
        exact hnever t (Finset.mem_range.mp ht) ⟨i, hi⟩
      simp [J_of_not_mem P i t ω hnot]
    have hsup_zero :
        Finset.univ.sup' hFinNonempty (fun i => G P w i T ω) = 0 :=
      Finset.sup'_eq_of_forall hFinNonempty (fun i => G P w i T ω)
        (fun i _ => htask_zero i)
    rw [htotal_zero, hsup_zero]

/-- A binary source observation is always between zero and one. -/
theorem observation_mem_unit_interval {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (X : Fin d → ℕ → Ω → Bool)
    (i : Fin d) (t : ℕ) (ω : Ω) :
    observation X i t ω ∈ Set.Icc (0 : ℝ) 1 := by
  cases h : X i t ω <;> simp [observation, h]

/-- The quota and binary-observation premises cap every task's processed
count pathwise at `q`. -/
theorem N_le_quota {Ω : Type*} [MeasurableSpace Ω] {d T q : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (i : Fin d) (v : ℕ) (hv : v ≤ T) (ω : Ω) :
    N P X i v ω ≤ q := by
  induction v with
  | zero => simp [N]
  | succ v ih =>
      have hvlt : v < T := by omega
      have hprev := ih (by omega)
      rw [N_succ]
      by_cases hmem : i ∈ P v ω
      · have hquota' := hquota i v hvlt ω hmem
        cases hXv : X i v ω <;> simp [hmem, hXv] at *
        · exact hprev
        · exact Nat.succ_le_of_lt hquota'
      · simp [hmem]
        exact hprev

/-- A lower bound on the genuine conditional expectation on the unresolved
event yields the corresponding one-round expectation inequality. -/
theorem conditional_service_integral {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m' : MeasurableSpace Ω) (hm' : m' ≤ m)
    (x w : Ω → ℝ) (S : Set Ω) (hS : MeasurableSet[m'] S)
    (a : ℝ) (hx : Integrable x μ) (hw : Integrable w μ)
    (hservice : ∀ᵐ ω ∂μ, ω ∈ S → a * w ω ≤ μ[x | m'] ω) :
    a * (∫ ω in S, w ω ∂μ) ≤ ∫ ω in S, x ω ∂μ := by
  have hserviceRestrict :
      ∀ᵐ ω ∂μ.restrict S, a * w ω ≤ μ[x | m'] ω :=
    (ae_restrict_iff' (hm' S hS)).2 hservice
  have hmono :
      ∫ ω in S, (a * w ω) ∂μ ≤ ∫ ω in S, (μ[x | m']) ω ∂μ :=
    setIntegral_mono_ae_restrict (hw.const_mul a).integrableOn
      integrable_condExp.integrableOn hserviceRestrict
  calc
    a * (∫ ω in S, w ω ∂μ) = ∫ ω in S, (a * w ω) ∂μ := by
      rw [integral_const_mul]
    _ ≤ ∫ ω in S, (μ[x | m']) ω ∂μ := hmono
    _ = ∫ ω in S, x ω ∂μ := setIntegral_condExp hm' hx hS

/-- The conditional exponential of a predictable binary indicator product is
computed from the actual conditional mean of the binary observation. -/
theorem condExp_exp_neg_binary_product {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m' : MeasurableSpace Ω) (hm' : m' ≤ m)
    (J x : Ω → ℝ) (hJmeas : StronglyMeasurable[m'] J)
    (hJbinary : ∀ ω, J ω = 0 ∨ J ω = 1)
    (hxbinary : ∀ ω, x ω = 0 ∨ x ω = 1)
    (hxint : Integrable x μ) (hJxint : Integrable (fun ω => J ω * x ω) μ) :
    μ[(fun ω => Real.exp (-(J ω * x ω))) | m'] =ᵐ[μ]
      fun ω => 1 - kappa * J ω * μ[x | m'] ω := by
  let D : Ω → ℝ := fun ω => J ω * x ω
  have hDint : Integrable D μ := hJxint
  have hscaleInt : Integrable (fun ω => kappa * D ω) μ := hDint.const_mul kappa
  have hsub := condExp_sub (integrable_const (1 : ℝ)) hscaleInt m'
  have hsmul :
      μ[(fun ω => kappa * D ω) | m'] =ᵐ[μ]
        fun ω => kappa * μ[D | m'] ω := by
    convert (condExp_smul (𝕜 := ℝ) kappa D m') using 1
  have hD_eq : D = J * x := by
    funext ω
    simp [D, Pi.mul_apply]
  have hmulProduct :=
    condExp_mul_of_stronglyMeasurable_left hJmeas hDint hxint
  have hmul : μ[D | m'] =ᵐ[μ] J * μ[x | m'] := by
    calc
      μ[D | m'] =ᵐ[μ] μ[J * x | m'] :=
        condExp_congr_ae (μ := μ) (m := m') (ae_of_all μ fun ω => congrFun hD_eq ω)
      _ =ᵐ[μ] J * μ[x | m'] := hmulProduct
  have hlinear :
      μ[(fun ω => 1 - kappa * D ω) | m'] =ᵐ[μ]
        fun ω => 1 - kappa * J ω * μ[x | m'] ω := by
    filter_upwards [hsub, hsmul, hmul] with ω hsubω hsmulω hmulω
    have hconstω := congrFun (condExp_const (μ := μ) hm' (1 : ℝ)) ω
    calc
      μ[(fun ω => 1 - kappa * D ω) | m'] ω =
          μ[(fun _ : Ω => 1) | m'] ω - μ[(fun ω => kappa * D ω) | m'] ω := hsubω
      _ = 1 - kappa * μ[D | m'] ω := by rw [hconstω, hsmulω]
      _ = 1 - kappa * J ω * μ[x | m'] ω := by
        change μ[D | m'] ω = J ω * μ[x | m'] ω at hmulω
        rw [hmulω]
        ring
  have hpoint :
      (fun ω => Real.exp (-(J ω * x ω))) = fun ω => 1 - kappa * D ω := by
    funext ω
    rcases hJbinary ω with hJ0 | hJ1
    · simp [D, kappa, hJ0]
    · rcases hxbinary ω with hx0 | hx1
      · simp [D, kappa, hJ1, hx0]
      · simp [D, kappa, hJ1, hx1]
  exact (condExp_congr_ae (μ := μ) (m := m') (ae_of_all μ fun ω => congrFun hpoint ω)).trans
    hlinear

/-- The source exponential process factors over one round into its previous
value, a predictable exponential, and the binary observation exponential. -/
theorem Z_succ_factor {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (i : Fin d) (t : ℕ) (ω : Ω) :
    Z P X w a i (t + 1) ω =
      Z P X w a i t ω * Real.exp (kappa * a * J P i t ω * w t ω) *
        Real.exp (-(J P i t ω * observation X i t ω)) := by
  change Real.exp (kappa * a * G P w i (t + 1) ω -
      (N P X i (t + 1) ω : ℝ)) = _
  rw [G_succ, N_succ, Nat.cast_add]
  have hinc :
      (if i ∈ P t ω ∧ X i t ω then (1 : ℕ) else 0 : ℕ) =
        (if i ∈ P t ω ∧ X i t ω then 1 else 0) := rfl
  have hcast :
      ((if i ∈ P t ω ∧ X i t ω then (1 : ℕ) else 0 : ℕ) : ℝ) =
        J P i t ω * observation X i t ω := by
    by_cases hm : i ∈ P t ω
    · cases hx : X i t ω <;> simp [hm, hx, J, observation]
    · simp [hm, J, observation]
  rw [hcast]
  calc
    Real.exp (kappa * a * (G P w i t ω + J P i t ω * w t ω) -
        ((N P X i t ω : ℝ) + J P i t ω * observation X i t ω)) =
        Real.exp ((kappa * a * G P w i t ω - (N P X i t ω : ℝ)) +
          (kappa * a * J P i t ω * w t ω) +
          (-(J P i t ω * observation X i t ω))) := by
      congr 1
      ring
    _ = Real.exp (kappa * a * G P w i t ω - (N P X i t ω : ℝ)) *
          Real.exp (kappa * a * J P i t ω * w t ω) *
            Real.exp (-(J P i t ω * observation X i t ω)) := by
      rw [Real.exp_add, Real.exp_add]
    _ = _ := rfl

/-- The source process is a nonnegative supermartingale under the actual
conditional service-mean premise. -/
theorem Z_supermartingale_step {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (i : Fin d) (t : ℕ) (ht : t < T) :
    μ[(fun ω => Z P X w a i (t + 1) ω) | ℱ (t + 1)] ≤ᵐ[μ]
      fun ω => Z P X w a i t ω := by
  let m' := ℱ (t + 1)
  let j : Ω → ℝ := J P i t
  let x : Ω → ℝ := observation X i t
  let y : Ω → ℝ := fun ω => Real.exp (-(j ω * x ω))
  let c : Ω → ℝ := fun ω =>
    Z P X w a i t ω * Real.exp (kappa * a * j ω * w t ω)
  have hjmeas : StronglyMeasurable[m'] j :=
    J_stronglyMeasurable ℱ P i t (hP i t ht)
  have hwmeas' : StronglyMeasurable[m'] (w t) := hw_meas t ht
  have hjbinary : ∀ ω, j ω = 0 ∨ j ω = 1 := by
    intro ω
    by_cases hmem : i ∈ P t ω
    · right
      exact J_of_mem P i t ω hmem
    · left
      exact J_of_not_mem P i t ω hmem
  have hxbinary : ∀ ω, x ω = 0 ∨ x ω = 1 := by
    intro ω
    cases hx : X i t ω <;> simp [x, observation, hx]
  have hxint : Integrable x μ := by
    have hxsm : StronglyMeasurable[m] x :=
      (hX_meas i t ht).mono (ℱ.le (t + 2))
    apply Integrable.of_mem_Icc (μ := μ) 0 1 hxsm.aemeasurable
    exact ae_of_all μ fun ω => observation_mem_unit_interval X i t ω
  have hjsm : StronglyMeasurable[m] j := hjmeas.mono (ℱ.le (t + 1))
  have hxsm : StronglyMeasurable[m] x :=
    (hX_meas i t ht).mono (ℱ.le (t + 2))
  have hdsm : StronglyMeasurable[m] (fun ω => j ω * x ω) := hjsm.mul hxsm
  have hjxbound : ∀ ω, j ω * x ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    rcases hjbinary ω with hj0 | hj1
    · simp [hj0]
    · rcases hxbinary ω with hx0 | hx1
      · simp [hj1, hx0]
      · simp [hj1, hx1]
  have hjxint : Integrable (fun ω => j ω * x ω) μ := by
    apply Integrable.of_mem_Icc (μ := μ) 0 1 (hdsm.aemeasurable (μ := μ))
    exact ae_of_all μ hjxbound
  have hcondIdentity := condExp_exp_neg_binary_product μ m' (ℱ.le (t + 1))
    j x hjmeas hjbinary hxbinary hxint hjxint
  have hserviceWeighted :
      ∀ᵐ ω ∂μ, kappa * a * j ω * w t ω ≤
        kappa * j ω * μ[x | m'] ω := by
    filter_upwards [hservice i t ht] with ω hsvc
    by_cases hmem : i ∈ P t ω
    · have hmul := mul_le_mul_of_nonneg_left (hsvc hmem) kappa_pos.le
      have hj : j ω = 1 := J_of_mem P i t ω hmem
      rw [hj]
      calc
        kappa * a * 1 * w t ω = kappa * (a * w t ω) := by ring
        _ ≤ kappa * μ[x | m'] ω := hmul
        _ = kappa * 1 * μ[x | m'] ω := by ring
    · have hj : j ω = 0 := J_of_not_mem P i t ω hmem
      simp [hj]
  have hcondBound :
      μ[y | m'] ≤ᵐ[μ] fun ω => Real.exp (-(kappa * a * j ω * w t ω)) := by
    filter_upwards [hcondIdentity, hserviceWeighted] with ω hce hs
    calc
      μ[y | m'] ω = 1 - kappa * j ω * μ[x | m'] ω := hce
      _ ≤ 1 - kappa * a * j ω * w t ω := by nlinarith [hs]
      _ ≤ Real.exp (-(kappa * a * j ω * w t ω)) := by
        have hexp := Real.add_one_le_exp (-(kappa * a * j ω * w t ω))
        nlinarith [hexp]
  have hZprevSm : StronglyMeasurable[m'] (Z P X w a i t) :=
    Z_stronglyMeasurable ℱ P X w a hP hw_meas hX_meas i t (by omega)
  have hjwSm : StronglyMeasurable[m'] (fun ω => j ω * w t ω) :=
    hjmeas.mul hwmeas'
  have hexpArgSm : StronglyMeasurable[m']
      (fun ω => kappa * a * j ω * w t ω) := by
    have hconst : StronglyMeasurable[m'] (fun _ : Ω => kappa * a) :=
      stronglyMeasurable_const
    have hprod := hconst.mul hjwSm
    have heq : (fun ω => kappa * a * j ω * w t ω) =
        fun ω => (kappa * a) * (j ω * w t ω) := by
      funext ω
      ring
    rw [heq]
    exact hprod
  have hfactorSm : StronglyMeasurable[m']
      (fun ω => Real.exp (kappa * a * j ω * w t ω)) :=
    Real.continuous_exp.comp_stronglyMeasurable hexpArgSm
  have hcSm : StronglyMeasurable[m'] c := hZprevSm.mul hfactorSm
  have hjwBound : ∀ ω, j ω * w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ) := by
    intro ω
    have hj := J_mem_unit_interval P i t ω
    have hw := hw_bound t ht ω
    constructor
    · exact mul_nonneg hj.1 hw.1
    · calc
        j ω * w t ω ≤ 1 * w t ω := mul_le_mul_of_nonneg_right hj.2 hw.1
        _ = w t ω := one_mul _
        _ ≤ (K : ℝ) := hw.2
  have hfactorBound : ∀ ω,
      Real.exp (kappa * a * j ω * w t ω) ≤ Real.exp (a * (K : ℝ)) := by
    intro ω
    have hjw := hjwBound ω
    have harg : kappa * a * j ω * w t ω ≤ a * (K : ℝ) := by
      calc
        kappa * a * j ω * w t ω = kappa * (a * (j ω * w t ω)) := by ring
        _ ≤ 1 * (a * (j ω * w t ω)) :=
          mul_le_mul_of_nonneg_right kappa_le_one (mul_nonneg ha.le hjw.1)
        _ = a * (j ω * w t ω) := one_mul _
        _ ≤ a * (K : ℝ) := mul_le_mul_of_nonneg_left hjw.2 ha.le
    exact Real.exp_le_exp.mpr harg
  have hcint : Integrable c μ := by
    have hcBound : ∀ ω,
        c ω ∈ Set.Icc (0 : ℝ) (Real.exp (a * ((T + 1 : ℕ) : ℝ) * (K : ℝ))) := by
      intro ω
      have hZ := Z_mem_Icc P X w a ha hw_bound i t (by omega) ω
      have hfactorPos : 0 ≤ Real.exp (kappa * a * j ω * w t ω) :=
        (Real.exp_pos _).le
      have hcUpper : c ω ≤
          Real.exp (a * (T : ℝ) * (K : ℝ)) * Real.exp (a * (K : ℝ)) :=
        mul_le_mul hZ.2 (hfactorBound ω) hfactorPos
          (Real.exp_pos _).le
      constructor
      · exact mul_nonneg hZ.1 hfactorPos
      · calc
          c ω ≤ Real.exp (a * (T : ℝ) * (K : ℝ)) * Real.exp (a * (K : ℝ)) := hcUpper
          _ = Real.exp (a * ((T + 1 : ℕ) : ℝ) * (K : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring
    apply Integrable.of_mem_Icc (μ := μ) 0 _
      (hcSm.mono (ℱ.le (t + 1))).aemeasurable
    exact ae_of_all μ hcBound
  have hySm : StronglyMeasurable[m] y := by
    dsimp [y]
    convert Real.continuous_exp.comp_stronglyMeasurable hdsm.neg using 1
  have hyBound : ∀ ω, y ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    rcases hjbinary ω with hj0 | hj1
    · simp [y, hj0]
    · rcases hxbinary ω with hx0 | hx1
      · simp [y, hj1, hx0]
      · constructor
        · exact (Real.exp_pos _).le
        · change Real.exp (-(j ω * x ω)) ≤ (1 : ℝ)
          rw [hj1, hx1]
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by norm_num)
  have hyint : Integrable y μ := by
    apply Integrable.of_mem_Icc (μ := μ) 0 1 (hySm.aemeasurable (μ := μ))
    exact ae_of_all μ hyBound
  have hfactor :
      (fun ω => Z P X w a i (t + 1) ω) = fun ω => c ω * y ω := by
    funext ω
    exact Z_succ_factor P X w a i t ω
  have hZnextInt := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound
    hX_meas i (t + 1) (by omega)
  have hcyInt : Integrable (fun ω => c ω * y ω) μ := by
    apply hZnextInt.congr
    filter_upwards with ω
    exact congrFun hfactor ω
  have hpull := condExp_mul_of_stronglyMeasurable_left hcSm hcyInt hyint
  have hceq := condExp_congr_ae (μ := μ) (m := m')
    (ae_of_all μ fun ω => congrFun hfactor ω)
  have hZprevNonneg : ∀ ω, 0 ≤ Z P X w a i t ω := fun ω => (Real.exp_pos _).le
  have hCnonneg : ∀ ω, 0 ≤ c ω := by
    intro ω
    exact mul_nonneg (hZprevNonneg ω) (Real.exp_pos _).le
  filter_upwards [hceq, hpull, hcondBound] with ω hceqω hpullω hcondω
  calc
    μ[(fun ω => Z P X w a i (t + 1) ω) | m'] ω =
        μ[(fun ω => c ω * y ω) | m'] ω := hceqω
    _ = c ω * μ[y | m'] ω := hpullω
    _ ≤ c ω * Real.exp (-(kappa * a * j ω * w t ω)) :=
      mul_le_mul_of_nonneg_left hcondω (hCnonneg ω)
    _ = Z P X w a i t ω := by
      dsimp [c, j]
      calc
        (Z P X w a i t ω * Real.exp (kappa * a * J P i t ω * w t ω)) *
            Real.exp (-(kappa * a * J P i t ω * w t ω)) =
            Z P X w a i t ω *
              (Real.exp (kappa * a * J P i t ω * w t ω) *
                Real.exp (-(kappa * a * J P i t ω * w t ω))) := by
                  rw [mul_assoc]
        _ = Z P X w a i t ω := by
          rw [← Real.exp_add]
          simp

/-- Integrating the one-round supermartingale inequalities gives the finite
horizon expectation bound for each source exponential process. -/
theorem integral_Z_le_one {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (i : Fin d) : ∫ ω, Z P X w a i T ω ∂μ ≤ 1 := by
  have hrec : ∀ v, v ≤ T → ∫ ω, Z P X w a i v ω ∂μ ≤ 1 := by
    intro v
    induction v with
    | zero =>
        intro _
        simp [Z, G, N]
    | succ v ih =>
        intro hv
        have hvlt : v < T := by omega
        have hprev := ih (by omega : v ≤ T)
        have hnextInt := Z_integrable μ ℱ P X w a ha hP hw_meas
          hw_bound hX_meas i (v + 1) (by omega)
        have hprevInt := Z_integrable μ ℱ P X w a ha hP hw_meas
          hw_bound hX_meas i v (by omega)
        have hstep := Z_supermartingale_step μ ℱ P X w a ha hP hw_meas
          hw_bound hX_meas hservice i v hvlt
        calc
          ∫ ω, Z P X w a i (v + 1) ω ∂μ =
              ∫ ω, μ[(fun ω => Z P X w a i (v + 1) ω) | ℱ (v + 1)] ω ∂μ :=
            (integral_condExp (ℱ.le (v + 1))).symm
          _ ≤ ∫ ω, Z P X w a i v ω ∂μ :=
            integral_mono_ae integrable_condExp hprevInt hstep
          _ ≤ 1 := hprev
  exact hrec T le_rfl

/-- The exponential moment of one task's predictable service charge is at
most the quota factor, by the literal source exponential supermartingale. -/
theorem integral_exp_task_charge_le_quota {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (i : Fin d) :
    ∫ ω, Real.exp (kappa * a * G P w i T ω) ∂μ ≤ Real.exp (q : ℝ) := by
  have hGsm' := G_stronglyMeasurable ℱ P w hP hw_meas i T le_rfl
  have hGsm : StronglyMeasurable[m] (G P w i T) := hGsm'.mono (ℱ.le (T + 1))
  have hargSm : StronglyMeasurable[m]
      (fun ω => kappa * a * G P w i T ω) := by
    have hconst : StronglyMeasurable[m] (fun _ : Ω => kappa * a) :=
      stronglyMeasurable_const
    have hmul := hconst.mul hGsm
    exact hmul
  have hExpSm : StronglyMeasurable[m]
      (fun ω => Real.exp (kappa * a * G P w i T ω)) :=
    Real.continuous_exp.comp_stronglyMeasurable hargSm
  have hExpIcc : ∀ ω, Real.exp (kappa * a * G P w i T ω) ∈
      Set.Icc (0 : ℝ) (Real.exp (a * (T : ℝ) * (K : ℝ))) := by
    intro ω
    have hG := G_mem_Icc P w hw_bound i T le_rfl ω
    have harg : kappa * a * G P w i T ω ≤ a * (T : ℝ) * (K : ℝ) := by
      have hmul : kappa * a * G P w i T ω ≤ a * G P w i T ω := by
        calc
          kappa * a * G P w i T ω = kappa * (a * G P w i T ω) := by ring
          _ ≤ 1 * (a * G P w i T ω) :=
            mul_le_mul_of_nonneg_right kappa_le_one (mul_nonneg ha.le hG.1)
          _ = a * G P w i T ω := one_mul _
      have hupper : a * G P w i T ω ≤ a * ((T : ℝ) * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hG.2 ha.le
      nlinarith [hmul, hupper]
    constructor
    · exact (Real.exp_pos _).le
    · exact Real.exp_le_exp.mpr harg
  have hExpInt : Integrable (fun ω => Real.exp (kappa * a * G P w i T ω)) μ := by
    apply Integrable.of_mem_Icc (μ := μ) 0 _ (hExpSm.aemeasurable (μ := μ))
    exact ae_of_all μ hExpIcc
  have hZInt := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound
    hX_meas i T le_rfl
  have hNle : ∀ ω, (N P X i T ω : ℝ) ≤ (q : ℝ) := by
    intro ω
    exact_mod_cast N_le_quota P X hquota i T le_rfl ω
  have hpoint : ∀ ω,
      Real.exp (kappa * a * G P w i T ω) ≤
        Real.exp (q : ℝ) * Z P X w a i T ω := by
    intro ω
    have hfactor : Real.exp (kappa * a * G P w i T ω) =
        Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) := by
      change Real.exp (kappa * a * G P w i T ω) =
        Real.exp (kappa * a * G P w i T ω - (N P X i T ω : ℝ)) * _
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    calc
      Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) ≤
          Z P X w a i T ω * Real.exp (q : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (hNle ω)) (Real.exp_pos _).le
      _ = Real.exp (q : ℝ) * Z P X w a i T ω := by ring
  have hZle := integral_Z_le_one μ ℱ P X w a ha hP hw_meas hw_bound
    hX_meas hservice i
  calc
    ∫ ω, Real.exp (kappa * a * G P w i T ω) ∂μ ≤
        ∫ ω, Real.exp (q : ℝ) * Z P X w a i T ω ∂μ :=
      integral_mono_ae hExpInt (hZInt.const_mul (Real.exp (q : ℝ))) <|
        ae_of_all μ hpoint
    _ = Real.exp (q : ℝ) * ∫ ω, Z P X w a i T ω ∂μ := by
      rw [integral_const_mul]
    _ ≤ Real.exp (q : ℝ) :=
      mul_le_of_le_one_right (Real.exp_pos _).le hZle

/-- Integrating the literal predictable task charge is the finite sum of its
integrals over the measurable unresolved-task events. -/
theorem integral_G_eq_setIntegral_sum {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω)
    {d T : ℕ} (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (i : Fin d)
    (hP : ∀ t, t < T → MeasurableSet[m] {ω | i ∈ P t ω})
    (hw : ∀ t, t < T → Integrable (w t) μ) :
    ∫ ω, G P w i T ω ∂μ =
      ∑ t ∈ Finset.range T, ∫ ω in {ω | i ∈ P t ω}, w t ω ∂μ := by
  change ∫ ω, ∑ t ∈ Finset.range T, J P i t ω * w t ω ∂μ = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [J_mul_eq_indicator, integral_indicator (hP t (Finset.mem_range.mp ht))]
  · intro t ht
    rw [J_mul_eq_indicator]
    exact (hw t (Finset.mem_range.mp ht)).indicator (hP t (Finset.mem_range.mp ht))

/-- The real expectation of the processed count is the sum of observation
integrals over the unresolved-task events. -/
theorem integral_N_eq_setIntegral_sum {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω)
    {d T : ℕ} (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (i : Fin d)
    (hP : ∀ t, t < T → MeasurableSet[m] {ω | i ∈ P t ω})
    (hX : ∀ t, t < T → Integrable (observation X i t) μ) :
    ∫ ω, (N P X i T ω : ℝ) ∂μ =
      ∑ t ∈ Finset.range T,
        ∫ ω in {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
  calc
    ∫ ω, (N P X i T ω : ℝ) ∂μ =
        ∫ ω, ∑ t ∈ Finset.range T, J P i t ω * observation X i t ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact N_cast_eq_source_sum P X i T ω
    _ = ∑ t ∈ Finset.range T,
          ∫ ω, J P i t ω * observation X i t ω ∂μ := by
      rw [integral_finsetSum]
      intro t ht
      rw [J_mul_eq_indicator]
      exact (hX t (Finset.mem_range.mp ht)).indicator
        (hP t (Finset.mem_range.mp ht))
    _ = ∑ t ∈ Finset.range T,
          ∫ ω in {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [J_mul_eq_indicator, integral_indicator (hP t (Finset.mem_range.mp ht))]

/-- The individual-task charge bound from conditional service means and the
source observation quota. -/
theorem task_charge_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (a : ℝ) (ha : 0 < a)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ)
    (hP : ∀ i t, t < T → MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω, w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (i : Fin d) : ∫ ω, G P w i T ω ∂μ ≤ (q : ℝ) / a := by
  have hw_int : ∀ t, t < T → Integrable (w t) μ := by
    intro t ht
    apply Integrable.of_mem_Icc 0 (K : ℝ)
      ((hw_meas t ht).mono (ℱ.le (t + 1))).aemeasurable
    exact ae_of_all μ fun ω => hw_bound t ht ω
  have hobs_int : ∀ t, t < T → Integrable (observation X i t) μ := by
    intro t ht
    apply Integrable.of_mem_Icc 0 1
      ((hX_meas i t ht).mono (ℱ.le (t + 2))).aemeasurable
    exact ae_of_all μ fun ω => observation_mem_unit_interval X i t ω
  have hG_eq := integral_G_eq_setIntegral_sum μ P w i
    (fun t ht => ℱ.le (t + 1) _ (hP i t ht)) hw_int
  have hN_eq := integral_N_eq_setIntegral_sum μ P X i
    (fun t ht => ℱ.le (t + 1) _ (hP i t ht)) hobs_int
  have hsum :
      ∑ t ∈ Finset.range T,
          a * (∫ ω in {ω | i ∈ P t ω}, w t ω ∂μ) ≤
        ∑ t ∈ Finset.range T,
          ∫ ω in {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
    apply Finset.sum_le_sum
    intro t ht
    exact conditional_service_integral μ (ℱ (t + 1)) (ℱ.le (t + 1))
      (observation X i t) (w t) {ω | i ∈ P t ω} (hP i t (Finset.mem_range.mp ht))
      a (hobs_int t (Finset.mem_range.mp ht)) (hw_int t (Finset.mem_range.mp ht))
      (hservice i t (Finset.mem_range.mp ht))
  have hmean :
      a * (∫ ω, G P w i T ω ∂μ) ≤ ∫ ω, (N P X i T ω : ℝ) ∂μ := by
    calc
      a * (∫ ω, G P w i T ω ∂μ) =
          ∑ t ∈ Finset.range T,
            a * (∫ ω in {ω | i ∈ P t ω}, w t ω ∂μ) := by
        rw [hG_eq, Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range T,
            ∫ ω in {ω | i ∈ P t ω}, observation X i t ω ∂μ := hsum
      _ = ∫ ω, (N P X i T ω : ℝ) ∂μ := hN_eq.symm
  have hN_int : Integrable (fun ω => (N P X i T ω : ℝ)) μ := by
    have hsum_int : Integrable
        (fun ω => ∑ t ∈ Finset.range T,
          J P i t ω * observation X i t ω) μ := by
      apply integrable_finsetSum
      intro t ht
      rw [J_mul_eq_indicator]
      exact (hobs_int t (Finset.mem_range.mp ht)).indicator
        (ℱ.le (t + 1) _ (hP i t (Finset.mem_range.mp ht)))
    apply hsum_int.congr
    filter_upwards with ω
    exact (N_cast_eq_source_sum P X i T ω).symm
  have hN_le : ∫ ω, (N P X i T ω : ℝ) ∂μ ≤ (q : ℝ) := by
    calc
      ∫ ω, (N P X i T ω : ℝ) ∂μ ≤ ∫ _ω, (q : ℝ) ∂μ :=
        integral_mono_ae hN_int (integrable_const (q : ℝ)) <|
          ae_of_all μ fun ω => Nat.cast_le.mpr (N_le_quota P X hquota i T le_rfl ω)
      _ = (q : ℝ) := by simp
  rw [le_div_iff₀ ha]
  nlinarith [hmean.trans hN_le]

/-- The phase charge is pathwise between zero and `T*K` under the source
phase-support and predictable weight bounds. -/
theorem totalCharge_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {d T K : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ)
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (ω : Ω) :
    totalCharge P sigma theta w T ω ∈
      Set.Icc (0 : ℝ) ((T : ℝ) * (K : ℝ)) := by
  have hA : ∀ t, t < T → A P sigma theta w t ω ∈
      Set.Icc (0 : ℝ) (K : ℝ) := by
    intro t ht
    rw [A_eq_ite_nonempty P sigma theta w hphase t ht ω]
    by_cases hne : (P t ω).Nonempty <;> simp [hne, hw_bound t ht ω]
  constructor
  · change 0 ≤ ∑ t ∈ Finset.range T, A P sigma theta w t ω
    exact Finset.sum_nonneg fun t ht => (hA t (Finset.mem_range.mp ht)).1
  · change (∑ t ∈ Finset.range T, A P sigma theta w t ω) ≤ _
    calc
      (∑ t ∈ Finset.range T, A P sigma theta w t ω) ≤
          ∑ t ∈ Finset.range T, (K : ℝ) :=
        Finset.sum_le_sum fun t ht => (hA t (Finset.mem_range.mp ht)).2
      _ = (T : ℝ) * (K : ℝ) := by simp

/-- The phase charge is measurable at the history after the deterministic
source horizon when the phase boundaries are pre-round stopping times. -/
theorem totalCharge_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {d T : ℕ}
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t)) :
    StronglyMeasurable[m] (totalCharge P sigma theta w T) := by
  have hsm : StronglyMeasurable[ℱ (T + 1)]
      (totalCharge P sigma theta w T) := by
    unfold totalCharge
    apply Finset.stronglyMeasurable_fun_sum
    intro t ht
    have htlt := Finset.mem_range.mp ht
    have hA := A_stronglyMeasurable ℱ P sigma theta w hsigma htheta
      hP hw_meas t htlt
    exact hA.mono (ℱ.mono (by omega : t + 1 ≤ T + 1))
  exact hsm.mono (ℱ.le (T + 1))

/-- The phase charge and its source exponential are integrable from their
pathwise bounds and stopped-history measurability. -/
theorem totalCharge_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ)) :
    Integrable (totalCharge P sigma theta w T) μ ∧
      Integrable (fun ω => Real.exp (kappa * a *
        totalCharge P sigma theta w T ω)) μ := by
  have htotalSM := totalCharge_stronglyMeasurable ℱ P sigma theta w
    hsigma htheta hP hw_meas
  have htotalIcc := fun ω => totalCharge_mem_Icc P sigma theta w
    hphase hw_bound ω
  have htotalInt : Integrable (totalCharge P sigma theta w T) μ := by
    apply Integrable.of_mem_Icc (μ := μ) 0 ((T : ℝ) * (K : ℝ))
      (htotalSM.aemeasurable (μ := μ))
    exact ae_of_all μ htotalIcc
  have hargSM : StronglyMeasurable[m]
      (fun ω => kappa * a * totalCharge P sigma theta w T ω) := by
    have hconst : StronglyMeasurable[m]
        (fun _ : Ω => kappa * a) := stronglyMeasurable_const
    exact hconst.mul htotalSM
  have hExpSM : StronglyMeasurable[m]
      (fun ω => Real.exp (kappa * a * totalCharge P sigma theta w T ω)) :=
    Real.continuous_exp.comp_stronglyMeasurable hargSM
  have hExpIcc : ∀ ω, Real.exp (kappa * a *
      totalCharge P sigma theta w T ω) ∈
      Set.Icc (0 : ℝ) (Real.exp (a * (T : ℝ) * (K : ℝ))) := by
    intro ω
    have htotal := htotalIcc ω
    have harg : kappa * a * totalCharge P sigma theta w T ω ≤
        a * (T : ℝ) * (K : ℝ) := by
      have hmul : kappa * a * totalCharge P sigma theta w T ω ≤
          a * totalCharge P sigma theta w T ω := by
        calc
          kappa * a * totalCharge P sigma theta w T ω =
              kappa * (a * totalCharge P sigma theta w T ω) := by ring
          _ ≤ 1 * (a * totalCharge P sigma theta w T ω) :=
            mul_le_mul_of_nonneg_right kappa_le_one
              (mul_nonneg ha.le htotal.1)
          _ = a * totalCharge P sigma theta w T ω := one_mul _
      have hupper : a * totalCharge P sigma theta w T ω ≤
          a * ((T : ℝ) * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left htotal.2 ha.le
      nlinarith [hmul, hupper]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr harg⟩
  have hExpInt : Integrable
      (fun ω => Real.exp (kappa * a * totalCharge P sigma theta w T ω)) μ := by
    apply Integrable.of_mem_Icc (μ := μ) 0 _
      (hExpSM.aemeasurable (μ := μ))
    exact ae_of_all μ hExpIcc
  exact ⟨htotalInt, hExpInt⟩

/-- The finite-horizon exponential moment of the phase's shared service
charge. All process, service, quota, phase-support, within-phase nesting, and
stopping-time inputs are explicit; this theorem is generic and proves no
protocol invariant. -/
theorem phase_totalCharge_exponential_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω) :
    ∫ ω, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
      (d : ℝ) * Real.exp (q : ℝ) := by
  have htaskExpInt : ∀ i,
      Integrable (fun ω => Real.exp (kappa * a * G P w i T ω)) μ := by
    intro i
    have hGsm' := G_stronglyMeasurable ℱ P w hP hw_meas i T le_rfl
    have hGsm : StronglyMeasurable[m] (G P w i T) :=
      hGsm'.mono (ℱ.le (T + 1))
    have hargSm : StronglyMeasurable[m]
        (fun ω => kappa * a * G P w i T ω) := by
      have hconst : StronglyMeasurable[m]
          (fun _ : Ω => kappa * a) := stronglyMeasurable_const
      exact hconst.mul hGsm
    have hExpSm : StronglyMeasurable[m]
        (fun ω => Real.exp (kappa * a * G P w i T ω)) :=
      Real.continuous_exp.comp_stronglyMeasurable hargSm
    have hExpBound : ∀ ω,
        Real.exp (kappa * a * G P w i T ω) ∈
          Set.Icc (0 : ℝ) (Real.exp (a * (T : ℝ) * (K : ℝ))) := by
      intro ω
      have hG := G_mem_Icc P w hw_bound i T le_rfl ω
      have harg : kappa * a * G P w i T ω ≤
          a * (T : ℝ) * (K : ℝ) := by
        have hmul : kappa * a * G P w i T ω ≤ a * G P w i T ω := by
          calc
            kappa * a * G P w i T ω = kappa * (a * G P w i T ω) := by ring
            _ ≤ 1 * (a * G P w i T ω) :=
              mul_le_mul_of_nonneg_right kappa_le_one (mul_nonneg ha.le hG.1)
            _ = a * G P w i T ω := one_mul _
        have hupper : a * G P w i T ω ≤ a * ((T : ℝ) * (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hG.2 ha.le
        nlinarith [hmul, hupper]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr harg⟩
    apply Integrable.of_mem_Icc (μ := μ) 0 _
      (hExpSm.aemeasurable (μ := μ))
    exact ae_of_all μ hExpBound
  have htaskSumInt : Integrable
      (fun ω => ∑ i ∈ Finset.univ, Real.exp (kappa * a * G P w i T ω)) μ := by
    apply integrable_finsetSum
    intro i hi
    exact htaskExpInt i
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have hpoint : ∀ ω,
      Real.exp (kappa * a * totalCharge P sigma theta w T ω) ≤
        ∑ i ∈ Finset.univ, Real.exp (kappa * a * G P w i T ω) := by
    intro ω
    have hmax := totalCharge_eq_maxTaskCharge hd P sigma theta w
      hphase hnested (fun t ht ω => (hw_bound t ht ω).1) ω
    have hFinNonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
    obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup' hFinNonempty (fun i => G P w i T ω)
    rw [hmax]
    change Real.exp (kappa * a *
      Finset.univ.sup' hFinNonempty (fun j => G P w j T ω)) ≤ _
    rw [hsup]
    exact Finset.single_le_sum
      (f := fun j : Fin d => Real.exp (kappa * a * G P w j T ω))
      (fun j hj => (Real.exp_pos _).le) hi
  have htaskMom : ∀ i,
      ∫ ω, Real.exp (kappa * a * G P w i T ω) ∂μ ≤ Real.exp (q : ℝ) := by
    intro i
    exact integral_exp_task_charge_le_quota μ ℱ P X w a ha hP hw_meas
      hw_bound hX_meas hquota hservice i
  calc
    ∫ ω, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
        ∫ ω, ∑ i ∈ Finset.univ,
          Real.exp (kappa * a * G P w i T ω) ∂μ :=
      integral_mono_ae htotalInt.2 htaskSumInt (ae_of_all μ hpoint)
    _ = ∑ i ∈ Finset.univ,
          ∫ ω, Real.exp (kappa * a * G P w i T ω) ∂μ := by
      rw [integral_finsetSum]
      intro i hi
      exact htaskExpInt i
    _ ≤ ∑ i ∈ Finset.univ, Real.exp (q : ℝ) :=
      Finset.sum_le_sum fun i hi => htaskMom i
    _ = (d : ℝ) * Real.exp (q : ℝ) := by simp

/-- Jensen's inequality converts the phase exponential-moment estimate into
the corresponding expected-charge bound. -/
theorem phase_totalCharge_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (hT : 0 < T) (hK : 0 < K) (hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T → StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T →
      ∀ᵐ ω ∂μ, i ∈ P t ω →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω) :
    ∫ ω, totalCharge P sigma theta w T ω ∂μ ≤
      ((q : ℝ) + Real.log (d : ℝ)) / (kappa * a) := by
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  let c : ℝ := kappa * a
  have hcpos : 0 < c := mul_pos kappa_pos ha
  have hconvex : ConvexOn ℝ Set.univ
      (fun x : ℝ => Real.exp (c * x)) := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ c) using 1
  have hJensen :
      Real.exp (c * (∫ ω, totalCharge P sigma theta w T ω ∂μ)) ≤
        ∫ ω, Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := by
    simpa [Function.comp_def, c] using
      hconvex.map_integral_le
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
        isClosed_univ (ae_of_all μ fun _ => Set.mem_univ _)
        htotalInt.1 htotalInt.2
  have hexpBound := phase_totalCharge_exponential_moment_bound μ hd hT hK hq
    ℱ P X w sigma theta a ha hsigma htheta hsigma_start hsigma_le_theta
    htheta_bound hP hphase hnested hw_meas hw_bound hX_meas hquota hservice
  have hlog : Real.exp (c * (∫ ω, totalCharge P sigma theta w T ω ∂μ)) ≤
      Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
    calc
      Real.exp (c * (∫ ω, totalCharge P sigma theta w T ω ∂μ)) ≤
          ∫ ω, Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := hJensen
      _ ≤ (d : ℝ) * Real.exp (q : ℝ) := hexpBound
      _ = Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
        rw [Real.exp_add]
        congr 1
        exact (Real.exp_log (Nat.cast_pos.mpr hd)).symm
  have hlinear := (Real.exp_le_exp.mp hlog)
  rw [le_div_iff₀ hcpos]
  dsimp [c]
  nlinarith [hlinear]

/-- A one-point phase beginning at source round two has an empty task set
before the phase and one unresolved task on source round two. This concrete
case checks the within-phase nesting premise without imposing global nesting.
-/
def laterStartTasks : ℕ → Unit → Finset (Fin 1) := fun t _ =>
  if t = 1 then {0} else ∅

/-- The first source round of the concrete later-start phase. -/
def laterStartSigma : Unit → ℕ := fun _ => 2

/-- The first excluded source round of the concrete later-start phase. -/
def laterStartTheta : Unit → ℕ := fun _ => 3

/-- The predictable weight for the concrete later-start phase. -/
def laterStartWeight : ℕ → Unit → ℝ := fun t _ => if t = 1 then 1 else 0

/-- Concrete source-round-two specialization of the within-phase maximum
charge identity for `T = 2`, `sigma = 2`, and `theta = 3`. -/
theorem later_start_phase_specialization :
    laterStartTasks 0 () = ∅ ∧
      laterStartTasks 1 () = {0} ∧
      totalCharge laterStartTasks laterStartSigma laterStartTheta
          laterStartWeight 2 () =
        maxTaskCharge (by omega) laterStartTasks laterStartWeight 2 () ∧
      totalCharge laterStartTasks laterStartSigma laterStartTheta
          laterStartWeight 2 () = 1 := by
  have hphase : ∀ t, t < 2 → ∀ ω : Unit,
      (laterStartTasks t ω).Nonempty →
        laterStartSigma ω ≤ t + 1 ∧ t + 1 < laterStartTheta ω := by
    intro t ht ω hne
    by_cases ht1 : t = 1
    · subst t
      simp [laterStartSigma, laterStartTheta]
    · have ht0 : t = 0 := by omega
      subst t
      simp [laterStartTasks] at hne
  have hnested : ∀ s t, s ≤ t → t < 2 → ∀ ω : Unit,
      laterStartSigma ω ≤ s + 1 → t + 1 < laterStartTheta ω →
        laterStartTasks t ω ⊆ laterStartTasks s ω := by
    intro s t hst ht ω hsigma htheta
    have hsigma' : 2 ≤ s + 1 := by simpa [laterStartSigma] using hsigma
    have htheta' : t + 1 < 3 := by simpa [laterStartTheta] using htheta
    have ht1 : t = 1 := by omega
    have hs1 : s = 1 := by omega
    subst t
    subst s
    simp [laterStartTasks]
  have hw_nonneg : ∀ t, t < 2 → ∀ ω : Unit,
      0 ≤ laterStartWeight t ω := by
    intro t ht ω
    simp only [laterStartWeight]
    split <;> positivity
  have hmax := totalCharge_eq_maxTaskCharge (d := 1) (T := 2)
    (by omega) laterStartTasks laterStartSigma laterStartTheta
    laterStartWeight hphase hnested hw_nonneg ()
  refine ⟨by simp [laterStartTasks], ?_⟩
  refine ⟨by simp [laterStartTasks], ?_⟩
  refine ⟨hmax, ?_⟩
  change (∑ t ∈ Finset.range 2,
    A laterStartTasks laterStartSigma laterStartTheta laterStartWeight t ()) = 1
  rw [Finset.sum_range_succ]
  simp [A, laterStartTasks, laterStartSigma, laterStartTheta,
    laterStartWeight, Set.indicator]

end Bandits.Support.PhaseServiceWaiting
