/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.RecordedRoundMoments
public import Bandits.Support.StoppedQueueBound
public import Bandits.Support.FiniteBanditModel

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical finite logical recording process

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:94-174,182-215,245-290`.
This is a finite logical input law with an explicit causal decision policy.
It does not identify that policy with the episode scheduler, or this law with
the physical protocol's private conditional recording law. Rewards are arbitrary
bounded reward matrices. Exact arithmetic integrality is an explicit input.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.CanonicalQueueProcess

open ConstructorDimensions CanonicalRecordingRates RecordedQueueRun
open RecordedRoundMoments StoppedQueueBound

variable {K : ℕ}

/-- The source learning-rate cap implies the inherited queue capacity bound. -/
theorem four_mul_eta_le_one (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p)) :
    4 * eta ≤ 1 := by
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast (m_pos p)
  have hK : (1 : ℝ) ≤ p.K := by exact_mod_cast (K_pos p)
  have hL : (1 : ℝ) ≤ L_stab p := by exact_mod_cast L_stab_ge_one p
  have hd : (4 : ℝ) ≤ 1024 * (p.m : ℝ) * p.K * L_stab p := by
    have hmk : (1 : ℝ) ≤ (p.m : ℝ) * p.K := one_le_mul_of_one_le_of_one_le hm hK
    have hmkL := one_le_mul_of_one_le_of_one_le hmk hL
    nlinarith only [hmkL]
  have hpos : 0 < 1024 * (p.m : ℝ) * p.K * L_stab p := lt_of_lt_of_le (by norm_num) hd
  have hmul := (le_div_iff₀ hpos).mp hcap
  have hsmall := mul_le_mul_of_nonneg_left hd heta.le
  nlinarith only [hmul, hsmall]

/-- Literal queue parameters; positivity and capacity are derived, not inputs. -/
noncomputable def queueParameters (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
    (n : ℕ) (hn : (n : ℝ) = eta * (D p : ℝ)) : RecordedQueueRun.Parameters where
  D := D p
  n := n
  eta := eta
  D_pos := D_pos p
  n_pos := by
    have h : (0 : ℝ) < n := hn ▸ mul_pos heta (Nat.cast_pos.mpr (D_pos p))
    exact_mod_cast h
  capacity_le_D := by
    have h := mul_le_mul_of_nonneg_right (four_mul_eta_le_one p heta hcap)
      (Nat.cast_nonneg (D p) : (0 : ℝ) ≤ D p)
    have hreal : (4 : ℝ) * n ≤ D p := by rw [hn]; nlinarith only [h]
    exact_mod_cast hreal
  eta_pos := heta
  n_eq_eta_mul_D := hn

/-- The sole constructor of the canonical shared recorded-arm rates. -/
noncomputable def canonicalRates (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) : RecordingRates p.K where
  rate := xi p eta anchor
  rate_pos := xi_pos p heta anchor
  rate_sum_le_one := sum_xi_le_one p heta hcap anchor hanchor

theorem beta_le_canonical_rate (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) (i : Fin p.K) :
    beta p eta ≤ (canonicalRates p eta heta hcap anchor hanchor).rate i :=
  beta_le_xi p heta anchor i

theorem thirtyTwo_mul_eta_le_canonical_rate
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) (i : Fin p.K) :
    32 * eta ≤ (canonicalRates p eta heta hcap anchor hanchor).rate i :=
  thirtyTwo_mul_eta_le_xi p heta anchor i

/-- Chronological finite outcome vectors, represented by nested snoc pairs. -/
def History (K : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => History K t × Option (Fin K)

instance historyFintype (K : ℕ) : (t : ℕ) → Fintype (History K t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => letI := historyFintype K t
             inferInstanceAs (Fintype (History K t × Option (Fin K)))

instance historyMeasurableSpace (K t : ℕ) : MeasurableSpace (History K t) := ⊤

/-- Honest internal decision data: only past outcomes are available. The
anchor index ranges over the actually constructed states numbered `0,...,t`.
Identifying these decisions with the physical episode scheduler is a separate
application obligation. -/
structure Policy (p : ConstructorDimensions.Parameters) where
  enabled : (t : Fin p.T) → History p.K t.val → Bool
  anchorIndex : (t : Fin p.T) → History p.K t.val → Fin (t.val + 1)

theorem scoreWeight_pos (q : RecordedQueueRun.Parameters) (s : RunState K)
    (i : Fin K) : 0 < RecordedQueueRun.scoreWeight q s i :=
  ScoreWeights.scoreWeight_pos (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr q.D_pos)) _

variable (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
  (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
  (n : ℕ) (hn : (n : ℝ) = eta * (D p : ℝ))

local notation "q" => queueParameters p eta heta hcap n hn

/-- Weights of the selected actual prefix state. `take` is used only at the
bounded policy index; generated lists below have exactly `t` entries. -/
noncomputable def selectedAnchor (policy : Policy p) (t : Fin p.T)
    (h : History p.K t.val) (rounds : List (RoundInput p.K)) : Fin p.K → ℝ :=
  RecordedQueueRun.scoreWeight q
    (run q (rounds.take (policy.anchorIndex t h).val))

theorem selectedAnchor_pos (policy : Policy p) (t : Fin p.T)
    (h : History p.K t.val) (rounds : List (RoundInput p.K)) (i : Fin p.K) :
    0 < selectedAnchor p eta heta hcap n hn policy t h rounds i :=
  scoreWeight_pos q _ i

/-- One canonical input built from past outcomes and the current single draw. -/
noncomputable def nextInput (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : Fin p.T) (h : History p.K t.val)
    (rounds : List (RoundInput p.K)) (o : Option (Fin p.K)) : RoundInput p.K :=
  fixedRoundInput q
    (canonicalRates p eta heta hcap
      (selectedAnchor p eta heta hcap n hn policy t h rounds)
      (selectedAnchor_pos p eta heta hcap n hn policy t h rounds))
    (rewards.reward t) (rewards.reward_mem_Icc t) (policy.enabled t h) o

/-- Generate exactly one accepted machine input for every calendar round. -/
noncomputable def generatedRounds (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) : (t : ℕ) → t ≤ p.T → History p.K t → List (RoundInput p.K)
  | 0, _, _ => []
  | t + 1, ht, h =>
    let rounds := generatedRounds rewards policy t (Nat.le_of_succ_le ht) h.1
    rounds ++ [nextInput p eta heta hcap n hn rewards policy
      ⟨t, Nat.lt_of_succ_le ht⟩ h.1 rounds h.2]

theorem generatedRounds_length (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    (generatedRounds p eta heta hcap n hn rewards policy t ht h).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [generatedRounds, List.length_append, List.length_singleton, ih]

/-- Actual terminal state of a generated outcome prefix, including its records. -/
noncomputable def prefixState (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) : RunState p.K :=
  run q (generatedRounds p eta heta hcap n hn rewards policy t ht h)

theorem prefixState_zero (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (h : History p.K 0) :
    prefixState p eta heta hcap n hn rewards policy 0 (Nat.zero_le _) h =
      initialState p.K := rfl

theorem prefixState_eq_run (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    prefixState p eta heta hcap n hn rewards policy t ht h =
      run q (generatedRounds p eta heta hcap n hn rewards policy t ht h) := rfl

theorem execute_append (qp : RecordedQueueRun.Parameters) (xs ys : List (RoundInput K))
    (s : RunState K) : execute qp (xs ++ ys) s = execute qp ys (execute qp xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (step qp s x)

theorem prefixState_succ (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : ℕ) (ht : t + 1 ≤ p.T)
    (h : History p.K t) (o : Option (Fin p.K)) :
    prefixState p eta heta hcap n hn rewards policy (t + 1) ht (h, o) =
      step q (prefixState p eta heta hcap n hn rewards policy t (by omega) h)
        (nextInput p eta heta hcap n hn rewards policy ⟨t, by omega⟩ h
          (generatedRounds p eta heta hcap n hn rewards policy t (by omega) h) o) := by
  simp only [prefixState, generatedRounds, run, execute_append, execute]

theorem nextInput_rate_bound (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : Fin p.T) (h : History p.K t.val)
    (rounds : List (RoundInput p.K)) (o : Option (Fin p.K)) (i : Fin p.K) :
    32 * eta ≤ (nextInput p eta heta hcap n hn rewards policy t h rounds o).rate i :=
  thirtyTwo_mul_eta_le_xi p heta _ i

theorem generatedRounds_rate_bound (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    ∀ r ∈ generatedRounds p eta heta hcap n hn rewards policy t ht h,
      ∀ i, 32 * eta ≤ r.rate i := by
  induction t with
  | zero => simp only [generatedRounds, List.not_mem_nil, false_implies, implies_true]
  | succ t ih =>
    intro r hr i
    rcases List.mem_append.mp hr with hr | hr
    · exact ih (Nat.le_of_succ_le ht) h.1 r hr i
    · have heq := List.mem_singleton.mp hr
      subst r
      exact nextInput_rate_bound p eta heta hcap n hn rewards policy _ _ _ _ i

/-- Canonical deterministic stopped-backlog bound on every generated path. -/
theorem prefixState_backlog_le_twice_threshold
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) (i : Fin p.K) :
    normalizedBacklog q (prefixState p eta heta hcap n hn rewards policy t ht h) i ≤
      2 * (1 / (32 * eta)) := by
  have hb := run_prefix_normalized_backlog_le_twice_threshold q
    (generatedRounds p eta heta hcap n hn rewards policy t ht h)
    (generatedRounds_rate_bound p eta heta hcap n hn rewards policy t ht h) t i
  simpa only [List.take_of_length_le (le_of_eq
    (generatedRounds_length p eta heta hcap n hn rewards policy t ht h)), prefixState,
      queueParameters] using hb

/-- Every arm has one chronological record per generated calendar round. -/
theorem prefixState_records_length
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) (i : Fin p.K) :
    ((prefixState p eta heta hcap n hn rewards policy t ht h).records i).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨h, o⟩ := h
    rw [prefixState_succ]
    simpa only [step, List.length_append, List.length_singleton] using
      congrArg (fun a : ℕ => a + 1) (ih (Nat.le_of_succ_le ht) h)

/-- The bounded policy index is within the generated input prefix. -/
theorem anchorIndex_le_generated_length
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : Fin p.T) (h : History p.K t.val) :
    (policy.anchorIndex t h).val ≤
      (generatedRounds p eta heta hcap n hn rewards policy t.val t.isLt.le h).length := by
  rw [generatedRounds_length]
  exact Nat.le_of_lt_succ (policy.anchorIndex t h).isLt

/-- The selected actual prefix has exactly the selected number of rounds;
the policy never invokes `take` outside the constructed history. -/
theorem selected_prefix_length
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : Fin p.T) (h : History p.K t.val) :
    ((generatedRounds p eta heta hcap n hn rewards policy t.val t.isLt.le h).take
      (policy.anchorIndex t h).val).length = (policy.anchorIndex t h).val := by
  rw [List.length_take]
  exact Nat.min_eq_left
    (anchorIndex_le_generated_length p eta heta hcap n hn rewards policy t h)

/-- Exact real form of truncated natural subtraction. -/
theorem nat_sub_cast_eq_max (a c : ℕ) :
    ((a - c : ℕ) : ℝ) = max ((a : ℝ) - c) 0 := by
  by_cases hc : c ≤ a
  · rw [Nat.cast_sub hc, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hc))]
  · have hac : a ≤ c := Nat.le_of_not_ge hc
    rw [Nat.sub_eq_zero_of_le hac, Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr hac))]

/-- Exact normalized max recursion for an enabled retained update. No
post-update non-overflow premise is imposed: the first overflowing update is
included. Source: `04_slow_fast_learner.tex:157-174,182-187,265-279`. -/
theorem normalizedBacklog_step_of_retained (qp : RecordedQueueRun.Parameters)
    (s : RunState K) (r : RoundInput K) (i : Fin K)
    (hs : s.overflow = false) (hr : r.enabled = true) :
    normalizedBacklog qp (step qp s r) i =
      max (normalizedBacklog qp s i + rawEstimate qp s r i - 4) 0 := by
  have hb : ((step qp s r).registers i).2 =
      (s.registers i).2 + quantizedArrival qp r i - 4 * qp.n := by
    simp only [step, acceptedRecord, hs, Bool.false_eq_true, ite_false, hr, ite_true,
      QueueReplay.transition]
    omega
  have hraw : rawEstimate qp s r i =
      (quantizedArrival qp r i : ℝ) / (qp.n : ℝ) := by
    simp only [rawEstimate, acceptedRecord, hs, Bool.false_eq_true, ite_false,
      hr, ite_true, acceptedArrival]
  rw [normalizedBacklog, hb, nat_sub_cast_eq_max,
    ← max_div_div_right (Nat.cast_nonneg qp.n)]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zero_div, hraw]
  congr 1
  unfold normalizedBacklog
  field_simp [ne_of_gt (Nat.cast_pos.mpr qp.n_pos)]

/-- Disabled and post-overflow steps preserve the normalized backlog exactly. -/
theorem normalizedBacklog_step_of_inactive (qp : RecordedQueueRun.Parameters)
    (s : RunState K) (r : RoundInput K) (i : Fin K)
    (h : r.enabled = false ∨ s.overflow = true) :
    normalizedBacklog qp (step qp s r) i = normalizedBacklog qp s i := by
  rcases h with hr | hs
  · unfold normalizedBacklog
    rw [(step_disabled_preserves qp s r hr i).1]
  · unfold normalizedBacklog
    rw [(step_after_overflow_preserves qp s r hs i).1]

/-- The exponential of the reflected backlog is bounded pointwise by one
plus the unreflected exponential. -/
theorem exp_mul_max_le (b x c : ℝ) :
    Real.exp (c * max (b + x) 0) ≤
      1 + Real.exp (c * b) * Real.exp (c * x) := by
  by_cases hx : 0 ≤ b + x
  · rw [max_eq_left hx, mul_add, Real.exp_add]
    exact le_add_of_nonneg_left zero_le_one
  · rw [max_eq_right (le_of_not_ge hx), mul_zero, Real.exp_zero]
    exact le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))

/-- The actual next-outcome kernel: canonical single-arm sampling on retained
enabled rounds, and a pure no-record outcome otherwise. -/
noncomputable def roundKernel (s : RunState K) (rates : RecordingRates K)
    (enabled : Bool) : PMF (Option (Fin K)) :=
  if enabled = true ∧ s.overflow = false then recordingOutcomePMF rates else PMF.pure none

theorem roundKernel_of_active (s : RunState K) (rates : RecordingRates K)
    (enabled : Bool) (he : enabled = true) (hs : s.overflow = false) :
    roundKernel s rates enabled = recordingOutcomePMF rates := by
  rw [roundKernel, ite_eq_left ⟨he, hs⟩]

theorem roundKernel_of_inactive (s : RunState K) (rates : RecordingRates K)
    (enabled : Bool) (hi : enabled = false ∨ s.overflow = true) :
    roundKernel s rates enabled = PMF.pure none := by
  have hnactive : ¬ (enabled = true ∧ s.overflow = false) := by
    rintro ⟨he, hs⟩
    rcases hi with hf | ht
    · rw [hf] at he
      cases he
    · rw [ht] at hs
      cases hs
  rw [roundKernel, ite_eq_right hnactive]

/-- Equality on inactive rounds, for any pre-state and exponential parameter. -/
theorem roundKernel_exponentialMoment_eq_of_inactive
    (qp : RecordedQueueRun.Parameters) (s : RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (hr : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (hi : enabled = false ∨ s.overflow = true) (c : ℝ) (i : Fin K) :
    ∫ o, Real.exp (c * normalizedBacklog qp
      (step qp s (fixedRoundInput qp rates reward hr enabled o)) i)
      ∂(roundKernel s rates enabled).toMeasure =
        Real.exp (c * normalizedBacklog qp s i) := by
  have heq : ∀ o, normalizedBacklog qp
      (step qp s (fixedRoundInput qp rates reward hr enabled o)) i =
        normalizedBacklog qp s i := fun _ =>
    normalizedBacklog_step_of_inactive qp s _ i hi
  simp_rw [heq]
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- One-step expected exponential growth for every pre-state, including frozen
and disabled states and the retained first overflowing successor. The explicit
`beta ≤ rate` input here is discharged canonically below. -/
theorem roundKernel_exponentialMoment_le (qp : RecordedQueueRun.Parameters)
    (s : RunState K) (rates : RecordingRates K) (reward : Fin K → ℝ)
    (hr : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1) (enabled : Bool)
    (c : ℝ) (hc : 0 < c) (hcr : ∀ i, c ≤ rates.rate i) (i : Fin K) :
    ∫ o, Real.exp (c * normalizedBacklog qp
      (step qp s (fixedRoundInput qp rates reward hr enabled o)) i)
      ∂(roundKernel s rates enabled).toMeasure ≤
        1 + Real.exp (c * normalizedBacklog qp s i) := by
  by_cases hactive : enabled = true ∧ s.overflow = false
  · obtain ⟨he, hs⟩ := hactive
    subst enabled
    rw [roundKernel, ite_eq_left ⟨rfl, hs⟩]
    have hpoint : ∀ o,
        Real.exp (c * normalizedBacklog qp
          (step qp s (fixedRoundInput qp rates reward hr true o)) i) ≤
        1 + Real.exp (c * normalizedBacklog qp s i) *
          Real.exp (c * (rawEstimate qp s
            (fixedRoundInput qp rates reward hr true o) i - 4)) := by
      intro o
      rw [normalizedBacklog_step_of_retained qp s _ i hs rfl]
      simpa only [add_sub_assoc] using exp_mul_max_le
        (normalizedBacklog qp s i)
        (rawEstimate qp s (fixedRoundInput qp rates reward hr true o) i - 4) c
    have hm := rawEstimate_exponentialMoment_le_one qp s rates reward hr i hs c hc (hcr i)
    calc
      _ ≤ ∫ o, (1 + Real.exp (c * normalizedBacklog qp s i) *
          Real.exp (c * (rawEstimate qp s
            (fixedRoundInput qp rates reward hr true o) i - 4)))
          ∂(recordingOutcomePMF rates).toMeasure :=
        integral_mono Integrable.of_finite Integrable.of_finite hpoint
      _ = 1 + Real.exp (c * normalizedBacklog qp s i) *
          (∫ o, Real.exp (c * (rawEstimate qp s
            (fixedRoundInput qp rates reward hr true o) i - 4))
          ∂(recordingOutcomePMF rates).toMeasure) := by
        rw [integral_add (integrable_const _) Integrable.of_finite,
          integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ 1 + Real.exp (c * normalizedBacklog qp s i) := by
        have hm' := mul_le_mul_of_nonneg_left hm
          (Real.exp_nonneg (c * normalizedBacklog qp s i))
        exact add_le_add le_rfl (by simpa only [mul_one] using hm')
  · have hi : enabled = false ∨ s.overflow = true := by
      cases enabled <;> cases hs : s.overflow <;> simp_all
    have hsame : ∀ o, normalizedBacklog qp
        (step qp s (fixedRoundInput qp rates reward hr enabled o)) i =
        normalizedBacklog qp s i := by
      intro o
      exact normalizedBacklog_step_of_inactive qp s _ i hi
    simp_rw [hsame]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact le_add_of_nonneg_left zero_le_one

/-- Expectation under a pure PMF in a measurable singleton space. -/
theorem integral_pure {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (a : A) (f : A → ℝ) : ∫ b, f b ∂(PMF.pure a).toMeasure = f a := by
  rw [PMF.toMeasure_pure]
  exact integral_dirac f a

/-- Finite-kernel Fubini identity from `PMF.bind_apply` and
`PMF.integral_eq_sum`, with no integrability premise needed. -/
theorem integral_bind_finite {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : PMF A) (κ : A → PMF B) (f : B → ℝ) :
    ∫ b, f b ∂(μ.bind κ).toMeasure =
      ∫ a, (∫ b, f b ∂(κ a).toMeasure) ∂μ.toMeasure := by
  classical
  simp only [PMF.integral_eq_sum, PMF.bind_apply, tsum_fintype, smul_eq_mul]
  simp_rw [ENNReal.toReal_sum (fun a _ =>
    ENNReal.mul_ne_top (μ.apply_ne_top a) ((κ a).apply_ne_top _)),
    ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The finite causal kernel at an actual generated prefix. -/
noncomputable def nextKernel (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) (t : Fin p.T) (h : History p.K t.val) : PMF (Option (Fin p.K)) :=
  let rounds := generatedRounds p eta heta hcap n hn rewards policy t.val t.isLt.le h
  roundKernel (run q rounds)
    (canonicalRates p eta heta hcap
      (selectedAnchor p eta heta hcap n hn policy t h rounds)
      (selectedAnchor_pos p eta heta hcap n hn policy t h rounds))
    (policy.enabled t h)

/-- The finite chronological path law is the actual iterated kernel bind.
Each extension appends one shared `Option (Fin K)` recording outcome. -/
noncomputable def pathLaw (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (policy : Policy p) : (t : ℕ) → t ≤ p.T → PMF (History p.K t)
  | 0, _ => PMF.pure ()
  | t + 1, ht =>
    (pathLaw rewards policy t (Nat.le_of_succ_le ht)).bind fun h =>
      (nextKernel p eta heta hcap n hn rewards policy ⟨t, Nat.lt_of_succ_le ht⟩ h).bind
        fun o => PMF.pure (h, o)

/-- Every real function of a finite generated prefix is measurable. -/
theorem measurable_history (t : ℕ) (f : History p.K t → ℝ) : Measurable f :=
  Measurable.of_discrete

/-- All finite-history observables have integrable finite-law expectations. -/
theorem integrable_history
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (f : History p.K t → ℝ) :
    Integrable f (pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure :=
  Integrable.of_finite

/-- The one-step exponential estimate with all rate inputs discharged by the
canonical constructor, at each actual generated prefix. -/
theorem nextKernel_exponentialMoment_le
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t + 1 ≤ p.T) (h : History p.K t) (i : Fin p.K) :
    ∫ o, Real.exp (beta p eta * normalizedBacklog q
      (prefixState p eta heta hcap n hn rewards policy (t + 1) ht (h, o)) i)
      ∂(nextKernel p eta heta hcap n hn rewards policy ⟨t, by omega⟩ h).toMeasure ≤
        1 + Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t (by omega) h) i) := by
  simp_rw [prefixState_succ]
  exact roundKernel_exponentialMoment_le q _ _ _ _ _ (beta p eta) (beta_pos p heta)
    (fun j => beta_le_xi p heta _ j) i

/-- Exact finite-kernel expectation recursion for the constructed path law. -/
theorem integral_pathLaw_succ
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t + 1 ≤ p.T) (f : History p.K (t + 1) → ℝ) :
    ∫ h, f h ∂(pathLaw p eta heta hcap n hn rewards policy (t + 1) ht).toMeasure =
      ∫ h, (∫ o, f (h, o)
        ∂(nextKernel p eta heta hcap n hn rewards policy ⟨t, by omega⟩ h).toMeasure)
        ∂(pathLaw p eta heta hcap n hn rewards policy t (by omega)).toMeasure := by
  rw [pathLaw, integral_bind_finite]
  congr 1
  funext h
  rw [integral_bind_finite]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun o =>
    integral_pure (A := History p.K (t + 1)) (h, o) f

/-- Iterated exponential backlog bound from the all-zero initial state.
Source: `04_slow_fast_learner.tex:265-284`. There are exactly `t` processed
calendar rounds in this expectation. -/
theorem exponentialMoment_le_time_add_one
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (i : Fin p.K) :
    ∫ h, Real.exp (beta p eta * normalizedBacklog q
      (prefixState p eta heta hcap n hn rewards policy t ht h) i)
      ∂(pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure ≤ (t : ℝ) + 1 := by
  induction t with
  | zero =>
    simp only [prefixState,
      generatedRounds, run, execute, normalizedBacklog, initialState,
      Nat.cast_zero, zero_div, mul_zero, Real.exp_zero, zero_add]
    rw [integral_const, probReal_univ]
    norm_num
  | succ t ih =>
    rw [integral_pathLaw_succ]
    calc
      _ ≤ ∫ h, (1 + Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t (by omega) h) i))
          ∂(pathLaw p eta heta hcap n hn rewards policy t (by omega)).toMeasure :=
        integral_mono Integrable.of_finite Integrable.of_finite
          (fun h => nextKernel_exponentialMoment_le p eta heta hcap n hn
            rewards policy t ht h i)
      _ = 1 + ∫ h, Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t (by omega) h) i)
          ∂(pathLaw p eta heta hcap n hn rewards policy t (by omega)).toMeasure := by
        rw [integral_add (integrable_const _) Integrable.of_finite,
          integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ (↑(t + 1) : ℝ) + 1 := by
        have hi := ih (Nat.le_of_succ_le ht)
        push_cast
        linarith only [hi]

/-- Disabled/frozen inputs have zero accepted arrivals and preserve every
score/backlog register, even though one no-op record is still appended. -/
theorem inactive_input_zero_and_preserves (qp : RecordedQueueRun.Parameters)
    (s : RunState K) (rates : RecordingRates K) (reward : Fin K → ℝ)
    (hr : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1) (enabled : Bool)
    (hi : enabled = false ∨ s.overflow = true) (o : Option (Fin K)) :
    (∀ i, rawEstimate qp s (fixedRoundInput qp rates reward hr enabled o) i = 0) ∧
      (∀ i, (step qp s (fixedRoundInput qp rates reward hr enabled o)).registers i =
        s.registers i) := by
  rcases hi with he | hs
  · subst enabled
    exact disabledRound_zero_and_preserves qp s rates reward hr o
  · constructor
    · intro i
      exact rawEstimate_eq_zero_after_overflow qp s _ i hs
    · intro i
      exact (step_after_overflow_preserves qp s _ hs i).1

/-- Exact canonical identity used at the terminal exponential threshold. -/
theorem beta_mul_threshold (hpos : 0 < eta) :
    beta p eta * (1 / (32 * eta)) = (L_stab p : ℝ) := by
  unfold beta
  field_simp [hpos.ne']

theorem beta_div_thirtyTwo_mul_eta (hpos : 0 < eta) :
    beta p eta / (32 * eta) = (L_stab p : ℝ) := by
  simpa only [div_eq_mul_inv, one_mul] using beta_mul_threshold p eta hpos

/-- Overflow by the processed horizon, expressed by the actual terminal flag. -/
noncomputable def overflowEvent
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) : Set (History p.K t) :=
  {h | (prefixState p eta heta hcap n hn rewards policy t ht h).overflow = true}

/-- The terminal event equals crossing at an actual processed successor. -/
theorem mem_overflowEvent_iff_prefix_crossing
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    h ∈ overflowEvent p eta heta hcap n hn rewards policy t ht ↔
      ∃ s, s < t ∧ ∃ i,
        normalizedBacklog q (run q
          ((generatedRounds p eta heta hcap n hn rewards policy t ht h).take (s + 1))) i >
            1 / (32 * eta) := by
  rw [overflowEvent, Set.mem_ofPred_eq, prefixState,
    run_overflow_iff_exists_prefix_threshold, generatedRounds_length]
  rfl

/-- Actual terminal overflow iff a terminal normalized backlog is above the
source threshold. Freezing retains the first crossing. -/
theorem mem_overflowEvent_iff_terminal_threshold
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    h ∈ overflowEvent p eta heta hcap n hn rewards policy t ht ↔
      ∃ i, normalizedBacklog q
        (prefixState p eta heta hcap n hn rewards policy t ht h) i > 1 / (32 * eta) :=
  run_overflow_iff_terminal_threshold q _

/-- Pointwise Markov and union bound: a threshold crossing at any arm is
paid for by the sum of its terminal exponential observables. -/
theorem overflow_indicator_le_exponential_sum
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) :
    (overflowEvent p eta heta hcap n hn rewards policy t ht).indicator
      (fun _ => (1 : ℝ)) h ≤
      Real.exp (-(L_stab p : ℝ)) * ∑ i : Fin p.K,
        Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t ht h) i) := by
  classical
  have hsum : 0 ≤ ∑ i : Fin p.K,
      Real.exp (beta p eta * normalizedBacklog q
        (prefixState p eta heta hcap n hn rewards policy t ht h) i) :=
    Finset.sum_nonneg fun i _ => Real.exp_nonneg _
  by_cases hh : h ∈ overflowEvent p eta heta hcap n hn rewards policy t ht
  · rw [Set.indicator_of_mem hh]
    obtain ⟨i, hi⟩ :=
      (mem_overflowEvent_iff_terminal_threshold p eta heta hcap n hn
        rewards policy t ht h).mp hh
    have hscaled := mul_lt_mul_of_pos_left hi (beta_pos p heta)
    rw [beta_mul_threshold p eta heta] at hscaled
    have he := Real.exp_le_exp.mpr hscaled.le
    have hunit : (1 : ℝ) ≤ Real.exp (-(L_stab p : ℝ)) *
        Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t ht h) i) := by
      have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (-(L_stab p : ℝ)))
      simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using hm
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin p.K => Real.exp (beta p eta * normalizedBacklog q
        (prefixState p eta heta hcap n hn rewards policy t ht h) j))
      (fun j _ => Real.exp_nonneg _) (Finset.mem_univ i)
    exact hunit.trans (mul_le_mul_of_nonneg_left hsingle (Real.exp_nonneg _))
  · rw [Set.indicator_of_notMem hh]
    exact mul_nonneg (Real.exp_nonneg _) hsum

/-- Finite-law terminal overflow probability. This is Markov's inequality and
an arm union bound applied to the constructed bind law, with its proved
exponential expectations, not an assumed recurrence or recordlaw.
Source: `04_slow_fast_learner.tex:279-289`. -/
theorem overflow_probability_le
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p)
    (t : ℕ) (ht : t ≤ p.T) :
    (pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure.real
      (overflowEvent p eta heta hcap n hn rewards policy t ht) ≤
        (p.K : ℝ) * ((t : ℝ) + 1) * Real.exp (-(L_stab p : ℝ)) := by
  classical
  let μ := (pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure
  let E := overflowEvent p eta heta hcap n hn rewards policy t ht
  have hE : MeasurableSet E := trivial
  rw [← integral_indicator_one (μ := μ) hE]
  calc
    _ ≤ ∫ h, Real.exp (-(L_stab p : ℝ)) * ∑ i : Fin p.K,
        Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t ht h) i) ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (overflow_indicator_le_exponential_sum p eta heta hcap n hn rewards policy t ht)
    _ = Real.exp (-(L_stab p : ℝ)) * ∑ i : Fin p.K,
        ∫ h, Real.exp (beta p eta * normalizedBacklog q
          (prefixState p eta heta hcap n hn rewards policy t ht h) i) ∂μ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun i _ => Integrable.of_finite)]
    _ ≤ Real.exp (-(L_stab p : ℝ)) * ∑ _i : Fin p.K, ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ =>
          exponentialMoment_le_time_add_one p eta heta hcap n hn rewards policy t ht i)
        (Real.exp_nonneg _)
    _ = (p.K : ℝ) * ((t : ℝ) + 1) * Real.exp (-(L_stab p : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The accepted ceiling-log estimate fully discharges the canonical terminal
counting factor, with the stronger source factor `1/2`. -/
theorem canonical_tail_factor_le_half (p : ConstructorDimensions.Parameters) :
    (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-(L_stab p : ℝ)) ≤
      1 / (2 * (N p : ℝ) ^ 2) := by
  have hK : (0 : ℝ) < p.K := Nat.cast_pos.mpr (K_pos p)
  have hN : (0 : ℝ) < N p := Nat.cast_pos.mpr (N_pos p)
  have hA : (0 : ℝ) < 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2 := by
    positivity
  have hlog := log_stabArgument_le_L_stab p
  push_cast at hlog
  have he : Real.exp (-(L_stab p : ℝ)) ≤
      1 / (2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2) := by
    calc
      _ ≤ Real.exp (-Real.log
          (2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hA, one_div]
  calc
    _ ≤ (p.K : ℝ) * ((p.T : ℝ) + 1) *
        (1 / (2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = 1 / (2 * (N p : ℝ) ^ 2) := by
      field_simp [hK.ne', hN.ne', (show (p.T : ℝ) + 1 ≠ 0 by positivity)]

/-- Terminal overflow probability for the constructed finite logical process.
This internal result does not establish physical scheduler/private-history
factorization, weighted backlog, final tuning, or manuscript lemma closure. -/
theorem terminal_overflow_probability_le_inv_N_sq
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p) :
    (pathLaw p eta heta hcap n hn rewards policy p.T le_rfl).toMeasure.real
      (overflowEvent p eta heta hcap n hn rewards policy p.T le_rfl) ≤
        1 / (N p : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < N p := Nat.cast_pos.mpr (N_pos p)
  calc
    _ ≤ (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-(L_stab p : ℝ)) :=
      overflow_probability_le p eta heta hcap n hn rewards policy p.T le_rfl
    _ ≤ 1 / (2 * (N p : ℝ) ^ 2) := canonical_tail_factor_le_half p
    _ ≤ 1 / (N p : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hN)
      nlinarith only [sq_nonneg (N p : ℝ)]

/-- The same probability bound in the measure's native extended-real carrier. -/
theorem terminal_overflow_measure_le_inv_N_sq
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (policy : Policy p) :
    (pathLaw p eta heta hcap n hn rewards policy p.T le_rfl).toMeasure
      (overflowEvent p eta heta hcap n hn rewards policy p.T le_rfl) ≤
        ENNReal.ofReal (1 / (N p : ℝ) ^ 2) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (terminal_overflow_probability_le_inv_N_sq p eta heta hcap n hn rewards policy)

end Bandits.Support.CanonicalQueueProcess

end
