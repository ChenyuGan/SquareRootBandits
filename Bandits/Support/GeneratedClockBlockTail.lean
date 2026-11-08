/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedClockConditionalMeans

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Localized lower tails for the generated block clocks

Apply the finite interval-clock bound to the literal generated one-clock
process on the original coordinate space. The interval is the one-based
calendar block, including a clipped final block. This file does not prove a
mean budget, a discovery cap, or a productive-block theorem.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:247-292,440-461`
and `sources/zip4/manuscript/07_public_setup.tex:15-25`.
-/

@[expose] public section

open MeasureTheory

namespace Bandits.Support.GeneratedClockBlockTail

open ConstructorDimensions BootstrapDimensions CompletePublicTable
open ActiveRoundActions
open BootstrapPrivateRoundStreams PrivateRoundFreshness
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open GeneratedClockConditionalMeans
open ReferenceInitializationRun
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters}

variable (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
  (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
  (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
  (s : Fin (n_boot p)) (focal : Follower p.m)

/-- The first one-based source index in block `s`.
Source: `appendix_b_communication.tex:247-252`. -/
noncomputable def blockClockStart (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) : ℕ := s.val * B_boot p + 1

/-- The inclusive one-based endpoint of block `s`, clipped at the horizon.
Source: `appendix_b_communication.tex:247-252`. -/
noncomputable def blockClockEnd (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) : ℕ := min p.T ((s.val + 1) * B_boot p)

/-- The literal simultaneous lower-clock event, with the manuscript tilt
`ell = 4 * b_N`. Its process is the accepted generated one-clock on the
original coordinate law and the enlarged analysis filtration. -/
noncomputable def clockGood : Set (Coordinates p) :=
  BootstrapIntervalBounds.lowerGood (originalLaw p) (analysisFiltration p)
    (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
    (blockClockStart p s) (blockClockEnd p s) (4 * (b_N p : ℝ))

/-- The source start lies in the horizon and every calendar block has a
nonempty one-based interval, including the clipped final block. -/
theorem blockClock_bounds (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) :
    1 ≤ blockClockStart p s ∧
      blockClockStart p s ≤ blockClockEnd p s ∧
      blockClockEnd p s ≤ p.T := by
  obtain ⟨t, ht⟩ := BootstrapDimensions.calendarBlock_nonempty p s
  have hmem := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht
  have hstartstop : s.val * B_boot p < min p.T ((s.val + 1) * B_boot p) :=
    lt_of_le_of_lt hmem.1 hmem.2
  constructor
  · simp [blockClockStart]
  constructor
  · exact Nat.succ_le_of_lt hstartstop
  · exact Nat.min_le_left _ _

private theorem oneClockTest_measurable (t : Fin p.T) :
    Measurable (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) := by
  unfold GeneratedClockConditionalMeans.oneClockTest
  exact (discoveryTest_measurable ids rewards rowCompletion scalarCompletion s t).div_const 8 |>.add
    (multicastTest_measurable ids rewards rowCompletion scalarCompletion s t focal)

private theorem oneClockTest_abs_le_one (t : Fin p.T)
    (z : Option (Descriptor p) × Current p) :
    |oneClockTest ids rewards rowCompletion scalarCompletion s t focal z| ≤ 1 := by
  rcases oneClockTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal z with
    ⟨hlo, hhi⟩
  exact abs_le.mpr ⟨by linarith, hhi⟩

/-- Every source index of the actual generated one-clock is adapted to the
analysis filtration at that index and integrable under `originalLaw`. The
zero branches at index zero, outside the selected block, and after the horizon
are included. -/
theorem oneClock_source_regular (n : ℕ) :
    StronglyMeasurable[analysisFiltration p n]
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n) ∧
      Integrable
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n)
        (originalLaw p) := by
  cases n with
  | zero =>
      constructor
      · change StronglyMeasurable[analysisFiltration p 0]
          (fun _ : Coordinates p => (0 : ℝ))
        exact stronglyMeasurable_const
      · change Integrable (fun _ : Coordinates p => (0 : ℝ)) (originalLaw p)
        exact integrable_const 0
  | succ n =>
      by_cases hn : n < p.T
      · let t : Fin p.T := ⟨n, hn⟩
        by_cases ht : t ∈ calendarBlock p s
        · have htest := testValue_adapted_integrable ids rewards C_star C_h eta s t ht
            (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)
            (oneClockTest_measurable ids rewards rowCompletion scalarCompletion s focal t)
            1 (by norm_num)
            (oneClockTest_abs_le_one ids rewards rowCompletion scalarCompletion s focal t)
          have hclock :
              oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
                  (n + 1) =
                testValue p ids rewards C_star C_h eta s t
                  (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) := by
            funext e
            simpa [GeneratedClockConditionalMeans.sourceClockIndex, t] using
              (oneClock_at_sourceIndex ids rewards C_star C_h eta rowCompletion
                scalarCompletion s t ht focal e)
          rw [hclock]
          constructor
          · have hm : Measurable[analysisFiltration p (n + 1)]
                (testValue p ids rewards C_star C_h eta s t
                  (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)) := by
              simpa [t] using htest.1
            exact hm.stronglyMeasurable
          · exact htest.2
        · have hclock :
              oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
                  (n + 1) = fun _ => 0 := by
            funext e
            simp [GeneratedClockConditionalMeans.oneClock, hn, ht, t]
          rw [hclock]
          exact ⟨stronglyMeasurable_const, integrable_const 0⟩
      · have hclock :
            oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
                (n + 1) = fun _ => 0 := by
          funext e
          simp [GeneratedClockConditionalMeans.oneClock, hn]
        rw [hclock]
        exact ⟨stronglyMeasurable_const, integrable_const 0⟩

/-- The actual one-clock is pointwise the scaled discovery clock plus the
multicast clock on every source index, including all analytic zero branches. -/
theorem oneClock_eq_discovery_div_add_multicast (n : ℕ) (e : Coordinates p) :
    oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e =
      discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s n e / 8 +
        multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e := by
  cases n with
  | zero =>
      simp [GeneratedClockConditionalMeans.oneClock,
        GeneratedClockConditionalMeans.discoveryClock,
        GeneratedClockConditionalMeans.multicastClock]
  | succ n =>
      by_cases hn : n < p.T
      · let t : Fin p.T := ⟨n, hn⟩
        by_cases ht : t ∈ calendarBlock p s
        · simp [GeneratedClockConditionalMeans.oneClock,
            GeneratedClockConditionalMeans.discoveryClock,
            GeneratedClockConditionalMeans.multicastClock,
            GeneratedClockConditionalMeans.oneClockTest,
            GeneratedBootstrapFiltration.testValue, hn, ht, t]
        · simp [GeneratedClockConditionalMeans.oneClock,
            GeneratedClockConditionalMeans.discoveryClock,
            GeneratedClockConditionalMeans.multicastClock, hn, ht, t]
      · simp [GeneratedClockConditionalMeans.oneClock,
          GeneratedClockConditionalMeans.discoveryClock,
          GeneratedClockConditionalMeans.multicastClock, hn]

/-- The stopped generated one-clock test remains pointwise in `[0,1]` at every
source index; all out-of-range branches are the literal zero branch. -/
theorem oneClock_source_unit_bounds (n : ℕ) (e : Coordinates p) :
    0 ≤ oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ∧
      oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ≤ 1 := by
  cases n with
  | zero =>
      simp [GeneratedClockConditionalMeans.oneClock]
  | succ n =>
      by_cases hn : n < p.T
      · let t : Fin p.T := ⟨n, hn⟩
        by_cases ht : t ∈ calendarBlock p s
        · simpa [GeneratedClockConditionalMeans.oneClock, hn, ht, t,
            GeneratedBootstrapFiltration.testValue] using
            oneClockTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal
              (descriptor p ids rewards C_star C_h eta s t e, current p t e)
        · simp [GeneratedClockConditionalMeans.oneClock, hn, ht, t]
      · simp [GeneratedClockConditionalMeans.oneClock, hn]

private theorem intervalSum_eq_calendarBlock_sum
    (Y : ℕ → Coordinates p → ℝ) (e : Coordinates p) :
    BootstrapIntervalBounds.intervalSum Y (blockClockStart p s) (blockClockEnd p s)
        (blockClockEnd p s) e =
      ∑ t ∈ calendarBlock p s, Y (GeneratedClockConditionalMeans.sourceClockIndex t) e := by
  classical
  rw [BootstrapIntervalBounds.intervalSum_eq_sum_Icc Y (Nat.le_refl _) e]
  symm
  apply Finset.sum_bij (fun t _ => GeneratedClockConditionalMeans.sourceClockIndex t)
  · intro t ht
    rw [Finset.mem_Icc]
    have hmem :=
      (BootstrapDimensions.mem_calendarBlock_iff_manuscriptRound p s t).mp ht
    simpa [blockClockStart, blockClockEnd, GeneratedClockConditionalMeans.sourceClockIndex,
      BootstrapDimensions.manuscriptRound] using hmem
  · intro t ht u hu htu
    apply Fin.ext
    dsimp [GeneratedClockConditionalMeans.sourceClockIndex] at htu
    omega
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hkα, hkβ⟩
    have hbounds := blockClock_bounds p s
    let t : Fin p.T := ⟨k - 1, by omega⟩
    have hstart : s.val * B_boot p ≤ k - 1 := by
      dsimp [blockClockStart] at hkα
      omega
    have hstop : k - 1 < min p.T ((s.val + 1) * B_boot p) := by
      dsimp [blockClockEnd] at hkβ
      omega
    have ht : t ∈ calendarBlock p s :=
      (BootstrapDimensions.mem_calendarBlock_iff p s t).mpr ⟨hstart, hstop⟩
    refine ⟨t, ht, ?_⟩
    dsimp [GeneratedClockConditionalMeans.sourceClockIndex, t]
    omega
  · intro t ht
    rfl

private theorem intervalSum_oneClock_decomposition (n : ℕ) (e : Coordinates p) :
    BootstrapIntervalBounds.intervalSum
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
        (blockClockStart p s) (blockClockEnd p s) n e =
      BootstrapIntervalBounds.intervalSum
          (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s)
          (blockClockStart p s) (blockClockEnd p s) n e / 8 +
        BootstrapIntervalBounds.intervalSum
          (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
          (blockClockStart p s) (blockClockEnd p s) n e := by
  classical
  unfold BootstrapIntervalBounds.intervalSum
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : blockClockStart p s ≤ k ∧ k ≤ blockClockEnd p s
  · simp only [ite_eq_left h]
    rw [oneClock_eq_discovery_div_add_multicast]
  · simp only [ite_eq_right h, zero_div, zero_add]

/-- The lower interval event is measurable in the original coordinates. -/
theorem clockGood_measurable : MeasurableSet (clockGood ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal) := by
  unfold clockGood
  exact BootstrapIntervalBounds.lowerGood_measurable
    (fun n _ _ => (oneClock_source_regular ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal n).1)
    (4 * (b_N p : ℝ))

/-- Every endpoint in the single fixed source interval satisfies the lower
estimate for the actual conditional mean of the generated one-clock. -/
theorem clockGood_lower_at_every_endpoint (e : Coordinates p)
    (he : e ∈ clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
    (n : ℕ) (hn : n ∈ Set.Icc (blockClockStart p s) (blockClockEnd p s)) :
    BootstrapIntervalBounds.intervalSum
        (BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
          (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal))
        (blockClockStart p s) (blockClockEnd p s) n e / 2 - 4 * (b_N p : ℝ) ≤
      BootstrapIntervalBounds.intervalSum
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
        (blockClockStart p s) (blockClockEnd p s) n e := by
  change ∀ n ∈ Set.Icc (blockClockStart p s) (blockClockEnd p s), _ at he
  exact he n hn

/-- Localization of the actual clock failure holds on every event measurable
at `alpha - 1`, without a positive-mass premise. -/
theorem clockGood_failure_localized (A : Set (Coordinates p))
    (hA : MeasurableSet[analysisFiltration p (blockClockStart p s - 1)] A) :
    (originalLaw p).real
        (A ∩ (clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)ᶜ) ≤
      Real.exp (-(4 * (b_N p : ℝ))) * (originalLaw p).real A := by
  have hbounds := blockClock_bounds p s
  have hX : ∀ n, blockClockStart p s ≤ n → n ≤ blockClockEnd p s →
      StronglyMeasurable[analysisFiltration p n]
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n) :=
    fun n _ _ => (oneClock_source_regular ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal n).1
  have hunit : ∀ n, blockClockStart p s ≤ n → n ≤ blockClockEnd p s →
      ∀ᵐ e ∂originalLaw p,
        0 ≤ oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ∧
          oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ≤ 1 := by
    intro n _ _
    exact ae_of_all _ (oneClock_source_unit_bounds ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal n)
  change MeasurableSet[analysisFiltration p (blockClockStart p s - 1)] A at hA
  exact BootstrapIntervalBounds.lower_failure_localized hX hunit hbounds.1
    hbounds.2.1 (4 * (b_N p : ℝ)) hA

/-- The corresponding almost-everywhere conditional probability at the
original analysis filtration time `alpha - 1`. -/
theorem clockGood_conditional_probability :
    (fun _ => 1 - Real.exp (-(4 * (b_N p : ℝ)))) ≤ᵐ[originalLaw p]
    (originalLaw p)[(clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal).indicator
        (fun _ => (1 : ℝ)) | analysisFiltration p (blockClockStart p s - 1)] := by
  have hbounds := blockClock_bounds p s
  have hX : ∀ n, blockClockStart p s ≤ n → n ≤ blockClockEnd p s →
      StronglyMeasurable[analysisFiltration p n]
        (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n) :=
    fun n _ _ => (oneClock_source_regular ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal n).1
  have hunit : ∀ n, blockClockStart p s ≤ n → n ≤ blockClockEnd p s →
      ∀ᵐ e ∂originalLaw p,
        0 ≤ oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ∧
          oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal n e ≤ 1 := by
    intro n _ _
    exact ae_of_all _ (oneClock_source_unit_bounds ids rewards C_star C_h eta
      rowCompletion scalarCompletion s focal n)
  exact BootstrapIntervalBounds.lower_conditional_probability hX hunit
    hbounds.1 hbounds.2.1 (4 * (b_N p : ℝ))

/-- Source dimensions give both requested failure-probability comparisons for
the manuscript tilt `ell = 4 * b_N`. -/
theorem source_clock_failure_exponent_bound (p : ConstructorDimensions.Parameters) :
    Real.exp (-(4 * (b_N p : ℝ))) ≤ (1 / (N p : ℝ)) ^ 2 ∧
      Real.exp (-(4 * (b_N p : ℝ))) < 1 / 8 := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have htwoN : (N p : ℝ) ≤ 2 * (N p : ℝ) := by nlinarith
  have hlog : Real.log (N p : ℝ) ≤ 2 * (b_N p : ℝ) :=
    (Real.log_le_log hNpos htwoN).trans (ConstructorDimensions.log_two_mul_N_le p)
  have htilt : -(4 * (b_N p : ℝ)) ≤ -(2 * Real.log (N p : ℝ)) := by
    nlinarith
  have hlogpow : Real.log ((N p : ℝ) ^ 2) = 2 * Real.log (N p : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hexp : Real.exp (-(2 * Real.log (N p : ℝ))) = 1 / (N p : ℝ) ^ 2 := by
    calc
      Real.exp (-(2 * Real.log (N p : ℝ))) =
          Real.exp (-Real.log ((N p : ℝ) ^ 2)) := by rw [hlogpow]
      _ = (Real.exp (Real.log ((N p : ℝ) ^ 2)))⁻¹ := by rw [Real.exp_neg]
      _ = ((N p : ℝ) ^ 2)⁻¹ := by rw [Real.exp_log (pow_pos hNpos 2)]
      _ = 1 / (N p : ℝ) ^ 2 := by rw [one_div]
  have hNge : 3 ≤ N p := by
    have hm : 2 ≤ p.m := p.two_le_m
    have hmk : p.m < p.K := p.m_lt_K
    have hK : 3 ≤ p.K := by omega
    exact hK.trans (ConstructorDimensions.K_le_N p)
  have hNgeReal : (3 : ℝ) ≤ (N p : ℝ) := by exact_mod_cast hNge
  have hNpow : (9 : ℝ) ≤ (N p : ℝ) ^ 2 := by nlinarith
  have hrecip : 1 / (N p : ℝ) ^ 2 ≤ (1 : ℝ) / 9 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hNpow)
  have hrecip' : 1 / (N p : ℝ) ^ 2 = (1 / (N p : ℝ)) ^ 2 := by
    rw [one_div_pow]
  constructor
  · calc
      Real.exp (-(4 * (b_N p : ℝ))) ≤
          Real.exp (-(2 * Real.log (N p : ℝ))) :=
            Real.exp_le_exp.mpr htilt
      _ = 1 / (N p : ℝ) ^ 2 := hexp
      _ = (1 / (N p : ℝ)) ^ 2 := hrecip'
  · calc
      Real.exp (-(4 * (b_N p : ℝ))) ≤ 1 / (N p : ℝ) ^ 2 := by
        calc
          Real.exp (-(4 * (b_N p : ℝ))) ≤
              Real.exp (-(2 * Real.log (N p : ℝ))) :=
                Real.exp_le_exp.mpr htilt
          _ = 1 / (N p : ℝ) ^ 2 := hexp
      _ ≤ (1 : ℝ) / 9 := hrecip
      _ < 1 / 8 := by norm_num

/-- At the clipped block endpoint, the multicast calendar sum is bounded by
the actual conditional-mean calendar sum and the actual discovery sum. This
is the interval-clock conclusion before the separately owned balance inputs. -/
theorem clockGood_multicast_calendar_lower (e : Coordinates p)
    (he : e ∈ clockGood ids rewards C_star C_h eta rowCompletion scalarCompletion s focal) :
    ∑ t ∈ calendarBlock p s,
        multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
          (GeneratedClockConditionalMeans.sourceClockIndex t) e ≥
      (∑ t ∈ calendarBlock p s,
        BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
          (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
          (GeneratedClockConditionalMeans.sourceClockIndex t) e) / 2 - 4 * (b_N p : ℝ) -
      (∑ t ∈ calendarBlock p s,
        discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s
          (GeneratedClockConditionalMeans.sourceClockIndex t) e) / 8 := by
  have hbounds := blockClock_bounds p s
  have hendpoint := clockGood_lower_at_every_endpoint ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal e he (blockClockEnd p s)
    ⟨hbounds.2.1, le_rfl⟩
  rw [intervalSum_oneClock_decomposition ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal (blockClockEnd p s) e] at hendpoint
  rw [intervalSum_eq_calendarBlock_sum s (BootstrapIntervalBounds.conditionalMean (originalLaw p)
      (analysisFiltration p)
      (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)) e] at hendpoint
  rw [intervalSum_eq_calendarBlock_sum s
      (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s) e] at hendpoint
  rw [intervalSum_eq_calendarBlock_sum s
      (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal) e] at hendpoint
  linarith

end Bandits.Support.GeneratedClockBlockTail

end
