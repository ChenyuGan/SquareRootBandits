/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalQueueProcess
public import Bandits.Support.RecordedMarginalGrowth
public import Bandits.Support.RecordedQueueSummation
public import Bandits.Support.RecordedRoundMoments
public import Bandits.Support.RecordedWeightedDrift

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Marginal-change correction on the canonical finite queue process

The correction is evaluated on the actual successor state of every generated
calendar round. Its one-step estimate uses the retained first overflowing
update and the canonical recorded-arm kernel. It does not identify the
arbitrary causal policy with the episode scheduler or establish a manuscript
queue or regret lemma.

Sources: sources/zip4/manuscript/04_slow_fast_learner.tex:140-174,182-187
(actual score and backlog updates, including the first overflow update),
:256-264 (raw first moments), and :428-452 (the signed marginal-change
term in summation by parts).
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.CanonicalQueueProcess
open Bandits.Support.RecordedQueueRun
open Bandits.Support.RecordedRoundMoments
open Bandits.Support.RecordedWeightedDrift
open Bandits.Support.StoppedQueueBound
open Bandits.Support.ProductSetLaw
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ConstructorDimensions
open scoped BigOperators

namespace Bandits.Support.CanonicalQueueCorrection

variable (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
  (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
  (n : ℕ) (hn : (n : ℝ) = eta * (D p : ℝ))
  (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
  (policy : CanonicalQueueProcess.Policy p)

local notation "q" => CanonicalQueueProcess.queueParameters p eta heta hcap n hn

/-- The signed marginal-change correction on the actual generated successor
of round t, including the backlog after that round's update. -/
noncomputable def roundCorrection (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val)
    (o : Option (Fin p.K)) : ℝ :=
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let sNext := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o)
  ∑ i : Fin p.K,
    (theta p.m (scoreWeight q sNext) i - theta p.m (scoreWeight q s) i) *
      normalizedBacklog q sNext i

/-- The retained incoming-state test and weighted backlog for an actual
calendar prefix. -/
noncomputable def retainedWeightedBacklog (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val) : ℝ :=
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  if policy.enabled t h = true ∧ s.overflow = false then
    RecordedWeightedDrift.weightedBacklog p.m q s
  else 0

/-- Conditional one-step correction budget: it is zero on disabled and
incoming-overflowed calendar steps. -/
noncomputable def conditionalCorrectionBudget (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val) : ℝ :=
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  if policy.enabled t h = true ∧ s.overflow = false then
    RecordedWeightedDrift.weightedBacklog p.m q s + (p.m : ℝ)
  else 0

/-- Chronological accumulation over the existing nested outcome history.
Every calendar extension contributes its actual signed correction. -/
noncomputable def accumulatedCorrection : (t : ℕ) → t ≤ p.T →
    CanonicalQueueProcess.History p.K t → ℝ
  | 0, _, _ => 0
  | t + 1, ht, h =>
      accumulatedCorrection t (Nat.le_of_succ_le ht) h.1 +
        roundCorrection p eta heta hcap n hn rewards policy
          ⟨t, Nat.lt_of_succ_le ht⟩ h.1 h.2

/-- On a disabled or incoming-overflowed step, every inclusion marginal is
preserved, so the signed correction is exactly zero. -/
theorem roundCorrection_eq_zero_of_inactive (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val)
    (o : Option (Fin p.K))
    (hinactive : policy.enabled t h = false ∨
      (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
        t.val t.isLt.le h).overflow = true) :
    roundCorrection p eta heta hcap n hn rewards policy t h o = 0 := by
  classical
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let r := CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
    (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
      t.val t.isLt.le h) o
  have hstep : CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
      (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o) = step q s r := by
    simpa [s, r] using CanonicalQueueProcess.prefixState_succ p eta heta hcap n hn
      rewards policy t.val (Nat.succ_le_of_lt t.isLt) h o
  have htheta (i : Fin p.K) :
      theta p.m (scoreWeight q
          (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
            (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o))) i =
        theta p.m (scoreWeight q s) i := by
    rw [hstep]
    apply RecordedMarginalGrowth.step_theta_eq_of_disabled_or_overflowed
    · exact hinactive
  simp [roundCorrection, s, htheta]

/-- The actual one-step correction is bounded by the current inclusion-weighted
backlog plus the actual raw arrivals, on an enabled non-overflow incoming
state. -/
theorem roundCorrection_le_raw (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val)
    (o : Option (Fin p.K))
    (henabled : policy.enabled t h = true)
    (hnotOverflow : (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards
      policy t.val t.isLt.le h).overflow = false) :
    roundCorrection p eta heta hcap n hn rewards policy t h o ≤
      8 * eta * ∑ i : Fin p.K,
        theta p.m (scoreWeight q
          (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
            t.val t.isLt.le h)) i *
          (normalizedBacklog q
              (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
                t.val t.isLt.le h) i +
            rawEstimate q
              (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
                t.val t.isLt.le h)
              (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
                  t.val t.isLt.le h) o) i) := by
  classical
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let r := CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h rounds o
  let sNext := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o)
  have hstep : sNext = step q s r := by
    simpa [sNext, s, r, rounds] using CanonicalQueueProcess.prefixState_succ p eta heta
      hcap n hn rewards policy t.val (Nat.succ_le_of_lt t.isLt) h o
  have hroundEnabled : r.enabled = true := by
    dsimp [r, CanonicalQueueProcess.nextInput]
    exact henabled
  have hbacklog_nonneg (i : Fin p.K) : 0 ≤ normalizedBacklog q s i := by
    change 0 ≤ ((s.registers i).2 : ℝ) / (n : ℝ)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hraw_nonneg (i : Fin p.K) : 0 ≤ rawEstimate q s r i :=
    RecordedRoundMoments.rawEstimate_nonneg q s r i
  have htheta_nonneg (i : Fin p.K) : 0 ≤ theta p.m (scoreWeight q s) i :=
    (RecordedMarginalGrowth.state_theta_pos q s i (ConstructorDimensions.m_pos p)
      p.m_lt_K).le
  have hbacklog_succ (i : Fin p.K) :
      normalizedBacklog q sNext i ≤ normalizedBacklog q s i + rawEstimate q s r i := by
    rw [hstep, CanonicalQueueProcess.normalizedBacklog_step_of_retained q s r i
      hnotOverflow hroundEnabled]
    apply max_le
    · linarith
    · exact add_nonneg (hbacklog_nonneg i) (hraw_nonneg i)
  have heta64 : eta ≤ 1 / 64 :=
    RecordedWeightedDrift.eta_le_one_div_sixtyFour p q hcap
  have htheta_growth (i : Fin p.K) :
      theta p.m (scoreWeight q sNext) i ≤
        (1 + 8 * eta) * theta p.m (scoreWeight q s) i := by
    have h := RecordedMarginalGrowth.step_theta_growth q s r i
      p.two_le_m p.m_lt_K heta64
    rw [hstep]
    exact h.1.trans h.2
  have hterm (i : Fin p.K) :
      (theta p.m (scoreWeight q sNext) i - theta p.m (scoreWeight q s) i) *
          normalizedBacklog q sNext i ≤
        8 * eta * (theta p.m (scoreWeight q s) i *
          (normalizedBacklog q s i + rawEstimate q s r i)) := by
    have hdiff : theta p.m (scoreWeight q sNext) i -
        theta p.m (scoreWeight q s) i ≤
          8 * eta * theta p.m (scoreWeight q s) i := by
      linarith [htheta_growth i]
    have hcoef : 0 ≤ 8 * eta * theta p.m (scoreWeight q s) i :=
      mul_nonneg (by positivity [heta]) (htheta_nonneg i)
    have hnext_nonneg : 0 ≤ normalizedBacklog q sNext i := by
      change 0 ≤ ((sNext.registers i).2 : ℝ) / (n : ℝ)
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      _ ≤ (8 * eta * theta p.m (scoreWeight q s) i) *
          normalizedBacklog q sNext i :=
        mul_le_mul_of_nonneg_right hdiff hnext_nonneg
      _ ≤ (8 * eta * theta p.m (scoreWeight q s) i) *
          (normalizedBacklog q s i + rawEstimate q s r i) :=
        mul_le_mul_of_nonneg_left (hbacklog_succ i) hcoef
      _ = 8 * eta * (theta p.m (scoreWeight q s) i *
          (normalizedBacklog q s i + rawEstimate q s r i)) := by ring
  calc
    roundCorrection p eta heta hcap n hn rewards policy t h o =
        ∑ i : Fin p.K,
          (theta p.m (scoreWeight q sNext) i - theta p.m (scoreWeight q s) i) *
            normalizedBacklog q sNext i := by
      simp [roundCorrection, s, sNext]
    _ ≤ ∑ i : Fin p.K,
          8 * eta * (theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i + rawEstimate q s r i)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = 8 * eta * ∑ i : Fin p.K,
          theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i + rawEstimate q s r i) := by
      rw [Finset.mul_sum]

/-- Under the actual next-kernel, the expected signed correction is controlled
by the retained incoming weighted backlog and one comparator-size term. The
canonical rate validity and raw first moments are obtained from the constructors
inside CanonicalQueueProcess and RecordedRoundMoments. -/
theorem roundCorrection_nextKernel_integral_le (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val) :
    ∫ o, roundCorrection p eta heta hcap n hn rewards policy t h o
      ∂(CanonicalQueueProcess.nextKernel p eta heta hcap n hn rewards policy t h).toMeasure ≤
        8 * eta * conditionalCorrectionBudget p eta heta hcap n hn rewards policy t h := by
  classical
  let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let s := CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let rates := CanonicalQueueProcess.canonicalRates p eta heta hcap
    (CanonicalQueueProcess.selectedAnchor p eta heta hcap n hn policy t h rounds)
    (CanonicalQueueProcess.selectedAnchor_pos p eta heta hcap n hn policy t h rounds)
  have hkernel :
      CanonicalQueueProcess.nextKernel p eta heta hcap n hn rewards policy t h =
        CanonicalQueueProcess.roundKernel s rates (policy.enabled t h) := by
    rfl
  have hnextInput (o : Option (Fin p.K)) :
      CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h rounds o =
        RecordedRoundMoments.fixedRoundInput q rates (rewards.reward t)
          (rewards.reward_mem_Icc t) (policy.enabled t h) o := by
    rfl
  by_cases hactive : policy.enabled t h = true ∧ s.overflow = false
  · obtain ⟨henabled, hnotOverflow⟩ := hactive
    have hrawmean (i : Fin p.K) :
        ∫ o, rawEstimate q s
            (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
              rounds o) i ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure ≤ 1 := by
      have hm := RecordedRoundMoments.rawEstimate_firstMoment_bounds q s rates
        (rewards.reward t) (rewards.reward_mem_Icc t) i hnotOverflow
      simpa [hnextInput, henabled] using hm.2.1.trans hm.2.2
    have htheta_nonneg (i : Fin p.K) : 0 ≤ theta p.m (scoreWeight q s) i :=
      (RecordedMarginalGrowth.state_theta_pos q s i (ConstructorDimensions.m_pos p)
        p.m_lt_K).le
    have hsumtheta := RecordedMarginalGrowth.state_sum_theta_eq_m q s
      (ConstructorDimensions.m_pos p) p.m_lt_K
    have hcoordinate (i : Fin p.K) :
        theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i +
              ∫ o, rawEstimate q s
                (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                  rounds o) i
                ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) ≤
          theta p.m (scoreWeight q s) i * normalizedBacklog q s i +
            theta p.m (scoreWeight q s) i := by
      have hmul := mul_le_mul_of_nonneg_left (hrawmean i) (htheta_nonneg i)
      nlinarith only [hmul]
    have hsumBound :
        ∑ i : Fin p.K, theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i +
              ∫ o, rawEstimate q s
                (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                  rounds o) i
                ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) ≤
          RecordedWeightedDrift.weightedBacklog p.m q s + (p.m : ℝ) := by
      calc
        _ ≤ ∑ i : Fin p.K,
              (theta p.m (scoreWeight q s) i * normalizedBacklog q s i +
                theta p.m (scoreWeight q s) i) :=
          Finset.sum_le_sum fun i _ => hcoordinate i
        _ = RecordedWeightedDrift.weightedBacklog p.m q s + (p.m : ℝ) := by
          rw [Finset.sum_add_distrib, hsumtheta]
          rfl
    have htermIntegral (i : Fin p.K) :
        ∫ o, theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i +
              rawEstimate q s
                (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                  rounds o) i)
            ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure =
          theta p.m (scoreWeight q s) i *
            (normalizedBacklog q s i +
              ∫ o, rawEstimate q s
                (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                  rounds o) i
                ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) := by
      rw [integral_const_mul,
        integral_add (integrable_const _) (Integrable.of_finite), integral_const,
        probReal_univ, smul_eq_mul, one_mul]
    have hmajorIntegral :
        ∫ o, 8 * eta * ∑ i : Fin p.K,
            theta p.m (scoreWeight q s) i *
              (normalizedBacklog q s i +
                rawEstimate q s
                  (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                    rounds o) i)
            ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure =
          8 * eta * ∑ i : Fin p.K,
            theta p.m (scoreWeight q s) i *
              (normalizedBacklog q s i +
                ∫ o, rawEstimate q s
                  (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                    rounds o) i
                  ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun _ _ => Integrable.of_finite)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact htermIntegral i
    have hpoint (o : Option (Fin p.K)) :
        roundCorrection p eta heta hcap n hn rewards policy t h o ≤
          8 * eta * ∑ i : Fin p.K,
            theta p.m (scoreWeight q s) i *
              (normalizedBacklog q s i +
                rawEstimate q s
                  (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                    rounds o) i) := by
      simpa [s, rounds] using roundCorrection_le_raw p eta heta hcap n hn rewards policy
        t h o henabled hnotOverflow
    rw [hkernel, CanonicalQueueProcess.roundKernel_of_active s rates
      (policy.enabled t h) henabled hnotOverflow]
    calc
      _ ≤ ∫ o, 8 * eta * ∑ i : Fin p.K,
            theta p.m (scoreWeight q s) i *
              (normalizedBacklog q s i +
                rawEstimate q s
                  (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                    rounds o) i)
            ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure :=
        integral_mono Integrable.of_finite Integrable.of_finite hpoint
      _ = 8 * eta * ∑ i : Fin p.K,
            theta p.m (scoreWeight q s) i *
              (normalizedBacklog q s i +
                ∫ o, rawEstimate q s
                  (CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h
                    rounds o) i
                  ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) := hmajorIntegral
      _ ≤ 8 * eta *
            (RecordedWeightedDrift.weightedBacklog p.m q s + (p.m : ℝ)) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity [heta])
      _ = 8 * eta *
            conditionalCorrectionBudget p eta heta hcap n hn rewards policy t h := by
        simp [conditionalCorrectionBudget, s, henabled, hnotOverflow]
  · have hinactive : policy.enabled t h = false ∨ s.overflow = true := by
      cases hen : policy.enabled t h <;> cases hs : s.overflow <;> simp_all
    have hzero (o : Option (Fin p.K)) :
        roundCorrection p eta heta hcap n hn rewards policy t h o = 0 := by
      apply roundCorrection_eq_zero_of_inactive p eta heta hcap n hn rewards policy t h o
      simpa [s] using hinactive
    rw [hkernel, CanonicalQueueProcess.roundKernel_of_inactive s rates
      (policy.enabled t h) hinactive]
    simp_rw [hzero]
    have hnotActive : ¬ (policy.enabled t h = true ∧ s.overflow = false) := by
      rintro ⟨he, hs⟩
      rcases hinactive with hd | ho
      · rw [hd] at he
        cases he
      · rw [ho] at hs
        cases hs
    simp [conditionalCorrectionBudget, s, hnotActive]



/-- The retained weighted backlog expectation at one actual calendar prefix. -/
noncomputable def retainedBacklogExpectation (t : Fin p.T) : ℝ :=
  ∫ h, retainedWeightedBacklog p eta heta hcap n hn rewards policy t h
    ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
      t.val t.isLt.le).toMeasure

/-- Sum of retained weighted-backlog expectations through the first t rounds.
Each summand is evaluated under that calendar prefix's actual path law. -/
noncomputable def retainedBacklogExpectationSum (t : ℕ) (ht : t ≤ p.T) : ℝ :=
  ∑ j : Fin t,
    retainedBacklogExpectation p eta heta hcap n hn rewards policy
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt ht⟩

/-- Appending one outcome adds precisely the correction from that actual
generated calendar round. -/
theorem accumulatedCorrection_succ (t : ℕ) (ht : t + 1 ≤ p.T)
    (h : CanonicalQueueProcess.History p.K t)
    (o : Option (Fin p.K)) :
    accumulatedCorrection p eta heta hcap n hn rewards policy
        (t + 1) ht (h, o) =
      accumulatedCorrection p eta heta hcap n hn rewards policy
        t (Nat.le_of_succ_le ht) h +
        roundCorrection p eta heta hcap n hn rewards policy
          ⟨t, Nat.lt_of_succ_le ht⟩ h o := rfl

/-- The one-step correction equals the signed marginal-change sum on the
generated round list. Its successor backlog is evaluated after the actual
generated update, as required by queue summation by parts. -/
theorem roundCorrection_eq_generatedRun_sum (t : Fin p.T)
    (h : CanonicalQueueProcess.History p.K t.val)
    (o : Option (Fin p.K)) :
    roundCorrection p eta heta hcap n hn rewards policy t h o =
      ∑ i : Fin p.K,
        (RecordedQueueSummation.runMarginal q p.m
            (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
              (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o))
            (t.val + 1) i -
          RecordedQueueSummation.runMarginal q p.m
            (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
              (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o))
            t.val i) *
          normalizedBacklog q
            (RecordedQueueRun.run q
              (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
                (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o))) i := by
  classical
  let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
    t.val t.isLt.le h
  let r := CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy t h rounds o
  let nextRounds := rounds ++ [r]
  have hgeneratedRounds :
      CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
        (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o) = nextRounds := by
    simp [nextRounds, rounds, CanonicalQueueProcess.generatedRounds, r]
  have hlength : rounds.length = t.val :=
    CanonicalQueueProcess.generatedRounds_length p eta heta hcap n hn rewards policy
      t.val t.isLt.le h
  have htake : nextRounds.take t.val = rounds := by
    dsimp [nextRounds]
    rw [List.take_append_of_le_length (le_of_eq hlength.symm)]
    exact List.take_of_length_le (le_of_eq hlength)
  have hstateCurrent :
      CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
        t.val t.isLt.le h =
        run q (nextRounds.take t.val) := by
    change run q rounds = run q (nextRounds.take t.val)
    rw [htake]
  have hstateNextFull :
      CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
        (t.val + 1) (Nat.succ_le_of_lt t.isLt) (h, o) =
        run q nextRounds := by
    unfold CanonicalQueueProcess.prefixState
    rw [hgeneratedRounds]
  have hlengthNext : nextRounds.length = t.val + 1 := by
    simp [nextRounds, hlength]
  have htakeNext : nextRounds.take (t.val + 1) = nextRounds :=
    List.take_of_length_le (le_of_eq hlengthNext)
  simp [roundCorrection, RecordedQueueSummation.runMarginal,
    hstateCurrent, hstateNextFull, hgeneratedRounds, htake, htakeNext]



/-- Sum of the conditional one-step bounds over the actual history law. -/
theorem roundCorrection_pathLaw_integral_le (t : Fin p.T) :
    ∫ h,
        (∫ o, roundCorrection p eta heta hcap n hn rewards policy t h o
          ∂(CanonicalQueueProcess.nextKernel p eta heta hcap n hn rewards policy t h).toMeasure)
        ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
          t.val t.isLt.le).toMeasure ≤
      8 * eta * (retainedBacklogExpectation p eta heta hcap n hn rewards policy t +
        (p.m : ℝ)) := by
  calc
    _ ≤ ∫ h, 8 * eta *
          conditionalCorrectionBudget p eta heta hcap n hn rewards policy t h
          ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
            t.val t.isLt.le).toMeasure :=
      integral_mono Integrable.of_finite Integrable.of_finite fun h =>
        roundCorrection_nextKernel_integral_le p eta heta hcap n hn rewards policy t h
    _ ≤ ∫ h, 8 * eta *
          (retainedWeightedBacklog p eta heta hcap n hn rewards policy t h +
            (p.m : ℝ))
          ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
            t.val t.isLt.le).toMeasure :=
      integral_mono Integrable.of_finite Integrable.of_finite fun h => by
        apply mul_le_mul_of_nonneg_left
        · by_cases hactive : policy.enabled t h = true ∧
              (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
                t.val t.isLt.le h).overflow = false
          · simp [conditionalCorrectionBudget, retainedWeightedBacklog, hactive]
          · have hnotActive : ¬ (policy.enabled t h = true ∧
                (CanonicalQueueProcess.prefixState p eta heta hcap n hn rewards policy
                  t.val t.isLt.le h).overflow = false) := hactive
            simp [conditionalCorrectionBudget, retainedWeightedBacklog, hnotActive]
        · positivity [heta]
    _ = 8 * eta *
          (retainedBacklogExpectation p eta heta hcap n hn rewards policy t + (p.m : ℝ)) := by
      rw [integral_const_mul,
        integral_add Integrable.of_finite (integrable_const _), integral_const,
        probReal_univ, smul_eq_mul, one_mul]
      rfl



/-- The retained-backlog expectation sum gains exactly the expectation at the
new calendar prefix when its horizon is extended by one. -/
theorem retainedBacklogExpectationSum_succ (t : ℕ) (ht : t + 1 ≤ p.T) :
    retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
        (t + 1) ht =
      retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
          t (Nat.le_of_succ_le ht) +
        retainedBacklogExpectation p eta heta hcap n hn rewards policy
          ⟨t, Nat.lt_of_succ_le ht⟩ := by
  unfold retainedBacklogExpectationSum
  rw [Fin.sum_univ_castSucc]
  simp [retainedBacklogExpectation]

/-- Chronological accumulated correction under the true path law is bounded by
the sum of expected retained weighted backlogs plus m per calendar round. No
bound on that remaining weighted-backlog sum is assumed here. -/
theorem accumulatedCorrection_pathLaw_integral_le :
    ∀ (t : ℕ) (ht : t ≤ p.T),
      ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy t ht h
        ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure ≤
        8 * eta * (retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
          t ht + (p.m : ℝ) * (t : ℝ)) := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp [accumulatedCorrection, retainedBacklogExpectationSum]
  | succ t ih =>
      intro ht
      let law := CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
        t (Nat.le_of_succ_le ht)
      let kernel (h : CanonicalQueueProcess.History p.K t) :=
        CanonicalQueueProcess.nextKernel p eta heta hcap n hn rewards policy
          ⟨t, Nat.lt_of_succ_le ht⟩ h
      have hsplit :
          ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy
              (t + 1) ht h
              ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
                (t + 1) ht).toMeasure =
            ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy
                t (Nat.le_of_succ_le ht) h ∂law.toMeasure +
              ∫ h, ∫ o, roundCorrection p eta heta hcap n hn rewards policy
                  ⟨t, Nat.lt_of_succ_le ht⟩ h o ∂(kernel h).toMeasure
                ∂law.toMeasure := by
        rw [CanonicalQueueProcess.integral_pathLaw_succ p eta heta hcap n hn rewards policy
          t ht]
        calc
          _ = ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy
                t (Nat.le_of_succ_le ht) h +
                ∫ o, roundCorrection p eta heta hcap n hn rewards policy
                  ⟨t, Nat.lt_of_succ_le ht⟩ h o ∂(kernel h).toMeasure
                ∂law.toMeasure := by
            apply integral_congr_ae
            filter_upwards [] with h
            simp only [accumulatedCorrection]
            rw [integral_add (integrable_const _) Integrable.of_finite,
              integral_const, probReal_univ, smul_eq_mul, one_mul]
          _ = ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy
                t (Nat.le_of_succ_le ht) h ∂law.toMeasure +
              ∫ h, ∫ o, roundCorrection p eta heta hcap n hn rewards policy
                  ⟨t, Nat.lt_of_succ_le ht⟩ h o ∂(kernel h).toMeasure
                ∂law.toMeasure := by
            rw [integral_add Integrable.of_finite Integrable.of_finite]
      have hstep := roundCorrection_pathLaw_integral_le p eta heta hcap n hn rewards policy
        ⟨t, Nat.lt_of_succ_le ht⟩
      have ih' := ih (Nat.le_of_succ_le ht)
      have hsum := retainedBacklogExpectationSum_succ p eta heta hcap n hn rewards policy
        t ht
      rw [hsplit]
      calc
        _ ≤ 8 * eta *
              (retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
                t (Nat.le_of_succ_le ht) + (p.m : ℝ) * (t : ℝ)) +
            8 * eta *
              (retainedBacklogExpectation p eta heta hcap n hn rewards policy
                ⟨t, Nat.lt_of_succ_le ht⟩ + (p.m : ℝ)) :=
          add_le_add ih' hstep
        _ = 8 * eta *
              (retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
                (t + 1) ht + (p.m : ℝ) * ((t + 1 : ℕ) : ℝ)) := by
          rw [hsum]
          push_cast
          ring

/-- The terminal accumulated correction expectation is bounded by the exact
sum of retained weighted-backlog expectations over all calendar rounds, plus
m times the horizon. -/
theorem terminal_accumulatedCorrection_expectation_le :
    ∫ h, accumulatedCorrection p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T) h
      ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T)).toMeasure ≤
      8 * eta *
        (retainedBacklogExpectationSum p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) + (p.m : ℝ) * (p.T : ℝ)) :=
  accumulatedCorrection_pathLaw_integral_le p eta heta hcap n hn rewards policy
    p.T (Nat.le_refl p.T)

end Bandits.Support.CanonicalQueueCorrection

end
