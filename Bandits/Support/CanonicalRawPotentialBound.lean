/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedPotentialTelescope
public import Bandits.Support.RecordedQueueSummation
public import Bandits.Support.CanonicalQueueProcess
public import Bandits.Support.CanonicalQueueCorrection

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Raw potential and retained-backlog bound on the canonical queue process

This module assembles the existing served-potential and queue summation results
on the actual generated round list. The signed successor-backlog corrections
are identified by recursion on the nested history with the accumulated
correction in CanonicalQueueCorrection. The expected bound retains the
weighted-backlog expectation sum for the downstream weighted-drift producer.

Sources: sources/zip4/manuscript/04_slow_fast_learner.tex:306-318 and
:393-452.
-/

@[expose] public section

open scoped BigOperators

namespace Bandits.Support.CanonicalRawPotentialBound

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalQueueProcess
open Bandits.Support.CanonicalQueueCorrection
open Bandits.Support.RecordedQueueRun
open Bandits.Support.RecordedPotentialStep
open Bandits.Support.RecordedQueueSummation
open Bandits.Support.RecordedPotentialTelescope
open Bandits.Support.ProductSetLaw
open Bandits.Support.StoppedQueueBound
open MeasureTheory

variable (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
  (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
  (n : ℕ) (hn : (n : ℝ) = eta * (D p : ℝ))
  (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
  (policy : CanonicalQueueProcess.Policy p)

local notation "q" => CanonicalQueueProcess.queueParameters p eta heta hcap n hn

/-- The actual raw comparator-minus-marginal sum on the generated prefix.
Each arrival, score prefix, and marginal is taken from the existing canonical
finite process. In particular, disabled and post-overflow calendar rounds
remain in the generated list. -/
noncomputable def generatedRawComparatorMinusMarginalSum
    (t : ℕ) (ht : t ≤ p.T) (h : CanonicalQueueProcess.History p.K t)
    (S : ProductSet p.K p.m) : ℝ :=
  let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn
    rewards policy t ht h
  let rawArrival := fun (j : Fin rounds.length) (i : Fin p.K) =>
    (RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord q
        (RecordedQueueRun.run q (rounds.take j.val)) rounds[j.val] i) : ℝ) /
      ((CanonicalQueueProcess.queueParameters p eta heta hcap n hn).n : ℝ)
  ∑ j : Fin rounds.length,
    ((∑ i ∈ S.1, rawArrival j i) -
      ∑ i : Fin p.K,
        RecordedQueueSummation.runMarginal q p.m rounds j.val i * rawArrival j i)

/-- Every generated-prefix signed successor-backlog sum is exactly the
chronological accumulated correction on that same nested history. The proof
uses the empty-prefix base case and the actual append recursion of
generatedRounds. -/
theorem generatedCorrectionSum_eq_accumulatedCorrection
    (t : ℕ) (ht : t ≤ p.T) (h : CanonicalQueueProcess.History p.K t) :
    (∑ j : Fin t, ∑ i : Fin p.K,
      (RecordedQueueSummation.runMarginal q p.m
          (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
            t ht h) (j.val + 1) i -
        RecordedQueueSummation.runMarginal q p.m
          (CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
            t ht h) j.val i) *
        StoppedQueueBound.normalizedBacklog q
          (RecordedQueueRun.run q
            ((CanonicalQueueProcess.generatedRounds p eta heta hcap n hn rewards policy
              t ht h).take (j.val + 1))) i) =
      CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
        t ht h := by
  classical
  induction t with
  | zero =>
      simp [CanonicalQueueProcess.generatedRounds,
        CanonicalQueueCorrection.accumulatedCorrection]
  | succ t ih =>
      obtain ⟨hprev, o⟩ := h
      let previous := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn
        rewards policy t (Nat.le_of_succ_le ht) hprev
      let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn
        rewards policy (t + 1) ht (hprev, o)
      have hpreviousLength : previous.length = t := by
        simpa [previous] using CanonicalQueueProcess.generatedRounds_length
          p eta heta hcap n hn rewards policy t (Nat.le_of_succ_le ht) hprev
      have hroundsLength : rounds.length = t + 1 := by
        simpa [rounds] using CanonicalQueueProcess.generatedRounds_length
          p eta heta hcap n hn rewards policy (t + 1) ht (hprev, o)
      have happend : rounds = previous ++
          [CanonicalQueueProcess.nextInput p eta heta hcap n hn rewards policy
            ⟨t, Nat.lt_of_succ_le ht⟩ hprev previous o] := rfl
      have htake (r : ℕ) (hr : r ≤ t) : rounds.take r = previous.take r := by
        rw [happend, List.take_append_of_le_length (by rw [hpreviousLength]; exact hr)]
      have hterm (j : Fin t) :
          (∑ i : Fin p.K,
            (RecordedQueueSummation.runMarginal q p.m rounds (j.val + 1) i -
              RecordedQueueSummation.runMarginal q p.m rounds j.val i) *
              StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (rounds.take (j.val + 1))) i) =
          (∑ i : Fin p.K,
            (RecordedQueueSummation.runMarginal q p.m previous (j.val + 1) i -
              RecordedQueueSummation.runMarginal q p.m previous j.val i) *
              StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (previous.take (j.val + 1))) i) := by
        simp only [RecordedQueueSummation.runMarginal,
          htake (j.val + 1) (by omega), htake j.val (by omega)]
      have htakeAll : rounds.take (t + 1) = rounds :=
        List.take_of_length_le (by omega)
      have hlast :
          (∑ i : Fin p.K,
            (RecordedQueueSummation.runMarginal q p.m rounds (t + 1) i -
              RecordedQueueSummation.runMarginal q p.m rounds t i) *
              StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (rounds.take (t + 1))) i) =
            CanonicalQueueCorrection.roundCorrection p eta heta hcap n hn rewards policy
              ⟨t, Nat.lt_of_succ_le ht⟩ hprev o := by
        have hc := CanonicalQueueCorrection.roundCorrection_eq_generatedRun_sum
          p eta heta hcap n hn rewards policy ⟨t, Nat.lt_of_succ_le ht⟩ hprev o
        simpa [rounds, htakeAll] using hc.symm
      have hsum :
          (∑ j : Fin t,
            ∑ i : Fin p.K,
              (RecordedQueueSummation.runMarginal q p.m rounds (j.val + 1) i -
                RecordedQueueSummation.runMarginal q p.m rounds j.val i) *
                StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take (j.val + 1))) i) =
            (∑ j : Fin t,
              ∑ i : Fin p.K,
                (RecordedQueueSummation.runMarginal q p.m previous (j.val + 1) i -
                  RecordedQueueSummation.runMarginal q p.m previous j.val i) *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (previous.take (j.val + 1))) i) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      change (∑ j : Fin (t + 1),
          ∑ i : Fin p.K,
            (RecordedQueueSummation.runMarginal q p.m rounds (j.val + 1) i -
              RecordedQueueSummation.runMarginal q p.m rounds j.val i) *
              StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (rounds.take (j.val + 1))) i) =
        CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
          (t + 1) ht (hprev, o)
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      calc
        (∑ j : Fin t,
            ∑ i : Fin p.K,
              (RecordedQueueSummation.runMarginal q p.m rounds (j.val + 1) i -
                RecordedQueueSummation.runMarginal q p.m rounds j.val i) *
                StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take (j.val + 1))) i) +
            ∑ i : Fin p.K,
              (RecordedQueueSummation.runMarginal q p.m rounds (t + 1) i -
                RecordedQueueSummation.runMarginal q p.m rounds t i) *
                StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take (t + 1))) i =
            (∑ j : Fin t,
              ∑ i : Fin p.K,
                (RecordedQueueSummation.runMarginal q p.m previous (j.val + 1) i -
                  RecordedQueueSummation.runMarginal q p.m previous j.val i) *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (previous.take (j.val + 1))) i) +
              CanonicalQueueCorrection.roundCorrection p eta heta hcap n hn rewards policy
                ⟨t, Nat.lt_of_succ_le ht⟩ hprev o := by
          rw [hsum, hlast]
        _ = CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
              t (Nat.le_of_succ_le ht) hprev +
              CanonicalQueueCorrection.roundCorrection p eta heta hcap n hn rewards policy
                ⟨t, Nat.lt_of_succ_le ht⟩ hprev o := by
          rw [ih (Nat.le_of_succ_le ht) hprev]
        _ = CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
              (t + 1) ht (hprev, o) := by
          rw [CanonicalQueueCorrection.accumulatedCorrection_succ]

private theorem four_mul_m_eta_le_one (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p)) :
    4 * (p.m : ℝ) * eta ≤ 1 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hL : (1 : ℝ) ≤ L_stab p := by
    exact_mod_cast (L_stab_ge_one p)
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * L_stab p :=
    one_le_mul_of_one_le_of_one_le hK hL
  have h256 : (1 : ℝ) ≤ 256 * (p.K : ℝ) * L_stab p := by
    nlinarith only [hKL]
  have hfactor :
      4 * (p.m : ℝ) ≤ 1024 * (p.m : ℝ) * p.K * L_stab p := by
    calc
      4 * (p.m : ℝ) = (4 * (p.m : ℝ)) * 1 := by ring
      _ ≤ (4 * (p.m : ℝ)) * (256 * (p.K : ℝ) * L_stab p) :=
        mul_le_mul_of_nonneg_left h256 (by positivity)
      _ = 1024 * (p.m : ℝ) * p.K * L_stab p := by ring
  have hcap' :
      eta * (1024 * (p.m : ℝ) * p.K * L_stab p) ≤ 1 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) <
      1024 * (p.m : ℝ) * p.K * L_stab p)).mp hcap
  calc
    4 * (p.m : ℝ) * eta = eta * (4 * (p.m : ℝ)) := by ring
    _ ≤ eta * (1024 * (p.m : ℝ) * p.K * L_stab p) :=
      mul_le_mul_of_nonneg_left hfactor heta.le
    _ ≤ 1 := hcap'

/-- The actual generated raw gap is bounded pathwise by the one-time served
potential, the terminal stopped-queue bound, and the exact accumulated signed
successor-backlog corrections. The rate condition and small-step premise are
derived from the canonical constructors. -/
theorem generatedRawComparatorMinusMarginalSum_le
    (h : CanonicalQueueProcess.History p.K p.T) (S : ProductSet p.K p.m) :
    generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T) h S ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * p.T +
        (p.m : ℝ) / (16 * eta) +
        CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h := by
  classical
  let rounds := CanonicalQueueProcess.generatedRounds p eta heta hcap n hn
    rewards policy p.T (Nat.le_refl p.T) h
  have hlength : rounds.length = p.T := by
    simpa [rounds] using CanonicalQueueProcess.generatedRounds_length
      p eta heta hcap n hn rewards policy p.T (Nat.le_refl p.T) h
  have htake : rounds.take rounds.length = rounds :=
    List.take_of_length_le (Nat.le_refl rounds.length)
  have hsmall := four_mul_m_eta_le_one p eta heta hcap
  have hrate := CanonicalQueueProcess.generatedRounds_rate_bound
    p eta heta hcap n hn rewards policy p.T (Nat.le_refl p.T) h
  have hpotential := RecordedPotentialTelescope.servedEstimate_cumulative_comparison
    q rounds p.two_le_m p.m_lt_K hsmall S
  have hpotential' :
      (∑ j : Fin rounds.length,
        ((∑ i ∈ S.1,
            RecordedPotentialStep.servedEstimate q
              (RecordedQueueRun.run q (rounds.take j.val)) (rounds[j.val]'j.isLt) i) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal q p.m rounds j.val i *
              RecordedPotentialStep.servedEstimate q
                (RecordedQueueRun.run q (rounds.take j.val))
                (rounds[j.val]'j.isLt) i)) ≤
        Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * p.T := by
    simpa [RecordedQueueSummation.runMarginal, hlength] using hpotential
  have hsummation := RecordedQueueSummation.run_raw_served_summation_by_parts_all
    q rounds p.two_le_m p.m_lt_K S
  have hcorrection := generatedCorrectionSum_eq_accumulatedCorrection
    p eta heta hcap n hn rewards policy p.T (Nat.le_refl p.T) h
  have hcorrection' :
      (∑ j : Fin rounds.length, ∑ i : Fin p.K,
        (RecordedQueueSummation.runMarginal q p.m rounds (j.val + 1) i -
          RecordedQueueSummation.runMarginal q p.m rounds j.val i) *
          StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.run q (rounds.take (j.val + 1))) i) =
        CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h := by
    rw [hlength]
    simpa [rounds] using hcorrection
  have hterminalBound :
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q (rounds.take p.T)) i) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal q p.m rounds p.T i *
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take p.T)) i ≤
        (p.m : ℝ) / (16 * eta) := by
    have hbacklog (i : Fin p.K) :
        StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.run q (rounds.take p.T)) i ≤
          1 / (16 * eta) := by
      have hb := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
        q rounds hrate p.T i
      have hscale : 2 * (1 / (32 * eta)) = 1 / (16 * eta) := by
        field_simp [ne_of_gt heta]
        ring
      calc
        _ ≤ 2 * (1 / (32 * eta)) := by
          simpa [CanonicalQueueProcess.queueParameters] using hb
        _ = 1 / (16 * eta) := hscale
    have hbacklogNonneg (i : Fin p.K) :
        0 ≤ StoppedQueueBound.normalizedBacklog q
          (RecordedQueueRun.run q (rounds.take p.T)) i := by
      change 0 ≤ ((RecordedQueueRun.run q (rounds.take p.T)).registers i).2 / (n : ℝ)
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hthetaNonneg (i : Fin p.K) :
        0 ≤ RecordedQueueSummation.runMarginal q p.m rounds p.T i :=
      (RecordedQueueSummation.runMarginal_pos q p.m rounds p.T i
        p.two_le_m p.m_lt_K).le
    have hweightedNonneg :
        0 ≤ ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal q p.m rounds p.T i *
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take p.T)) i :=
      Finset.sum_nonneg fun i hi =>
        mul_nonneg (hthetaNonneg i) (hbacklogNonneg i)
    have hcomparator :
        (∑ i ∈ S.1,
          StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.run q (rounds.take p.T)) i) ≤
          (p.m : ℝ) / (16 * eta) := by
      have hcard : S.1.card = p.m :=
        (Finset.mem_powersetCard.mp S.2).2
      calc
        _ ≤ ∑ i ∈ S.1, 1 / (16 * eta) :=
          Finset.sum_le_sum fun i hi => hbacklog i
        _ = (p.m : ℝ) / (16 * eta) := by
          simp [hcard, Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt heta]
    linarith only [hcomparator, hweightedNonneg]
  have hrawIdentity :
      generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h S =
        (∑ j : Fin rounds.length,
          ((∑ i ∈ S.1,
              RecordedPotentialStep.servedEstimate q
                (RecordedQueueRun.run q (rounds.take j.val))
                (rounds[j.val]'j.isLt) i) -
            ∑ i : Fin p.K,
              RecordedQueueSummation.runMarginal q p.m rounds j.val i *
                RecordedPotentialStep.servedEstimate q
                  (RecordedQueueRun.run q (rounds.take j.val))
                  (rounds[j.val]'j.isLt) i)) +
        (∑ i ∈ S.1,
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take p.T)) i) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal q p.m rounds p.T i *
              StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (rounds.take p.T)) i +
        CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h := by
    rw [hcorrection'] at hsummation
    simpa [generatedRawComparatorMinusMarginalSum, rounds, hlength,
      RecordedQueueSummation.runMarginal] using hsummation
  rw [hrawIdentity]
  linarith only [hpotential', hterminalBound]

/-- Finite generated histories make the actual raw-gap observable integrable
under their iterated canonical path law. -/
theorem generatedRawComparatorMinusMarginalSum_integrable
    (t : ℕ) (ht : t ≤ p.T) (S : ProductSet p.K p.m) :
    Integrable
      (fun h : CanonicalQueueProcess.History p.K t =>
        generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
          t ht h S)
      (CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy t ht).toMeasure :=
  CanonicalQueueProcess.integrable_history p eta heta hcap n hn rewards policy t ht _

/-- Expected raw gap on the actual canonical path law. The retained
weighted-backlog expectation remains explicit for the downstream
CanonicalWeightedBacklog producer; this theorem does not assume its
conclusion or transfer the result to real rewards. -/
theorem generatedRawComparatorMinusMarginalSum_expectation_le
    (S : ProductSet p.K p.m) :
    ∫ h, generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T) h S
      ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T)).toMeasure ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * p.T +
        (p.m : ℝ) / (16 * eta) +
        8 * eta *
          (CanonicalQueueCorrection.retainedBacklogExpectationSum p eta heta hcap n hn
            rewards policy p.T (Nat.le_refl p.T) + (p.m : ℝ) * p.T) := by
  let law := CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
    p.T (Nat.le_refl p.T)
  let constant : ℝ :=
    Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda q +
      16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * p.T +
      (p.m : ℝ) / (16 * eta)
  have hrawIntegrable :=
    generatedRawComparatorMinusMarginalSum_integrable p eta heta hcap n hn rewards policy
      p.T (Nat.le_refl p.T) S
  have hcorrectionIntegrable :=
    CanonicalQueueProcess.integrable_history p eta heta hcap n hn rewards policy p.T
      (Nat.le_refl p.T)
      (CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
        p.T (Nat.le_refl p.T))
  have hpoint (h : CanonicalQueueProcess.History p.K p.T) :
      generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h S ≤
        constant +
          CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T) h := by
    simpa [constant] using
      generatedRawComparatorMinusMarginalSum_le p eta heta hcap n hn rewards policy h S
  have hmain :
      ∫ h, generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h S ∂law.toMeasure ≤
        ∫ h, constant +
          CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T) h ∂law.toMeasure :=
    integral_mono hrawIntegrable
      (Integrable.add (integrable_const _) hcorrectionIntegrable) hpoint
  have hintegral :
      ∫ h, constant +
          CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T) h ∂law.toMeasure =
        constant +
          ∫ h, CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T) h ∂law.toMeasure := by
    rw [integral_add (integrable_const _) hcorrectionIntegrable,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hcorrection :=
    CanonicalQueueCorrection.terminal_accumulatedCorrection_expectation_le
      p eta heta hcap n hn rewards policy
  have hmain' :
      ∫ h, generatedRawComparatorMinusMarginalSum p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h S
        ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T)).toMeasure ≤
        constant +
          ∫ h, CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T) h
          ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T)).toMeasure := by
    rw [hintegral] at hmain
    simpa [law] using hmain
  calc
    _ ≤ constant +
        ∫ h, CanonicalQueueCorrection.accumulatedCorrection p eta heta hcap n hn rewards policy
          p.T (Nat.le_refl p.T) h
          ∂(CanonicalQueueProcess.pathLaw p eta heta hcap n hn rewards policy
            p.T (Nat.le_refl p.T)).toMeasure := hmain'
    _ ≤ constant +
        8 * eta *
          (CanonicalQueueCorrection.retainedBacklogExpectationSum p eta heta hcap n hn
            rewards policy p.T (Nat.le_refl p.T) + (p.m : ℝ) * p.T) := by
      exact add_le_add_right hcorrection constant
    _ = _ := by simp [constant]

end Bandits.Support.CanonicalRawPotentialBound

end
