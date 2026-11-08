/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapLaunchMonitor
public import Bandits.Support.BootstrapStartupCostScale
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedProductiveExitBudget
public import Bandits.Support.GeneratedUninformedSupportObstruction
public import Bandits.Support.InitializationFailureProvenance
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.ReferenceInitializationRun

import Mathlib.Tactic.Linarith

/-!
# Deterministic forced-correction obstruction

On the accepted reference initialization run, a forced correction at the
first strict monitor crossing implies one of the literal importance,
productive-count, latent-activity, or upper-monitor violations. The upper
monitor event uses the stopped support prefix from the same input.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:572-635`,
`appendix_b_communication.tex:637-682`,
`appendix_b_communication.tex:737-765`, and
`sources/zip4/manuscript/07_public_setup.tex:106-140`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.BootstrapStartupCostScale
open Bandits.Support.GeneratedBootstrapGainBudget
open Bandits.Support.GeneratedProductiveExitBudget
open Bandits.Support.GeneratedUninformedSupportObstruction
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.InitializationFailureProvenance
open scoped BigOperators

namespace Bandits.Support.GeneratedForcedCorrectionObstruction

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The upper arm-monitor violation `E_plus` on the accepted input. Its
support term includes a block exactly when the actual run had not crossed at
that block's incoming boundary. -/
def monitorUpperObstruction (x : ReferenceInitializationRun.Input p) : Prop :=
  ∃ a : Fin p.K, ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
    (p.K : ℝ) * ((ReferenceInitializationRun.run x r).counters a : ℝ) >
      2 * (∑ s : Fin r,
        (if (ReferenceInitializationRun.run x s.val).crossing = none then
          (1 : ℝ) else 0) *
          GeneratedBootstrapGainBudget.rewardSupportCountAt x
            ⟨s.val, s.isLt.trans_le hr⟩ a) +
        (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))

/-- A forced correction on the actual reference run is covered by one of the
three accepted support obstructions or the literal upper monitor violation.
The only scalar premise is `C_star ≥ 2^20`; the left side is the actual
`forcedCorrectionAt` witness, not a supplied monitor or support estimate. -/
theorem forcedCorrection_obstruction_subset
    (x : ReferenceInitializationRun.Input p)
    (hCstar : (2 : ℝ) ^ 20 ≤ x.C_star)
    (htarget : ∃ s : Fin (n_boot p), ∃ i : Follower p.m,
      InitializationFailureProvenance.forcedCorrectionAt x s i) :
    importanceObstruction x ∨ productiveObstruction x ∨
      latentActivityObstruction x ∨ monitorUpperObstruction x := by
  classical
  rcases htarget with ⟨s, i, hforce⟩
  rcases hforce with ⟨hblock, hcross, hcompleted, _, hmonitor, hdeclared, _, _⟩
  by_cases hI : importanceObstruction x
  · exact Or.inl hI
  by_cases hP : productiveObstruction x
  · exact Or.inr (Or.inl hP)
  by_cases hA : latentActivityObstruction x
  · exact Or.inr (Or.inr (Or.inl hA))
  by_cases hPlus : monitorUpperObstruction x
  · exact Or.inr (Or.inr (Or.inr hPlus))

  let r := s.val + 1
  have hcompleted_lt : s.val < n_boot p := by
    rw [← hcompleted]
    exact hblock
  have hr : r ≤ n_boot p := by
    dsimp [r]
    exact Nat.succ_le_of_lt hcompleted_lt
  have hactivation : (ReferenceInitializationRun.run x s.val).activation i = none := by
    by_contra hne
    cases ha : (ReferenceInitializationRun.run x s.val).activation i with
    | none => exact hne ha
    | some a =>
        have hsaved := ReferenceInitializationRun.declaredActivation_of_activated
          x (ReferenceInitializationRun.run x s.val) hblock i a ha
        rw [hdeclared] at hsaved
        cases hsaved
  have hVs : prelaunchUninformedIndicator x i s.val = 1 := by
    simp [prelaunchUninformedIndicator, hcross, hactivation]
  have hV : ∀ q : ℕ, q < r →
      prelaunchUninformedIndicator x i q = 1 := by
    intro q hqr
    have hqs : q ≤ s.val := by dsimp [r] at hqr; omega
    have hanti := prelaunchUninformedIndicator_antitone x i hqs s.isLt.le
    have hle := prelaunchUninformedIndicator_le_one x i q
    rw [hVs] at hanti
    linarith
  have hnoCross : ∀ q : ℕ, q < r →
      (ReferenceInitializationRun.run x q).crossing = none := by
    intro q hqr
    have hqs : q ≤ s.val := by dsimp [r] at hqr; omega
    exact InitializationFailureProvenance.run_prefix_no_crossing_of_no_crossing
      x hqs hcross

  let ell : ℝ := 4 * (b_N p : ℝ)
  have hCstar2 : (2 : ℝ) ≤ x.C_star := by
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
    exact hpow.trans hCstar
  have hbudgetNat : p.m * p.K * B_boot p * (4 * b_N p) ≤
      Q x.C_star x.C_h p :=
    BootstrapStartupCostScale.bootstrap_arm_budget_le_Q
      x.C_h x.C_star p hCstar2
  have hbudget : (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell ≤
      (Q x.C_star x.C_h p : ℝ) := by
    dsimp [ell]
    exact_mod_cast hbudgetNat

  have hsupport (S : Finset (Fin p.K))
      (hS : S ∈ ProductSetLaw.support p.K p.m) :
      (∑ a ∈ S, supportCountPrefix x r hr a) ≤
        (Q x.C_star x.C_h p : ℝ) := by
    by_contra hlargeNot
    have hlarge : (Q x.C_star x.C_h p : ℝ) <
        ∑ a ∈ S, supportCountPrefix x r hr a := lt_of_not_ge hlargeNot
    have hbad := unfinishedSupport_obstruction_subset x hCstar
      ⟨i, r, hr, S, hS, hV, hlarge⟩
    rcases hbad with h | h | h
    · exact hI h
    · exact hP h
    · exact hA h

  have hstoppedEq (a : Fin p.K) :
      (∑ s' : Fin r,
        (if (ReferenceInitializationRun.run x s'.val).crossing = none then
          (1 : ℝ) else 0) *
          GeneratedBootstrapGainBudget.rewardSupportCountAt x
            ⟨s'.val, s'.isLt.trans_le hr⟩ a) =
        supportCountPrefix x r hr a := by
    unfold supportCountPrefix
    apply Finset.sum_congr rfl
    intro s' hs'
    have hnone := hnoCross s'.val s'.isLt
    simp [hnone]

  have harmBound (a : Fin p.K) :
      (p.K : ℝ) *
          ((ReferenceInitializationRun.run x r).counters a : ℝ) ≤
        2 * supportCountPrefix x r hr a +
          (p.K : ℝ) * (B_boot p : ℝ) * ell := by
    by_contra hnot
    have hstrict : (p.K : ℝ) *
        ((ReferenceInitializationRun.run x r).counters a : ℝ) >
          2 * supportCountPrefix x r hr a +
            (p.K : ℝ) * (B_boot p : ℝ) * ell := lt_of_not_ge hnot
    apply hPlus
    refine ⟨a, r, hr, ?_⟩
    rw [hstoppedEq a]
    simpa [ell] using hstrict

  have hsetBound (S : Finset (Fin p.K))
      (hS : S ∈ ProductSetLaw.support p.K p.m) :
      p.K * (∑ a ∈ S, (ReferenceInitializationRun.run x r).counters a) ≤
        3 * Q x.C_star x.C_h p := by
    have hreal : (p.K : ℝ) *
          (∑ a ∈ S, (ReferenceInitializationRun.run x r).counters a : ℝ) ≤
        3 * (Q x.C_star x.C_h p : ℝ) := by
      calc
        (p.K : ℝ) *
            (∑ a ∈ S, (ReferenceInitializationRun.run x r).counters a : ℝ) =
            ∑ a ∈ S, (p.K : ℝ) *
              (ReferenceInitializationRun.run x r).counters a := by
                rw [Finset.mul_sum]
        _ ≤ ∑ a ∈ S,
              (2 * supportCountPrefix x r hr a +
                (p.K : ℝ) * (B_boot p : ℝ) * ell) := by
              apply Finset.sum_le_sum
              intro a ha
              exact harmBound a
        _ = 2 * (∑ a ∈ S, supportCountPrefix x r hr a) +
              (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell := by
              simp [Finset.sum_add_distrib, Finset.mul_sum,
                BootstrapLaunchMonitor.supportedSet_card p hS]
              ring
        _ ≤ 3 * (Q x.C_star x.C_h p : ℝ) := by
              have hs := hsupport S hS
              nlinarith [hs, hbudget]
    exact_mod_cast hreal

  have hmonitorBound : BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.run x r).counters ≤
      3 * Q x.C_star x.C_h p := by
    change p.K * BootstrapLaunchMonitor.maximumSupportedCounterSum p
        (ReferenceInitializationRun.run x r).counters ≤
      3 * Q x.C_star x.C_h p
    have hmax := Finset.max'_mem
      (BootstrapLaunchMonitor.supportedSetSums p
        (ReferenceInitializationRun.run x r).counters)
      (BootstrapLaunchMonitor.supportedSetSums_nonempty p
        (ReferenceInitializationRun.run x r).counters)
    rcases Finset.mem_image.mp hmax with ⟨S, hS, hEq⟩
    unfold BootstrapLaunchMonitor.maximumSupportedCounterSum
    rw [← hEq]
    exact hsetBound S hS

  have hsucc : ReferenceInitializationRun.run x r =
      ReferenceInitializationRun.finishBlock x
        (ReferenceInitializationRun.run x s.val) hblock := by
    dsimp [r]
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x _ hcross hblock]
  have hcounter : (ReferenceInitializationRun.run x r).counters =
      ReferenceInitializationRun.updatedCounters x
        (ReferenceInitializationRun.run x s.val) hblock := by
    rw [hsucc]
    rfl
  have hmonitorActual : BootstrapLaunchMonitor.monitorValue p
      (ReferenceInitializationRun.run x r).counters >
        4 * Q x.C_star x.C_h p := by
    rw [hcounter]
    exact hmonitor
  omega

end Bandits.Support.GeneratedForcedCorrectionObstruction
