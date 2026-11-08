/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedBootstrapMonitor
public import Bandits.Support.InitializationFailureProvenance
public import Bandits.Support.InitializationRowObservables

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Stopped comparator support and prelaunch reward mass

This module defines the literal stopped support deficit event and proves the
support-side comparison for the strict prelaunch reward sum.  The comparison
includes the actual launch block, clipped final block, and `T + 1` sentinel.
The integrated row-observable API does not expose a general-prefix expansion
of its named comparator charge, so this file does not claim an inclusion from
that charge event. Sources:
`appendix_b_communication.tex:658-682,737-765` and
`07_public_setup.tex:106-140`.

These are deterministic facts over the existing reference input.  They do
not assert that the monitor deficit event is unlikely.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Bandits.Support.GeneratedComparatorChargeObstruction

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceInitializationRun

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- Stopped rounded-reward support through the first `r` actual block
opportunities.  The map from `Fin r` to `Fin n_boot` is the canonical initial
segment inclusion, and a block is retained exactly while its pre-block
reference boundary has not crossed the launch threshold. -/
def stoppedRewardSupportPrefix
    (x : ReferenceInitializationRun.Input p) (r : ℕ) (hr : r ≤ n_boot p)
    (a : Fin p.K) : ℝ :=
  ∑ s : Fin r,
    if (ReferenceInitializationRun.run x (Fin.castLE hr s).val).crossing = none then
      GeneratedBootstrapGainBudget.rewardSupportCountAt x (Fin.castLE hr s) a
    else 0

/-- The literal monitor-deficit obstruction on the existing reference input.
The per-arm counter is read at the same reference prefix as the stopped
rounded-reward support. -/
def comparatorMonitorDeficit (x : ReferenceInitializationRun.Input p) : Prop :=
  ∃ a : Fin p.K, ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
    stoppedRewardSupportPrefix x r hr a >
      128 * ((p.K : ℝ) *
        ((ReferenceInitializationRun.run x r).counters a : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))

private def stoppedBlocks (x : ReferenceInitializationRun.Input p) :
    Finset (Fin (n_boot p)) :=
  Finset.univ.filter fun s => (ReferenceInitializationRun.run x s.val).crossing = none

def stoppedRounds (x : ReferenceInitializationRun.Input p) :
    Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    (ReferenceInitializationRun.run x (roundBlockIndex p t).val).crossing = none

private theorem rewardMass_le_support (x : ReferenceInitializationRun.Input p)
    (t : Fin p.T) (a : Fin p.K) :
    ((x.rewards t a).val : ℝ) / (D p : ℝ) ≤
      BootstrapDownCountMean.rewardSupport p x.rewards t a := by
  unfold BootstrapDownCountMean.rewardSupport
  rw [RealRewardGridCount.realRewardGridValue]
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  by_cases hzero : (x.rewards t a).val = 0
  · simp [hzero]
  · have hpos : 0 < ((x.rewards t a).val : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hzero)
    have hratio : 0 < ((x.rewards t a).val : ℝ) / (D p : ℝ) := div_pos hpos hD
    split_ifs
    have hval : (x.rewards t a).val ≤ D p := by omega
    have hval' : ((x.rewards t a).val : ℝ) ≤ (D p : ℝ) := by exact_mod_cast hval
    exact (div_le_one hD).2 hval'

theorem stopped_support_prefix_eq_round_support
    (x : ReferenceInitializationRun.Input p) (a : Fin p.K) :
    stoppedRewardSupportPrefix x (n_boot p) le_rfl a =
      ∑ t ∈ stoppedRounds x,
        BootstrapDownCountMean.rewardSupport p x.rewards t a := by
  classical
  have hunion : (stoppedBlocks x).biUnion (calendarBlock p) = stoppedRounds x := by
    ext t
    simp only [stoppedRounds, stoppedBlocks, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨s, hs, hst⟩
      have hindex : s = roundBlockIndex p t := by
        apply Fin.ext
        exact (mem_calendarBlock_iff_quotient p s t).1 hst
      simpa [hindex] using hs
    · intro ht
      exact ⟨roundBlockIndex p t, ht, round_mem_quotient_block p t⟩
  have hdisjoint : Set.PairwiseDisjoint (↑(stoppedBlocks x)) (calendarBlock p) := by
    intro s hs r hr hne
    exact calendarBlocks_disjoint p s r hne
  calc
    stoppedRewardSupportPrefix x (n_boot p) le_rfl a =
        ∑ s ∈ stoppedBlocks x,
          GeneratedBootstrapGainBudget.rewardSupportCountAt x s a := by
          unfold stoppedRewardSupportPrefix stoppedBlocks
          simp only [Fin.castLE_rfl, id_eq]
          rw [← Finset.sum_filter]
    _ = ∑ s ∈ stoppedBlocks x, ∑ t ∈ calendarBlock p s,
          BootstrapDownCountMean.rewardSupport p x.rewards t a := by
          rfl
    _ = ∑ t ∈ (stoppedBlocks x).biUnion (calendarBlock p),
          BootstrapDownCountMean.rewardSupport p x.rewards t a := by
          symm
          exact Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ stoppedRounds x,
          BootstrapDownCountMean.rewardSupport p x.rewards t a := by rw [hunion]

private theorem run_crossing_none_of_preceding
    (x : ReferenceInitializationRun.Input p) {s q : ℕ} (hsq : s ≤ q)
    (hq : (ReferenceInitializationRun.run x q).crossing = none) :
    (ReferenceInitializationRun.run x s).crossing = none := by
  by_contra hnot
  have hs : (ReferenceInitializationRun.run x s).crossing.isSome = true := by
    cases he : (ReferenceInitializationRun.run x s).crossing <;> simp_all
  have hstop := ReferenceInitializationRun.run_stops_at_crossing x s (q - s) hs
  rw [Nat.add_sub_of_le hsq] at hstop
  rw [hstop] at hq
  exact hnot hq

private theorem prelaunch_round_in_stoppedRounds
    (x : ReferenceInitializationRun.Input p) (t : Fin p.T)
    (ht : t.val + 1 < InitializationRowObservables.launchRoundAtBoundary p
      (ReferenceInitializationRun.output x)) :
    t ∈ stoppedRounds x := by
  classical
  unfold stoppedRounds
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  let s := roundBlockIndex p t
  have hst : t ∈ calendarBlock p s := round_mem_quotient_block p t
  by_cases hnone : (ReferenceInitializationRun.output x).crossing = none
  · have hendpoint := InitializationFailureProvenance.output_no_crossing_sentinel_and_full_charge
      x x.rewards (∅ : Finset (Fin p.K)) hnone
    have hlaunch := InitializationRowObservables.launchRound_output_boundary p x
    have hboundary : InitializationRowObservables.launchRoundAtBoundary p
        (ReferenceInitializationRun.output x) = p.T + 1 := by
      calc
        _ = ReferenceInitializationRun.launchRound x := hlaunch.symm
        _ = p.T + 1 := hendpoint.1
    have htime : t.val + 1 < p.T + 1 := by rw [← hboundary]; exact ht
    have hsnone : (ReferenceInitializationRun.run x s.val).crossing = none := by
      by_contra hnot
      have hsome : (ReferenceInitializationRun.run x s.val).crossing.isSome = true := by
        cases he : (ReferenceInitializationRun.run x s.val).crossing <;> simp_all
      have hout := ReferenceInitializationRun.output_eq_of_crossing x s.val
        (Nat.le_of_lt s.isLt) hsome
      rw [hout] at hnone
      simp [hnone] at hsome
    exact hsnone
  · have hcross : (ReferenceInitializationRun.output x).crossing.isSome = true := by
      cases he : (ReferenceInitializationRun.output x).crossing <;> simp_all
    by_cases hterminal : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed = p.T
    · have hendpoint :=
        InitializationFailureProvenance.output_terminal_crossing_sentinel_and_full_charge
          x x.rewards (∅ : Finset (Fin p.K)) hcross hterminal
      have hlaunch := InitializationRowObservables.launchRound_output_boundary p x
      have hboundary : InitializationRowObservables.launchRoundAtBoundary p
          (ReferenceInitializationRun.output x) = p.T + 1 := by
        calc
          _ = ReferenceInitializationRun.launchRound x := hlaunch.symm
          _ = p.T + 1 := hendpoint.1
      have htime : t.val + 1 < p.T + 1 := by rw [← hboundary]; exact ht
      obtain ⟨q, hq, hqsucc, hqnone, _, _, _, _, hout⟩ :=
        GeneratedBootstrapMonitor.output_crossing_first_boundary x hcross
      have hqle : q ≤ n_boot p := by omega
      have hqprogress := ReferenceInitializationRun.run_progress x q hqle
      have hqcompleted : (ReferenceInitializationRun.run x q).completed = q :=
        hqprogress.resolve_left (by simp [hqnone])
      have hqcompleted' :
          (ReferenceInitializationRun.run x (q + 1)).completed = q + 1 := by
        have hstep : ReferenceInitializationRun.run x (q + 1) =
            ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hq := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hqnone hq]
        rw [hstep]
        change (ReferenceInitializationRun.run x q).completed + 1 = q + 1
        rw [hqcompleted]
      have houtcompleted :
          (ReferenceInitializationRun.output x).completed = q + 1 := by
        rw [hout, hqcompleted']
      have hqterminal : q + 1 = n_boot p := by
        by_contra hnotq
        have hlt : q + 1 < n_boot p := by omega
        have hnextNat : q + 2 ≤ n_boot p := by omega
        have hnextReal : (q : ℝ) + 2 ≤ (n_boot p : ℝ) := by exact_mod_cast hnextNat
        have hceil := n_boot_real_upper_bound p
        have hdiv : ((q + 1 : ℕ) : ℝ) < (p.T : ℝ) / (B_boot p : ℝ) := by
          exact_mod_cast (show (q : ℝ) + 1 <
            (p.T : ℝ) / (B_boot p : ℝ) by linarith)
        have hprodReal : ((q + 1 : ℕ) : ℝ) * (B_boot p : ℝ) < (p.T : ℝ) := by
          exact (lt_div_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).1 hdiv
        have hprod : (q + 1) * B_boot p < p.T := by exact_mod_cast hprodReal
        have hmin : min p.T ((q + 1) * B_boot p) = (q + 1) * B_boot p :=
          Nat.min_eq_right (Nat.le_of_lt hprod)
        rw [houtcompleted, ReferenceInitializationRun.elapsed, hmin] at hterminal
        omega
      have hsq : s.val ≤ q := by omega
      have hsnone : (ReferenceInitializationRun.run x s.val).crossing = none := by
        apply run_crossing_none_of_preceding x hsq hqnone
      exact hsnone
    · obtain ⟨q, hq, hqsucc, hqnone, _, _, _, hlaunchFirst, _⟩ :=
        GeneratedBootstrapMonitor.output_crossing_first_boundary x hcross
      have hlaunch := InitializationRowObservables.launchRound_output_boundary p x
      have htime : t.val <
          ReferencePrelaunchPhysicalReplay.blockEnd p
            (ReferenceInitializationRun.nextBlock
              (ReferenceInitializationRun.run x q) hq) := by
        rw [← hlaunch, hlaunchFirst] at ht
        omega
      have hqle : q ≤ n_boot p := by omega
      have hqprogress := ReferenceInitializationRun.run_progress x q hqle
      have hqcompleted : (ReferenceInitializationRun.run x q).completed = q :=
        hqprogress.resolve_left (by simp [hqnone])
      have hqblock :
          ReferencePrelaunchPhysicalReplay.blockEnd p
            (ReferenceInitializationRun.nextBlock
              (ReferenceInitializationRun.run x q) hq) =
            min p.T ((q + 1) * B_boot p) := by
        simp [ReferencePrelaunchPhysicalReplay.blockEnd,
          ReferenceInitializationRun.nextBlock, hqcompleted]
      rcases (mem_calendarBlock_iff p s t).1 hst with ⟨hstart, _⟩
      have hsq : s.val ≤ q := by
        by_contra hnot
        have hqs : q + 1 ≤ s.val := by omega
        have hmul : (q + 1) * B_boot p ≤ s.val * B_boot p :=
          Nat.mul_le_mul_right _ hqs
        rw [hqblock] at htime
        have hle : min p.T ((q + 1) * B_boot p) ≤ (q + 1) * B_boot p :=
          Nat.min_le_right _ _
        omega
      exact run_crossing_none_of_preceding x hsq hqnone

/-- The literal per-arm denominator-`D` reward sum through the strict launch
endpoint is bounded by support in the same actual stopped blocks.  This
statement does not identify the hidden body of
`InitializationRowObservables.comparatorChargeAtBoundary`. -/
theorem normalized_prelaunch_reward_mass_le_stopped_support
    (x : ReferenceInitializationRun.Input p) (a : Fin p.K) :
    (∑ t : Fin p.T,
      if t.val + 1 < InitializationRowObservables.launchRoundAtBoundary p
          (ReferenceInitializationRun.output x) then
        ((x.rewards t a).val : ℝ) / (D p : ℝ)
      else 0) ≤ stoppedRewardSupportPrefix x (n_boot p) le_rfl a := by
  classical
  have hsubset :
      (Finset.univ.filter fun t : Fin p.T =>
        t.val + 1 < InitializationRowObservables.launchRoundAtBoundary p
          (ReferenceInitializationRun.output x)) ⊆ stoppedRounds x := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨_, hpre⟩
    exact prelaunch_round_in_stoppedRounds x t hpre
  rw [stopped_support_prefix_eq_round_support x a]
  rw [← Finset.sum_filter]
  calc
    ∑ t ∈ Finset.univ.filter (fun t : Fin p.T =>
        t.val + 1 < InitializationRowObservables.launchRoundAtBoundary p
          (ReferenceInitializationRun.output x)),
        ((x.rewards t a).val : ℝ) / (D p : ℝ) ≤
      ∑ t ∈ stoppedRounds x, BootstrapDownCountMean.rewardSupport p x.rewards t a := by
        calc
          _ ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin p.T =>
              t.val + 1 < InitializationRowObservables.launchRoundAtBoundary p
                (ReferenceInitializationRun.output x)),
              BootstrapDownCountMean.rewardSupport p x.rewards t a :=
            Finset.sum_le_sum fun t ht => rewardMass_le_support x t a
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro t ht hnot
            unfold BootstrapDownCountMean.rewardSupport
            split_ifs <;> norm_num)

end Bandits.Support.GeneratedComparatorChargeObstruction

end
