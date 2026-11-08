/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun

import Mathlib.Algebra.BigOperators.Fin

/-!
# Generated-history counters and the actual bootstrap launch monitor

This module connects the accepted, stopped `ReferenceInitializationRun` to
the coordinator's DOWN-positive counters on exactly its generated physical
prefix.  It proves the deterministic first-crossing overshoot, including the
shortened final calendar block.  Sources:
`07_public_setup.tex:40-55,98-144` and
`appendix_b_communication.tex:640-682,749-765`.

The results are deterministic internal facts.  They do not establish a
conditional mean, comparator support, a causal private-history law, expected
regret, or manuscript-level monitor closure.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Bandits.Support.GeneratedBootstrapMonitor

open Bandits.Support.BootstrapDimensions
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

variable {p : ConstructorDimensions.Parameters}

/-- One actual coordinator credit, applied by the accepted monitor replay
operation. -/
def creditReplay (c : Fin p.K → ℕ)
    (credits : List (Option (Fin p.K))) : Fin p.K → ℕ :=
  credits.foldl BootstrapLaunchMonitor.creditCounter c

/-- Counter sum on a finite generated coordinator history.  The index is the
history's own finite physical prefix; no postlaunch tail is supplied. -/
def generatedHistoryCount (x : ReferenceInitializationRun.Input p) (n : ℕ)
    (hist : ReferencePrelaunchFollower.LocalHistory p n) (hn : n ≤ p.T)
    (a : Fin p.K) : ℕ :=
  ∑ u : Fin n,
    if generatedDownArm x n hn hist u = some a then 1 else 0

/-- The actual per-arm count in one completed block of a stopped run, read
from that run's generated coordinator history. -/
def historyBlockCount (x : ReferenceInitializationRun.Input p) (n : ℕ)
    (hn : n ≤ p.T) (hist : ReferencePrelaunchFollower.LocalHistory p n)
    (s : Fin (n_boot p)) (hs : blockEnd p s ≤ n) (a : Fin p.K) : ℕ :=
  ∑ u : Fin (blockLength p s),
    if generatedDownArm x n hn hist
        ⟨(blockEmbed u).val,
          Nat.lt_of_lt_of_le (blockEmbed u).isLt hs⟩ = some a then 1 else 0

/-- The per-arm count in one completed block of an actual boundary, read only
from its generated coordinator history. -/
def runBlockCount (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (s : Fin b.completed) (a : Fin p.K) : ℕ :=
  let sb : Fin (n_boot p) := ⟨s.val, Nat.lt_of_lt_of_le s.isLt b.completed_le⟩
  historyBlockCount x (elapsed p b.completed) (elapsed_le_T p b.completed)
    (b.history (coordinator p.two_le_m)) sb (by
      unfold blockEnd elapsed
      exact min_le_min_left _
        (Nat.mul_le_mul_right (B_boot p) (Nat.succ_le_of_lt s.isLt))) a

private theorem sum_calendarBlock_eq_sum_blockRound
    (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) (f : Fin p.T → ℕ) :
    (∑ t ∈ calendarBlock p s, f t) =
      ∑ u : Fin (blockLength p s), f (blockRound p s u) := by
  classical
  symm
  apply Finset.sum_bij (fun u _ => blockRound p s u)
  · intro u hu
    exact blockRound_mem p s u
  · intro u hu v hv huv
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val huv)
  · intro t ht
    obtain ⟨u, hu⟩ := exists_blockRound p s t ht
    exact ⟨u, Finset.mem_univ _, hu⟩
  · intro u hu
    rfl

private theorem creditReplay_ofFn_apply {K n : ℕ}
    (c : Fin K → ℕ) (credits : Fin n → Option (Fin K)) (a : Fin K) :
    (List.ofFn credits).foldl BootstrapLaunchMonitor.creditCounter c a =
      c a + ∑ u : Fin n, if credits u = some a then 1 else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.foldl_cons, Fin.sum_univ_succ]
      rw [ih (BootstrapLaunchMonitor.creditCounter c (credits 0))
        (fun u => credits u.succ)]
      simp only [BootstrapLaunchMonitor.creditCounter]
      omega

private theorem creditReplay_mono (c : Fin p.K → ℕ)
    (credits : List (Option (Fin p.K))) (a : Fin p.K) :
    c a ≤ creditReplay c credits a := by
  induction credits generalizing c with
  | nil => simp [creditReplay]
  | cons head tail ih =>
      simp only [creditReplay, List.foldl_cons]
      exact (BootstrapLaunchMonitor.creditCounter_mono c head a).trans
        (ih (BootstrapLaunchMonitor.creditCounter c head))

private theorem creditReplay_monitor_le
    (p : ConstructorDimensions.Parameters)
    (c : Fin p.K → ℕ) (credits : List (Option (Fin p.K))) :
    BootstrapLaunchMonitor.monitorValue p
        (credits.foldl BootstrapLaunchMonitor.creditCounter c) ≤
      BootstrapLaunchMonitor.monitorValue p c + p.K * credits.length := by
  induction credits using List.reverseRecOn generalizing c with
  | nil => simp
  | append_singleton cs last ih =>
      simp only [List.length_append, List.length_singleton]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      calc
        BootstrapLaunchMonitor.monitorValue p
            (BootstrapLaunchMonitor.creditCounter (cs.foldl
              BootstrapLaunchMonitor.creditCounter c) last) ≤
            BootstrapLaunchMonitor.monitorValue p
              (cs.foldl BootstrapLaunchMonitor.creditCounter c) + p.K :=
          BootstrapLaunchMonitor.monitorValue_credit_le p _ _
        _ ≤ (BootstrapLaunchMonitor.monitorValue p c + p.K * cs.length) + p.K :=
          Nat.add_le_add_right (ih c) _
        _ = BootstrapLaunchMonitor.monitorValue p c + p.K * (cs.length + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega

private theorem updatedCounters_eq_creditReplay (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) :
    ∀ a : Fin p.K,
      updatedCounters x b h a =
        creditReplay b.counters
          (List.ofFn fun u : Fin (blockLength p (nextBlock b h)) =>
            downArm x b h (blockRound p (nextBlock b h) u)) a := by
  intro a
  unfold creditReplay
  rw [updatedCounters_eq_credit_fold x b h a]
  rw [sum_calendarBlock_eq_sum_blockRound p (nextBlock b h)]
  simp only [BootstrapLaunchMonitor.creditCounter, zero_add]
  exact (creditReplay_ofFn_apply b.counters
    (fun u : Fin (blockLength p (nextBlock b h)) =>
      downArm x b h (blockRound p (nextBlock b h) u)) a).symm

private theorem generatedHistoryCount_extend (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (a : Fin p.K) :
    generatedHistoryCount x (elapsed p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m))
        (elapsed_le_T p (b.completed + 1)) a =
      generatedHistoryCount x (elapsed p b.completed)
        (b.history (coordinator p.two_le_m)) (elapsed_le_T p b.completed) a +
      historyBlockCount x (elapsed p (b.completed + 1))
        (elapsed_le_T p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m)) (nextBlock b h)
        (by rw [← elapsed_succ_eq_blockEnd]) a := by
  have hlen : elapsed p (b.completed + 1) =
      elapsed p b.completed + blockLength p (nextBlock b h) := by
    rw [elapsed_succ_eq_blockEnd, blockEnd_eq_start_add_length, elapsed_eq_blockStart]
  let f : Fin (elapsed p (b.completed + 1)) → ℕ := fun u =>
    if generatedDownArm x (elapsed p (b.completed + 1))
        (elapsed_le_T p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m)) u = some a then 1 else 0
  let g : Fin (elapsed p b.completed + blockLength p (nextBlock b h)) → ℕ :=
    fun u => f (Fin.cast hlen.symm u)
  have hreindex : (∑ u : Fin (elapsed p (b.completed + 1)), f u) =
      ∑ u : Fin (elapsed p b.completed + blockLength p (nextBlock b h)), g u := by
    exact Fintype.sum_equiv (finCongr hlen) f g (by intro u; rfl)
  unfold generatedHistoryCount historyBlockCount
  change (∑ u : Fin (elapsed p (b.completed + 1)), f u) = _
  rw [hreindex, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro u hu
    have hidx : Fin.cast hlen.symm (Fin.castAdd
        (blockLength p (nextBlock b h)) u) =
          ⟨u.val, Nat.lt_of_lt_of_le u.isLt (elapsed_mono p (Nat.le_succ _))⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd]
    change f (Fin.cast hlen.symm (Fin.castAdd
      (blockLength p (nextBlock b h)) u)) = _
    dsimp [f]
    unfold generatedDownArm
    rw [hidx, extendedHistory_prefix]
    have hcal :
        ReferencePrelaunchFollower.calendar
            (elapsed_le_T p (b.completed + 1))
            (⟨u.val, Nat.lt_of_lt_of_le u.isLt
              (elapsed_mono p (Nat.le_succ _))⟩ :
              Fin (elapsed p (b.completed + 1))) =
          ReferencePrelaunchFollower.calendar
            (elapsed_le_T p b.completed) u := by
      apply Fin.ext
      rfl
    rw [hcal]
  · apply Finset.sum_congr rfl
    intro u hu
    have hidx : Fin.cast hlen.symm (Fin.natAdd (elapsed p b.completed) u) =
        ⟨(blockEmbed u).val,
          Nat.lt_of_lt_of_le (blockEmbed u).isLt
            (by rw [← elapsed_succ_eq_blockEnd])⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, blockEmbed]
      rw [elapsed_eq_blockStart]
    change f (Fin.cast hlen.symm (Fin.natAdd (elapsed p b.completed) u)) = _
    dsimp [f]
    unfold generatedDownArm
    rw [hidx]

private theorem historyBlockCount_extend_prefix
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (s : Fin b.completed)
    (hs : blockEnd p ⟨s.val, Nat.lt_trans s.isLt h⟩ ≤ elapsed p b.completed)
    (a : Fin p.K) :
    historyBlockCount x (elapsed p (b.completed + 1))
        (elapsed_le_T p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m))
        ⟨s.val, Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt s.isLt)
          (Nat.succ_le_of_lt h)⟩
        (hs.trans (elapsed_mono p (by omega))) a =
      historyBlockCount x (elapsed p b.completed)
        (elapsed_le_T p b.completed) (b.history (coordinator p.two_le_m))
        ⟨s.val, Nat.lt_trans s.isLt h⟩ hs a := by
  unfold historyBlockCount
  apply Finset.sum_congr rfl
  intro u hu
  let oldIndex : Fin (elapsed p b.completed) :=
    ⟨(blockEmbed u).val,
      Nat.lt_of_lt_of_le (blockEmbed u).isLt hs⟩
  let newIndex : Fin (elapsed p (b.completed + 1)) :=
    ⟨(blockEmbed u).val,
      Nat.lt_of_lt_of_le (blockEmbed u).isLt
        (hs.trans (elapsed_mono p (by omega)))⟩
  have hidx : newIndex =
      ⟨oldIndex.val,
        Nat.lt_of_lt_of_le oldIndex.isLt
          (elapsed_mono p (Nat.le_succ _))⟩ := by
    apply Fin.ext
    rfl
  change (if generatedDownArm x _ _ _ newIndex = some a then 1 else 0) = _
  rw [hidx]
  unfold generatedDownArm
  rw [extendedHistory_prefix]
  have hcal :
      ReferencePrelaunchFollower.calendar
          (elapsed_le_T p (b.completed + 1))
          ⟨oldIndex.val,
            Nat.lt_of_lt_of_le oldIndex.isLt
              (elapsed_mono p (Nat.le_succ _))⟩ =
        ReferencePrelaunchFollower.calendar
          (elapsed_le_T p b.completed) oldIndex := by
    apply Fin.ext
    rfl
  rw [hcal]

private theorem finishBlock_counters_eq_generatedHistoryCount
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (hpref : ∀ a : Fin p.K,
      b.counters a = generatedHistoryCount x (elapsed p b.completed)
        (b.history (coordinator p.two_le_m)) (elapsed_le_T p b.completed) a) :
    ∀ a : Fin p.K,
      (finishBlock x b h).counters a =
        generatedHistoryCount x (elapsed p (b.completed + 1))
          (extendedHistory x b h (coordinator p.two_le_m))
          (elapsed_le_T p (b.completed + 1)) a := by
  intro a
  change updatedCounters x b h a =
    generatedHistoryCount x (elapsed p (b.completed + 1))
      (extendedHistory x b h (coordinator p.two_le_m))
      (elapsed_le_T p (b.completed + 1)) a
  rw [updatedCounters_eq_creditReplay x b h a]
  unfold creditReplay
  rw [creditReplay_ofFn_apply]
  calc
    (b.counters a +
        (∑ u : Fin (blockLength p (nextBlock b h)),
          if downArm x b h (blockRound p (nextBlock b h) u) = some a then 1 else 0)) =
      generatedHistoryCount x (elapsed p b.completed)
        (b.history (coordinator p.two_le_m)) (elapsed_le_T p b.completed) a +
      historyBlockCount x (elapsed p (b.completed + 1))
        (elapsed_le_T p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m)) (nextBlock b h)
        (by rw [← elapsed_succ_eq_blockEnd]) a := by
      rw [hpref a]
      congr 1
      unfold historyBlockCount
      apply Finset.sum_congr rfl
      intro u hu
      have hidx : (⟨(blockEmbed u).val,
          (blockEmbed u).isLt⟩ :
          Fin (elapsed p (b.completed + 1))) = blockEmbed u := by
        apply Fin.ext
        rfl
      rw [hidx]
      rw [← downArm_eq_generatedDownArm x b h u]
    _ = generatedHistoryCount x (elapsed p (b.completed + 1))
        (extendedHistory x b h (coordinator p.two_le_m))
        (elapsed_le_T p (b.completed + 1)) a :=
      (generatedHistoryCount_extend x b h a).symm

/-- Every arm's generated-history count in a calendar block lies between zero
and the clipped block length. -/
theorem historyBlockCount_bounds (x : ReferenceInitializationRun.Input p) (n : ℕ)
    (hn : n ≤ p.T) (hist : ReferencePrelaunchFollower.LocalHistory p n)
    (s : Fin (n_boot p)) (hs : blockEnd p s ≤ n) (a : Fin p.K) :
    0 ≤ historyBlockCount x n hn hist s hs a ∧
      historyBlockCount x n hn hist s hs a ≤ blockLength p s := by
  constructor
  · exact Nat.zero_le _
  · unfold historyBlockCount
    calc
      ((∑ u : Fin (blockLength p s),
          if generatedDownArm x n hn hist
              ⟨(blockEmbed u).val, Nat.lt_of_lt_of_le (blockEmbed u).isLt hs⟩ = some a
          then 1 else 0)) ≤ (∑ _u : Fin (blockLength p s), 1) := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases hc : generatedDownArm x n hn hist
            ⟨(blockEmbed u).val, Nat.lt_of_lt_of_le (blockEmbed u).isLt hs⟩ = some a
        · simp [hc]
        · simp [hc]
      _ = blockLength p s := by simp

/-- Every arm's actual count in a completed run block lies between zero and
the clipped block length. -/
theorem runBlockCount_bounds (x : ReferenceInitializationRun.Input p) (r : ℕ)
    (s : Fin (run x r).completed) (a : Fin p.K) :
    0 ≤ runBlockCount x (run x r) s a ∧
      runBlockCount x (run x r) s a ≤ blockLength p
        ⟨s.val, Nat.lt_of_lt_of_le s.isLt (run x r).completed_le⟩ := by
  unfold runBlockCount
  exact historyBlockCount_bounds x _ _ _ _ _ _

/-- Actual cumulative counters equal the finite sum of generated DOWN-positive
arms on the run's own stopped coordinator history. -/
theorem run_counters_eq_generatedHistoryCount
    (x : ReferenceInitializationRun.Input p) (r : ℕ) (a : Fin p.K) :
    (run x r).counters a =
      generatedHistoryCount x (elapsed p (run x r).completed)
        ((run x r).history (coordinator p.two_le_m))
        (elapsed_le_T p (run x r).completed) a := by
  induction r generalizing a with
  | zero =>
      change 0 = generatedHistoryCount x (elapsed p 0)
        ((initial p).history (coordinator p.two_le_m)) (elapsed_le_T p 0) a
      unfold generatedHistoryCount
      have hz : elapsed p 0 = 0 := by simp [elapsed]
      symm
      apply Finset.sum_eq_zero
      intro u hu
      have hlt := u.isLt
      have hlt0 : u.val < 0 := by simpa only [hz] using hlt
      omega
  | succ r ih =>
      by_cases hp : (run x r).crossing.isSome = true
      · rw [run_succ, advance_of_crossing x _ hp]
        exact ih a
      · have hnone : (run x r).crossing = none := by
          cases he : (run x r).crossing <;> simp_all only [Option.isSome_some,
            Option.isSome_none, not_true_eq_false]
        by_cases h : (run x r).completed < n_boot p
        · have hnext := finishBlock_counters_eq_generatedHistoryCount x
            (run x r) h (fun arm => ih arm)
          rw [run_succ, advance_of_no_crossing x _ hnone h]
          change updatedCounters x (run x r) h a = _
          exact hnext a
        · rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          exact ih a

/-- A state equality transports the finite sum of its completed block counts. -/
private theorem runBlockCount_sum_congr (x : ReferenceInitializationRun.Input p)
    (b c : ReferenceInitializationRun.Boundary p) (h : b = c) (a : Fin p.K) :
    (∑ s : Fin b.completed, runBlockCount x b s a) =
      ∑ s : Fin c.completed, runBlockCount x c s a := by
  cases h
  rfl

/-- The same actual counters are the sum of the per-arm generated counts in
each completed physical block of the stopped run. -/
theorem run_counters_eq_stoppedBlockSum
    (x : ReferenceInitializationRun.Input p) (r : ℕ) (a : Fin p.K) :
    (run x r).counters a =
      ∑ s : Fin (run x r).completed, runBlockCount x (run x r) s a := by
  induction r generalizing a with
  | zero =>
      change 0 = ∑ s : Fin 0, runBlockCount x (initial p) s a
      simp
  | succ r ih =>
      by_cases hp : (run x r).crossing.isSome = true
      · have hstate : run x (r + 1) = run x r := by
          rw [run_succ, advance_of_crossing x _ hp]
        calc
          (run x (r + 1)).counters a = (run x r).counters a := by rw [hstate]
          _ = ∑ s : Fin (run x r).completed, runBlockCount x (run x r) s a := ih a
          _ = ∑ s : Fin (run x (r + 1)).completed,
                runBlockCount x (run x (r + 1)) s a :=
            (runBlockCount_sum_congr x _ _ hstate a).symm
      · have hnone : (run x r).crossing = none := by
          cases he : (run x r).crossing <;> simp_all only [Option.isSome_some,
            Option.isSome_none, not_true_eq_false]
        by_cases h : (run x r).completed < n_boot p
        · let b := run x r
          have hrun : run x (r + 1) = finishBlock x b h := by
            dsimp [b]
            rw [run_succ, advance_of_no_crossing x _ hnone h]
          have hcounter :
              (finishBlock x b h).counters a =
                b.counters a +
                  historyBlockCount x (elapsed p (b.completed + 1))
                    (elapsed_le_T p (b.completed + 1))
                    (extendedHistory x b h (coordinator p.two_le_m))
                    (nextBlock b h) (by rw [← elapsed_succ_eq_blockEnd]) a := by
            have h := finishBlock_counters_eq_generatedHistoryCount x b h
              (fun arm => by
                simpa only [b] using run_counters_eq_generatedHistoryCount x r arm) a
            rw [generatedHistoryCount_extend] at h
            rw [← run_counters_eq_generatedHistoryCount x r a] at h
            simpa only [b] using h
          have hprev : ∀ s : Fin b.completed,
              runBlockCount x (finishBlock x b h) (Fin.castSucc s) a =
                runBlockCount x b s a := by
            intro s
            unfold runBlockCount
            have hs : blockEnd p ⟨s.val, Nat.lt_trans s.isLt h⟩ ≤
                elapsed p b.completed := by
              unfold blockEnd elapsed
              exact min_le_min_left _
                (Nat.mul_le_mul_right (B_boot p) (Nat.succ_le_of_lt s.isLt))
            exact historyBlockCount_extend_prefix x b h s hs a
          have hlast :
              runBlockCount x (finishBlock x b h) (Fin.last b.completed) a =
                historyBlockCount x (elapsed p (b.completed + 1))
                  (elapsed_le_T p (b.completed + 1))
                  (extendedHistory x b h (coordinator p.two_le_m))
                  (nextBlock b h) (by rw [← elapsed_succ_eq_blockEnd]) a := by
            simp [runBlockCount, finishBlock, nextBlock]
          have hsumFinish :
              (∑ s : Fin (finishBlock x b h).completed,
                  runBlockCount x (finishBlock x b h) s a) =
                (∑ s : Fin b.completed, runBlockCount x b s a) +
                  historyBlockCount x (elapsed p (b.completed + 1))
                    (elapsed_le_T p (b.completed + 1))
                    (extendedHistory x b h (coordinator p.two_le_m))
                    (nextBlock b h) (by rw [← elapsed_succ_eq_blockEnd]) a := by
            change (∑ s : Fin (b.completed + 1),
                runBlockCount x (finishBlock x b h) s a) = _
            rw [Fin.sum_univ_castSucc]
            congr 1
            · apply Finset.sum_congr rfl
              intro s hs
              exact hprev s
          calc
            (run x (r + 1)).counters a = (finishBlock x b h).counters a := by
              rw [hrun]
            _ = b.counters a +
                  historyBlockCount x (elapsed p (b.completed + 1))
                    (elapsed_le_T p (b.completed + 1))
                    (extendedHistory x b h (coordinator p.two_le_m))
                    (nextBlock b h) (by rw [← elapsed_succ_eq_blockEnd]) a := hcounter
            _ = (∑ s : Fin b.completed, runBlockCount x b s a) +
                  historyBlockCount x (elapsed p (b.completed + 1))
                    (elapsed_le_T p (b.completed + 1))
                    (extendedHistory x b h (coordinator p.two_le_m))
                    (nextBlock b h) (by rw [← elapsed_succ_eq_blockEnd]) a := by
              rw [ih a]
            _ = ∑ s : Fin (finishBlock x b h).completed,
                  runBlockCount x (finishBlock x b h) s a := hsumFinish.symm
            _ = ∑ s : Fin (run x (r + 1)).completed,
                  runBlockCount x (run x (r + 1)) s a :=
              runBlockCount_sum_congr x _ _ hrun.symm a
        · have hstate : run x (r + 1) = run x r := by
            rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          calc
            (run x (r + 1)).counters a = (run x r).counters a := by rw [hstate]
            _ = ∑ s : Fin (run x r).completed, runBlockCount x (run x r) s a := ih a
            _ = ∑ s : Fin (run x (r + 1)).completed,
                  runBlockCount x (run x (r + 1)) s a :=
              (runBlockCount_sum_congr x _ _ hstate a).symm

/-- The actual update of one physical block increases the monitor by at most
`K` times that block's calendar length. -/
theorem finishBlock_monitor_le (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) :
    BootstrapLaunchMonitor.monitorValue p (finishBlock x b h).counters ≤
      BootstrapLaunchMonitor.monitorValue p b.counters +
        p.K * blockLength p (nextBlock b h) := by
  have hcounter : (finishBlock x b h).counters =
      creditReplay b.counters
        (List.ofFn fun u : Fin (blockLength p (nextBlock b h)) =>
          downArm x b h (blockRound p (nextBlock b h) u)) := by
    funext a
    change updatedCounters x b h a = _
    exact updatedCounters_eq_creditReplay x b h a
  have hfold := creditReplay_monitor_le p b.counters
    (List.ofFn fun u : Fin (blockLength p (nextBlock b h)) =>
      downArm x b h (blockRound p (nextBlock b h) u))
  rw [hcounter]
  simpa only [creditReplay, List.length_ofFn] using hfold

/-- The actual one-block monitor increment is nonnegative and bounded by `K`
times the exact clipped calendar-block cardinality. -/
theorem finishBlock_monitor_increment (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) :
    0 ≤ BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) -
        BootstrapLaunchMonitor.monitorValue p b.counters ∧
      BootstrapLaunchMonitor.monitorValue p b.counters ≤
        BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) ∧
      BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) -
          BootstrapLaunchMonitor.monitorValue p b.counters ≤
        p.K * (calendarBlock p (nextBlock b h)).card := by
  have hmono : ∀ a : Fin p.K, b.counters a ≤ updatedCounters x b h a := by
    intro a
    rw [updatedCounters_eq_creditReplay x b h a]
    exact creditReplay_mono b.counters
      (List.ofFn fun u : Fin (blockLength p (nextBlock b h)) =>
        downArm x b h (blockRound p (nextBlock b h) u)) a
  have hlow := BootstrapLaunchMonitor.monitorValue_mono p hmono
  have hhigh := finishBlock_monitor_le x b h
  change BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) ≤
      BootstrapLaunchMonitor.monitorValue p b.counters +
        p.K * blockLength p (nextBlock b h) at hhigh
  rw [blockLength_eq_calendarBlock_card] at hhigh
  constructor
  · exact Nat.zero_le _
  · constructor
    · exact hlow
    · omega

/-- The source monitor's strict first-crossing convention is preserved by the
actual run: the first crossing block is fully executed and launch is on its
next round. -/
private theorem run_crossing_has_first_boundary
    (x : ReferenceInitializationRun.Input p) (n : ℕ)
    (hc : (run x n).crossing.isSome = true) :
    ∃ r, ∃ h : (run x r).completed < n_boot p,
      r + 1 ≤ n ∧
      (run x r).crossing = none ∧
      crosses x (run x r) h = true ∧
      run x n = run x (r + 1) := by
  induction n with
  | zero =>
      simp [run, initial] at hc
  | succ n ih =>
      by_cases hp : (run x n).crossing.isSome = true
      · obtain ⟨r, h, hr, hnone, hcross, hfreeze⟩ := ih hp
        refine ⟨r, h, by omega, hnone, hcross, ?_⟩
        rw [run_succ, advance_of_crossing x _ hp]
        exact hfreeze
      · have hnone : (run x n).crossing = none := by
          cases he : (run x n).crossing <;> simp_all only [Option.isSome_some,
            Option.isSome_none, not_true_eq_false]
        by_cases h : (run x n).completed < n_boot p
        · have hs : run x (n + 1) = finishBlock x (run x n) h := by
            rw [run_succ, advance_of_no_crossing x _ hnone h]
          have hcross : crosses x (run x n) h = true := by
            rw [hs] at hc
            change (if crosses x (run x n) h then some _ else none).isSome = true at hc
            cases he : crosses x (run x n) h <;> simp_all only [↓reduceIte,
              Option.isSome_none, Option.isSome_some, Bool.false_eq_true]
          exact ⟨n, h, by omega, hnone, hcross, rfl⟩
        · rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)] at hc
          simp [hnone] at hc

/-- At an actual crossing output, the accepted run's own first boundary is
strictly above threshold, every earlier boundary is at most threshold, and
the actual source launch round is one after the clipped end of that block. -/
theorem output_crossing_first_boundary (x : ReferenceInitializationRun.Input p)
    (hc : (output x).crossing.isSome = true) :
    ∃ r, ∃ h : (run x r).completed < n_boot p,
      r + 1 ≤ n_boot p ∧
      (run x r).crossing = none ∧
      (run x (r + 1)).crossing = some (nextBlock (run x r) h) ∧
      BootstrapLaunchMonitor.monitorValue p (run x (r + 1)).counters >
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p ∧
      (∀ q ≤ r, BootstrapLaunchMonitor.monitorValue p (run x q).counters ≤
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p) ∧
      launchRound x = blockEnd p (nextBlock (run x r) h) + 1 ∧
      output x = run x (r + 1) := by
  obtain ⟨r, h, hr, hnone, hcross, hfreeze⟩ :=
    run_crossing_has_first_boundary x (n_boot p) (by simpa [output] using hc)
  have hfirst := first_boundary_crossing x r hnone h hcross
  have hlaunch := launchRound_of_first_crossing x r hr hnone h hcross
  exact ⟨r, h, hr, hnone, hfirst.1, hfirst.2.1, hfirst.2.2, hlaunch, hfreeze⟩

/-- With no actual crossing, the actual output monitor remains at or below
the strict source threshold. -/
theorem output_monitor_le_threshold_of_no_crossing
    (x : ReferenceInitializationRun.Input p)
    (hc : (output x).crossing = none) :
    BootstrapLaunchMonitor.monitorValue p (output x).counters ≤
      4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
  exact run_monitor_le_before_launch x (n_boot p) (by simpa [output] using hc)

/-- Deterministic actual launch overshoot. The launched output includes the
entire crossing block, whose length is at most `B_boot`; no-crossing outputs
obey the sharper threshold bound. -/
theorem output_monitor_le_threshold_add_block
    (x : ReferenceInitializationRun.Input p) :
    BootstrapLaunchMonitor.monitorValue p (output x).counters ≤
      4 * BootstrapStartupCostScale.Q x.C_star x.C_h p + p.K * B_boot p := by
  by_cases hc : (output x).crossing.isSome = true
  · obtain ⟨r, h, hr, hnone, _, _, hprior, _, hfreeze⟩ :=
      output_crossing_first_boundary x hc
    have hstep := finishBlock_monitor_le x (run x r) h
    have hs : run x (r + 1) = finishBlock x (run x r) h := by
      rw [run_succ, advance_of_no_crossing x _ hnone h]
    have hlen : blockLength p (nextBlock (run x r) h) ≤ B_boot p := by
      rw [blockLength_eq_calendarBlock_card]
      exact calendarBlock_card_le_B_boot p (nextBlock (run x r) h)
    rw [hfreeze, hs]
    calc
      BootstrapLaunchMonitor.monitorValue p (finishBlock x (run x r) h).counters ≤
          BootstrapLaunchMonitor.monitorValue p (run x r).counters +
            p.K * blockLength p (nextBlock (run x r) h) := hstep
      _ ≤ 4 * BootstrapStartupCostScale.Q x.C_star x.C_h p +
            p.K * blockLength p (nextBlock (run x r) h) :=
        Nat.add_le_add_right (hprior r le_rfl) _
      _ ≤ 4 * BootstrapStartupCostScale.Q x.C_star x.C_h p + p.K * B_boot p := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left p.K hlen) _
  · have hnone : (output x).crossing = none := by
      cases he : (output x).crossing <;> simp_all only [Option.isSome_some,
        Option.isSome_none, not_true_eq_false]
    have hbase := output_monitor_le_threshold_of_no_crossing x hnone
    omega

/-- The sharper bound for the actual no-crossing output, including the
`T+1` terminal launch-round convention. -/
theorem output_monitor_le_threshold_of_no_crossing'
    (x : ReferenceInitializationRun.Input p)
    (hc : (output x).crossing = none) :
    BootstrapLaunchMonitor.monitorValue p (output x).counters ≤
      4 * BootstrapStartupCostScale.Q x.C_star x.C_h p ∧
    launchRound x = p.T + 1 := by
  exact ⟨output_monitor_le_threshold_of_no_crossing x hc, by
    simp [ReferenceInitializationRun.launchRound, hc]⟩

end Bandits.Support.GeneratedBootstrapMonitor

end
