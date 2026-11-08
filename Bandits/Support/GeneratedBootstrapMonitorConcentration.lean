/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapIntervalBounds
public import Bandits.Support.BootstrapLaunchMonitor
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedBootstrapMonitor
public import Bandits.Support.GeneratedBootstrapMonitorMeans
public import Bandits.Support.GeneratedMonitorCountAdaptedness
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.ReferenceInitializationRun

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stopped bootstrap monitor concentration

The literal stopped support and coordinator counters are compared on every
block prefix under the original complete-row/private-coordinate law and the
causal boundary filtration. The interval-clock estimates are assembled from
the accepted source-shifted DOWN tests and their conditional means.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:247-292,
642-682,753-765` and `sources/zip4/manuscript/07_public_setup.tex:42-49,106-140`.

These are internal concentration and finite-set comparisons. They do not
claim that the manuscript coordinator-monitor lemma or any regret theorem is
proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.GeneratedBootstrapMonitorConcentration

open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapIntervalBounds
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.ConstructorDimensions
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapGainBudget
open Bandits.Support.GeneratedBootstrapMonitorMeans
open Bandits.Support.GeneratedMonitorCountAdaptedness
open Bandits.Support.ReferenceInitializationRun

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

variable {p : Parameters}

/-- The fixed source tail parameter `ell = 4 b_N`. -/
@[expose] def monitorTail (p : Parameters) : ℝ := 4 * (b_N p : ℝ)

/-- The stopped support prefix, using the actual reference run and its
incoming no-launch guards. The index type `Fin (n_boot + 1)` represents every
boundary `r ≤ n_boot`, including both endpoints. -/
@[expose] def stoppedSupportPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) (e : Coordinates p) : ℝ :=
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  ∑ s : Fin r.val,
    GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta
        ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ e *
      GeneratedBootstrapGainBudget.rewardSupportCountAt x
        ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ a

/-- The literal arm counter at boundary `r` in the same stopped run used by
`stoppedSupportPrefix`. -/
@[expose] def stoppedCounterPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) (e : Coordinates p) : ℝ :=
  ((ReferenceInitializationRun.run
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e) r.val).counters a : ℝ)

/-- The unguarded rounded-reward support prefix on the same clipped blocks. -/
@[expose] def unstoppedSupportPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) (e : Coordinates p) : ℝ :=
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  ∑ s : Fin r.val,
    GeneratedBootstrapGainBudget.rewardSupportCountAt x
      ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ a

/-- The lower stopped arm comparison, simultaneous over every boundary. -/
@[expose] def armLowerMonitorGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    Set (Coordinates p) :=
  {e | ∀ r : Fin (n_boot p + 1),
    stoppedSupportPrefix p ids rewards C_star C_h eta r a e ≤
      128 * ((p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e +
        (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p)}

/-- The upper stopped arm comparison, simultaneous over every boundary. -/
@[expose] def armUpperMonitorGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    Set (Coordinates p) :=
  {e | ∀ r : Fin (n_boot p + 1),
    (p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e ≤
      2 * stoppedSupportPrefix p ids rewards C_star C_h eta r a e +
        (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p}

/-- The simultaneous stopped arm event. -/
@[expose] def monitorPrefixGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) : Set (Coordinates p) :=
  ⋂ a : Fin p.K,
    armLowerMonitorGood p ids rewards C_star C_h eta a ∩
      armUpperMonitorGood p ids rewards C_star C_h eta a

/-- The literal existential failure event over arms and all block boundaries. -/
@[expose] def monitorPrefixFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) : Set (Coordinates p) :=
  {e | ∃ a : Fin p.K, ∃ r : Fin (n_boot p + 1),
    stoppedSupportPrefix p ids rewards C_star C_h eta r a e >
        128 * ((p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) ∨
      (p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e >
        2 * stoppedSupportPrefix p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p}

/-- Maximum stopped support over the actual finite family of `m`-element
supports. -/
@[expose] def maximumStoppedSupport (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (e : Coordinates p) : ℝ :=
  ((ProductSetLaw.support p.K p.m).image
      (fun S => ∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e)).max'
    ((ProductSetLaw.support_nonempty (m_pos p) p.m_lt_K).image _)

/-- Measurability of the actual stopped support prefix under the ambient
original-law measurable space. -/
theorem measurable_stoppedSupportPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) :
    Measurable (stoppedSupportPrefix p ids rewards C_star C_h eta r a) := by
  classical
  unfold stoppedSupportPrefix
  refine Finset.measurable_fun_sum Finset.univ fun s hs => ?_
  let sb : Fin (n_boot p) :=
    ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩
  have hguard := GeneratedBootstrapMonitorMeans.measurable_noLaunchWeight_at_boundary
    p ids rewards C_star C_h eta sb
  have hguard' : Measurable
      (GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta sb) :=
    hguard.mono (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient
      p sb.val) (by rfl)
  change Measurable (fun e : Coordinates p =>
    GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta sb e *
      BootstrapDownCountMean.rewardSupportCount p sb rewards a)
  exact hguard'.mul_const _

/-- Measurability of each stopped arm counter prefix. -/
theorem measurable_stoppedCounterPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) :
    Measurable (stoppedCounterPrefix p ids rewards C_star C_h eta r a) := by
  unfold stoppedCounterPrefix
  have hm := (measurable_pi_apply a).comp
    ((GeneratedBootstrapBlockFiltrationRepair.measurable_run_counters
    p r.val ids rewards C_star C_h eta).mono
      (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p r.val)
      (by rfl))
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hm

private theorem intervalSum_shifted_fin_sum {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (T r : ℕ) (hr : r ≤ T) (e : Ω) :
    BootstrapIntervalBounds.intervalSum f 1 T r e =
      ∑ s : Fin r, f (s.val + 1) e := by
  induction r with
  | zero => simp [BootstrapIntervalBounds.intervalSum]
  | succ r ih =>
      have hr' : r ≤ T := Nat.le_trans (Nat.le_succ r) hr
      have hlast : 1 ≤ r + 1 ∧ r + 1 ≤ T := by omega
      have hrec : BootstrapIntervalBounds.intervalSum f 1 T (r + 1) e =
          BootstrapIntervalBounds.intervalSum f 1 T r e + f (r + 1) e := by
        simp [BootstrapIntervalBounds.intervalSum, Finset.sum_range_succ, hlast]
      rw [hrec, ih hr']
      rw [Fin.sum_univ_castSucc]
      simp

private theorem sourcePrefixCounter_eq_clockSum (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) (e : Coordinates p) :
    BootstrapIntervalBounds.intervalSum
        (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
          p ids rewards C_star C_h eta t a e) 1 (n_boot p) r.val e =
      stoppedCounterPrefix p ids rewards C_star C_h eta r a e /
        (B_boot p : ℝ) := by
  have hr : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
  rw [intervalSum_shifted_fin_sum _ _ _ hr]
  change (∑ s : Fin r.val,
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest p ids rewards C_star C_h eta
        (s.val + 1) a e) = _
  calc
    _ = ∑ s : Fin r.val,
        GeneratedBootstrapMonitorMeans.normalizedDownBlockTest p ids rewards C_star C_h eta
          ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e := by
      apply Finset.sum_congr rfl
      intro s hs
      let sb : Fin (n_boot p) := ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩
      exact (GeneratedBootstrapMonitorMeans.normalizedDownBlockTest_eq_sourceShifted_at_block
        p ids rewards C_star C_h eta sb a e).symm
    _ = (∑ s : Fin r.val,
          GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e) / (B_boot p : ℝ) := by
      change (∑ s : Fin r.val,
          GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e / (B_boot p : ℝ)) = _
      rw [Finset.sum_div]
    _ = stoppedCounterPrefix p ids rewards C_star C_h eta r a e /
        (B_boot p : ℝ) := by
      rw [GeneratedBootstrapMonitorMeans.downBlockTest_prefix_sum_eq_counter
        p ids rewards C_star C_h eta r.val hr a e]
      rfl

private theorem sourcePrefixPredictable_eq_scaledSupport (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) (e : Coordinates p) :
    (p.K : ℝ) * (B_boot p : ℝ) *
        (∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ a e) =
      stoppedSupportPrefix p ids rewards C_star C_h eta r a e := by
  unfold stoppedSupportPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  let sb : Fin (n_boot p) :=
    ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩
  have hcount : GeneratedBootstrapGainBudget.rewardSupportCountAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) sb a =
      GeneratedDownBlockBoundaryMean.roundedPositiveCount p sb rewards a := by
    unfold GeneratedBootstrapGainBudget.rewardSupportCountAt
    exact (GeneratedDownBlockBoundaryMean.roundedPositiveCount_eq_rewardSupportCount
      sb rewards a).symm
  rw [GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue,
    hcount]
  unfold GeneratedBootstrapMonitorMeans.noLaunchWeight
    GeneratedBootstrapMonitorMeans.noLaunchEvent
  rw [GeneratedDownBlockBoundaryMean.roundedPositiveCount_eq_rewardSupportCount]
  by_cases h : (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val).crossing = none
  · simp [h]
    have hK : (p.K : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (K_pos p).ne')
    have hB : (B_boot p : ℝ) ≠ 0 :=
      (Nat.cast_ne_zero.mpr (B_boot_pos p).ne')
    field_simp
  · simp [h]

private theorem intervalMeanPrefix_bounds_ae (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      ∀ r : Fin (n_boot p + 1),
        (∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt
              (Nat.le_of_lt_succ r.isLt)⟩ a e) / 64 ≤
          BootstrapIntervalBounds.intervalSum
            (fun t e => BootstrapIntervalBounds.conditionalMean
              (GeneratedBootstrapRoundLaw.originalLaw p)
              (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
              (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
                p ids rewards C_star C_h eta t a e) t e)
            1 (n_boot p) r.val e ∧
        BootstrapIntervalBounds.intervalSum
            (fun t e => BootstrapIntervalBounds.conditionalMean
              (GeneratedBootstrapRoundLaw.originalLaw p)
              (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
              (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
                p ids rewards C_star C_h eta t a e) t e)
            1 (n_boot p) r.val e ≤
          ∑ s : Fin r.val,
            GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
              p ids rewards C_star C_h eta
              ⟨s.val, Nat.lt_of_lt_of_le s.isLt
                (Nat.le_of_lt_succ r.isLt)⟩ a e := by
  have hmean := fun s : Fin (n_boot p) =>
    GeneratedBootstrapMonitorMeans.sourceShiftedDownBlockTest_condExp_bounds
      p ids rewards C_star C_h eta s a
  have hlow : ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      ∀ s : Fin (n_boot p),
        GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta s a e / 64 ≤
          BootstrapIntervalBounds.conditionalMean
            (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
            (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
              p ids rewards C_star C_h eta t a e) (s.val + 1) e := by
    apply ae_all_iff.mpr
    intro s
    have h := hmean s
    filter_upwards [h.1] with e he
    simpa [BootstrapIntervalBounds.conditionalMean,
      GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration] using he
  have hupp : ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      ∀ s : Fin (n_boot p),
        BootstrapIntervalBounds.conditionalMean
            (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
            (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
              p ids rewards C_star C_h eta t a e) (s.val + 1) e ≤
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta s a e := by
    apply ae_all_iff.mpr
    intro s
    have h := hmean s
    filter_upwards [h.2] with e he
    simpa [BootstrapIntervalBounds.conditionalMean,
      GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration] using he
  filter_upwards [hlow, hupp] with e hlow hupp
  intro r
  have hr : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
  rw [intervalSum_shifted_fin_sum
    (fun t e => BootstrapIntervalBounds.conditionalMean
      (GeneratedBootstrapRoundLaw.originalLaw p)
      (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
        p ids rewards C_star C_h eta t a e) t e) _ _ hr]
  constructor
  · have hsum : (∑ s : Fin r.val,
        GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
          p ids rewards C_star C_h eta
          ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e / 64) ≤
        ∑ s : Fin r.val,
          BootstrapIntervalBounds.conditionalMean
            (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
            (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
              p ids rewards C_star C_h eta t a e) (s.val + 1) e := by
      apply Finset.sum_le_sum
      intro s hs
      exact hlow ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩
    simpa only [Finset.sum_div] using hsum
  · apply Finset.sum_le_sum
    intro s hs
    exact hupp ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩

private theorem interval_arm_good_lower (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K)
    (e : Coordinates p)
    (hclock : e ∈ BootstrapIntervalBounds.lowerGood
      (GeneratedBootstrapRoundLaw.originalLaw p)
      (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
        p ids rewards C_star C_h eta t a e) 1 (n_boot p) (monitorTail p))
    (hmeans : ∀ r : Fin (n_boot p + 1),
      (∑ s : Fin r.val,
        GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
          p ids rewards C_star C_h eta
          ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ a e) / 64 ≤
        BootstrapIntervalBounds.intervalSum
          (fun t e => BootstrapIntervalBounds.conditionalMean
            (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
            (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
              p ids rewards C_star C_h eta t a e) t e)
          1 (n_boot p) r.val e) :
    e ∈ armLowerMonitorGood p ids rewards C_star C_h eta a := by
  intro r
  by_cases hr0 : r.val = 0
  · have hrzero : r = 0 := Fin.ext hr0
    subst r
    have hs : stoppedSupportPrefix p ids rewards C_star C_h eta 0 a e = 0 := by
      unfold stoppedSupportPrefix
      apply Finset.sum_eq_zero
      intro s hs
      exact Fin.elim0 s
    have hc : stoppedCounterPrefix p ids rewards C_star C_h eta 0 a e = 0 := by
      simp [stoppedCounterPrefix, ReferenceInitializationRun.run_zero,
        ReferenceInitializationRun.initial]
    rw [hs, hc]
    simp only [mul_zero, zero_add]
    have htail : 0 ≤ monitorTail p := by unfold monitorTail; positivity
    have hadd : 0 ≤ (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) htail
    exact mul_nonneg (by norm_num) hadd
  · have hrpos : 1 ≤ r.val := by omega
    have hrle : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
    have hclockr := hclock r.val ⟨hrpos, hrle⟩
    have hX := sourcePrefixCounter_eq_clockSum p ids rewards C_star C_h eta r a e
    have hS := sourcePrefixPredictable_eq_scaledSupport p ids rewards C_star C_h eta r a e
    have hmean := hmeans r
    unfold stoppedCounterPrefix at hX
    rw [hX] at hclockr
    rw [← hS]
    have hKnonneg : 0 ≤ (p.K : ℝ) := Nat.cast_nonneg _
    have hBnonneg : 0 ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
    have hscale : (p.K : ℝ) * (B_boot p : ℝ) *
        (∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e) ≤
        128 * ((p.K : ℝ) *
          (((ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) r.val).counters a : ℝ)) +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) := by
      have hmean' : (∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e) / 128 ≤
          BootstrapIntervalBounds.intervalSum
            (fun t e => BootstrapIntervalBounds.conditionalMean
              (GeneratedBootstrapRoundLaw.originalLaw p)
              (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
              (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
                p ids rewards C_star C_h eta t a e) t e) 1 (n_boot p) r.val e / 2 := by
        linarith [hmean]
      have hobs' : BootstrapIntervalBounds.intervalSum
            (fun t e => BootstrapIntervalBounds.conditionalMean
              (GeneratedBootstrapRoundLaw.originalLaw p)
              (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
              (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
                p ids rewards C_star C_h eta t a e) t e) 1 (n_boot p) r.val e / 2 ≤
          (((ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) r.val).counters a : ℝ) /
            (B_boot p : ℝ)) + monitorTail p := by
        linarith [hclockr]
      have hcombined := hmean'.trans hobs'
      have hlin0 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mp hcombined
      have hlin :
          (∑ s : Fin r.val,
            GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
              p ids rewards C_star C_h eta
              ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e) ≤
            128 * ((((ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput
                p ids rewards C_star C_h eta e) r.val).counters a : ℝ) /
              (B_boot p : ℝ)) + monitorTail p) := by
        nlinarith [hlin0]
      have hmul := mul_le_mul_of_nonneg_left hlin
        (mul_nonneg hKnonneg hBnonneg)
      have hright : (p.K : ℝ) * (B_boot p : ℝ) *
          (128 * ((((ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) r.val).counters a : ℝ) /
            (B_boot p : ℝ)) + monitorTail p)) =
        128 * ((p.K : ℝ) *
          (((ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) r.val).counters a : ℝ)) +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) := by
        field_simp [Nat.cast_ne_zero.mpr (B_boot_pos p).ne'] <;> ring_nf
      rw [hright] at hmul
      exact hmul
    exact hscale

private theorem interval_arm_good_upper (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K)
    (e : Coordinates p)
    (hclock : e ∈ BootstrapIntervalBounds.upperGood
      (GeneratedBootstrapRoundLaw.originalLaw p)
      (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
        p ids rewards C_star C_h eta t a e) 1 (n_boot p) (monitorTail p))
    (hmeans : ∀ r : Fin (n_boot p + 1),
        BootstrapIntervalBounds.intervalSum
          (fun t e => BootstrapIntervalBounds.conditionalMean
            (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
            (fun t e => GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
              p ids rewards C_star C_h eta t a e) t e)
          1 (n_boot p) r.val e ≤
        ∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩ a e) :
    e ∈ armUpperMonitorGood p ids rewards C_star C_h eta a := by
  intro r
  by_cases hr0 : r.val = 0
  · have hrzero : r = 0 := Fin.ext hr0
    subst r
    have hs : stoppedSupportPrefix p ids rewards C_star C_h eta 0 a e = 0 := by
      unfold stoppedSupportPrefix
      apply Finset.sum_eq_zero
      intro s hs
      exact Fin.elim0 s
    have hc : stoppedCounterPrefix p ids rewards C_star C_h eta 0 a e = 0 := by
      simp [stoppedCounterPrefix, ReferenceInitializationRun.run_zero,
        ReferenceInitializationRun.initial]
    rw [hs, hc]
    simp only [mul_zero, zero_add]
    have htail : 0 ≤ monitorTail p := by unfold monitorTail; positivity
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) htail
  · have hrpos : 1 ≤ r.val := by omega
    have hrle : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
    have hclockr := hclock r.val ⟨hrpos, hrle⟩
    have hX := sourcePrefixCounter_eq_clockSum p ids rewards C_star C_h eta r a e
    have hS := sourcePrefixPredictable_eq_scaledSupport p ids rewards C_star C_h eta r a e
    rw [hX] at hclockr
    have hlin : stoppedCounterPrefix p ids rewards C_star C_h eta r a e /
        (B_boot p : ℝ) ≤
      2 * (∑ s : Fin r.val,
        GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
          p ids rewards C_star C_h eta
          ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e) + monitorTail p := by
      linarith [hmeans r]
    have hKnonneg : 0 ≤ (p.K : ℝ) := Nat.cast_nonneg _
    have hBnonneg : 0 ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hlin (mul_nonneg hKnonneg hBnonneg)
    have hleft : (p.K : ℝ) * (B_boot p : ℝ) *
        (stoppedCounterPrefix p ids rewards C_star C_h eta r a e /
          (B_boot p : ℝ)) = (p.K : ℝ) *
          stoppedCounterPrefix p ids rewards C_star C_h eta r a e := by
      field_simp [Nat.cast_ne_zero.mpr (B_boot_pos p).ne']
    have hright : (p.K : ℝ) * (B_boot p : ℝ) *
        (2 * (∑ s : Fin r.val,
          GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
            p ids rewards C_star C_h eta
            ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e) + monitorTail p) =
        2 * ((p.K : ℝ) * (B_boot p : ℝ) *
          (∑ s : Fin r.val,
            GeneratedBootstrapMonitorMeans.normalizedDownBlockPredictableValue
              p ids rewards C_star C_h eta
              ⟨s.val, Nat.lt_of_lt_of_le s.isLt hrle⟩ a e)) +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p := by ring
    rw [hleft, hright, hS] at hmul
    exact hmul

/-- The lower stopped arm event is measurable. -/
theorem measurableSet_armLowerMonitorGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    MeasurableSet (armLowerMonitorGood p ids rewards C_star C_h eta a) := by
  classical
  simp only [armLowerMonitorGood, Set.setOf_forall]
  refine MeasurableSet.iInter fun r => ?_
  have hS := measurable_stoppedSupportPrefix p ids rewards C_star C_h eta r a
  have hC := measurable_stoppedCounterPrefix p ids rewards C_star C_h eta r a
  exact measurableSet_le hS
    (((measurable_const.mul hC).add_const
      ((p.K : ℝ) * (B_boot p : ℝ) * monitorTail p)).const_mul 128)

/-- The upper stopped arm event is measurable. -/
theorem measurableSet_armUpperMonitorGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    MeasurableSet (armUpperMonitorGood p ids rewards C_star C_h eta a) := by
  classical
  simp only [armUpperMonitorGood, Set.setOf_forall]
  refine MeasurableSet.iInter fun r => ?_
  have hS := measurable_stoppedSupportPrefix p ids rewards C_star C_h eta r a
  have hC := measurable_stoppedCounterPrefix p ids rewards C_star C_h eta r a
  exact measurableSet_le ((measurable_const.mul hC))
    ((hS.const_mul 2).add_const ((p.K : ℝ) * (B_boot p : ℝ) * monitorTail p))

/-- The simultaneous stopped monitor event is measurable. -/
theorem measurableSet_monitorPrefixGood (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorPrefixGood p ids rewards C_star C_h eta) := by
  classical
  simp only [monitorPrefixGood, Set.mem_iInter, Set.mem_inter_iff]
  exact MeasurableSet.iInter fun a =>
    (measurableSet_armLowerMonitorGood p ids rewards C_star C_h eta a).inter
      (measurableSet_armUpperMonitorGood p ids rewards C_star C_h eta a)

/-- The literal existential event is exactly the complement of the simultaneous
good event. -/
theorem monitorPrefixFailure_eq_compl (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    monitorPrefixFailure p ids rewards C_star C_h eta =
      (monitorPrefixGood p ids rewards C_star C_h eta)ᶜ := by
  ext e
  constructor
  · rintro ⟨a, r, hbad⟩
    change e ∉ monitorPrefixGood p ids rewards C_star C_h eta
    intro hgood
    simp only [monitorPrefixGood, Set.mem_iInter, Set.mem_inter_iff,
      armLowerMonitorGood, armUpperMonitorGood, Set.mem_setOf_eq] at hgood
    rcases hbad with hbad | hbad
    · exact (not_le_of_gt hbad) ((hgood a).1 r)
    · exact (not_le_of_gt hbad) ((hgood a).2 r)
  · intro hbad
    change e ∉ monitorPrefixGood p ids rewards C_star C_h eta at hbad
    simp only [monitorPrefixGood, Set.mem_iInter, Set.mem_inter_iff,
      armLowerMonitorGood, armUpperMonitorGood, Set.mem_setOf_eq] at hbad
    push_neg at hbad
    change ∃ a : Fin p.K, ∃ r : Fin (n_boot p + 1),
      stoppedSupportPrefix p ids rewards C_star C_h eta r a e >
          128 * ((p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e +
            (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) ∨
        (p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e >
          2 * stoppedSupportPrefix p ids rewards C_star C_h eta r a e +
            (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p
    obtain ⟨a, hchoose⟩ := hbad
    by_cases hlo : ∀ r : Fin (n_boot p + 1),
        stoppedSupportPrefix p ids rewards C_star C_h eta r a e ≤
          128 * ((p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e +
            (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p)
    · obtain ⟨r, hupper⟩ := hchoose hlo
      exact ⟨a, r, Or.inr hupper⟩
    · push_neg at hlo
      obtain ⟨r, hlower⟩ := hlo
      exact ⟨a, r, Or.inl hlower⟩

/-- Measurability of the explicit existential failure event. -/
theorem measurableSet_monitorPrefixFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorPrefixFailure p ids rewards C_star C_h eta) := by
  rw [monitorPrefixFailure_eq_compl]
  exact (measurableSet_monitorPrefixGood p ids rewards C_star C_h eta).compl

/-- For each arm, the lower stopped failure has the source one-tail bound. -/
theorem armLowerMonitorFailure_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ≤
      Real.exp (-monitorTail p) := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let F := GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p
  let X : ℕ → Coordinates p → ℝ := fun t e =>
    GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
      p ids rewards C_star C_h eta t a e
  have hX : ∀ t, 1 ≤ t → t ≤ n_boot p → StronglyMeasurable[F t] (X t) := by
    intro t ht hT
    exact GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_stronglyAdapted
      p ids rewards C_star C_h eta a t
  have hb : ∀ t, 1 ≤ t → t ≤ n_boot p → ∀ᵐ e ∂μ, 0 ≤ X t e ∧ X t e ≤ 1 := by
    intro t ht hT
    exact ae_of_all μ fun e =>
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_mem_unitInterval
        p ids rewards C_star C_h eta t a e
  have hclock := BootstrapIntervalBounds.lower_failure_localized
    hX hb le_rfl (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (n_boot_pos p)))
    (monitorTail p) (A := Set.univ) MeasurableSet.univ
  have hmean := intervalMeanPrefix_bounds_ae p ids rewards C_star C_h eta a
  have hsub :
      (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ≤ᵐ[μ]
        (BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p)
          (monitorTail p))ᶜ := by
    filter_upwards [hmean] with e hmean
    intro hbad he
    exact hbad (interval_arm_good_lower p ids rewards C_star C_h eta a e he
      (fun r => (hmean r).1))
  have hm := measure_mono_ae hsub
  have hclock' : μ.real (Set.univ ∩
      (BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p)
        (monitorTail p))ᶜ) ≤ Real.exp (-monitorTail p) := by
    simpa only [Set.univ_inter, MeasureTheory.probReal_univ, mul_one] using hclock
  have hm' : μ.real ((armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ) ≤
      μ.real ((BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p)
        (monitorTail p))ᶜ) := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hm
  exact hm'.trans (by simpa only [Set.univ_inter] using hclock')

/-- For each arm, the upper stopped failure has the source one-tail bound. -/
theorem armUpperMonitorFailure_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ ≤
      Real.exp (-monitorTail p) := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let F := GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p
  let X : ℕ → Coordinates p → ℝ := fun t e =>
    GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest
      p ids rewards C_star C_h eta t a e
  have hX : ∀ t, 1 ≤ t → t ≤ n_boot p → StronglyMeasurable[F t] (X t) := by
    intro t ht hT
    exact GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_stronglyAdapted
      p ids rewards C_star C_h eta a t
  have hb : ∀ t, 1 ≤ t → t ≤ n_boot p → ∀ᵐ e ∂μ, 0 ≤ X t e ∧ X t e ≤ 1 := by
    intro t ht hT
    exact ae_of_all μ fun e =>
      GeneratedMonitorCountAdaptedness.sourceShiftedDownBlockTest_mem_unitInterval
        p ids rewards C_star C_h eta t a e
  have hclock := BootstrapIntervalBounds.upper_failure_localized
    hX hb le_rfl (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (n_boot_pos p)))
    (monitorTail p) (A := Set.univ) MeasurableSet.univ
  have hmean := intervalMeanPrefix_bounds_ae p ids rewards C_star C_h eta a
  have hsub :
      (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ ≤ᵐ[μ]
        (BootstrapIntervalBounds.upperGood μ F X 1 (n_boot p)
          (monitorTail p))ᶜ := by
    filter_upwards [hmean] with e hmean
    intro hbad he
    exact hbad (interval_arm_good_upper p ids rewards C_star C_h eta a e he
      (fun r => (hmean r).2))
  have hm := measure_mono_ae hsub
  have hclock' : μ.real (Set.univ ∩
      (BootstrapIntervalBounds.upperGood μ F X 1 (n_boot p)
        (monitorTail p))ᶜ) ≤ Real.exp (-monitorTail p) := by
    simpa only [Set.univ_inter, MeasureTheory.probReal_univ, mul_one] using hclock
  have hm' : μ.real ((armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ) ≤
      μ.real ((BootstrapIntervalBounds.upperGood μ F X 1 (n_boot p)
        (monitorTail p))ᶜ) := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hm
  exact hm'.trans (by simpa only [Set.univ_inter] using hclock')

/-- The exact failure event is measurable and its union bound ranges only over
arms and the two interval tails; each interval clock already controls every
prefix boundary. -/
theorem monitorPrefixFailure_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorPrefixGood p ids rewards C_star C_h eta) ∧
      (GeneratedBootstrapRoundLaw.originalLaw p).real
          (monitorPrefixGood p ids rewards C_star C_h eta)ᶜ ≤
        2 * (p.K : ℝ) * Real.exp (-monitorTail p) := by
  classical
  constructor
  · exact measurableSet_monitorPrefixGood p ids rewards C_star C_h eta
  · let μ := GeneratedBootstrapRoundLaw.originalLaw p
    have hunion : (monitorPrefixGood p ids rewards C_star C_h eta)ᶜ =
        ⋃ a : Fin p.K,
          (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ∪
            (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ := by
      simp only [monitorPrefixGood, Set.compl_iInter, Set.compl_inter]
    rw [hunion]
    calc
      μ.real (⋃ a : Fin p.K,
          (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ∪
            (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ) ≤
          ∑ a : Fin p.K,
            μ.real ((armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ∪
              (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun a : Fin p.K =>
            (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ ∪
              (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ)
      _ ≤ ∑ a : Fin p.K,
            (μ.real (armLowerMonitorGood p ids rewards C_star C_h eta a)ᶜ +
              μ.real (armUpperMonitorGood p ids rewards C_star C_h eta a)ᶜ) :=
        Finset.sum_le_sum fun a ha => MeasureTheory.measureReal_union_le _ _
      _ ≤ ∑ a : Fin p.K, (Real.exp (-monitorTail p) +
            Real.exp (-monitorTail p)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact add_le_add
          (armLowerMonitorFailure_measure_le p ids rewards C_star C_h eta a)
          (armUpperMonitorFailure_measure_le p ids rewards C_star C_h eta a)
      _ = 2 * (p.K : ℝ) * Real.exp (-monitorTail p) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
          nsmul_eq_mul]
        ring

/-- Measurability and the two-tail union bound for the literal existential
failure event. -/
theorem literalMonitorPrefixFailure_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorPrefixFailure p ids rewards C_star C_h eta) ∧
      (GeneratedBootstrapRoundLaw.originalLaw p).real
          (monitorPrefixFailure p ids rewards C_star C_h eta) ≤
        2 * (p.K : ℝ) * Real.exp (-monitorTail p) := by
  constructor
  · exact measurableSet_monitorPrefixFailure p ids rewards C_star C_h eta
  · rw [monitorPrefixFailure_eq_compl]
    exact (monitorPrefixFailure_measure_le p ids rewards C_star C_h eta).2

/-- The actual constructor dimensions imply the requested `N⁻²` tail bound. -/
theorem monitorTail_union_le_inv_N_sq (p : Parameters) :
    2 * (p.K : ℝ) * Real.exp (-monitorTail p) ≤ 1 / (N p : ℝ) ^ 2 := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hNge : (1 : ℝ) ≤ (N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.N_pos p)
  have h2K : 2 * p.K ≤ N p := by
    have hmT : 1 ≤ p.m * (p.T + 1) :=
      Nat.mul_le_mul (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
        (by omega : 1 ≤ p.T + 1)
    have hmul := Nat.mul_le_mul_left (2 * p.K) hmT
    simpa [ConstructorDimensions.N, Nat.mul_assoc] using hmul
  have hD : N p + 1 ≤ 2 ^ b_N p :=
    Nat.le_pow_clog (by norm_num) (N p + 1)
  have hpow : (N p : ℝ) + 1 ≤ (2 : ℝ) ^ b_N p := by
    exact_mod_cast hD
  have hexp : (2 : ℝ) ^ (4 * b_N p) ≤ Real.exp (4 * (b_N p : ℝ)) := by
    have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
      calc
        (2 : ℝ) = 1 + 1 := by norm_num
        _ ≤ Real.exp 1 := Real.add_one_le_exp 1
    have hpow : (2 : ℝ) ^ (4 * b_N p) ≤ (Real.exp 1) ^ (4 * b_N p) :=
      pow_le_pow_left₀ (by norm_num) hexp2 _
    have hexpeq : Real.exp (4 * (b_N p : ℝ)) =
        (Real.exp 1) ^ (4 * b_N p) := by
      rw [show 4 * (b_N p : ℝ) = ((4 * b_N p : ℕ) : ℝ) by norm_num]
      rw [← Real.exp_nat_mul (1 : ℝ) (4 * b_N p)]
      congr 1
      norm_num
    exact hpow.trans_eq hexpeq.symm
  have hpow4 : ((N p : ℝ) + 1) ^ 4 ≤ (2 : ℝ) ^ (4 * b_N p) := by
    calc
      ((N p : ℝ) + 1) ^ 4 ≤ ((2 : ℝ) ^ b_N p) ^ 4 := by
        exact pow_le_pow_left₀ (by positivity) hpow _
      _ = (2 : ℝ) ^ (4 * b_N p) := by
        rw [← pow_mul]
        congr 1
        omega
  have hexpInv : Real.exp (-(4 * (b_N p : ℝ))) ≤
      1 / ((N p : ℝ) + 1) ^ 4 := by
    rw [Real.exp_neg]
    have hypos : 0 < ((N p : ℝ) + 1) ^ 4 := pow_pos (by linarith) _
    have hinv := (inv_le_inv₀ (Real.exp_pos _) hypos).2 (hpow4.trans hexp)
    simpa only [one_div] using hinv
  have h2Kreal : 2 * (p.K : ℝ) ≤ (N p : ℝ) := by exact_mod_cast h2K
  have hNcube : (N p : ℝ) ^ 3 ≤ ((N p : ℝ) + 1) ^ 4 := by
    have hbase : (N p : ℝ) ≤ (N p : ℝ) + 1 := by linarith
    have hpow3 := pow_le_pow_left₀ (by positivity : 0 ≤ (N p : ℝ)) hbase 3
    have hy : (1 : ℝ) ≤ (N p : ℝ) + 1 := by linarith
    have hy34 : ((N p : ℝ) + 1) ^ 3 ≤ ((N p : ℝ) + 1) ^ 4 := by
      calc
        ((N p : ℝ) + 1) ^ 3 = ((N p : ℝ) + 1) ^ 3 * 1 := by ring
        _ ≤ ((N p : ℝ) + 1) ^ 3 * ((N p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
        _ = ((N p : ℝ) + 1) ^ 4 := by rw [pow_succ]; ring
    exact hpow3.trans hy34
  have hratio : (N p : ℝ) / ((N p : ℝ) + 1) ^ 4 ≤ 1 / (N p : ℝ) ^ 2 := by
    rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < (N p : ℝ) + 1) 4)]
    field_simp
    nlinarith [hNcube]
  calc
    2 * (p.K : ℝ) * Real.exp (-monitorTail p) ≤
        (N p : ℝ) / ((N p : ℝ) + 1) ^ 4 := by
      rw [monitorTail]
      have hden : 0 < ((N p : ℝ) + 1) ^ 4 := pow_pos (by linarith) _
      have hmult := mul_le_mul_of_nonneg_left hexpInv
        (show 0 ≤ 2 * (p.K : ℝ) by positivity)
      calc
        2 * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ≤
            2 * (p.K : ℝ) / ((N p : ℝ) + 1) ^ 4 := by
          simpa [one_div, div_eq_mul_inv] using hmult
        _ ≤ (N p : ℝ) / ((N p : ℝ) + 1) ^ 4 :=
          div_le_div_of_nonneg_right h2Kreal (le_of_lt hden)
    _ ≤ 1 / (N p : ℝ) ^ 2 := hratio

/-- The full two-sided stopped monitor failure event is at most `N⁻²`. -/
theorem monitorPrefixFailure_measure_le_inv_N_sq (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorPrefixGood p ids rewards C_star C_h eta)ᶜ ≤
      1 / (N p : ℝ) ^ 2 := by
  have h := (monitorPrefixFailure_measure_le p ids rewards C_star C_h eta).2
  exact h.trans (monitorTail_union_le_inv_N_sq p)

/-- The explicit existential event also satisfies the derived `N⁻²` bound. -/
theorem literalMonitorPrefixFailure_measure_le_inv_N_sq (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorPrefixFailure p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  rw [monitorPrefixFailure_eq_compl]
  exact monitorPrefixFailure_measure_le_inv_N_sq p ids rewards C_star C_h eta

/-- Every supported comparator set satisfies both summed arm inequalities
simultaneously on `monitorPrefixGood`. -/
theorem supportedPrefix_bounds (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (e : Coordinates p)
    (he : e ∈ monitorPrefixGood p ids rewards C_star C_h eta)
    (S : Finset (Fin p.K)) (hS : S ∈ ProductSetLaw.support p.K p.m) :
    (∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) ≤
      128 * ((p.K : ℝ) *
        (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) ∧
    (p.K : ℝ) *
        (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) ≤
      2 * (∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p := by
  have hgood (a : Fin p.K) :
      e ∈ armLowerMonitorGood p ids rewards C_star C_h eta a ∧
      e ∈ armUpperMonitorGood p ids rewards C_star C_h eta a := by
    change e ∈ armLowerMonitorGood p ids rewards C_star C_h eta a ∧
      e ∈ armUpperMonitorGood p ids rewards C_star C_h eta a
    exact (Set.mem_iInter.mp he) a
  have hcard := BootstrapLaunchMonitor.supportedSet_card p hS
  constructor
  · calc
      _ ≤ ∑ a ∈ S,
          128 * ((p.K : ℝ) * stoppedCounterPrefix p ids rewards C_star C_h eta r a e +
            (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (hgood a).1 r
      _ = 128 * ((p.K : ℝ) *
            (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) +
            (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_mul]
        ring
  · calc
      (p.K : ℝ) *
          (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) =
        ∑ a ∈ S, (p.K : ℝ) *
          stoppedCounterPrefix p ids rewards C_star C_h eta r a e := by
            rw [Finset.mul_sum]
      _ ≤ ∑ a ∈ S,
          (2 * stoppedSupportPrefix p ids rewards C_star C_h eta r a e +
            (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (hgood a).2 r
      _ = 2 * (∑ a ∈ S,
            stoppedSupportPrefix p ids rewards C_star C_h eta r a e) +
          (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_mul]
        ring

/-- The maximum support prefix is compared with the already-defined source
monitor on the actual run counters. -/
theorem maximumSupport_monitorValue_bounds (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (r : Fin (n_boot p + 1)) (e : Coordinates p)
    (he : e ∈ monitorPrefixGood p ids rewards C_star C_h eta) :
    maximumStoppedSupport p ids rewards C_star C_h eta r e ≤
      128 * ((BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) r.val).counters : ℝ) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) ∧
    (BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) r.val).counters : ℝ) ≤
      2 * maximumStoppedSupport p ids rewards C_star C_h eta r e +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p := by
  classical
  let c := fun a : Fin p.K =>
    (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) r.val).counters a
  let add := (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p
  have hsupport : ∀ S ∈ ProductSetLaw.support p.K p.m,
      (∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) ≤
        128 * ((p.K : ℝ) * (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) + add) ∧
      (p.K : ℝ) *
          (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) ≤
        2 * (∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) + add := by
    intro S hS
    exact supportedPrefix_bounds p ids rewards C_star C_h eta r e he S hS
  have hcounter_eq : ∀ a, stoppedCounterPrefix p ids rewards C_star C_h eta r a e =
      (c a : ℝ) := by intro a; rfl
  have hmaxCounter_mem :
      BootstrapLaunchMonitor.maximumSupportedCounterSum p c ∈
        BootstrapLaunchMonitor.supportedSetSums p c :=
    Finset.max'_mem _ _
  obtain ⟨Smax, hSmax, hsummax⟩ := Finset.mem_image.mp hmaxCounter_mem
  have hsummax' : (∑ a ∈ Smax, c a) =
      BootstrapLaunchMonitor.maximumSupportedCounterSum p c := hsummax
  have hsupport_max_le : maximumStoppedSupport p ids rewards C_star C_h eta r e ≤
      128 * ((BootstrapLaunchMonitor.monitorValue p c : ℝ) + add) := by
    unfold maximumStoppedSupport
    apply Finset.max'_le
      ((ProductSetLaw.support p.K p.m).image
        (fun S => ∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e))
      ((ProductSetLaw.support_nonempty (m_pos p) p.m_lt_K).image _)
      (128 * ((BootstrapLaunchMonitor.monitorValue p c : ℝ) + add))
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨S, hS, rfl⟩
    have h := hsupport S hS
    have hcs :
        (∑ a ∈ S, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) =
          (∑ a ∈ S, (c a : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hcounter_eq a
    have hsumle_nat : (∑ a ∈ S, c a) ≤
        BootstrapLaunchMonitor.maximumSupportedCounterSum p c := by
      have hmem : (∑ a ∈ S, c a) ∈ BootstrapLaunchMonitor.supportedSetSums p c :=
        Finset.mem_image.mpr ⟨S, hS, rfl⟩
      exact Finset.le_max' _ _ hmem
    have hsumle : (∑ a ∈ S, (c a : ℝ)) ≤
        (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) := by
      exact_mod_cast hsumle_nat
    have hmon : (BootstrapLaunchMonitor.monitorValue p c : ℝ) =
        (p.K : ℝ) * (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) := by
      simp only [BootstrapLaunchMonitor.monitorValue, Nat.cast_mul]
    rw [hcs] at h
    rw [hmon]
    calc
      (∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) ≤
          128 * ((p.K : ℝ) * (∑ a ∈ S, (c a : ℝ)) + add) := h.1
      _ ≤ 128 * ((p.K : ℝ) *
            (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) + add) := by
        gcongr
  have hmonitor_le :
      (BootstrapLaunchMonitor.monitorValue p c : ℝ) ≤
        2 * maximumStoppedSupport p ids rewards C_star C_h eta r e + add := by
    have hmaxArm := hsupport Smax hSmax
    have hcounterSum :
        (∑ a ∈ Smax, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) =
          (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) := by
      calc
        (∑ a ∈ Smax, stoppedCounterPrefix p ids rewards C_star C_h eta r a e) =
            (∑ a ∈ Smax, (c a : ℝ)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hcounter_eq a
        _ = ((∑ a ∈ Smax, c a : ℕ) : ℝ) := by simp
        _ = (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) := by
          exact_mod_cast hsummax'
    rw [hcounterSum] at hmaxArm
    have hmon : (BootstrapLaunchMonitor.monitorValue p c : ℝ) =
        (p.K : ℝ) *
          (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) := by
      simp only [BootstrapLaunchMonitor.monitorValue, Nat.cast_mul]
    rw [hmon]
    calc
      (p.K : ℝ) *
          (BootstrapLaunchMonitor.maximumSupportedCounterSum p c : ℝ) ≤
        2 * (∑ a ∈ Smax, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) + add :=
          hmaxArm.2
      _ ≤ 2 * maximumStoppedSupport p ids rewards C_star C_h eta r e + add := by
        have hmem : (∑ a ∈ Smax, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) ∈
            (ProductSetLaw.support p.K p.m).image
              (fun S => ∑ a ∈ S, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) :=
          Finset.mem_image.mpr ⟨Smax, hSmax, rfl⟩
        have hle : (∑ a ∈ Smax, stoppedSupportPrefix p ids rewards C_star C_h eta r a e) ≤
            maximumStoppedSupport p ids rewards C_star C_h eta r e := by
          unfold maximumStoppedSupport
          exact Finset.le_max' _ _ hmem
        gcongr
  have hc : c = (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) r.val).counters := by
    funext a
    rfl
  rw [hc] at hsupport_max_le hmonitor_le
  constructor
  · simpa [add] using hsupport_max_le
  · simpa [add] using hmonitor_le

/-- A genuine no-crossing boundary forces every earlier incoming guard to be
one by persistence of the actual stopped run. -/
theorem noLaunchWeight_eq_one_of_run_no_crossing (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (q : ℕ) (hq : q ≤ n_boot p)
    (hqnone : (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) q).crossing = none)
    (s : Fin (n_boot p)) (hs : s.val ≤ q) :
    GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta s e = 1 := by
  have hsn : (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val).crossing = none := by
    by_contra hnot
    have hsome : (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) s.val).crossing.isSome = true := by
      cases h : (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val).crossing <;> simp_all
    have hfreeze := ReferenceInitializationRun.run_stops_at_crossing
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val (q - s.val) hsome
    rw [Nat.add_sub_of_le hs] at hfreeze
    rw [hfreeze] at hqnone
    exact hnot hqnone
  simp [GeneratedBootstrapMonitorMeans.noLaunchWeight,
    GeneratedBootstrapMonitorMeans.noLaunchEvent, hsn]

/-- A previously crossed stopped boundary turns its actual next no-launch
weight off, including on all already-crossed tails. -/
theorem noLaunchWeight_eq_zero_of_run_crossed (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (s : Fin (n_boot p))
    (hc : (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val).crossing ≠ none) :
    GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta s e = 0 := by
  simp [GeneratedBootstrapMonitorMeans.noLaunchWeight,
    GeneratedBootstrapMonitorMeans.noLaunchEvent, hc]

/-- Every prefix ending no later than a genuine no-crossing boundary has all
its actual incoming no-launch guards equal to one. -/
theorem stoppedSupport_eq_unstopped_of_run_no_crossing (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (q : ℕ) (hq : q ≤ n_boot p)
    (hqnone : (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) q).crossing = none)
    (r : Fin (n_boot p + 1)) (hr : r.val ≤ q + 1) (a : Fin p.K) :
    stoppedSupportPrefix p ids rewards C_star C_h eta r a e =
      unstoppedSupportPrefix p ids rewards C_star C_h eta r a e := by
  unfold stoppedSupportPrefix unstoppedSupportPrefix
  apply Finset.sum_congr rfl
  intro s hs
  let sb : Fin (n_boot p) :=
    ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_of_lt_succ r.isLt)⟩
  have hsb_le : sb.val ≤ q := by
    have hslt : s.val < q + 1 := s.isLt.trans_le hr
    exact Nat.lt_succ_iff.mp hslt
  change GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta sb e *
      GeneratedBootstrapGainBudget.rewardSupportCountAt
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) sb a = _
  rw [noLaunchWeight_eq_one_of_run_no_crossing p ids rewards C_star C_h eta e
    q hq hqnone sb hsb_le]
  simp [sb]

/-- If the actual output has no crossing, every support guard through the
terminal boundary is one, including the shortened final calendar block. -/
theorem stoppedSupport_eq_unstopped_of_no_launch (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (hc : (ReferenceInitializationRun.output
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)).crossing = none)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) :
    stoppedSupportPrefix p ids rewards C_star C_h eta r a e =
      unstoppedSupportPrefix p ids rewards C_star C_h eta r a e := by
  apply stoppedSupport_eq_unstopped_of_run_no_crossing p ids rewards C_star C_h eta e
    (n_boot p) le_rfl ?_ r (Nat.le_of_lt r.isLt) a
  simpa [ReferenceInitializationRun.output] using hc

/-- Through the first launching block, all incoming support guards are
derived from the actual run's persistence up to its first crossing boundary.
The returned launch monitor also uses the existing deterministic one-block
overshoot theorem. -/
theorem stoppedSupport_eq_unstopped_through_first_crossing (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (a : Fin p.K)
    (hc : (ReferenceInitializationRun.output
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)).crossing.isSome = true) :
    ∃ q, ∃ hq : q + 1 ≤ n_boot p,
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) q).crossing = none ∧
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) (q + 1)).crossing.isSome = true ∧
      stoppedSupportPrefix p ids rewards C_star C_h eta
          ⟨q + 1, Nat.lt_succ_of_le hq⟩ a e =
        unstoppedSupportPrefix p ids rewards C_star C_h eta
          ⟨q + 1, Nat.lt_succ_of_le hq⟩ a e ∧
      BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.output
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)).counters ≤
        4 * BootstrapStartupCostScale.Q
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e).C_star
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e).C_h p + p.K * B_boot p := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  obtain ⟨q, _, hq, hnone, hcrossing, _, _, _, _⟩ :=
    GeneratedBootstrapMonitor.output_crossing_first_boundary x (by
      simpa [x, ReferenceInitializationRun.output] using hc)
  have hprefix := stoppedSupport_eq_unstopped_of_run_no_crossing
    p ids rewards C_star C_h eta e q (Nat.le_trans (Nat.le_succ q) hq) hnone
    ⟨q + 1, Nat.lt_succ_of_le hq⟩ (le_rfl) a
  refine ⟨q, hq, hnone, ?_, hprefix, ?_⟩
  · change (ReferenceInitializationRun.run x (q + 1)).crossing.isSome = true
    rw [hcrossing]
    rfl
  · simpa [x, ReferenceInitializationRun.output] using
      GeneratedBootstrapMonitor.output_monitor_le_threshold_add_block x

end Bandits.Support.GeneratedBootstrapMonitorConcentration

end
