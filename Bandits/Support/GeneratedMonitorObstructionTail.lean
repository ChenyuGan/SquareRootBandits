/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapMonitorConcentration
public import Bandits.Support.GeneratedComparatorChargeObstruction
public import Bandits.Support.GeneratedForcedCorrectionObstruction

import Mathlib.MeasureTheory.Measure.Real

/-!
# Literal startup monitor obstruction tails

The existing comparator-deficit and upper-monitor obstruction predicates are
pulled back to the original complete-row/private-coordinate carrier. Their
stopped prefixes agree with the accepted monitor prefixes, including every
already-stopped boundary. This identifies their union with the literal
two-sided monitor failure event and transfers its tail estimates.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:642-682,753-765`
and `sources/zip4/manuscript/07_public_setup.tex:106-140`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.GeneratedMonitorObstructionTail

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapGainBudget
open Bandits.Support.GeneratedBootstrapMonitorConcentration
open Bandits.Support.GeneratedBootstrapMonitorMeans
open Bandits.Support.ReferenceInitializationRun

abbrev Parameters := GeneratedBootstrapMonitorConcentration.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapMonitorConcentration.Coordinates p

variable {p : Parameters}

/-- The pullback of the existing comparator monitor-deficit obstruction to
the original coordinates and their single reference input. -/
def comparatorMonitorDeficitPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) : Set (Coordinates p) :=
  {e | GeneratedComparatorChargeObstruction.comparatorMonitorDeficit
    (referenceInput p ids rewards C_star C_h eta e)}

/-- The pullback of the existing upper-monitor obstruction to the original
coordinates and their single reference input. -/
def monitorUpperObstructionPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) : Set (Coordinates p) :=
  {e | GeneratedForcedCorrectionObstruction.monitorUpperObstruction
    (referenceInput p ids rewards C_star C_h eta e)}

/-- The union of the two existing literal startup monitor obstructions. -/
def monitorObstructionPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) : Set (Coordinates p) :=
  {e | GeneratedComparatorChargeObstruction.comparatorMonitorDeficit
      (referenceInput p ids rewards C_star C_h eta e) ∨
    GeneratedForcedCorrectionObstruction.monitorUpperObstruction
      (referenceInput p ids rewards C_star C_h eta e)}

/-- The literal comparator stopped support prefix is the accepted stopped
monitor prefix on the same reference input. The guard equality is reduced
from the body of `noLaunchWeight`, including its event membership and the
`Fin` prefix casts. -/
theorem stoppedRewardSupportPrefix_eq_stoppedSupportPrefix (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
        (referenceInput p ids rewards C_star C_h eta e) r hr a =
      GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
        p ids rewards C_star C_h eta ⟨r, Nat.lt_succ_of_le hr⟩ a e := by
  classical
  let x := referenceInput p ids rewards C_star C_h eta e
  simp only [GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix,
    GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix]
  refine Finset.sum_congr rfl ?_
  intro s hs
  let sb : Fin (n_boot p) := ⟨s.val, s.isLt.trans_le hr⟩
  have hcast : Fin.castLE hr s = sb := Fin.ext rfl
  change (if (ReferenceInitializationRun.run x (Fin.castLE hr s).val).crossing = none then
      GeneratedBootstrapGainBudget.rewardSupportCountAt x (Fin.castLE hr s) a else 0) =
    GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta
        ⟨s.val, Nat.lt_of_lt_of_le s.isLt
          (Nat.le_of_lt_succ (Nat.lt_succ_of_le hr))⟩ e *
      GeneratedBootstrapGainBudget.rewardSupportCountAt x sb a
  rw [hcast]
  have hweight :
      GeneratedBootstrapMonitorMeans.noLaunchWeight p ids rewards C_star C_h eta sb e =
        (if (ReferenceInitializationRun.run x sb.val).crossing = none then
          (1 : ℝ) else 0) := by
    change (if e ∈ GeneratedBootstrapMonitorMeans.noLaunchEvent
        p ids rewards C_star C_h eta sb then (1 : ℝ) else 0) =
      (if (ReferenceInitializationRun.run x sb.val).crossing = none then
        (1 : ℝ) else 0)
    simp only [GeneratedBootstrapMonitorMeans.noLaunchEvent,
      Set.mem_ofPred_eq, x]
    by_cases hcross :
        (ReferenceInitializationRun.run
          (referenceInput p ids rewards C_star C_h eta e) sb.val).crossing = none
    · simp [hcross]
    · simp [hcross]
  rw [hweight]
  by_cases hcross : (ReferenceInitializationRun.run x sb.val).crossing = none
  · simp [hcross]
  · simp [hcross]

private theorem forcedSupportPrefix_eq_stoppedRewardSupportPrefix
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    (∑ s : Fin r,
      (if (ReferenceInitializationRun.run
          (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none then
          (1 : ℝ) else 0) *
        GeneratedBootstrapGainBudget.rewardSupportCountAt
          (referenceInput p ids rewards C_star C_h eta e)
          ⟨s.val, s.isLt.trans_le hr⟩ a) =
      GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
        (referenceInput p ids rewards C_star C_h eta e) r hr a := by
  classical
  let x := referenceInput p ids rewards C_star C_h eta e
  simp only [GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix]
  refine Finset.sum_congr rfl ?_
  intro s hs
  let sb : Fin (n_boot p) := ⟨s.val, s.isLt.trans_le hr⟩
  have hcast : Fin.castLE hr s = sb := Fin.ext rfl
  have hsbval : sb.val = s.val := rfl
  change (if (ReferenceInitializationRun.run x s.val).crossing = none then
      (1 : ℝ) else 0) *
        GeneratedBootstrapGainBudget.rewardSupportCountAt x sb a =
    (if (ReferenceInitializationRun.run x (Fin.castLE hr s).val).crossing = none then
      GeneratedBootstrapGainBudget.rewardSupportCountAt x (Fin.castLE hr s) a else 0)
  rw [hcast]
  rw [← hsbval]
  simp

private theorem stoppedRewardSupportPrefix_eq_stoppedSupportPrefix_fin
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (r : Fin (n_boot p + 1)) (a : Fin p.K) :
    GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
        (referenceInput p ids rewards C_star C_h eta e) r.val
        (Nat.le_of_lt_succ r.isLt) a =
      GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
        p ids rewards C_star C_h eta r a e := by
  have h := stoppedRewardSupportPrefix_eq_stoppedSupportPrefix p ids rewards
    C_star C_h eta e r.val (Nat.le_of_lt_succ r.isLt) a
  have hfin :
      (⟨r.val, Nat.lt_succ_of_le (Nat.le_of_lt_succ r.isLt)⟩ :
        Fin (n_boot p + 1)) = r := Fin.ext rfl
  rw [hfin] at h
  exact h

private theorem comparatorMonitorDeficitPullback_eq_finite_union
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    comparatorMonitorDeficitPullback p ids rewards C_star C_h eta =
      ⋃ a : Fin p.K, ⋃ r : Fin (n_boot p + 1),
        {e | GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
            (referenceInput p ids rewards C_star C_h eta e) r.val
            (Nat.le_of_lt_succ r.isLt) a >
          128 * ((p.K : ℝ) *
            ((ReferenceInitializationRun.run
              (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) +
            (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} := by
  ext e
  simp only [comparatorMonitorDeficitPullback, Set.mem_ofPred_eq,
    GeneratedComparatorChargeObstruction.comparatorMonitorDeficit,
    Set.mem_iUnion]
  constructor
  · rintro ⟨a, r, hr, hbad⟩
    exact ⟨a, ⟨r, Nat.lt_succ_of_le hr⟩, hbad⟩
  · rintro ⟨a, r, hbad⟩
    exact ⟨a, r.val, Nat.le_of_lt_succ r.isLt, hbad⟩

private theorem monitorUpperObstructionPullback_eq_finite_union
    (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    monitorUpperObstructionPullback p ids rewards C_star C_h eta =
      ⋃ a : Fin p.K, ⋃ r : Fin (n_boot p + 1),
        {e | (p.K : ℝ) *
              ((ReferenceInitializationRun.run
                (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) >
            2 * (∑ s : Fin r.val,
              (if (ReferenceInitializationRun.run
                  (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none then
                  (1 : ℝ) else 0) *
                GeneratedBootstrapGainBudget.rewardSupportCountAt
                  (referenceInput p ids rewards C_star C_h eta e)
                  ⟨s.val, s.isLt.trans_le (Nat.le_of_lt_succ r.isLt)⟩ a) +
            (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))} := by
  ext e
  simp only [monitorUpperObstructionPullback, Set.mem_ofPred_eq,
    GeneratedForcedCorrectionObstruction.monitorUpperObstruction,
    Set.mem_iUnion]
  constructor
  · rintro ⟨a, r, hr, hbad⟩
    exact ⟨a, ⟨r, Nat.lt_succ_of_le hr⟩, hbad⟩
  · rintro ⟨a, r, hbad⟩
    exact ⟨a, r.val, Nat.le_of_lt_succ r.isLt, hbad⟩

/-- Ambient measurability of the literal comparator-deficit pullback. Its
finite arm/boundary union is proved from the accepted stopped-prefix
measurability, not inferred from the combined event. -/
theorem measurableSet_comparatorMonitorDeficitPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (comparatorMonitorDeficitPullback p ids rewards C_star C_h eta) := by
  rw [comparatorMonitorDeficitPullback_eq_finite_union]
  classical
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun r => ?_
  let hr : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
  have hprefix : ∀ e : Coordinates p,
      GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
          (referenceInput p ids rewards C_star C_h eta e) r.val hr a =
        GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
          p ids rewards C_star C_h eta r a e := by
    intro e
    exact stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
      p ids rewards C_star C_h eta e r.val hr a
  have hfiber :
      {e | GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
          (referenceInput p ids rewards C_star C_h eta e) r.val hr a >
        128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) +
          (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} =
      {e | GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
          p ids rewards C_star C_h eta r a e >
        128 * ((p.K : ℝ) *
          GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
            p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) *
            GeneratedBootstrapMonitorConcentration.monitorTail p)} := by
    ext e
    change GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
          (referenceInput p ids rewards C_star C_h eta e) r.val hr a >
        128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) +
          (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))) ↔
      GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
          p ids rewards C_star C_h eta r a e >
        128 * ((p.K : ℝ) *
          GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
            p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) *
            GeneratedBootstrapMonitorConcentration.monitorTail p)
    rw [hprefix e]
    simp [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
      GeneratedBootstrapMonitorConcentration.monitorTail]
  rw [hfiber]
  have hS := GeneratedBootstrapMonitorConcentration.measurable_stoppedSupportPrefix
    p ids rewards C_star C_h eta r a
  have hC := GeneratedBootstrapMonitorConcentration.measurable_stoppedCounterPrefix
    p ids rewards C_star C_h eta r a
  exact measurableSet_lt
    (((measurable_const.mul hC).add_const
      ((p.K : ℝ) * (B_boot p : ℝ) * monitorTail p)).const_mul 128) hS

/-- Ambient measurability of the literal upper-monitor obstruction pullback.
Its finite arm/boundary union uses the accepted stopped support and counter
prefix measurability. -/
theorem measurableSet_monitorUpperObstructionPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorUpperObstructionPullback p ids rewards C_star C_h eta) := by
  rw [monitorUpperObstructionPullback_eq_finite_union]
  classical
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun r => ?_
  let hr : r.val ≤ n_boot p := Nat.le_of_lt_succ r.isLt
  have hsum : ∀ e : Coordinates p,
      (∑ s : Fin r.val,
        (if (ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none then
            (1 : ℝ) else 0) *
          GeneratedBootstrapGainBudget.rewardSupportCountAt
            (referenceInput p ids rewards C_star C_h eta e)
            ⟨s.val, s.isLt.trans_le hr⟩ a) =
        GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
          (referenceInput p ids rewards C_star C_h eta e) r.val hr a := by
    intro e
    exact forcedSupportPrefix_eq_stoppedRewardSupportPrefix
      p ids rewards C_star C_h eta e r.val hr a
  have hprefix : ∀ e : Coordinates p,
      GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix
          (referenceInput p ids rewards C_star C_h eta e) r.val hr a =
        GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
          p ids rewards C_star C_h eta r a e := by
    intro e
    exact stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
      p ids rewards C_star C_h eta e r.val hr a
  have hfiber :
      {e | (p.K : ℝ) *
            ((ReferenceInitializationRun.run
              (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) >
          2 * (∑ s : Fin r.val,
            (if (ReferenceInitializationRun.run
                (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none then
                (1 : ℝ) else 0) *
              GeneratedBootstrapGainBudget.rewardSupportCountAt
                (referenceInput p ids rewards C_star C_h eta e)
                ⟨s.val, s.isLt.trans_le hr⟩ a) +
          (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))} =
      {e | (p.K : ℝ) *
            GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
              p ids rewards C_star C_h eta r a e >
          2 * GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
              p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) *
            GeneratedBootstrapMonitorConcentration.monitorTail p} := by
    ext e
    change (p.K : ℝ) *
            ((ReferenceInitializationRun.run
              (referenceInput p ids rewards C_star C_h eta e) r.val).counters a : ℝ) >
          2 * (∑ s : Fin r.val,
            (if (ReferenceInitializationRun.run
                (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none then
                (1 : ℝ) else 0) *
              GeneratedBootstrapGainBudget.rewardSupportCountAt
                (referenceInput p ids rewards C_star C_h eta e)
                ⟨s.val, s.isLt.trans_le hr⟩ a) +
          (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)) ↔
      (p.K : ℝ) *
          GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
            p ids rewards C_star C_h eta r a e >
        2 * GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
            p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) *
            GeneratedBootstrapMonitorConcentration.monitorTail p
    rw [hsum e, hprefix e]
    simp [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
      GeneratedBootstrapMonitorConcentration.monitorTail]
  rw [hfiber]
  have hS := GeneratedBootstrapMonitorConcentration.measurable_stoppedSupportPrefix
    p ids rewards C_star C_h eta r a
  have hC := GeneratedBootstrapMonitorConcentration.measurable_stoppedCounterPrefix
    p ids rewards C_star C_h eta r a
  exact measurableSet_lt
    ((hS.const_mul 2).add_const
      ((p.K : ℝ) * (B_boot p : ℝ) * monitorTail p))
    (measurable_const.mul hC)

/-- The combined literal pullback is the set-theoretic union of its two
individual pullbacks. -/
theorem monitorObstructionPullback_eq_union (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    monitorObstructionPullback p ids rewards C_star C_h eta =
      comparatorMonitorDeficitPullback p ids rewards C_star C_h eta ∪
        monitorUpperObstructionPullback p ids rewards C_star C_h eta := by
  ext e
  simp only [monitorObstructionPullback, comparatorMonitorDeficitPullback,
    monitorUpperObstructionPullback, Set.mem_ofPred_eq, Set.mem_union]

/-- Ambient measurability of the union of both literal pullback events. -/
theorem measurableSet_monitorObstructionPullback (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet (monitorObstructionPullback p ids rewards C_star C_h eta) := by
  rw [monitorObstructionPullback_eq_union]
  exact (measurableSet_comparatorMonitorDeficitPullback
    p ids rewards C_star C_h eta).union
      (measurableSet_monitorUpperObstructionPullback p ids rewards C_star C_h eta)

/-- The union of the two existing obstruction pullbacks is exactly the
literal two-sided stopped-prefix failure event on the original coordinates.
Both strict inequalities and all boundaries are retained. -/
theorem literalMonitorObstructionEvent_eq_monitorPrefixFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    {e | GeneratedComparatorChargeObstruction.comparatorMonitorDeficit
        (referenceInput p ids rewards C_star C_h eta e) ∨
      GeneratedForcedCorrectionObstruction.monitorUpperObstruction
        (referenceInput p ids rewards C_star C_h eta e)} =
      GeneratedBootstrapMonitorConcentration.monitorPrefixFailure
        p ids rewards C_star C_h eta := by
  ext e
  change (GeneratedComparatorChargeObstruction.comparatorMonitorDeficit
      (referenceInput p ids rewards C_star C_h eta e) ∨
    GeneratedForcedCorrectionObstruction.monitorUpperObstruction
      (referenceInput p ids rewards C_star C_h eta e)) ↔ _
  change _ ↔ ∃ a : Fin p.K, ∃ r : Fin (n_boot p + 1),
    GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
        p ids rewards C_star C_h eta r a e >
        128 * ((p.K : ℝ) *
          GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
            p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p) ∨
      (p.K : ℝ) *
          GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix
            p ids rewards C_star C_h eta r a e >
        2 * GeneratedBootstrapMonitorConcentration.stoppedSupportPrefix
            p ids rewards C_star C_h eta r a e +
          (p.K : ℝ) * (B_boot p : ℝ) * monitorTail p
  constructor
  · intro h
    rcases h with hcomp | hupper
    · rcases hcomp with ⟨a, r, hr, hbad⟩
      refine ⟨a, ⟨r, Nat.lt_succ_of_le hr⟩, Or.inl ?_⟩
      have hp := stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
        p ids rewards C_star C_h eta e r hr a
      rw [hp] at hbad
      simpa [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
        GeneratedBootstrapMonitorConcentration.monitorTail] using hbad
    · rcases hupper with ⟨a, r, hr, hbad⟩
      refine ⟨a, ⟨r, Nat.lt_succ_of_le hr⟩, Or.inr ?_⟩
      have hs := forcedSupportPrefix_eq_stoppedRewardSupportPrefix
        p ids rewards C_star C_h eta e r hr a
      have hp := stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
        p ids rewards C_star C_h eta e r hr a
      have hsp := hs.trans hp
      rw [hsp] at hbad
      simpa [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
        GeneratedBootstrapMonitorConcentration.monitorTail] using hbad
  · rintro ⟨a, r, hbad⟩
    rcases hbad with hlow | hhigh
    · left
      refine ⟨a, r.val, Nat.le_of_lt_succ r.isLt, ?_⟩
      have hp := stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
        p ids rewards C_star C_h eta e r.val (Nat.le_of_lt_succ r.isLt) a
      have hfin :
          (⟨r.val, Nat.lt_succ_of_le (Nat.le_of_lt_succ r.isLt)⟩ :
            Fin (n_boot p + 1)) = r := Fin.ext rfl
      rw [hfin] at hp
      rw [← hp] at hlow
      simpa [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
        GeneratedBootstrapMonitorConcentration.monitorTail] using hlow
    · right
      refine ⟨a, r.val, Nat.le_of_lt_succ r.isLt, ?_⟩
      have hs := forcedSupportPrefix_eq_stoppedRewardSupportPrefix
        p ids rewards C_star C_h eta e r.val (Nat.le_of_lt_succ r.isLt) a
      have hp := stoppedRewardSupportPrefix_eq_stoppedSupportPrefix
        p ids rewards C_star C_h eta e r.val (Nat.le_of_lt_succ r.isLt) a
      have hfin :
          (⟨r.val, Nat.lt_succ_of_le (Nat.le_of_lt_succ r.isLt)⟩ :
            Fin (n_boot p + 1)) = r := Fin.ext rfl
      rw [hfin] at hp
      have hsp := hs.trans hp
      rw [← hsp] at hhigh
      simpa [GeneratedBootstrapMonitorConcentration.stoppedCounterPrefix,
        GeneratedBootstrapMonitorConcentration.monitorTail] using hhigh

/-- The named union event has the exact literal monitor-prefix failure set. -/
theorem monitorObstructionPullback_eq_monitorPrefixFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    monitorObstructionPullback p ids rewards C_star C_h eta =
      GeneratedBootstrapMonitorConcentration.monitorPrefixFailure
        p ids rewards C_star C_h eta := by
  simpa [monitorObstructionPullback] using
    (literalMonitorObstructionEvent_eq_monitorPrefixFailure
      p ids rewards C_star C_h eta)

/-- The exact combined startup obstruction event receives the literal
two-tail monitor estimate. -/
theorem monitorObstructionPullback_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorObstructionPullback p ids rewards C_star C_h eta) ≤
      2 * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
  rw [monitorObstructionPullback_eq_monitorPrefixFailure]
  simpa [GeneratedBootstrapMonitorConcentration.monitorTail] using
    (GeneratedBootstrapMonitorConcentration.literalMonitorPrefixFailure_measure_le
      p ids rewards C_star C_h eta).2

/-- The exact combined startup obstruction event retains the single
`N⁻²` estimate from the accepted literal failure event. -/
theorem monitorObstructionPullback_measure_le_inv_N_sq (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorObstructionPullback p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  rw [monitorObstructionPullback_eq_monitorPrefixFailure]
  exact GeneratedBootstrapMonitorConcentration.literalMonitorPrefixFailure_measure_le_inv_N_sq
    p ids rewards C_star C_h eta

private theorem measureReal_mono_of_subset (p : Parameters) {s t : Set (Coordinates p)}
    (hsub : s ⊆ t) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real s ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real t := by
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

/-- The comparator monitor-deficit pullback inherits the combined
two-tail estimate by measure monotonicity. -/
theorem comparatorMonitorDeficitPullback_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (comparatorMonitorDeficitPullback p ids rewards C_star C_h eta) ≤
      2 * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (comparatorMonitorDeficitPullback p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hmono := measureReal_mono_of_subset p (s :=
    comparatorMonitorDeficitPullback p ids rewards C_star C_h eta)
    (t := monitorObstructionPullback p ids rewards C_star C_h eta)
    (fun _ he => Or.inl he)
  exact ⟨hmono.trans (monitorObstructionPullback_measure_le p ids rewards C_star C_h eta),
    hmono.trans (monitorObstructionPullback_measure_le_inv_N_sq p ids rewards C_star C_h eta)⟩

/-- The upper-monitor obstruction pullback inherits the combined two-tail
estimate by measure monotonicity. -/
theorem monitorUpperObstructionPullback_measure_le (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorUpperObstructionPullback p ids rewards C_star C_h eta) ≤
      2 * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (monitorUpperObstructionPullback p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hmono := measureReal_mono_of_subset p (s :=
    monitorUpperObstructionPullback p ids rewards C_star C_h eta)
    (t := monitorObstructionPullback p ids rewards C_star C_h eta)
    (fun _ he => Or.inr he)
  exact ⟨hmono.trans (monitorObstructionPullback_measure_le p ids rewards C_star C_h eta),
    hmono.trans (monitorObstructionPullback_measure_le_inv_N_sq p ids rewards C_star C_h eta)⟩

end Bandits.Support.GeneratedMonitorObstructionTail

end
