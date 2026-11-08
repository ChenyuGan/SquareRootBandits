/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedComparatorChargeObstruction
public import Bandits.Support.InitializationRowObservables
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapStartupCostScale

/-!
# Deterministic comparator-charge obstruction assembly

The literal prelaunch comparator charge is bounded by the launch-monitor
threshold and its actual crossing-block overshoot whenever the existing
comparator-monitor deficit does not occur. Thus a supported comparator whose
charge exceeds that threshold witnesses the literal deficit. Sources:
`appendix_b_communication.tex:753-765` and `07_public_setup.tex:106-140`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Bandits.Support.GeneratedComparatorChargeAssembly

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceInitializationRun

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

private theorem stoppedSupportPrefix_le_of_not_comparatorMonitorDeficit
    (x : ReferenceInitializationRun.Input p)
    (hnot : ¬ GeneratedComparatorChargeObstruction.comparatorMonitorDeficit x)
    (a : Fin p.K) :
    GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix x
        (n_boot p) le_rfl a ≤
      128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.output x).counters a : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))) := by
  by_contra hbad
  have hstrict := not_le.mp hbad
  have hdeficit : GeneratedComparatorChargeObstruction.comparatorMonitorDeficit x := by
    refine ⟨a, n_boot p, le_rfl, ?_⟩
    simpa only [ReferenceInitializationRun.output] using hstrict
  exact hnot hdeficit

private theorem comparatorCharge_le_of_not_comparatorMonitorDeficit
    (x : ReferenceInitializationRun.Input p)
    (S : Finset (Fin p.K))
    (hS : S ∈ ProductSetLaw.support p.K p.m)
    (hnot : ¬ GeneratedComparatorChargeObstruction.comparatorMonitorDeficit x) :
    InitializationRowObservables.comparatorChargeAtBoundary p x.rewards S
        (ReferenceInitializationRun.output x) ≤
      128 * (4 *
          (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) *
          (4 * (b_N p : ℝ))) := by
  classical
  let ell : ℝ := 4 * (b_N p : ℝ)
  change InitializationRowObservables.comparatorChargeAtBoundary p x.rewards S
      (ReferenceInitializationRun.output x) ≤
    128 * (4 * (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
      (p.K : ℝ) * (B_boot p : ℝ) + (p.m : ℝ) * (p.K : ℝ) *
        (B_boot p : ℝ) * ell)
  have hcard : S.card = p.m := BootstrapLaunchMonitor.supportedSet_card p hS
  have hchargeExpand :
      InitializationRowObservables.comparatorChargeAtBoundary p x.rewards S
          (ReferenceInitializationRun.output x) =
        ∑ a ∈ S, ∑ t : Fin p.T,
          if t.val + 1 <
              InitializationRowObservables.launchRoundAtBoundary p
                (ReferenceInitializationRun.output x) then
            ((x.rewards t a).val : ℝ) / (D p : ℝ)
          else 0 := by
    rw [InitializationRowObservables.comparatorChargeAtBoundary_eq_sum]
    exact Finset.sum_comm
  have hsupport (a : Fin p.K) :
      GeneratedComparatorChargeObstruction.stoppedRewardSupportPrefix x
          (n_boot p) le_rfl a ≤
        128 * ((p.K : ℝ) *
            ((ReferenceInitializationRun.output x).counters a : ℝ) +
          (p.K : ℝ) * (B_boot p : ℝ) * ell) := by
    simpa only [ell] using
      stoppedSupportPrefix_le_of_not_comparatorMonitorDeficit x hnot a
  have hsumMass :
      (∑ a ∈ S, ∑ t : Fin p.T,
        if t.val + 1 <
            InitializationRowObservables.launchRoundAtBoundary p
              (ReferenceInitializationRun.output x) then
          ((x.rewards t a).val : ℝ) / (D p : ℝ)
        else 0) ≤
      ∑ a ∈ S, 128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.output x).counters a : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) * ell) := by
    apply Finset.sum_le_sum
    intro a ha
    exact (GeneratedComparatorChargeObstruction.normalized_prelaunch_reward_mass_le_stopped_support
      x a).trans (hsupport a)
  have hsumBound :
      (∑ a ∈ S, 128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.output x).counters a : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) * ell)) ≤
      128 * ((p.K : ℝ) *
          (∑ a ∈ S, ((ReferenceInitializationRun.output x).counters a : ℝ)) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard]
    ring_nf
    exact le_rfl
  let counters : Fin p.K → ℕ := (ReferenceInitializationRun.output x).counters
  have hsumMem : (∑ a ∈ S, counters a) ∈
      BootstrapLaunchMonitor.supportedSetSums p counters :=
    Finset.mem_image.mpr ⟨S, hS, rfl⟩
  have hsumMax : (∑ a ∈ S, counters a) ≤
      BootstrapLaunchMonitor.maximumSupportedCounterSum p counters := by
    simpa only [BootstrapLaunchMonitor.maximumSupportedCounterSum] using
      (Finset.le_max' (BootstrapLaunchMonitor.supportedSetSums p counters) _ hsumMem)
  have hmonitorNat : p.K * (∑ a ∈ S, counters a) ≤
      BootstrapLaunchMonitor.monitorValue p counters := by
    unfold BootstrapLaunchMonitor.monitorValue
    exact Nat.mul_le_mul_left p.K hsumMax
  have hmonitorBound :=
    hmonitorNat.trans (GeneratedBootstrapMonitor.output_monitor_le_threshold_add_block x)
  have hmonitorReal :
      (p.K : ℝ) *
          (∑ a ∈ S, ((ReferenceInitializationRun.output x).counters a : ℝ)) ≤
        4 * (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
          (p.K : ℝ) * (B_boot p : ℝ) := by
    have hcast :
        ((p.K * (∑ a ∈ S, counters a) : ℕ) : ℝ) ≤
          ((4 * BootstrapStartupCostScale.Q x.C_star x.C_h p +
              p.K * B_boot p : ℕ) : ℝ) := Nat.cast_le.mpr hmonitorBound
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_sum, Nat.cast_ofNat] using hcast
  have hmonitorAndPadding :
      (p.K : ℝ) *
          (∑ a ∈ S, ((ReferenceInitializationRun.output x).counters a : ℝ)) +
          (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell ≤
        (4 * (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
            (p.K : ℝ) * (B_boot p : ℝ)) +
          (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell :=
    add_le_add_left hmonitorReal _
  calc
    InitializationRowObservables.comparatorChargeAtBoundary p x.rewards S
        (ReferenceInitializationRun.output x) =
      ∑ a ∈ S, ∑ t : Fin p.T,
        if t.val + 1 <
            InitializationRowObservables.launchRoundAtBoundary p
              (ReferenceInitializationRun.output x) then
          ((x.rewards t a).val : ℝ) / (D p : ℝ)
        else 0 := hchargeExpand
    _ ≤ ∑ a ∈ S, 128 * ((p.K : ℝ) *
          ((ReferenceInitializationRun.output x).counters a : ℝ) +
        (p.K : ℝ) * (B_boot p : ℝ) * ell) := hsumMass
    _ ≤ 128 * ((p.K : ℝ) *
          (∑ a ∈ S, ((ReferenceInitializationRun.output x).counters a : ℝ)) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell) := hsumBound
    _ ≤ 128 * ((4 * (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
          (p.K : ℝ) * (B_boot p : ℝ)) +
        (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * ell) :=
      mul_le_mul_of_nonneg_left hmonitorAndPadding (by norm_num)

/-- A supported comparator whose literal strict-prelaunch charge exceeds the
launch threshold with clipped-block overshoot witnesses the existing literal
comparator-monitor deficit. The inclusion is deterministic and is stated for
the actual generated output. Sources:
`appendix_b_communication.tex:753-765` and `07_public_setup.tex:106-140`.
-/
theorem comparatorCharge_obstruction_subset
    (x : ReferenceInitializationRun.Input p) :
    (∃ S : Finset (Fin p.K),
      S ∈ ProductSetLaw.support p.K p.m ∧
        InitializationRowObservables.comparatorChargeAtBoundary p x.rewards S
            (ReferenceInitializationRun.output x) >
          128 * (4 * (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) +
            (p.K : ℝ) * (B_boot p : ℝ) +
            (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) *
              (4 * (b_N p : ℝ)))) →
      GeneratedComparatorChargeObstruction.comparatorMonitorDeficit x := by
  rintro ⟨S, hS, hlarge⟩
  by_contra hnot
  exact (not_le_of_gt hlarge)
    (comparatorCharge_le_of_not_comparatorMonitorDeficit x S hS hnot)

end Bandits.Support.GeneratedComparatorChargeAssembly

end
