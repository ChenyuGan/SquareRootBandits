/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedBootstrapPotential
public import Bandits.Support.ReferenceInitializationRun

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual productive-exit budget

The indicators here are read from the existing stopped reference
initialization recursion. The prelaunch-and-uninformed indicator tests both
the actual crossing and the actual activation state. Productive opportunities
reuse the accepted gain-budget indicator without introducing another test for
activity, held arms, rewards, support, or threshold.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:588-625` and
`sources/zip4/manuscript/07_public_setup.tex:129-140`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapGainBudget
open Bandits.Support.GeneratedBootstrapPotential
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators

namespace Bandits.Support.GeneratedProductiveExitBudget

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The literal real indicator that the actual boundary has neither a launch
crossing nor an activation for follower `i`. -/
def prelaunchUninformedIndicator (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (r : ℕ) : ℝ :=
  if (ReferenceInitializationRun.run x r).crossing = none ∧
      (ReferenceInitializationRun.run x r).activation i = none then 1 else 0

/-- The productive-exit increment `Pᵢ(s) * (1 - Vᵢ(s+1))`, using exactly
`GeneratedBootstrapGainBudget.productiveIndicator` for `Pᵢ(s)`. -/
def productiveExitIndicator (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) : ℝ :=
  GeneratedBootstrapGainBudget.productiveIndicator x i s *
    (1 - prelaunchUninformedIndicator x i (s.val + 1))

/-- The actual one-step decrease of the prelaunch-and-uninformed indicator. -/
def exitIncrement (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) : ℝ :=
  prelaunchUninformedIndicator x i s.val -
    prelaunchUninformedIndicator x i (s.val + 1)

theorem prelaunchUninformedIndicator_eq_zero_or_one
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m) (r : ℕ) :
    prelaunchUninformedIndicator x i r = 0 ∨
      prelaunchUninformedIndicator x i r = 1 := by
  by_cases h : (ReferenceInitializationRun.run x r).crossing = none ∧
      (ReferenceInitializationRun.run x r).activation i = none
  · right
    simp [prelaunchUninformedIndicator, h]
  · left
    simp [prelaunchUninformedIndicator, h]

theorem prelaunchUninformedIndicator_nonneg
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m) (r : ℕ) :
    0 ≤ prelaunchUninformedIndicator x i r := by
  rcases prelaunchUninformedIndicator_eq_zero_or_one x i r with h | h <;>
    simp [h]

theorem prelaunchUninformedIndicator_le_one
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m) (r : ℕ) :
    prelaunchUninformedIndicator x i r ≤ 1 := by
  rcases prelaunchUninformedIndicator_eq_zero_or_one x i r with h | h <;>
    simp [h]

/-- Initially there is no crossing and no follower activation. -/
theorem prelaunchUninformedIndicator_zero
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m) :
    prelaunchUninformedIndicator x i 0 = 1 := by
  simp [prelaunchUninformedIndicator, ReferenceInitializationRun.run_zero,
    ReferenceInitializationRun.initial]

/-- On the finite boundary domain, the actual prelaunch-and-uninformed
indicator is nonincreasing. Activation persistence handles natural and
forced activations; `run_stops_at_crossing` handles launch-forced removal. -/
theorem prelaunchUninformedIndicator_antitone
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    {r q : ℕ} (hrq : r ≤ q) (hq : q ≤ n_boot p) :
    prelaunchUninformedIndicator x i q ≤
      prelaunchUninformedIndicator x i r := by
  by_cases hqV : (ReferenceInitializationRun.run x q).crossing = none ∧
      (ReferenceInitializationRun.run x q).activation i = none
  · have hrCross : (ReferenceInitializationRun.run x r).crossing = none := by
      by_contra hrCross
      have hrSome : (ReferenceInitializationRun.run x r).crossing.isSome = true := by
        cases h : (ReferenceInitializationRun.run x r).crossing <;> simp_all
      have hrun := ReferenceInitializationRun.run_stops_at_crossing x r (q - r) hrSome
      have hrq' : r + (q - r) = q := Nat.add_sub_of_le hrq
      have hrun' : ReferenceInitializationRun.run x q =
          ReferenceInitializationRun.run x r := by
        calc
          ReferenceInitializationRun.run x q =
              ReferenceInitializationRun.run x (r + (q - r)) := by rw [hrq']
          _ = ReferenceInitializationRun.run x r := hrun
      have hcrossEq := congrArg ReferenceInitializationRun.Boundary.crossing hrun'
      rw [hqV.1] at hcrossEq
      exact hrCross hcrossEq.symm
    have hrActivation : (ReferenceInitializationRun.run x r).activation i = none := by
      by_contra hrActivation
      have hpersist := GeneratedBootstrapPotential.activation_persistent x i hrq hq hrActivation
      exact hpersist hqV.2
    simp [prelaunchUninformedIndicator, hqV, hrCross, hrActivation]
  · simp [prelaunchUninformedIndicator, hqV]
    exact prelaunchUninformedIndicator_nonneg x i r

/-- The accepted productive indicator is a zero-one real. -/
theorem productiveIndicator_eq_zero_or_one
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    GeneratedBootstrapGainBudget.productiveIndicator x i s = 0 ∨
      GeneratedBootstrapGainBudget.productiveIndicator x i s = 1 := by
  by_cases h : (GeneratedBootstrapGainBudget.blockAt x i s).enabled = true ∧
      (GeneratedBootstrapGainBudget.startupThreshold x : ℝ) ≤
        GeneratedBootstrapGainBudget.rewardSupportCountAt x s
          (GeneratedBootstrapGainBudget.blockAt x i s).held
  · right
    simp [GeneratedBootstrapGainBudget.productiveIndicator, h]
  · left
    simp [GeneratedBootstrapGainBudget.productiveIndicator, h]

/-- An enabled actual analysis block itself certifies that its incoming run
boundary has no crossing and no activation for this follower. -/
theorem actualBlock_enabled_imp_no_crossing_and_activation_none
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p))
    (henabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = true) :
    (ReferenceInitializationRun.run x s.val).crossing = none ∧
      (ReferenceInitializationRun.run x s.val).activation i = none := by
  let b := ReferenceInitializationRun.run x s.val
  have hcross : b.crossing = none := by
    by_contra hcross
    have hdisabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
      simp [GeneratedBootstrapPotential.actualBlock, b, hcross]
    rw [hdisabled] at henabled
    contradiction
  have hinformed : i ∈ ReferenceInitializationRun.uninformed b := by
    by_contra hinformed
    have hdisabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
      simp [GeneratedBootstrapPotential.actualBlock, b, hcross, hinformed]
    rw [hdisabled] at henabled
    contradiction
  exact ⟨hcross, (ReferenceInitializationRun.mem_uninformed b i).mp hinformed⟩

/-- A positive productive indicator implies the exact actual pre-block state
tested by `Vᵢ(s)`. No second productivity, support, or activity predicate is
introduced. -/
theorem productiveIndicator_le_prelaunchUninformed
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    GeneratedBootstrapGainBudget.productiveIndicator x i s ≤
      prelaunchUninformedIndicator x i s.val := by
  by_cases hproductive :
      (GeneratedBootstrapGainBudget.blockAt x i s).enabled = true ∧
        (GeneratedBootstrapGainBudget.startupThreshold x : ℝ) ≤
          GeneratedBootstrapGainBudget.rewardSupportCountAt x s
            (GeneratedBootstrapGainBudget.blockAt x i s).held
  · have hP : GeneratedBootstrapGainBudget.productiveIndicator x i s = 1 := by
      simp [GeneratedBootstrapGainBudget.productiveIndicator, hproductive]
    have henabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = true := by
      simpa [GeneratedBootstrapGainBudget.blockAt] using hproductive.1
    have hstate := actualBlock_enabled_imp_no_crossing_and_activation_none x i s henabled
    rw [hP]
    simp [prelaunchUninformedIndicator, hstate.1, hstate.2]
  · have hP : GeneratedBootstrapGainBudget.productiveIndicator x i s = 0 := by
      simp [GeneratedBootstrapGainBudget.productiveIndicator, hproductive]
    rw [hP]
    exact prelaunchUninformedIndicator_nonneg x i s.val

/-- The actual productive-exit increment lies in `[0,1]`. -/
theorem productiveExitIndicator_mem_Icc
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    productiveExitIndicator x i s ∈ Set.Icc 0 1 := by
  rcases productiveIndicator_eq_zero_or_one x i s with hP | hP
  · simp [productiveExitIndicator, hP]
  · rcases prelaunchUninformedIndicator_eq_zero_or_one x i (s.val + 1) with
      hV | hV <;> simp [productiveExitIndicator, hP, hV]

/-- The productive exit is bounded pointwise by the actual decrease of `V`. -/
theorem productiveExitIndicator_le_exitIncrement
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    productiveExitIndicator x i s ≤ exitIncrement x i s := by
  have hP_le := productiveIndicator_le_prelaunchUninformed x i s
  have hVmono := prelaunchUninformedIndicator_antitone x i
    (Nat.le_succ s.val) (Nat.succ_le_of_lt s.isLt)
  rcases prelaunchUninformedIndicator_eq_zero_or_one x i (s.val + 1) with
    hVzero | hVone
  · simpa [exitIncrement, productiveExitIndicator, hVzero] using hP_le
  · have hVprev : prelaunchUninformedIndicator x i s.val = 1 := by
      have hle := prelaunchUninformedIndicator_le_one x i s.val
      rw [hVone] at hVmono
      exact le_antisymm hle hVmono
    simp [exitIncrement, productiveExitIndicator, hVone, hVprev]

/-- Telescoping over the first `r` genuine block opportunities bounds the sum
of productive exits by `Vᵢ(0)-Vᵢ(r)`. The casted indices stay strictly below
`n_boot p`, so `r=n_boot p` adds no extra opportunity. -/
theorem productiveExit_sum_le_sub_boundary
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p) :
    (∑ s : Fin r, productiveExitIndicator x i
      ⟨s.val, s.isLt.trans_le hr⟩) ≤
        prelaunchUninformedIndicator x i 0 -
          prelaunchUninformedIndicator x i r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hrprev : r ≤ n_boot p := Nat.le_of_succ_le hr
      have hprefix := ih hrprev
      have hlast := productiveExitIndicator_le_exitIncrement x i
        ⟨r, Nat.lt_of_succ_le hr⟩
      change
        (∑ s : Fin r, productiveExitIndicator x i
          ⟨s.val, s.isLt.trans_le hrprev⟩) +
            productiveExitIndicator x i ⟨r, Nat.lt_of_succ_le hr⟩ ≤
          prelaunchUninformedIndicator x i 0 -
            prelaunchUninformedIndicator x i (r + 1)
      calc
        (∑ s : Fin r, productiveExitIndicator x i
          ⟨s.val, s.isLt.trans_le hrprev⟩) +
            productiveExitIndicator x i ⟨r, Nat.lt_of_succ_le hr⟩ ≤
          (prelaunchUninformedIndicator x i 0 -
              prelaunchUninformedIndicator x i r) +
            (prelaunchUninformedIndicator x i r -
              prelaunchUninformedIndicator x i (r + 1)) :=
          add_le_add hprefix hlast
        _ = prelaunchUninformedIndicator x i 0 -
              prelaunchUninformedIndicator x i (r + 1) := by ring

/-- Since `Vᵢ(0)=1` and `Vᵢ(r)≥0`, the total productive-exit budget is at most
one at every genuine boundary, including the shortened final block boundary. -/
theorem productiveExit_sum_le_one
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p) :
    (∑ s : Fin r, productiveExitIndicator x i
      ⟨s.val, s.isLt.trans_le hr⟩) ≤ 1 := by
  calc
    (∑ s : Fin r, productiveExitIndicator x i
      ⟨s.val, s.isLt.trans_le hr⟩) ≤
        prelaunchUninformedIndicator x i 0 -
          prelaunchUninformedIndicator x i r :=
      productiveExit_sum_le_sub_boundary x i r hr
    _ ≤ 1 := by
      rw [prelaunchUninformedIndicator_zero]
      linarith [prelaunchUninformedIndicator_nonneg x i r]

/-- If a productive exit occurs and the next boundary is not a launch
crossing, then removal is the actual saved declaration produced by
`finishBlock`. A crossing can instead force removal, so productive exit alone
does not certify that a natural declaration occurred. -/
theorem productiveExit_eq_one_of_no_crossing_declared
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p))
    (hExit : productiveExitIndicator x i s = 1)
    (hNoNextCrossing :
      (ReferenceInitializationRun.run x (s.val + 1)).crossing = none) :
    ∃ h : (ReferenceInitializationRun.run x s.val).completed < n_boot p,
      ReferenceInitializationRun.declaredActivation x
        (ReferenceInitializationRun.run x s.val) h i ≠ none := by
  have hP : GeneratedBootstrapGainBudget.productiveIndicator x i s = 1 := by
    rcases productiveIndicator_eq_zero_or_one x i s with hP | hP
    · simp [productiveExitIndicator, hP] at hExit
    · exact hP
  have hproductive :
      (GeneratedBootstrapGainBudget.blockAt x i s).enabled = true ∧
        (GeneratedBootstrapGainBudget.startupThreshold x : ℝ) ≤
          GeneratedBootstrapGainBudget.rewardSupportCountAt x s
            (GeneratedBootstrapGainBudget.blockAt x i s).held := by
    by_contra hproductive
    have hPzero : GeneratedBootstrapGainBudget.productiveIndicator x i s = 0 := by
      simp [GeneratedBootstrapGainBudget.productiveIndicator, hproductive]
    rw [hPzero] at hP
    norm_num at hP
  have henabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = true := by
    simpa [GeneratedBootstrapGainBudget.blockAt] using hproductive.1
  have hstate := actualBlock_enabled_imp_no_crossing_and_activation_none x i s henabled
  have hprocessed := GeneratedBootstrapPotential.run_processes_opportunity x s hstate.1
  have hcomplete := hprocessed.2.1
  have hfinish : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x s.val)
        hcomplete := hprocessed.2.2
  refine ⟨hcomplete, ?_⟩
  have hVnext : prelaunchUninformedIndicator x i (s.val + 1) = 0 := by
    have hEq : 1 * (1 - prelaunchUninformedIndicator x i (s.val + 1)) = 1 := by
      simpa [productiveExitIndicator, hP] using hExit
    nlinarith [hEq]
  have hActivationNext :
      (ReferenceInitializationRun.run x (s.val + 1)).activation i ≠ none := by
    by_contra hnone
    have hone : prelaunchUninformedIndicator x i (s.val + 1) = 1 := by
      simp [prelaunchUninformedIndicator, hNoNextCrossing, hnone]
    rw [hVnext] at hone
    norm_num at hone
  have hcrosses :
      ReferenceInitializationRun.crosses x (ReferenceInitializationRun.run x s.val)
        hcomplete = false := by
    have hc := hNoNextCrossing
    rw [hfinish] at hc
    rcases ReferenceInitializationRun.finishBlock_equations x
        (ReferenceInitializationRun.run x s.val) hcomplete with
      ⟨_, _, _, _, _, hCrossEq⟩
    rw [hCrossEq] at hc
    cases h : ReferenceInitializationRun.crosses x
        (ReferenceInitializationRun.run x s.val) hcomplete <;> simp_all
  have hfinal :
      ReferenceInitializationRun.finalActivation x
        (ReferenceInitializationRun.run x s.val) hcomplete i ≠ none := by
    have hfinishActivation :
        (ReferenceInitializationRun.finishBlock x
          (ReferenceInitializationRun.run x s.val) hcomplete).activation i ≠ none := by
      rw [← hfinish]
      exact hActivationNext
    change ReferenceInitializationRun.finalActivation x
      (ReferenceInitializationRun.run x s.val) hcomplete i ≠ none at hfinishActivation
    exact hfinishActivation
  have hdeclaredEq :
      ReferenceInitializationRun.finalActivation x
        (ReferenceInitializationRun.run x s.val) hcomplete i =
      ReferenceInitializationRun.declaredActivation x
        (ReferenceInitializationRun.run x s.val) hcomplete i := by
    simp [ReferenceInitializationRun.finalActivation, ReferenceInitializationRun.forced,
      hcrosses]
  rw [hdeclaredEq] at hfinal
  exact hfinal

/-- The actual indicator `Vᵢ(r)` is measurable at its source-prefix boundary
sigma algebra. -/
theorem measurable_prelaunchUninformedIndicator
    (p : Parameters) (r : ℕ) (_hr : r ≤ n_boot p)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) :
    @Measurable (Coordinates p) ℝ (boundarySigma p r) inferInstance
      (fun e => prelaunchUninformedIndicator
        (referenceInput p ids rewards C_star C_h eta e) i r) := by
  have hrun := GeneratedBootstrapBlockFiltrationRepair.measurable_run p r ids rewards
    C_star C_h eta
  have hcross := GeneratedBootstrapBlockFiltrationRepair.measurable_run_crossing p r ids
    rewards C_star C_h eta
  have hactivation :
      @Measurable (Coordinates p) (Option (ReferencePrelaunchFollower.Activation p))
        (boundarySigma p r) inferInstance
        (fun e => (ReferenceInitializationRun.run
          (referenceInput p ids rewards C_star C_h eta e) r).activation i) := by
    exact (measurable_of_countable
      (fun b : ReferenceInitializationRun.Boundary p => b.activation i)).comp hrun
  have hcrossSet : @MeasurableSet (Coordinates p) (boundarySigma p r)
      {e | (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).crossing = none} :=
    (measurableSet_singleton none).preimage hcross
  have hactivationSet : @MeasurableSet (Coordinates p) (boundarySigma p r)
      {e | (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).activation i = none} :=
    (measurableSet_singleton none).preimage hactivation
  change @Measurable (Coordinates p) ℝ (boundarySigma p r) inferInstance
    (fun e => if
      (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).crossing = none ∧
      (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).activation i = none
      then 1 else 0)
  exact Measurable.ite (hcrossSet.inter hactivationSet)
    measurable_const measurable_const

/-- The actual exit difference is measurable at the next boundary. The
incoming term is promoted along the accepted boundary filtration. -/
theorem measurable_exitIncrement_at_next_boundary
    (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) :
    @Measurable (Coordinates p) ℝ (boundarySigma p (s.val + 1)) inferInstance
      (fun e => exitIncrement
        (referenceInput p ids rewards C_star C_h eta e) i s) := by
  have hprev := measurable_prelaunchUninformedIndicator p s.val s.isLt.le
    ids rewards C_star C_h eta i
  have hnext := measurable_prelaunchUninformedIndicator p (s.val + 1)
    (Nat.succ_le_of_lt s.isLt) ids rewards C_star C_h eta i
  have hspace := (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p).mono'
    (Nat.le_succ s.val)
  have hprev' : @Measurable (Coordinates p) ℝ (boundarySigma p (s.val + 1))
      inferInstance (fun e => prelaunchUninformedIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s.val) :=
    hprev.mono hspace le_rfl
  change @Measurable (Coordinates p) ℝ (boundarySigma p (s.val + 1)) inferInstance
    (fun e =>
    prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e) i s.val -
      prelaunchUninformedIndicator
        (referenceInput p ids rewards C_star C_h eta e) i (s.val + 1))
  exact hprev'.sub hnext

end Bandits.Support.GeneratedProductiveExitBudget

end
