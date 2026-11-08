/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedImportanceConditionalMean
public import Bandits.Support.GeneratedUninformedSupportObstruction
public import Bandits.Support.IdentificationGoodEvent

import Bandits.Support.BootstrapIntervalBounds
import Bandits.Support.GeneratedBootstrapGainBudget
import Bandits.Support.GeneratedImportanceGainAdaptedness
import Bandits.Support.GeneratedProductiveExitBudget
import Bandits.Support.ReferenceInitializationRun

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import Lean.Elab.Tactic.Omega

/-!
# Actual bootstrap importance support tail

For fixed good IDs, a whole denominator-`D` reward table, and the same fixed
run constants, this module proves the simultaneous support/importance tail on
the actual original-coordinate reference run. The concentration process is
the accepted normalized actual importance process, whose conditional lower
mean is proved in `GeneratedImportanceConditionalMean`; no conditional-mean
or history premise is supplied here.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:572-584,620-635`
and `sources/zip4/manuscript/07_public_setup.tex:63-115`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedImportanceConditionalMean
open Bandits.Support.GeneratedImportanceGainAdaptedness
open Bandits.Support.GeneratedProductiveExitBudget
open Bandits.Support.GeneratedUninformedSupportObstruction
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open scoped Classical BigOperators

namespace Bandits.Support.GeneratedBootstrapSupportTail

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates := GeneratedBootstrapBlockFiltrationRepair.Coordinates

variable (p : Parameters)

private theorem intervalSum_eq_fin_succ_sum
    {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    {r T : ℕ} (hr : r ≤ T) (e : Ω) :
    BootstrapIntervalBounds.intervalSum Y 1 T r e =
      ∑ s : Fin r, Y (s.val + 1) e := by
  rw [BootstrapIntervalBounds.intervalSum_eq_sum_Icc Y hr e]
  symm
  apply Finset.sum_bij (fun s _ => s.val + 1)
  · intro s hs
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · intro s₁ hs₁ s₂ hs₂ h
    apply Fin.ext
    exact Nat.add_right_cancel h
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht₁, htr⟩
    refine ⟨⟨t - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change (t - 1) + 1 = t
    omega
  · intro s hs
    rfl

private theorem blockSupportCount_eq_rewardSupportCount
    (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    GeneratedBlockChoiceAverages.blockSupportCount p s rewards a =
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
  unfold GeneratedBlockChoiceAverages.blockSupportCount
    GeneratedBlockChoiceAverages.roundedSupportChi
    BootstrapDownCountMean.rewardSupportCount BootstrapDownCountMean.rewardSupport
  apply Finset.sum_congr rfl
  intro t ht
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos (k : Fin (D p + 1)) :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) k ↔
        0 < k.val := by
    rw [RealRewardGridCount.realRewardGridValue]
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < k.val ↔ 0 < k.val by rfl)
  by_cases hk : 0 < (rewards t a).val
  · have hp := (hpos (rewards t a)).2 hk
    simp [hk, hp]
  · have hp : ¬ 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t a) := by
      intro h
      exact hk ((hpos (rewards t a)).1 h)
    simp [hk, hp]

private theorem supportCountPrefix_eq_blockSupport_sum
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (e : Coordinates p) (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a =
      ∑ s : Fin r, GeneratedBlockChoiceAverages.blockSupportCount p
        ⟨s.val, s.isLt.trans_le hr⟩ rewards a := by
  unfold supportCountPrefix
  apply Finset.sum_congr rfl
  intro s hs
  change BootstrapDownCountMean.rewardSupportCount p
      ⟨s.val, s.isLt.trans_le hr⟩ rewards a =
    GeneratedBlockChoiceAverages.blockSupportCount p
      ⟨s.val, s.isLt.trans_le hr⟩ rewards a
  exact (blockSupportCount_eq_rewardSupportCount p
    ⟨s.val, s.isLt.trans_le hr⟩ rewards a).symm

private theorem fixedPairImportanceObstruction_measurable
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) :
    MeasurableSet {e : Coordinates p | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
      (∀ q : ℕ, q < r →
        prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e) i q = 1) ∧
      supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
        1024 * (p.m : ℝ) *
          (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} := by
  classical
  let Pfx := fun e : Coordinates p => referenceInput p ids rewards C_star C_h eta e
  let pairPrefix (r : ℕ) (hr : r ≤ n_boot p) : Set (Coordinates p) :=
    {e | (∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1) ∧
      supportCountPrefix (Pfx e) r hr a >
        1024 * (p.m : ℝ) *
          (importancePrefix (Pfx e) i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))}
  have hsupport (r : ℕ) (hr : r ≤ n_boot p) :
      Measurable (fun e : Coordinates p => supportCountPrefix (Pfx e) r hr a) := by
    unfold supportCountPrefix
    apply Finset.measurable_fun_sum
    intro s hs
    change Measurable (fun _ : Coordinates p =>
      BootstrapDownCountMean.rewardSupportCount p
        ⟨s.val, s.isLt.trans_le hr⟩ rewards a)
    exact measurable_const
  have himportance (r : ℕ) (hr : r ≤ n_boot p) :
      Measurable (fun e : Coordinates p => importancePrefix (Pfx e) i r hr a) := by
    unfold importancePrefix
    apply Finset.measurable_fun_sum
    intro s hs
    change Measurable (actualImportanceObservable p ids rewards C_star C_h eta i
      ⟨s.val, s.isLt.trans_le hr⟩ a)
    exact actualImportance_measurable p ids rewards C_star C_h eta i
      ⟨s.val, s.isLt.trans_le hr⟩ a
  have hpairPrefix (r : ℕ) (hr : r ≤ n_boot p) : MeasurableSet (pairPrefix r hr) := by
    have hV : MeasurableSet {e : Coordinates p |
        ∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1} := by
      let eligible : Set (Coordinates p) := ⋂ q : ℕ,
        if hq : q < r then
          {e | prelaunchUninformedIndicator (Pfx e) i q = 1}
        else Set.univ
      have heq : {e : Coordinates p |
          ∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1} = eligible := by
        ext e
        simp [eligible]
      rw [heq]
      apply MeasurableSet.iInter
      intro q
      by_cases hq : q < r
      · have hqboot : q ≤ n_boot p := by omega
        have hVq := measurable_prelaunchUninformedIndicator p q hqboot
          ids rewards C_star C_h eta i
        have hVqAmbient : Measurable (fun e : Coordinates p =>
            prelaunchUninformedIndicator (Pfx e) i q) :=
          hVq.mono (boundaryFiltration_le_ambient p q) le_rfl
        simp only [dif_pos hq]
        exact (measurableSet_singleton (1 : ℝ)).preimage hVqAmbient
      · simp only [dif_neg hq]
        exact MeasurableSet.univ
    have hS := hsupport r hr
    have hI := himportance r hr
    have hRhs : Measurable (fun e : Coordinates p =>
        1024 * (p.m : ℝ) *
          (importancePrefix (Pfx e) i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))) := by
      exact measurable_const.mul (hI.add_const _)
    have hLarge : MeasurableSet {e : Coordinates p |
        1024 * (p.m : ℝ) *
            (importancePrefix (Pfx e) i r hr a +
              2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))) <
          supportCountPrefix (Pfx e) r hr a} := measurableSet_lt hRhs hS
    change MeasurableSet
      ({e : Coordinates p |
        ∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1} ∩
        {e : Coordinates p |
          1024 * (p.m : ℝ) *
              (importancePrefix (Pfx e) i r hr a +
                2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ))) <
            supportCountPrefix (Pfx e) r hr a})
    exact hV.inter hLarge
  have heq :
      {e : Coordinates p | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
        (∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1) ∧
        supportCountPrefix (Pfx e) r hr a >
          1024 * (p.m : ℝ) *
            (importancePrefix (Pfx e) i r hr a +
              2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} =
      ⋃ r : ℕ,
        {e : Coordinates p | ∃ hr : r ≤ n_boot p,
          (∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1) ∧
          supportCountPrefix (Pfx e) r hr a >
            1024 * (p.m : ℝ) *
              (importancePrefix (Pfx e) i r hr a +
                2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  rw [heq]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : r ≤ n_boot p
  · let hr' : r ≤ n_boot p := hr
    have hfixed :
        {e : Coordinates p | ∃ hr : r ≤ n_boot p,
          (∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1) ∧
          supportCountPrefix (Pfx e) r hr a >
            1024 * (p.m : ℝ) *
              (importancePrefix (Pfx e) i r hr a +
                2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} =
        pairPrefix r hr' := by
      ext e
      constructor
      · rintro ⟨hr0, h⟩
        have : hr0 = hr' := Subsingleton.elim _ _
        subst hr0
        exact h
      · intro h
        exact ⟨hr', h⟩
    rw [hfixed]
    exact hpairPrefix r hr'
  · have hempty :
        {e : Coordinates p | ∃ hr : r ≤ n_boot p,
          (∀ q : ℕ, q < r → prelaunchUninformedIndicator (Pfx e) i q = 1) ∧
          supportCountPrefix (Pfx e) r hr a >
            1024 * (p.m : ℝ) *
              (importancePrefix (Pfx e) i r hr a +
                2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      rcases he with ⟨hr', _⟩
      exact (hr hr').elim
    rw [hempty]
    exact MeasurableSet.empty

/-- The actual pullback of the accepted literal importance obstruction is
ambient measurable on the original coordinate law. -/
theorem measurableSet_importanceObstruction_preimage
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet {e : Coordinates p |
      importanceObstruction (referenceInput p ids rewards C_star C_h eta e)} := by
  classical
  let pairSlice (i : Follower p.m) (a : Fin p.K) : Set (Coordinates p) :=
    {e | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
      (∀ q : ℕ, q < r →
        prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e) i q = 1) ∧
      supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
        1024 * (p.m : ℝ) *
          (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))}
  have heq :
      {e : Coordinates p | importanceObstruction
        (referenceInput p ids rewards C_star C_h eta e)} =
      ⋃ i : Follower p.m, ⋃ a : Fin p.K, pairSlice i a := by
    ext e
    simp only [importanceObstruction, pairSlice, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro a
  exact fixedPairImportanceObstruction_measurable p ids rewards C_star C_h eta i a

/-- For one fixed actual follower and arm, the lower interval event controls
all eligible prefixes simultaneously, including the clipped last block. -/
theorem fixedPairImportanceObstruction_measure_le
    (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real {e : Coordinates p |
      ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
        (∀ q : ℕ, q < r →
          prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e) i q = 1) ∧
        supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
          1024 * (p.m : ℝ) *
            (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
              2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))} ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  classical
  let P := GeneratedBootstrapRoundLaw.originalLaw p
  let F := boundaryFiltration p
  let X : ℕ → Coordinates p → ℝ := fun n =>
    normalizedActualImportanceProcess p ids rewards C_star C_h eta i a n
  let ℓ : ℝ := 4 * (b_N p : ℝ)
  let U : ℝ := 2 * (p.K : ℝ) * (B_boot p : ℝ)
  have hU : 0 < U := by
    dsimp [U]
    exact mul_pos (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)))
      (Nat.cast_pos.mpr (BootstrapDimensions.B_boot_pos p))
  have hℓ : 0 < ℓ := by
    dsimp [ℓ]
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (ConstructorDimensions.b_N_pos p))
  have hα : 1 ≤ n_boot p := by
    exact Nat.succ_le_of_lt (BootstrapDimensions.n_boot_pos p)
  have hstrongActual : StronglyAdapted F
      (fun n e => actualImportanceProcess p ids rewards C_star C_h eta i a n e) :=
    (actualImportanceProcess_adapted p ids rewards C_star C_h eta i a).stronglyAdapted
  have hX : ∀ t, 1 ≤ t → t ≤ n_boot p → StronglyMeasurable[F t] (X t) := by
    intro t ht₁ htT
    change StronglyMeasurable[F t]
      (fun e => actualImportanceProcess p ids rewards C_star C_h eta i a t e / U)
    have hmul := (hstrongActual t).const_mul U⁻¹
    convert hmul using 1
    funext e
    exact div_eq_inv_mul _ U
  have hb : ∀ t, 1 ≤ t → t ≤ n_boot p →
      ∀ᵐ e ∂P, 0 ≤ X t e ∧ X t e ≤ 1 := by
    intro t ht₁ htT
    let s : Fin (n_boot p) := ⟨t - 1, by omega⟩
    have htime : s.val + 1 = t := by
      dsimp [s]
      omega
    filter_upwards with e
    change 0 ≤ normalizedActualImportanceProcess p ids rewards C_star C_h eta
        i a t e ∧ normalizedActualImportanceProcess p ids rewards C_star C_h eta
        i a t e ≤ 1
    rw [← htime, normalizedActualImportanceProcess_at_opportunity]
    exact scaledActualImportance_mem_Icc p ids rewards C_star C_h eta i s a e
  have hmean : ∀ᵐ e ∂P, ∀ s : Fin (n_boot p),
      GeneratedBootstrapImportanceMean.actualImportanceMeanLower
          p ids rewards C_star C_h eta i s a e / U ≤
        BootstrapIntervalBounds.conditionalMean P F X (s.val + 1) e := by
    rw [ae_all_iff]
    intro s
    have hs := normalizedActualImportanceProcess_condExp_ge_at_opportunity
      p ids hgood rewards C_star C_h eta i s a
    simpa [BootstrapIntervalBounds.conditionalMean, P, F, X, U,
      Nat.add_sub_cancel, boundaryFiltration] using hs
  have hbadSubset : P {e : Coordinates p |
      ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
        (∀ q : ℕ, q < r →
          prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e)
            i q = 1) ∧
        supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
          1024 * (p.m : ℝ) *
            (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
              U * ℓ)} ≤ P (BootstrapIntervalBounds.lowerGood P F X 1 (n_boot p) ℓ)ᶜ := by
    apply measure_mono_ae
    filter_upwards [hmean] with e hmean_e
    intro hbad hLG
    rcases hbad with ⟨r, hr, hV, hthreshold⟩
    by_cases hr0 : r = 0
    · subst r
      have hpositive : 0 < 1024 * (p.m : ℝ) *
          (0 + U * ℓ) := by
        rw [zero_add]
        exact mul_pos
          (mul_pos (by norm_num) (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)))
          (mul_pos hU hℓ)
      have hthreshold' : (0 : ℝ) > 1024 * (p.m : ℝ) * (0 + U * ℓ) := by
        simpa [supportCountPrefix, importancePrefix] using hthreshold
      exact (not_lt_of_ge (le_of_lt hpositive)) hthreshold'
    · have hrpos : 1 ≤ r := by omega
      let x := referenceInput p ids rewards C_star C_h eta e
      have hsumSupport :
          supportCountPrefix x r hr a =
            ∑ s : Fin r, GeneratedBlockChoiceAverages.blockSupportCount p
              ⟨s.val, s.isLt.trans_le hr⟩ rewards a :=
        supportCountPrefix_eq_blockSupport_sum p ids rewards C_star C_h eta e r hr a
      have hsumLower :
          (∑ s : Fin r,
            GeneratedBootstrapImportanceMean.actualImportanceMeanLower
                p ids rewards C_star C_h eta i
                ⟨s.val, s.isLt.trans_le hr⟩ a e / U) =
            supportCountPrefix x r hr a / (512 * (p.m : ℝ) * U) := by
        calc
          _ = ∑ s : Fin r,
                GeneratedBlockChoiceAverages.blockSupportCount p
                    ⟨s.val, s.isLt.trans_le hr⟩ rewards a /
                  (512 * (p.m : ℝ) * U) := by
            apply Finset.sum_congr rfl
            intro s hs
            have hVs :
                prelaunchUninformedIndicator x i s.val = 1 := hV s.val s.isLt
            have hguard :
                GeneratedBootstrapImportanceMean.actualUnlaunchedUninformedGuard
                    p ids rewards C_star C_h eta i
                    ⟨s.val, s.isLt.trans_le hr⟩ e = 1 := by
              simpa [GeneratedBootstrapImportanceMean.actualUnlaunchedUninformedGuard,
                GeneratedProductiveExitBudget.prelaunchUninformedIndicator] using hVs
            have hterm :
                GeneratedBootstrapImportanceMean.actualImportanceMeanLower
                    p ids rewards C_star C_h eta i
                    ⟨s.val, s.isLt.trans_le hr⟩ a e =
                  GeneratedBlockChoiceAverages.blockSupportCount p
                    ⟨s.val, s.isLt.trans_le hr⟩ rewards a /
                    (512 * (p.m : ℝ)) := by
              simp [GeneratedBootstrapImportanceMean.actualImportanceMeanLower, hguard]
            rw [hterm]
            ring
          _ = supportCountPrefix x r hr a / (512 * (p.m : ℝ) * U) := by
            rw [← Finset.sum_div, ← hsumSupport]
      have hsumImportance :
          (∑ s : Fin r, X (s.val + 1) e) = importancePrefix x i r hr a / U := by
        change (∑ s : Fin r,
          actualImportanceProcess p ids rewards C_star C_h eta i a (s.val + 1) e / U) = _
        rw [← Finset.sum_div]
        rw [actualImportanceProcess_sum_eq_actual_run_sum p ids rewards C_star C_h eta
          i a r hr e]
        rfl
      have hmeans_le :
          (∑ s : Fin r,
            GeneratedBootstrapImportanceMean.actualImportanceMeanLower
                p ids rewards C_star C_h eta i
              ⟨s.val, s.isLt.trans_le hr⟩ a e / U) ≤
          ∑ s : Fin r, BootstrapIntervalBounds.conditionalMean P F X
            (s.val + 1) e := by
        apply Finset.sum_le_sum
        intro s hs
        exact hmean_e ⟨s.val, s.isLt.trans_le hr⟩
      have hLG_r := hLG r ⟨hrpos, hr⟩
      rw [intervalSum_eq_fin_succ_sum (fun n e =>
        BootstrapIntervalBounds.conditionalMean P F X n e) hr e,
        intervalSum_eq_fin_succ_sum X hr e] at hLG_r
      have hprefixBound :
          supportCountPrefix x r hr a / (1024 * (p.m : ℝ) * U) - ℓ ≤
            importancePrefix x i r hr a / U := by
        calc
          _ =
              ((∑ s : Fin r,
            GeneratedBootstrapImportanceMean.actualImportanceMeanLower
                p ids rewards C_star C_h eta i
                  ⟨s.val, s.isLt.trans_le hr⟩ a e / U) / 2) - ℓ := by
              rw [hsumLower]
              ring
          _ ≤
              ((∑ s : Fin r, BootstrapIntervalBounds.conditionalMean P F X
                (s.val + 1) e) / 2) - ℓ := by
              exact sub_le_sub_right (div_le_div_of_nonneg_right hmeans_le (by norm_num)) _
          _ ≤ ∑ s : Fin r, X (s.val + 1) e := hLG_r
          _ = importancePrefix x i r hr a / U := hsumImportance
      have hm : (0 : ℝ) < (p.m : ℝ) :=
        Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
      have hden : 0 < 1024 * (p.m : ℝ) * U := by positivity
      have hscaled : supportCountPrefix x r hr a / (1024 * (p.m : ℝ) * U) ≤
          importancePrefix x i r hr a / U + ℓ := by
        linarith only [hprefixBound]
      have hright : importancePrefix x i r hr a / U + ℓ =
          (1024 * (p.m : ℝ) *
            (importancePrefix x i r hr a + U * ℓ)) /
              (1024 * (p.m : ℝ) * U) := by
        field_simp [ne_of_gt hden, ne_of_gt hU, ne_of_gt hm]
      have hcommon : supportCountPrefix x r hr a / (1024 * (p.m : ℝ) * U) ≤
          (1024 * (p.m : ℝ) *
            (importancePrefix x i r hr a + U * ℓ)) /
              (1024 * (p.m : ℝ) * U) := by
        rw [← hright]
        exact hscaled
      have hnotStrict : supportCountPrefix x r hr a ≤
          1024 * (p.m : ℝ) *
            (importancePrefix x i r hr a + U * ℓ) := by
        have hmul := (div_le_iff₀ hden).mp hcommon
        have hmulEq :
            (1024 * (p.m : ℝ) *
              (importancePrefix x i r hr a + U * ℓ)) /
                (1024 * (p.m : ℝ) * U) * (1024 * (p.m : ℝ) * U) =
              1024 * (p.m : ℝ) *
                (importancePrefix x i r hr a + U * ℓ) := by
          field_simp [ne_of_gt hden]
        rw [hmulEq] at hmul
        exact hmul
      exact (not_lt_of_ge hnotStrict) hthreshold
  have hconcentration := BootstrapIntervalBounds.lower_failure_localized
    (P := P) (F := F) (X := X) (α := 1) (T := n_boot p)
    hX hb (by norm_num) hα ℓ (A := Set.univ) MeasurableSet.univ
  have hbad : P.real {e : Coordinates p |
      ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
        (∀ q : ℕ, q < r →
          prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e)
            i q = 1) ∧
        supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
          1024 * (p.m : ℝ) *
            (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
              U * ℓ)} ≤ P.real (BootstrapIntervalBounds.lowerGood P F X 1 (n_boot p) ℓ)ᶜ := by
    have hm := hbadSubset
    have hm' : P {e : Coordinates p | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
        (∀ q : ℕ, q < r →
          prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e)
            i q = 1) ∧
        supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
          1024 * (p.m : ℝ) *
            (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
              U * ℓ)} ≤
        P (BootstrapIntervalBounds.lowerGood P F X 1 (n_boot p) ℓ)ᶜ := by
      simpa [U, ℓ] using hm
    exact ENNReal.toReal_mono (measure_ne_top _ _) hm'
  have hfailure := hconcentration
  have hfailure' : P.real (Set.univ ∩
      (BootstrapIntervalBounds.lowerGood P F X 1 (n_boot p) ℓ)ᶜ) ≤
        Real.exp (-ℓ) * P.real Set.univ := hfailure
  have hfailure'' : P.real (BootstrapIntervalBounds.lowerGood P F X 1 (n_boot p) ℓ)ᶜ ≤
      Real.exp (-ℓ) := by
    simpa using hfailure'
  have hcombined := hbad.trans hfailure''
  simpa [P, ℓ] using hcombined

/-- The actual original-coordinate pullback of the literal importance
obstruction has the source's fixed-follower/arm union bound. -/
theorem importanceObstruction_measure_le
    (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real {e : Coordinates p |
      importanceObstruction (referenceInput p ids rewards C_star C_h eta e)} ≤
      ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
  classical
  let pairSlice (i : Follower p.m) (a : Fin p.K) : Set (Coordinates p) :=
    {e | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
      (∀ q : ℕ, q < r →
        prelaunchUninformedIndicator (referenceInput p ids rewards C_star C_h eta e) i q = 1) ∧
      supportCountPrefix (referenceInput p ids rewards C_star C_h eta e) r hr a >
        1024 * (p.m : ℝ) *
          (importancePrefix (referenceInput p ids rewards C_star C_h eta e) i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))}
  have heq :
      {e : Coordinates p | importanceObstruction
        (referenceInput p ids rewards C_star C_h eta e)} =
      ⋃ i : Follower p.m, ⋃ a : Fin p.K, pairSlice i a := by
    ext e
    simp only [importanceObstruction, pairSlice, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [heq]
  calc
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (⋃ i : Follower p.m, ⋃ a : Fin p.K, pairSlice i a) ≤
        ∑ i : Follower p.m,
          (GeneratedBootstrapRoundLaw.originalLaw p).real (⋃ a : Fin p.K, pairSlice i a) :=
      MeasureTheory.measureReal_iUnion_fintype_le
        (μ := GeneratedBootstrapRoundLaw.originalLaw p)
        (fun i : Follower p.m => ⋃ a : Fin p.K, pairSlice i a)
    _ ≤ ∑ i : Follower p.m, ∑ a : Fin p.K,
          (GeneratedBootstrapRoundLaw.originalLaw p).real (pairSlice i a) := by
      apply Finset.sum_le_sum
      intro i hi
      exact MeasureTheory.measureReal_iUnion_fintype_le
        (μ := GeneratedBootstrapRoundLaw.originalLaw p)
        (fun a : Fin p.K => pairSlice i a)
    _ ≤ ∑ i : Follower p.m, ∑ a : Fin p.K,
          Real.exp (-(4 * (b_N p : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro a ha
      exact fixedPairImportanceObstruction_measure_le p ids hgood rewards
        C_star C_h eta i a
    _ = ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          Real.exp (-(4 * (b_N p : ℝ))) := by
      simp [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount,
        Finset.sum_const, nsmul_eq_mul]
      have hcard :
          (Finset.univ : Finset (Fin (PublicDiscreteDraws.followerCount p.m))).card =
            p.m - 1 := by
        rw [Finset.card_univ, Fintype.card_fin, PublicDiscreteDraws.followerCount]
      change ((Finset.univ : Finset (Fin (PublicDiscreteDraws.followerCount p.m))).card : ℝ) *
        ((p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ)))) = _
      rw [hcard]
      ring

end Bandits.Support.GeneratedBootstrapSupportTail

end
