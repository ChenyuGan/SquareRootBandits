/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedProductiveSuccessMean
public import Bandits.Support.GeneratedUninformedSupportObstruction
public import Bandits.Support.BootstrapIntervalBounds
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Productive opportunity count tail on the original reference coordinates

For the fixed whole ID array and rounded reward table, this module bounds the
literal productive-prefix obstruction on the unchanged original law. The
concentration process is the accepted shifted productive-exit process on the
existing held-arm reveal filtration. Its opportunity means are consumed at
every genuine block, and its prefix budget includes the completing or first
launch-crossing block.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-415,586-625`
and `sources/zip4/manuscript/07_public_setup.tex:63-115`.

This is internal probability on the auxiliary original-coordinate law. It
does not transfer to manuscript or local histories, condition on a selected
`J` or published output, or close a source-facing theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedHeldArmRevealFiltration
open Bandits.Support.GeneratedProductiveSuccessMean
open Bandits.Support.GeneratedUninformedSupportObstruction
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators

namespace Bandits.Support.GeneratedProductiveCountTail

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) :=
  GeneratedBootstrapBlockFiltrationRepair.Coordinates p

/-- The literal per-follower event that some productive prefix exceeds the
source threshold. The existential ranges over every canonical prefix,
including the empty and complete bootstrap prefixes. -/
def productivePrefixFailureEvent (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (i : Follower p.m) : Set (Coordinates p) :=
  {e | ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
    productivePrefixCount
      (referenceInput p ids rewards C_star C_h eta e) i r hr >
        32 * (p.K : ℝ) * (1 + 4 * (b_N p : ℝ))}

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

section FixedData

variable (p : Parameters) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate) (i : Follower p.m)

/-- Ambient measurability of the exact all-prefix productive failure event.
No good-ID or numerical-regime hypothesis is needed for measurability. -/
theorem measurableSet_productivePrefixFailureEvent :
    MeasurableSet (productivePrefixFailureEvent p ids rewards C_star C_h eta i) := by
  classical
  let x := referenceInput p ids rewards C_star C_h eta
  have hP (s : Fin (n_boot p)) :
      Measurable (fun e : Coordinates p =>
        GeneratedBootstrapGainBudget.productiveIndicator (x e) i s) := by
    exact (GeneratedHeldArmRevealFiltration.measurable_productiveIndicator
      p ids rewards C_star C_h eta i s).mono
        ((revealSigma_le_nextBoundary p ids rewards C_star C_h eta i s).trans
          (boundaryFiltration_le_ambient p (s.val + 1))) le_rfl
  have hcount (r : ℕ) (hr : r ≤ n_boot p) :
      Measurable (fun e : Coordinates p =>
        productivePrefixCount (x e) i r hr) := by
    unfold productivePrefixCount
    apply Finset.measurable_fun_sum
    intro s hs
    change Measurable (fun e : Coordinates p =>
      GeneratedBootstrapGainBudget.productiveIndicator (x e) i
        ⟨s.val, s.isLt.trans_le hr⟩)
    exact hP ⟨s.val, s.isLt.trans_le hr⟩
  have heq : productivePrefixFailureEvent p ids rewards C_star C_h eta i =
      ⋃ r : {r : ℕ // r ≤ n_boot p},
        {e | productivePrefixCount (x e) i r.1 r.2 >
          32 * (p.K : ℝ) * (1 + 4 * (b_N p : ℝ))} := by
    ext e
    simp only [productivePrefixFailureEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr, hlarge⟩
      exact ⟨⟨r, hr⟩, hlarge⟩
    · rintro ⟨⟨r, hr⟩, hlarge⟩
      exact ⟨r, hr, hlarge⟩
  rw [heq]
  exact MeasurableSet.iUnion fun r =>
    measurableSet_lt measurable_const (hcount r.1 r.2)

/-- The literal per-follower productive-prefix tail under the original law.
The only substantive regime inputs are the stated good-ID event and
`4096 ≤ C_h`; the conditional mean and shifted process are consumed from the
accepted productive-success module. -/
theorem productivePrefixFailureEvent_measure_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
      (productivePrefixFailureEvent p ids rewards C_star C_h eta i) ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  classical
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let F := heldArmRevealFiltration p ids rewards C_star C_h eta i
  let x := referenceInput p ids rewards C_star C_h eta
  let X : ℕ → Coordinates p → ℝ :=
    productiveExitProcess p ids rewards C_star C_h eta i
  let ell : ℝ := 4 * (b_N p : ℝ)
  let c : ℝ := 1 / (16 * (p.K : ℝ))
  have hKpos : 0 < (p.K : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos one_pos (mul_pos (by norm_num) hKpos)
  have hStrong : StronglyAdapted F X := by
    simpa only [F, X] using
      (GeneratedProductiveSuccessMean.stronglyAdapted_productiveExitProcess
        p ids rewards C_star C_h eta i)
  have hX : ∀ t, 1 ≤ t → t ≤ n_boot p →
      StronglyMeasurable[F t] (X t) := by
    intro t ht₁ htT
    exact hStrong t
  have hb : ∀ t, 1 ≤ t → t ≤ n_boot p →
      ∀ᵐ e ∂μ, 0 ≤ X t e ∧ X t e ≤ 1 := by
    intro t ht₁ htT
    filter_upwards with e
    exact GeneratedProductiveSuccessMean.productiveExitProcess_mem_Icc
      p ids rewards C_star C_h eta i t e
  have hαT : 1 ≤ n_boot p :=
    Nat.succ_le_of_lt (BootstrapDimensions.n_boot_pos p)
  have hmean : ∀ᵐ e ∂μ, ∀ s : Fin (n_boot p),
      c * GeneratedBootstrapGainBudget.productiveIndicator (x e) i s ≤
        BootstrapIntervalBounds.conditionalMean μ F X (s.val + 1) e := by
    rw [ae_all_iff]
    intro s
    have hs := GeneratedProductiveSuccessMean.productiveExitProcess_condExp_ge_at_opportunity
      p ids rewards C_star C_h eta i hgood hC_h s
    filter_upwards [hs] with e hse
    simpa [BootstrapIntervalBounds.conditionalMean, μ, F, X, x, c] using hse
  have hbadSubset :
      μ (productivePrefixFailureEvent p ids rewards C_star C_h eta i) ≤
        μ (BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p) ell)ᶜ := by
    apply measure_mono_ae
    filter_upwards [hmean] with e hmean_e
    intro hbad hgoodLower
    rcases hbad with ⟨r, hr, hthreshold⟩
    by_cases hr0 : r = 0
    · subst r
      have hzero : productivePrefixCount (x e) i 0 hr = 0 := by
        simp [productivePrefixCount]
      rw [hzero] at hthreshold
      have hell_nonneg : 0 ≤ ell := by
        dsimp [ell]
        positivity
      have hthreshold_pos :
          0 < 32 * (p.K : ℝ) * (1 + ell) := by
        positivity
      have hzero_bad : (0 : ℝ) > 32 * (p.K : ℝ) * (1 + ell) := by
        simpa [ell] using hthreshold
      exact (not_lt_of_ge hthreshold_pos.le) hzero_bad
    · have hrpos : 1 ≤ r := by omega
      change ∀ n ∈ Set.Icc 1 (n_boot p),
        BootstrapIntervalBounds.intervalSum
            (BootstrapIntervalBounds.conditionalMean μ F X) 1 (n_boot p) n e / 2 - ell ≤
          BootstrapIntervalBounds.intervalSum X 1 (n_boot p) n e at hgoodLower
      have hLG := hgoodLower r (Set.mem_Icc.mpr ⟨hrpos, hr⟩)
      have hcountMean :
          c * productivePrefixCount (x e) i r hr ≤
            BootstrapIntervalBounds.intervalSum
              (BootstrapIntervalBounds.conditionalMean μ F X) 1 (n_boot p) r e := by
        calc
          c * productivePrefixCount (x e) i r hr =
              ∑ s : Fin r, c * GeneratedBootstrapGainBudget.productiveIndicator
                (x e) i ⟨s.val, s.isLt.trans_le hr⟩ := by
                  simp only [productivePrefixCount, Finset.mul_sum]
          _ ≤ ∑ s : Fin r,
                BootstrapIntervalBounds.conditionalMean μ F X (s.val + 1) e := by
            apply Finset.sum_le_sum
            intro s hs
            simpa [x, c] using hmean_e ⟨s.val, s.isLt.trans_le hr⟩
          _ = BootstrapIntervalBounds.intervalSum
                (BootstrapIntervalBounds.conditionalMean μ F X) 1 (n_boot p) r e :=
              (intervalSum_eq_fin_succ_sum
                (Y := BootstrapIntervalBounds.conditionalMean μ F X)
                (T := n_boot p) hr e).symm
      have hsumExit :
          BootstrapIntervalBounds.intervalSum X 1 (n_boot p) r e =
            ∑ t ∈ Finset.range (r + 1), X t e := by
        rw [intervalSum_eq_fin_succ_sum (Y := X) (T := n_boot p) hr e,
          GeneratedProductiveSuccessMean.productiveExitProcess_prefix_sum
            p ids rewards C_star C_h eta i r hr e]
        apply Finset.sum_congr rfl
        intro s hs
        simpa only [X] using
          (GeneratedProductiveSuccessMean.productiveExitProcess_at_opportunity
            p ids rewards C_star C_h eta i
            ⟨s.val, s.isLt.trans_le hr⟩ e)
      have hprefix :
          BootstrapIntervalBounds.intervalSum X 1 (n_boot p) r e ≤ 1 := by
        rw [hsumExit]
        exact GeneratedProductiveSuccessMean.productiveExitProcess_prefix_sum_le_one
          p ids rewards C_star C_h eta i r hr e
      have hmeanBound :
          BootstrapIntervalBounds.intervalSum
              (BootstrapIntervalBounds.conditionalMean μ F X) 1 (n_boot p) r e ≤
            2 * (1 + ell) := by
        linarith only [hLG, hprefix]
      have hthreshold' : productivePrefixCount (x e) i r hr >
          32 * (p.K : ℝ) * (1 + ell) := by
        simpa [ell] using hthreshold
      have hscale : c * (32 * (p.K : ℝ) * (1 + ell)) = 2 * (1 + ell) := by
        dsimp [c]
        field_simp [ne_of_gt hKpos]
        ring
      have hstrict := mul_lt_mul_of_pos_left hthreshold' hcpos
      rw [hscale] at hstrict
      exact (not_lt_of_ge (hcountMean.trans hmeanBound)) hstrict
  have hbadReal :
      μ.real (productivePrefixFailureEvent p ids rewards C_star C_h eta i) ≤
        μ.real (BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p) ell)ᶜ :=
    ENNReal.toReal_mono (measure_ne_top _ _) hbadSubset
  have hconcentration := BootstrapIntervalBounds.lower_failure_localized
    (P := μ) (F := F) (X := X) (α := 1) (T := n_boot p)
    hX hb (by norm_num) hαT ell (A := Set.univ) MeasurableSet.univ
  have hfailure :
      μ.real (BootstrapIntervalBounds.lowerGood μ F X 1 (n_boot p) ell)ᶜ ≤
        Real.exp (-ell) := by
    simpa using hconcentration
  have hcombined := hbadReal.trans hfailure
  simpa [μ, ell] using hcombined

/-- The preimage of the existing literal global productive obstruction is
exactly the finite union of the per-follower events. -/
theorem productiveObstruction_preimage_eq_iUnion :
    {e : Coordinates p | productiveObstruction
        (referenceInput p ids rewards C_star C_h eta e)} =
      ⋃ i : Follower p.m,
        productivePrefixFailureEvent p ids rewards C_star C_h eta i := by
  ext e
  simp only [GeneratedUninformedSupportObstruction.productiveObstruction,
    productivePrefixFailureEvent, Set.mem_iUnion, Set.mem_ofPred_eq]

/-- The existing literal global obstruction is measurable on the original
coordinate carrier, independently of the probability regime. -/
theorem measurableSet_productiveObstruction_preimage :
    MeasurableSet {e : Coordinates p | productiveObstruction
      (referenceInput p ids rewards C_star C_h eta e)} := by
  rw [productiveObstruction_preimage_eq_iUnion p ids rewards C_star C_h eta]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_productivePrefixFailureEvent p ids rewards C_star C_h eta i

/-- The original-law probability of the exact finite-follower union defining
the literal productive obstruction. -/
theorem productiveObstruction_measure_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
      {e : Coordinates p | productiveObstruction
        (referenceInput p ids rewards C_star C_h eta e)} ≤
      ((p.m - 1 : ℕ) : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
  classical
  rw [productiveObstruction_preimage_eq_iUnion p ids rewards C_star C_h eta]
  calc
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (⋃ i : Follower p.m,
          productivePrefixFailureEvent p ids rewards C_star C_h eta i) ≤
        ∑ i : Follower p.m,
          (GeneratedBootstrapRoundLaw.originalLaw p).real
            (productivePrefixFailureEvent p ids rewards C_star C_h eta i) :=
      MeasureTheory.measureReal_iUnion_fintype_le
        (μ := GeneratedBootstrapRoundLaw.originalLaw p) _
    _ ≤ ∑ i : Follower p.m, Real.exp (-(4 * (b_N p : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact productivePrefixFailureEvent_measure_le
        p ids rewards C_star C_h eta i hgood hC_h
    _ = ((p.m - 1 : ℕ) : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
      have hcard : (Finset.univ : Finset (Follower p.m)).card = p.m - 1 := by
        change Fintype.card (Fin (p.m - 1)) = p.m - 1
        simp
      calc
        (∑ i : Follower p.m, Real.exp (-(4 * (b_N p : ℝ)))) =
            ((Finset.univ : Finset (Follower p.m)).card : ℝ) *
              Real.exp (-(4 * (b_N p : ℝ))) := by simp
        _ = _ := by rw [hcard]

end FixedData

end Bandits.Support.GeneratedProductiveCountTail

end
