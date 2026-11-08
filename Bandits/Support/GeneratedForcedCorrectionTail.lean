/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapSupportTail
public import Bandits.Support.GeneratedProductiveCountTail
public import Bandits.Support.GeneratedMonitorObstructionTail

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual forced-correction probability on the original reference run

The literal event is the existence of a follower forced at the first strict
monitor crossing, after the pending declarations from that block have taken
effect. Its proof uses the accepted importance, productive-count, original
activity, and upper-monitor obstructions on the same complete-row/private
coordinates and fixed reference input.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:572-635,
642-682,748-765` and `sources/zip4/manuscript/07_public_setup.tex:129-164`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedLatentActivityTail
open Bandits.Support.GeneratedProductiveCountTail
open Bandits.Support.GeneratedUninformedSupportObstruction
open Bandits.Support.GeneratedForcedCorrectionObstruction
open Bandits.Support.GeneratedMonitorObstructionTail
open Bandits.Support.InitializationFailureProvenance
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveRoundActions
open scoped Classical BigOperators

namespace Bandits.Support.GeneratedForcedCorrectionTail

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) :=
  GeneratedBootstrapBlockFiltrationRepair.Coordinates p

variable (p : Parameters)
variable (ids : CompletePublicTable.IDArray p)
variable (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
variable (C_star C_h : ℝ)
variable (eta : ReferencePrelaunchFollower.LearningRate)

/-- The exact event `E_force`: some follower is corrected on some actual
processed bootstrap block by the fixed reference input. -/
def forcedCorrectionEvent : Set (Coordinates p) :=
  {e | ∃ s : Fin (n_boot p), ∃ i : Follower p.m,
    InitializationFailureProvenance.forcedCorrectionAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s i}

/-- The fixed reference input retains the original extended private arrays. -/
theorem referenceInput_coordinates (e : Coordinates p) :
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e).coordinates = e.2 := rfl

private theorem forcedCorrectionAt_implies_output_forcedFailure
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (i : Follower p.m)
    (hcause : InitializationFailureProvenance.forcedCorrectionAt x s i) :
    (ReferenceInitializationRun.output x).forcedFailure i = true := by
  rcases hcause with ⟨h, hcross, _, _, _, _, hforce, hfinish⟩
  let b := ReferenceInitializationRun.run x s.val
  have hnone : b.crossing = none := by simpa [b] using hcross
  have hforced := (ReferenceInitializationRun.forced_iff x b h i).mp hforce
  have hnext : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b h := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x b hnone h]
  have hstop : (ReferenceInitializationRun.run x (s.val + 1)).crossing.isSome = true := by
    rw [hnext]
    change (if ReferenceInitializationRun.crosses x b h then
      some (ReferenceInitializationRun.nextBlock b h) else none).isSome = true
    simp [hforced.1]
  have hout := ReferenceInitializationRun.output_eq_of_crossing x (s.val + 1)
    (Nat.succ_le_of_lt s.isLt) hstop
  rw [hout, hnext]
  exact hfinish

/-- The actual run's accumulated forced-failure bit is exactly the existence
of a prior literal forced-correction witness. -/
private theorem run_forcedFailure_iff_forcedCorrection_before
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m) :
    ∀ n, n ≤ n_boot p →
      ((ReferenceInitializationRun.run x n).forcedFailure i = true ↔
        ∃ s : ℕ, s < n ∧ ∃ hs : s < n_boot p,
          InitializationFailureProvenance.forcedCorrectionAt x ⟨s, hs⟩ i) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [ReferenceInitializationRun.run_zero, ReferenceInitializationRun.initial]
  | succ n ih =>
      intro hn
      have hlt : n < n_boot p := by omega
      have ihn := ih (by omega : n ≤ n_boot p)
      rw [ReferenceInitializationRun.run_succ]
      by_cases hcross : (ReferenceInitializationRun.run x n).crossing.isSome = true
      · rw [ReferenceInitializationRun.advance_of_crossing x _ hcross]
        constructor
        · intro hflag
          rcases ihn.mp hflag with ⟨s, hs, hsboot, hforce⟩
          exact ⟨s, by omega, hsboot, hforce⟩
        · rintro ⟨s, hs, hsboot, hforce⟩
          have hslt : s < n := by
            by_contra hnot
            have heq : s = n := by omega
            subst s
            rcases hforce with ⟨hblock, hnone, _, _, _, _, _, _⟩
            simp [hnone] at hcross
          exact ihn.mpr ⟨s, hslt, hsboot, hforce⟩
      · have hnone : (ReferenceInitializationRun.run x n).crossing = none := by
          cases he : (ReferenceInitializationRun.run x n).crossing with
          | none => rfl
          | some r => simp [he] at hcross
        have hcompleted : (ReferenceInitializationRun.run x n).completed = n := by
          rcases ReferenceInitializationRun.run_progress x n (by omega) with hstop | hdone
          · simp [hnone] at hstop
          · exact hdone
        have hblock : (ReferenceInitializationRun.run x n).completed < n_boot p := by
          rw [hcompleted]
          exact hlt
        rw [ReferenceInitializationRun.advance_of_no_crossing x _ hnone hblock]
        change ((ReferenceInitializationRun.run x n).forcedFailure i ||
          ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x n)
            hblock i) = true ↔ _
        constructor
        · intro hflag
          by_cases hprev :
              (ReferenceInitializationRun.run x n).forcedFailure i = true
          · rcases ihn.mp hprev with ⟨s, hs, hsboot, hforce⟩
            exact ⟨s, by omega, hsboot, hforce⟩
          · have hprevFalse :
                (ReferenceInitializationRun.run x n).forcedFailure i = false :=
              Bool.eq_false_iff.mpr hprev
            have hnew :
                ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x n)
                  hblock i = true := by
              simpa [hprevFalse] using hflag
            have hcurrent :=
              (InitializationFailureProvenance.forcedCorrectionAt_current_iff
                x n hlt hnone hcompleted i hprevFalse).2 hnew
            exact ⟨n, by omega, hlt, hcurrent⟩
        · rintro ⟨s, hs, hsboot, hforce⟩
          by_cases hslt : s < n
          · have hprev := ihn.mpr ⟨s, hslt, hsboot, hforce⟩
            simp [hprev]
          · have heq : s = n := by omega
            subst s
            have hforce' := hforce
            rcases hforce with ⟨_, _, _, hprevFalse, _, _, _, _⟩
            have hnew := (InitializationFailureProvenance.forcedCorrectionAt_current_iff
              x n hlt hnone hcompleted i hprevFalse).1 hforce'
            simp [hprevFalse, hnew]

/-- The literal forced-correction event is the finite union of terminal
forced-failure flags from that same actual reference run. -/
theorem forcedCorrectionEvent_eq_iUnion_output_forcedFailure :
    forcedCorrectionEvent p ids rewards C_star C_h eta =
      ⋃ i : Follower p.m,
        {e : Coordinates p |
          (ReferenceInitializationRun.output
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e)).forcedFailure i = true} := by
  ext e
  simp only [forcedCorrectionEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨s, i, hforce⟩
    exact ⟨i, forcedCorrectionAt_implies_output_forcedFailure p
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s i hforce⟩
  · rintro ⟨i, hflag⟩
    have hrun := (run_forcedFailure_iff_forcedCorrection_before p
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) i (n_boot p) le_rfl).mp (by
          simpa [ReferenceInitializationRun.output] using hflag)
    rcases hrun with ⟨s, hs, hboot, hforce⟩
    exact ⟨⟨s, hboot⟩, i, hforce⟩

/-- Ambient measurability of the exact literal forced-correction event. The
proof uses the accepted measurable actual run and its accumulated output bit. -/
theorem measurableSet_forcedCorrectionEvent :
    MeasurableSet (forcedCorrectionEvent p ids rewards C_star C_h eta) := by
  rw [forcedCorrectionEvent_eq_iUnion_output_forcedFailure]
  apply MeasurableSet.iUnion
  intro i
  let z : Coordinates p → ReferenceInitializationMeasurability.InputCoordinates p :=
    fun e => (ids, e)
  have hz : Measurable z := measurable_const.prodMk measurable_id
  have hrun := (ReferenceInitializationMeasurability.measurable_run_forcedFailure
    p C_star C_h eta rewards (n_boot p)).comp hz
  have hflag := (measurable_pi_apply i).comp hrun
  change MeasurableSet {e : Coordinates p |
    (ReferenceInitializationRun.output
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)).forcedFailure i = true}
  have hflag' : Measurable (fun e : Coordinates p =>
      (ReferenceInitializationRun.output
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e)).forcedFailure i) := by
    simpa [z, ReferenceInitializationMeasurability.inputOfCoordinates,
      ReferenceInitializationRun.output,
      GeneratedBootstrapBlockFiltrationRepair.referenceInput,
      GeneratedBootstrapRoundLaw.input, Function.comp_def] using hflag
  exact (measurableSet_singleton true).preimage hflag'

/-- Original and extended activity-tail events are the same pullback of the
accepted raw follower-block event. The original private arrays are retained. -/
theorem originalActivityTailEvent_eq_extended_private_preimage
    (i : Follower p.m) :
    GeneratedLatentActivityTail.originalActivityTailEvent p i =
      (fun e : Coordinates p => e.2) ⁻¹'
        GeneratedLatentActivityTail.extendedActivityTailEvent p i := by
  rw [GeneratedLatentActivityTail.originalActivityTailEvent_eq_raw_preimage,
    GeneratedLatentActivityTail.extendedActivityTailEvent_eq_raw_preimage]
  rfl

/-- The latent-activity obstruction on the reference input pulls back to the
finite union of the literal original-coordinate activity-tail events. -/
theorem latentActivityObstruction_preimage_eq_iUnion :
    {e : Coordinates p | _root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e)} =
      ⋃ i : Follower p.m,
        GeneratedLatentActivityTail.originalActivityTailEvent p i := by
  ext e
  simp only [_root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction,
    Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [referenceInput_coordinates p ids rewards C_star C_h eta e] at hi
    have hevent := originalActivityTailEvent_eq_extended_private_preimage p i
    have hi' : e ∈ GeneratedLatentActivityTail.originalActivityTailEvent p i := by
      rw [hevent]
      exact hi
    exact ⟨i, hi'⟩
  · rintro ⟨i, hi⟩
    have hevent := originalActivityTailEvent_eq_extended_private_preimage p i
    rw [hevent] at hi
    have hi' : (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e).coordinates ∈
          GeneratedLatentActivityTail.extendedActivityTailEvent p i := by
      rw [referenceInput_coordinates p ids rewards C_star C_h eta e]
      exact hi
    exact ⟨i, hi'⟩

/-- Ambient measurability of the exact latent-activity obstruction pullback. -/
theorem measurableSet_latentActivityObstruction_preimage :
    MeasurableSet {e : Coordinates p |
      _root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e)} := by
  rw [latentActivityObstruction_preimage_eq_iUnion p ids rewards C_star C_h eta]
  exact MeasurableSet.iUnion fun i =>
    GeneratedLatentActivityTail.measurable_originalActivityTailEvent p i

/-- The original-law tail of the exact latent-activity obstruction, with the
full follower cardinality `m - 1`. -/
theorem latentActivityObstruction_preimage_measure_le :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
      {e : Coordinates p |
        _root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)} ≤
      ((p.m - 1 : ℕ) : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
  rw [latentActivityObstruction_preimage_eq_iUnion p ids rewards C_star C_h eta]
  calc
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (⋃ i : Follower p.m,
          GeneratedLatentActivityTail.originalActivityTailEvent p i) ≤
        ∑ i : Follower p.m,
          (GeneratedBootstrapRoundLaw.originalLaw p).real
            (GeneratedLatentActivityTail.originalActivityTailEvent p i) :=
      MeasureTheory.measureReal_iUnion_fintype_le
        (μ := GeneratedBootstrapRoundLaw.originalLaw p) _
    _ ≤ ∑ i : Follower p.m, Real.exp (-(4 * (b_N p : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact GeneratedLatentActivityTail.original_activity_prefix_tail p i
    _ = ((p.m - 1 : ℕ) : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) := by
      have hcard : (Finset.univ : Finset (Follower p.m)).card = p.m - 1 := by
        change Fintype.card (Fin (p.m - 1)) = p.m - 1
        simp
      simp [Finset.sum_const, hcard, nsmul_eq_mul]

/-- The exact forced-correction event is contained in the four accepted
literal obstruction events on the same fixed reference input. -/
theorem forcedCorrectionEvent_subset_obstructions
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    forcedCorrectionEvent p ids rewards C_star C_h eta ⊆
      {e : Coordinates p |
        _root_.Bandits.Support.GeneratedUninformedSupportObstruction.importanceObstruction
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)} ∪
      {e : Coordinates p |
        _root_.Bandits.Support.GeneratedUninformedSupportObstruction.productiveObstruction
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)} ∪
      {e : Coordinates p |
        _root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)} ∪
      GeneratedMonitorObstructionTail.monitorUpperObstructionPullback
        p ids rewards C_star C_h eta := by
  intro e he
  rcases he with ⟨s, i, hforce⟩
  have hCstar' : (2 : ℝ) ^ 20 ≤
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e).C_star := by
    simpa [GeneratedBootstrapBlockFiltrationRepair.referenceInput,
      GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using hCstar
  have hsubset := _root_.Bandits.Support.GeneratedForcedCorrectionObstruction.forcedCorrection_obstruction_subset
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e) hCstar' ⟨s, i, hforce⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq,
    _root_.Bandits.Support.GeneratedMonitorObstructionTail.monitorUpperObstructionPullback]
  rcases hsubset with hI | hP | hA | hplus
  · exact Or.inl (Or.inl (Or.inl hI))
  · exact Or.inl (Or.inl (Or.inr hP))
  · exact Or.inl (Or.inr hA)
  · exact Or.inr hplus

private theorem forcedCorrection_exp_tail_weight_le_inv_N_sq :
    4 * (p.m : ℝ) * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hNplus : 0 < (N p : ℝ) + 1 := by linarith
  have hTone : 1 ≤ p.T := p.one_le_T
  have hTtwo : 2 ≤ p.T + 1 := by omega
  have hweightNat : 4 * p.m * p.K ≤ N p := by
    calc
      4 * p.m * p.K = (2 * p.K * p.m) * 2 := by ring
      _ ≤ (2 * p.K * p.m) * (p.T + 1) := Nat.mul_le_mul_left _ hTtwo
      _ = N p := by rw [ConstructorDimensions.N]
  have hweight : 4 * (p.m : ℝ) * (p.K : ℝ) ≤ (N p : ℝ) := by
    exact_mod_cast hweightNat
  have hD : N p + 1 ≤ 2 ^ b_N p :=
    Nat.le_pow_clog (by norm_num) (N p + 1)
  have hpow : (N p : ℝ) + 1 ≤ (2 : ℝ) ^ b_N p := by
    exact_mod_cast hD
  have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := Real.add_one_le_exp 1
  have hexpPow : (2 : ℝ) ^ (4 * b_N p) ≤ Real.exp (4 * (b_N p : ℝ)) := by
    have hpow' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp2
      (4 * b_N p)
    have hexpeq : Real.exp (4 * (b_N p : ℝ)) =
        (Real.exp 1) ^ (4 * b_N p) := by
      rw [show 4 * (b_N p : ℝ) = ((4 * b_N p : ℕ) : ℝ) by norm_num]
      rw [← Real.exp_nat_mul (1 : ℝ) (4 * b_N p)]
      congr 1
      norm_num
    exact hpow'.trans_eq hexpeq.symm
  have hpow4 : ((N p : ℝ) + 1) ^ 4 ≤ (2 : ℝ) ^ (4 * b_N p) := by
    calc
      ((N p : ℝ) + 1) ^ 4 ≤ ((2 : ℝ) ^ b_N p) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hpow _
      _ = (2 : ℝ) ^ (4 * b_N p) := by
        rw [← pow_mul]
        congr 1
        omega
  have hexpInv : Real.exp (-(4 * (b_N p : ℝ))) ≤
      1 / ((N p : ℝ) + 1) ^ 4 := by
    rw [Real.exp_neg]
    have hypos : 0 < ((N p : ℝ) + 1) ^ 4 := pow_pos hNplus 4
    have hinv := (inv_le_inv₀ (Real.exp_pos _) hypos).2 (hpow4.trans hexpPow)
    simpa only [one_div] using hinv
  have hexpInv' : (Real.exp (4 * (b_N p : ℝ)))⁻¹ ≤
      1 / ((N p : ℝ) + 1) ^ 4 := by
    simpa only [Real.exp_neg] using hexpInv
  have hNcube : (N p : ℝ) ^ 3 ≤ ((N p : ℝ) + 1) ^ 4 := by
    have hbase : (N p : ℝ) ≤ (N p : ℝ) + 1 := by linarith
    have hpow3 := pow_le_pow_left₀ (by positivity : 0 ≤ (N p : ℝ)) hbase 3
    have hbaseOne : (1 : ℝ) ≤ (N p : ℝ) + 1 := by linarith
    have hpow34 : ((N p : ℝ) + 1) ^ 3 ≤ ((N p : ℝ) + 1) ^ 4 := by
      calc
        ((N p : ℝ) + 1) ^ 3 = ((N p : ℝ) + 1) ^ 3 * 1 := by ring
        _ ≤ ((N p : ℝ) + 1) ^ 3 * ((N p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hbaseOne (by positivity)
        _ = ((N p : ℝ) + 1) ^ 4 := by rw [pow_succ]; ring
    exact hpow3.trans hpow34
  have hratio : (N p : ℝ) / ((N p : ℝ) + 1) ^ 4 ≤ 1 / (N p : ℝ) ^ 2 := by
    rw [div_le_iff₀ (pow_pos hNplus 4)]
    field_simp
    nlinarith [hNcube]
  calc
    4 * (p.m : ℝ) * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ≤
        (N p : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) :=
      mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)
    _ ≤ (N p : ℝ) / ((N p : ℝ) + 1) ^ 4 := by
      rw [Real.exp_neg]
      simpa [one_div, div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left hexpInv' (le_of_lt hNpos))
    _ ≤ 1 / (N p : ℝ) ^ 2 := hratio

/-- The actual forced-correction probability on the entire original
complete-row/private product, with only the source probability-regime inputs.
The displayed chain is the exact four-obstruction union coefficient, its
`4 m K` simplification, and the resulting `N⁻²` bound. -/
theorem forcedCorrectionEvent_measure_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
      (((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        2 * ((p.m - 1 : ℕ) : ℝ) + 2 * (p.K : ℝ)) *
          Real.exp (-(4 * (b_N p : ℝ))) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
      4 * (p.m : ℝ) * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  let E_I : Set (Coordinates p) := {e |
    _root_.Bandits.Support.GeneratedUninformedSupportObstruction.importanceObstruction
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)}
  let E_P : Set (Coordinates p) := {e |
    _root_.Bandits.Support.GeneratedUninformedSupportObstruction.productiveObstruction
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)}
  let E_A : Set (Coordinates p) := {e |
    _root_.Bandits.Support.GeneratedUninformedSupportObstruction.latentActivityObstruction
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e)}
  let E_plus : Set (Coordinates p) :=
    GeneratedMonitorObstructionTail.monitorUpperObstructionPullback
      p ids rewards C_star C_h eta
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let τ : ℝ := Real.exp (-(4 * (b_N p : ℝ)))
  have hsub : forcedCorrectionEvent p ids rewards C_star C_h eta ⊆
      E_I ∪ E_P ∪ E_A ∪ E_plus := by
    exact forcedCorrectionEvent_subset_obstructions p ids rewards C_star C_h eta hCstar
  have hunion : μ.real (E_I ∪ E_P ∪ E_A ∪ E_plus) ≤
      μ.real E_I + μ.real E_P + μ.real E_A + μ.real E_plus := by
    have hplus := MeasureTheory.measureReal_union_le (μ := μ)
      ((E_I ∪ E_P) ∪ E_A) E_plus
    have hA := MeasureTheory.measureReal_union_le (μ := μ) (E_I ∪ E_P) E_A
    have hbase := MeasureTheory.measureReal_union_le (μ := μ) E_I E_P
    linarith
  have hI : μ.real E_I ≤ ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * τ := by
    simpa [E_I, μ, τ] using
      (_root_.Bandits.Support.GeneratedBootstrapSupportTail.importanceObstruction_measure_le
        p ids hgood rewards C_star C_h eta)
  have hP : μ.real E_P ≤ ((p.m - 1 : ℕ) : ℝ) * τ := by
    simpa [E_P, μ, τ] using
      (_root_.Bandits.Support.GeneratedProductiveCountTail.productiveObstruction_measure_le
        p ids rewards C_star C_h eta hgood hC_h)
  have hA : μ.real E_A ≤ ((p.m - 1 : ℕ) : ℝ) * τ := by
    simpa [E_A, μ, τ] using
      (latentActivityObstruction_preimage_measure_le p ids rewards C_star C_h eta)
  have hPlus : μ.real E_plus ≤ 2 * (p.K : ℝ) * τ := by
    exact (GeneratedMonitorObstructionTail.monitorUpperObstructionPullback_measure_le
      p ids rewards C_star C_h eta).1
  have hfirst : μ.real (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
      (((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        2 * ((p.m - 1 : ℕ) : ℝ) + 2 * (p.K : ℝ)) * τ := by
    calc
      μ.real (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
          μ.real (E_I ∪ E_P ∪ E_A ∪ E_plus) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ μ.real E_I + μ.real E_P + μ.real E_A + μ.real E_plus := hunion
      _ ≤ (((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * τ) +
            (((p.m - 1 : ℕ) : ℝ) * τ) +
            (((p.m - 1 : ℕ) : ℝ) * τ) + (2 * (p.K : ℝ) * τ) :=
        add_le_add (add_le_add (add_le_add hI hP) hA) hPlus
      _ = (((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
            2 * ((p.m - 1 : ℕ) : ℝ) + 2 * (p.K : ℝ)) * τ := by ring
  have hm1 : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
    have hmLower : 2 ≤ p.m := p.two_le_m
    rw [Nat.cast_sub (by omega : 1 ≤ p.m), Nat.cast_one]
  have hm : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
  have hKnat : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
  have hK : (2 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
  have hmpos : 0 ≤ (p.m : ℝ) := by positivity
  have hKpos : 0 ≤ (p.K : ℝ) := by positivity
  have hKsub : 0 ≤ (p.K : ℝ) - 1 := by linarith
  have hmsub : 0 ≤ (p.m : ℝ) - 1 := by linarith
  have hmk_ge_m : (p.m : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    nlinarith [mul_nonneg hmpos hKsub]
  have hmk_ge_K : (p.K : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    nlinarith [mul_nonneg hKpos hmsub]
  have hcoeff :
      ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        2 * ((p.m - 1 : ℕ) : ℝ) + 2 * (p.K : ℝ) ≤
      4 * (p.m : ℝ) * (p.K : ℝ) := by
    rw [hm1]
    nlinarith [hmk_ge_m, hmk_ge_K]
  have hsecond : μ.real (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
      4 * (p.m : ℝ) * (p.K : ℝ) * τ := by
    calc
      μ.real (forcedCorrectionEvent p ids rewards C_star C_h eta) ≤
          (((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
            2 * ((p.m - 1 : ℕ) : ℝ) + 2 * (p.K : ℝ)) * τ := hfirst
      _ ≤ 4 * (p.m : ℝ) * (p.K : ℝ) * τ :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
  exact ⟨by simpa [τ] using hfirst,
    by simpa [τ] using hsecond,
    (hsecond.trans (by simpa [τ] using
      forcedCorrection_exp_tail_weight_le_inv_N_sq p))⟩

end Bandits.Support.GeneratedForcedCorrectionTail

end
