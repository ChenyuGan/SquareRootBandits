/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CausalBootstrapBlockProduct
public import Bandits.Support.GeneratedBlockGainAveraging
public import Bandits.Support.GeneratedBlockChoiceAverages
public import Bandits.Support.GeneratedImportanceGainAdaptedness
public import Bandits.Support.IdentificationGoodEvent

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Conditional mean of the reference bootstrap importance gain

The lower process is the literal real indicator that the accepted
`ReferenceInitializationRun` is unlaunched and the selected follower is still
uninformed, times the rounded support in the current clipped block.  The
conditional mean is intended on the original-coordinate causal boundary
filtration.  Sources: `appendix_b_communication.tex:376-415,503-584` and
`07_public_setup.tex:63-115`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.GeneratedBootstrapImportanceMean

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.BootstrapBlockIsolation
open Bandits.Support.CompletePublicTable
open Bandits.Support.CausalBootstrapBlockProduct
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBlockChoiceAverages
open Bandits.Support.GeneratedBlockGainAveraging
open Bandits.Support.GeneratedImportanceGainAdaptedness
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates := GeneratedBootstrapBlockFiltrationRepair.Coordinates
abbrev SourcePrefix (p : Parameters) (s : Fin (n_boot p)) :=
  GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val
abbrev SidePast (p : Parameters) (s : Fin (n_boot p)) :=
  GeneratedBlockStartLaw.SidePast p s

variable {p : Parameters}

/-- The literal source guard at the incoming boundary before opportunity `s`.
It is a real indicator of the accepted run fields, rather than a separately
sampled stopping process. -/
def actualUnlaunchedUninformedGuard (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : Coordinates p) : ℝ :=
  let b := ReferenceInitializationRun.run
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e) s.val
  if b.crossing = none ∧ b.activation i = none then 1 else 0

theorem actualUnlaunchedUninformedGuard_eq_one_iff (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : Coordinates p) :
    actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e = 1 ↔
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) s.val).crossing = none ∧
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) s.val).activation i = none := by
  simp [actualUnlaunchedUninformedGuard]

theorem actualUnlaunchedUninformedGuard_eq_indicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : Coordinates p) :
    actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e =
      if (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val).crossing = none ∧
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val).activation i = none
      then (1 : ℝ) else 0 := rfl

/-- The source lower process, with the literal rounded denominator-`D` support
count in the current calendar block. -/
def actualImportanceMeanLower (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) (e : Coordinates p) : ℝ :=
  actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e *
    blockSupportCount p s rewards a / (512 * (p.m : ℝ))

theorem actualUnlaunchedUninformedGuard_nonneg (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : Coordinates p) :
    0 ≤ actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e := by
  simp only [actualUnlaunchedUninformedGuard]
  split_ifs <;> norm_num

theorem actualImportanceMeanLower_nonneg (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) (e : Coordinates p) :
    0 ≤ actualImportanceMeanLower p ids rewards C_star C_h eta i s a e := by
  unfold actualImportanceMeanLower
  exact div_nonneg
    (mul_nonneg
      (actualUnlaunchedUninformedGuard_nonneg p ids rewards C_star C_h eta i s e)
      (blockSupportCount_nonneg p s rewards a))
    (by positivity)

theorem actualUnlaunchedUninformedGuard_measurable_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (Coordinates p) ℝ (boundarySigma p s.val) inferInstance
      (actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s) := by
  let runAt := fun e : Coordinates p => ReferenceInitializationRun.run
    (referenceInput p ids rewards C_star C_h eta e) s.val
  have hcross : @Measurable (Coordinates p) (Option (Fin (n_boot p)))
      (boundarySigma p s.val) inferInstance (fun e => (runAt e).crossing) := by
    simpa only [runAt] using measurable_run_crossing p s.val ids rewards C_star C_h eta
  have hactAll : @Measurable (Coordinates p)
      (Follower p.m → Option (Activation p)) (boundarySigma p s.val) inferInstance
      (fun e => (runAt e).activation) := by
    simpa only [runAt] using
      measurable_run_activation p s.val ids rewards C_star C_h eta
  have hact : Measurable[boundarySigma p s.val]
      (fun e : Coordinates p => (runAt e).activation i) :=
    (measurable_pi_apply i).comp hactAll
  have hguard : MeasurableSet[boundarySigma p s.val]
      {e : Coordinates p | (runAt e).crossing = none} :=
    (measurableSet_singleton none).preimage hcross
  have hinformed : MeasurableSet[boundarySigma p s.val]
      {e : Coordinates p | (runAt e).activation i = none} :=
    (measurableSet_singleton none).preimage hact
  have hset : MeasurableSet[boundarySigma p s.val]
      {e : Coordinates p | (runAt e).crossing = none ∧
        (runAt e).activation i = none} := hguard.inter hinformed
  have hEq : actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s =
      fun e : Coordinates p =>
        if e ∈ {e : Coordinates p | (runAt e).crossing = none ∧
            (runAt e).activation i = none} then (1 : ℝ) else 0 := by
    funext e
    simp [actualUnlaunchedUninformedGuard, runAt]
  rw [hEq]
  simpa only [Set.mem_setOf_eq] using
    (measurable_const.ite hset measurable_const)

theorem actualImportanceMeanLower_measurable_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    @Measurable (Coordinates p) ℝ (boundarySigma p s.val) inferInstance
      (actualImportanceMeanLower p ids rewards C_star C_h eta i s a) := by
  have hV := actualUnlaunchedUninformedGuard_measurable_boundary
    p ids rewards C_star C_h eta i s
  have hbase := (hV.const_mul (blockSupportCount p s rewards a)).div_const
    (512 * (p.m : ℝ))
  change @Measurable (Coordinates p) ℝ (boundarySigma p s.val) inferInstance (fun e =>
    actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e *
      blockSupportCount p s rewards a / (512 * (p.m : ℝ)))
  convert hbase using 1 <;> (funext e <;> ring)

theorem actualImportanceMeanLower_integrable (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    Integrable (actualImportanceMeanLower p ids rewards C_star C_h eta i s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  let c := blockSupportCount p s rewards a / (512 * (p.m : ℝ))
  have hmeas := actualImportanceMeanLower_measurable_boundary p ids rewards
    C_star C_h eta i s a
  have hc : 0 ≤ c := div_nonneg (blockSupportCount_nonneg p s rewards a) (by positivity)
  have hle : ∀ e, actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ≤ c := by
    intro e
    have hV : actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e ≤ 1 := by
      simp only [actualUnlaunchedUninformedGuard]
      split_ifs <;> norm_num
    have hs := blockSupportCount_nonneg p s rewards a
    have hmp : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hm : 0 < 512 * (p.m : ℝ) := by positivity
    change (actualUnlaunchedUninformedGuard p ids rewards C_star C_h eta i s e *
      blockSupportCount p s rewards a) / (512 * (p.m : ℝ)) ≤
        blockSupportCount p s rewards a / (512 * (p.m : ℝ))
    exact div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right hV hs) hm.le
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  change Integrable (actualImportanceMeanLower p ids rewards C_star C_h eta i s a) μ
  change @Measurable (Coordinates p) ℝ (boundaryFiltration p s.val) inferInstance
      (actualImportanceMeanLower p ids rewards C_star C_h eta i s a) at hmeas
  have hambient : Measurable
      (actualImportanceMeanLower p ids rewards C_star C_h eta i s a) :=
    hmeas.mono (boundaryFiltration_le_ambient p s.val) (le_refl _)
  apply Integrable.mono_nonneg (μ := μ) (integrable_const c)
    hambient.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun e => actualImportanceMeanLower_nonneg
      p ids rewards C_star C_h eta i s a e
  · exact Filter.Eventually.of_forall hle

/-- Pull a measurable causal-prefix cell back to the retained side only
through the first coordinate of the accepted side-prefix-remainder
equivalence. The side remainder is retained in the carrier. -/
def sourcePrefixSideCell (p : Parameters) (s : Fin (n_boot p))
    (E : Set (SourcePrefix p s)) : Set (SidePast p s) :=
  {w | (sidePastPrefixRemainderEquiv p s w).1 ∈ E}

theorem measurableSet_sourcePrefixSideCell (p : Parameters) (s : Fin (n_boot p))
    (E : Set (SourcePrefix p s)) (hE : MeasurableSet E) :
    MeasurableSet (sourcePrefixSideCell p s E) := by
  exact hE.preimage
    (measurable_fst.comp (sidePastPrefixRemainderEquiv p s).measurable)

/-- The accepted causal product's source projection reconstructs the prefix
component of the retained-side decomposition. This identifies prefix cells
without conditioning on `SidePast`. -/
theorem analysisSide_sourcePrefixSideCell_iff (p : Parameters)
    (s : Fin (n_boot p)) (E : Set (SourcePrefix p s))
    (e : GeneratedBlockStartLaw.OriginalCoordinates p) :
    GeneratedBlockStartLaw.analysisSideOf p s e ∈ sourcePrefixSideCell p s E ↔
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e ∈ E := by
  change ((sidePastPrefixRemainderEquiv p s
      (GeneratedBlockStartLaw.analysisSideOf p s e)).1 ∈ E) ↔ _
  have hproj :
      (sidePastPrefixRemainderEquiv p s
        (GeneratedBlockStartLaw.analysisSideOf p s e)).1 =
        (causalProductEquiv p s e).1 := by
    rfl
  rw [hproj, causalProductEquiv_sourcePrefix]

/-- An arbitrary measurable causal-prefix cell intersected with one literal
incoming boundary. -/
def sourcePrefixBoundaryCell (p : Parameters) (s : Fin (n_boot p))
    (E : Set (SourcePrefix p s)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p) :
    Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  {e | GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e ∈ E ∧
    GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b}

theorem analysisSide_sourcePrefixBoundaryCell_iff (p : Parameters)
    (s : Fin (n_boot p)) (E : Set (SourcePrefix p s))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (e : GeneratedBlockStartLaw.OriginalCoordinates p) :
    e ∈ {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈
          sourcePrefixSideCell p s E ∧
        GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} ↔
      e ∈ sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b := by
  simp only [Set.mem_setOf_eq, sourcePrefixBoundaryCell]
  rw [analysisSide_sourcePrefixSideCell_iff p s E e]

theorem measurableSet_sourcePrefixBoundaryCell (p : Parameters)
    (s : Fin (n_boot p)) (E : Set (SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) := by
  exact (hE.preimage (GeneratedBootstrapBlockFiltrationRepair.measurable_sourcePrefix p s.val)).inter
    (GeneratedBlockStartLaw.measurable_boundaryAtOriginal_atom p s ids rewards C_star C_h eta b)

/-- Exact local factorization of an actual generated guard after restricting
to an arbitrary measurable retained-side cell. It is an unnormalized
identity, so zero-mass cells remain covered. -/
def generatedProcessedGuardFutureEventWithSide (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (A : Set (SidePast p s))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (GeneratedBlockGuardLaw.IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (GeneratedBlockChoiceAverages.FutureRow p s)) :
    Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
    e ∈ GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
      C_star C_h eta b hcompleted hnotStopped G H C}

private theorem sumProfileGuardAtoms_eq_ofReal (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (G : Set (GeneratedBlockGuardLaw.IncomingProfile p b)) :
    (∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
      BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c) =
      ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
        b.numerators b.weight_ge_one
        (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈ G)) := by
  classical
  let law := BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one
  let guard := fun c : GeneratedBlockGuardLaw.Profile p =>
    GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈ G
  calc
    (∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G, law c) =
        ∑ c : GeneratedBlockGuardLaw.Profile p, if guard c then law c else 0 := by
      simp only [GeneratedBlockGuardLaw.profileGuardAtoms, Finset.sum_filter]
      simp [guard]
    _ = ∑ c : GeneratedBlockGuardLaw.Profile p,
        ENNReal.ofReal (if guard c then (law c).toReal else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hg : guard c
      · simp [hg, ENNReal.ofReal_toReal (law.apply_ne_top c)]
      · simp [hg]
    _ = ENNReal.ofReal (∑ c : GeneratedBlockGuardLaw.Profile p,
          if guard c then (law c).toReal else 0) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro c hc
      by_cases hg : guard c <;> simp [hg]
    _ = ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
          b.numerators b.weight_ge_one guard) := by
      simp [guard, law, BootstrapBlockIsolation.privateBlockProfileEventProbability]

private theorem sumTargetGuardAtoms_eq_ofReal (p : Parameters) (H : Set (Fin p.K)) :
    (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
      ENNReal.ofReal (1 / (p.K : ℝ))) =
      ENNReal.ofReal (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
        1 / (p.K : ℝ)) := by
  classical
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro z hz
  positivity

private theorem sumGuardedAtomMasses (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (G : Set (GeneratedBlockGuardLaw.IncomingProfile p b)) (H : Set (Fin p.K))
    (B F : ENNReal) :
    (∑ q ∈ GeneratedBlockGuardLaw.guardedProfileTargetAtoms p b G H,
      B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
        b.weight_ge_one q.1 * ENNReal.ofReal (1 / (p.K : ℝ)) * F) =
      B * (∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c) *
        (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
          ENNReal.ofReal (1 / (p.K : ℝ))) * F := by
  classical
  rw [GeneratedBlockGuardLaw.guardedProfileTargetAtoms,
    Finset.product_eq_sprod, Finset.sum_product]
  calc
    _ = ∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
        ∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
          (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
            b.weight_ge_one c) * (ENNReal.ofReal (1 / (p.K : ℝ)) * F) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro z hz
      ac_rfl
    _ = ∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
        (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
            ENNReal.ofReal (1 / (p.K : ℝ)) * F) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
        (B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          ((∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
            ENNReal.ofReal (1 / (p.K : ℝ))) * F) := by
      congr 1
      rw [← Finset.sum_mul]
    _ = (∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
        B * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c) *
          ((∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
            ENNReal.ofReal (1 / (p.K : ℝ))) * F) := by
      rw [← Finset.sum_mul]
    _ = _ := by
      rw [← Finset.mul_sum]
      ac_rfl

/-- Guarded profile/target/future cells remain product-factored after an
arbitrary measurable source-side restriction. -/
theorem generatedProcessedGuardFutureEventWithSide_measure (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (G : Set (GeneratedBlockGuardLaw.IncomingProfile p b)) (H : Set (Fin p.K))
    (C : Set (GeneratedBlockChoiceAverages.FutureRow p s)) (hC : MeasurableSet C) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (generatedProcessedGuardFutureEventWithSide p s ids rewards C_star C_h eta A b
        hcompleted hnotStopped G H C) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
          GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
        b.numerators b.weight_ge_one
        (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈ G)) *
      ENNReal.ofReal (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
        1 / (p.K : ℝ)) *
      CompleteRowStoppingLaw.futureArrayLaw p
        (GeneratedBlockStartLaw.blockStartIndex p s) C := by
  classical
  let atoms := GeneratedBlockGuardLaw.guardedProfileTargetAtoms p b G H
  have hUnion : generatedProcessedGuardFutureEventWithSide p s ids rewards C_star C_h eta
      A b hcompleted hnotStopped G H C =
      ⋃ q ∈ atoms,
        GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEventWithSide p s ids
          rewards C_star C_h eta A b q.1 q.2 C := by
    ext e
    constructor
    · rintro ⟨hside, he⟩
      rcases he with ⟨hb, hprof, htarget, hfuture, _, _⟩
      let c := GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2
      let z := GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2
      have hp := GeneratedBlockChoiceAverages.actualProcessedProfile_eq_generatedProfile
        p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
      have hz := GeneratedBlockChoiceAverages.actualProcessedTarget_eq_generatedTarget
        p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
      have hP : GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈ G := by
        simpa [c, hp] using hprof
      have hZ : z ∈ H := by simpa [z, hz] using htarget
      have hq : (c, z) ∈ atoms := by
        simp [atoms, GeneratedBlockGuardLaw.guardedProfileTargetAtoms,
          GeneratedBlockGuardLaw.profileGuardAtoms, GeneratedBlockGuardLaw.targetGuardAtoms,
          hP, hZ]
      refine Set.mem_iUnion.2 ⟨(c, z), Set.mem_iUnion.2 ⟨hq, ?_⟩⟩
      exact ⟨hside, ⟨hb, rfl, rfl, hfuture⟩⟩
    · intro he
      rcases Set.mem_iUnion.1 he with ⟨q, hq⟩
      rcases Set.mem_iUnion.1 hq with ⟨hqmem, hcell⟩
      have hguard : GeneratedBlockGuardLaw.sourceRestrictedProfile p b q.1 ∈ G ∧
          q.2 ∈ H := by
        simpa [atoms, GeneratedBlockGuardLaw.guardedProfileTargetAtoms,
          GeneratedBlockGuardLaw.profileGuardAtoms, GeneratedBlockGuardLaw.targetGuardAtoms]
          using hqmem
      rcases hcell with ⟨hside, ⟨hb, hprof, htarget, hfuture⟩⟩
      have hp := GeneratedBlockChoiceAverages.actualProcessedProfile_eq_generatedProfile
        p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
      have hz := GeneratedBlockChoiceAverages.actualProcessedTarget_eq_generatedTarget
        p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
      have hP : GeneratedBlockGuardLaw.sourceRestrictedProfile p b
          (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) ∈ G := by
        rw [hprof]
        exact hguard.1
      have hZ : GeneratedBlockDrawLaw.generatedCurrentTarget p s e.2 ∈ H := by
        rw [htarget]
        exact hguard.2
      refine ⟨hside, ⟨hb, ?_, ?_, hfuture, hp, hz⟩⟩
      · rw [hp]
        exact hP
      · rw [hz]
        exact hZ
  have hdisj : Set.PairwiseDisjoint (↑atoms : Set (GeneratedBlockGuardLaw.Profile p × Fin p.K))
      (fun q => GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEventWithSide
        p s ids rewards C_star C_h eta A b q.1 q.2 C) := by
    intro q hq r hr hqr
    apply Set.disjoint_left.2
    intro e heq her
    rcases heq with ⟨_, ⟨hbq, hprofq, htargetq, _⟩⟩
    rcases her with ⟨_, ⟨hbr, hprofr, htargetr, _⟩⟩
    apply hqr
    apply Prod.ext
    · exact hprofq.symm.trans hprofr
    · exact htargetq.symm.trans htargetr
  have hmeas : ∀ q ∈ atoms,
      MeasurableSet (GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEventWithSide
        p s ids rewards C_star C_h eta A b q.1 q.2 C) := by
    intro q hq
    exact GeneratedBlockStartLaw.measurableSet_generatedBoundaryProfileTargetFutureEventWithSide
      p s ids rewards C_star C_h eta A hA b q.1 q.2 C hC
  rw [hUnion]
  calc
    _ = ∑ q ∈ atoms,
        GeneratedBlockStartLaw.originalCoordinatesLaw p
          (GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEventWithSide p s ids
            rewards C_star C_h eta A b q.1 q.2 C) :=
      MeasureTheory.measure_biUnion_finset hdisj hmeas
    _ = GeneratedBlockStartLaw.originalCoordinatesLaw p
          {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
            GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
        ENNReal.ofReal (BootstrapBlockIsolation.privateBlockProfileEventProbability p
          b.numerators b.weight_ge_one
          (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈ G)) *
        ENNReal.ofReal (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
          1 / (p.K : ℝ)) *
        CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s) C := by
      let base := GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
          GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b}
      let future := CompleteRowStoppingLaw.futureArrayLaw p
        (GeneratedBlockStartLaw.blockStartIndex p s) C
      calc
        _ = ∑ q ∈ atoms,
            (base * BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
              b.weight_ge_one q.1 * ENNReal.ofReal (1 / (p.K : ℝ)) * future) := by
          apply Finset.sum_congr rfl
          intro q hq
          simpa [base, future,
            GeneratedBlockStartLaw.generatedBoundaryProfileTargetFutureEventWithSide] using
            GeneratedBlockStartLaw.generatedBoundary_jointProfileTargetFuture_factorization_with_side
              p s ids rewards C_star C_h eta A hA b q.1 q.2 C hC
        _ = base *
            (∑ c ∈ GeneratedBlockGuardLaw.profileGuardAtoms p b G,
              BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
                b.weight_ge_one c) *
            (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p H,
              ENNReal.ofReal (1 / (p.K : ℝ))) * future := by
          simpa [atoms] using sumGuardedAtomMasses p b G H base future
        _ = _ := by
          rw [sumProfileGuardAtoms_eq_ofReal p b G]
          rw [sumTargetGuardAtoms_eq_ofReal p H]

/-- The literal side-restricted active-held event for the actual reference
run. -/
def activeHeldEventWithSide (p : Parameters) (s : Fin (n_boot p))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (A : Set (SidePast p s))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a : Fin p.K) : Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  generatedProcessedGuardFutureEventWithSide p s ids rewards C_star C_h eta A b
    hcompleted hnotStopped (GeneratedBlockGuardLaw.focalActiveHeldGuard p b i a)
    Set.univ Set.univ

/-- A support-choice cell restricted by an arbitrary retained-side event. -/
def supportChoiceCellWithSide (p : Parameters) (s : Fin (n_boot p))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (A : Set (SidePast p s))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a : Fin p.K) (u : Fin (A_id p)) : Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  generatedProcessedGuardFutureEventWithSide p s ids rewards C_star C_h eta A b
    hcompleted hnotStopped (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z ≠ a} Set.univ

/-- The same literal source choice cell with one fixed coordinator target. -/
def supportChoiceTargetCellWithSide (p : Parameters) (s : Fin (n_boot p))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (A : Set (SidePast p s))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a z : Fin p.K) (u : Fin (A_id p)) :
    Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  generatedProcessedGuardFutureEventWithSide p s ids rewards C_star C_h eta A b
    hcompleted hnotStopped (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {q | q = z} Set.univ

private theorem sourceRestriction_focalIsolation_iff (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (i : GeneratedBlockGuardLaw.Incoming p b) (a : Fin p.K)
    (c : GeneratedBlockGuardLaw.Profile p) :
    GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationGuard p b i a ↔
      BootstrapBlockIsolation.isolatedBootstrapEvent
        (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
        (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c := by
  constructor
  · intro h
    refine ⟨⟨h.1, h.2.1⟩, ?_⟩
    intro k hk
    obtain ⟨hkNe, hkU⟩ := Finset.mem_erase.mp hk
    obtain ⟨j, hj, hindex⟩ :=
      (GeneratedBlockGuardLaw.mem_sourceIncomingFinset_iff p b k).mp hkU
    have hji : (⟨j, hj⟩ : GeneratedBlockGuardLaw.Incoming p b) ≠ i := by
      intro hEq
      have hEqIndex : k = BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        have hjiVal : j = i.1 := congrArg Subtype.val hEq
        exact hindex.symm.trans
          (congrArg (BootstrapPhysicalInput.sourceFollowerIndex p) hjiVal)
      exact hkNe hEqIndex
    simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile, hindex] using h.2.2
      ⟨j, hj⟩ hji
  · rintro ⟨hactive, hinactive⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile,
        GeneratedBlockGuardLaw.focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.1
    · simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile,
        GeneratedBlockGuardLaw.focalIsolationGuard,
        BootstrapBlockIsolation.distinguishedEvent] using hactive.2
    · intro j hji
      have hindexNe : BootstrapPhysicalInput.sourceFollowerIndex p j.1 ≠
          BootstrapPhysicalInput.sourceFollowerIndex p i.1 := by
        intro hEq
        exact hji (Subtype.ext
          (GeneratedBlockGuardLaw.sourceFollowerIndex_injective p hEq))
      have hmember :=
        GeneratedBlockGuardLaw.sourceFollowerIndex_mem_sourceIncomingFinset p b j
      have hstatus := hinactive
        (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
        (Finset.mem_erase.mpr ⟨hindexNe, hmember⟩)
      simpa [GeneratedBlockGuardLaw.sourceRestrictedProfile] using hstatus

private theorem profileProbability_focalIsolationPrivateId (p : Parameters)
    (b : ReferenceInitializationRun.Boundary p)
    (i : GeneratedBlockGuardLaw.Incoming p b) (a : Fin p.K) (u : Fin (A_id p)) :
    BootstrapBlockIsolation.privateBlockProfileEventProbability p b.numerators
      b.weight_ge_one
      (fun c => GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u) =
      ((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * BootstrapBlockConstruction.privateIdProbability p u) *
        (1 - 1 / (p.m : ℝ)) ^
          ((GeneratedBlockGuardLaw.sourceIncomingFinset p b).card - 1) := by
  have hevent : (fun c : GeneratedBlockGuardLaw.Profile p =>
      GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u) =
      (fun c => BootstrapBlockIsolation.isolatedBootstrapEvent
          (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
          (BootstrapPhysicalInput.sourceFollowerIndex p i.1) a c ∧
        (c (BootstrapPhysicalInput.sourceFollowerIndex p i.1)).2.2 = u) := by
    funext c
    apply propext
    change (GeneratedBlockGuardLaw.sourceRestrictedProfile p b c ∈
        GeneratedBlockGuardLaw.focalIsolationGuard p b i a ∧
      (GeneratedBlockGuardLaw.sourceRestrictedProfile p b c i).2.2 = u) ↔ _
    rw [sourceRestriction_focalIsolation_iff]
    rfl
  rw [hevent]
  exact BootstrapBlockIsolation.isolatedBootstrapEvent_privateId_probability p
    b.numerators b.weight_ge_one (GeneratedBlockGuardLaw.sourceIncomingFinset p b)
    (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
    (GeneratedBlockGuardLaw.sourceFollowerIndex_mem_sourceIncomingFinset p b i) a u

private theorem targetAvoidance_probability (p : Parameters) (a : Fin p.K) :
    (∑ z ∈ GeneratedBlockGuardLaw.targetGuardAtoms p {z | z ≠ a},
      1 / (p.K : ℝ)) = ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
  classical
  have ha : a ∈ (Finset.univ : Finset (Fin p.K)) := Finset.mem_univ _
  have hatoms : GeneratedBlockGuardLaw.targetGuardAtoms p {z | z ≠ a} =
      Finset.univ.erase a := by
    ext z
    simp [GeneratedBlockGuardLaw.targetGuardAtoms]
  calc
    _ = ∑ z ∈ Finset.univ.erase a, 1 / (p.K : ℝ) := by rw [hatoms]
    _ = ((p.K - 1 : ℕ) : ℝ) * (1 / (p.K : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem ha,
        Fintype.card_fin]
    _ = _ := by ring

/-- The localized support choice retains the focal held probability, the
activity factor, the uniform private ID, the target avoidance, and the full
literal source-prefix-side mass. -/
theorem supportChoiceCellWithSide_measure (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a : Fin p.K) (u : Fin (A_id p)) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (supportChoiceCellWithSide p s ids rewards C_star C_h eta A b hcompleted
        hnotStopped i a u) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
          GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
        (1 - 1 / (p.m : ℝ)) ^
          (GeneratedBlockChoiceAverages.incomingCount p b - 1)) *
      ENNReal.ofReal (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) := by
  have hfactor := generatedProcessedGuardFutureEventWithSide_measure p s ids rewards
    C_star C_h eta A hA b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {z | z ≠ a} Set.univ MeasurableSet.univ
  have htarget := targetAvoidance_probability p a
  have hprofile := profileProbability_focalIsolationPrivateId p b i a u
  have hpId : BootstrapBlockConstruction.privateIdProbability p u = 1 / (A_id p : ℝ) := by
    simp [BootstrapBlockConstruction.privateIdProbability]
  have hinc : GeneratedBlockChoiceAverages.incomingCount p b =
      (GeneratedBlockGuardLaw.sourceIncomingFinset p b).card := by
    rfl
  rw [supportChoiceCellWithSide, hfactor, hprofile, htarget, hpId, hinc]
  simp [GeneratedBlockChoiceAverages.supportChoiceCell,
    GeneratedBlockChoiceAverages.isolatedPrivateIDTargetFutureEvent,
    GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
    CompleteRowStoppingLaw.futureArrayLaw]

/-- Every fixed target atom retains the full measurable source-prefix cell;
the identity is unnormalized and so also covers zero-mass cells. -/
theorem supportChoiceTargetCellWithSide_measure (p : Parameters)
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (A : Set (SidePast p s)) (hA : MeasurableSet A)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a z : Fin p.K) (u : Fin (A_id p)) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta A b hcompleted
        hnotStopped i a z u) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        {e | GeneratedBlockStartLaw.analysisSideOf p s e ∈ A ∧
          GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b} *
      ENNReal.ofReal (((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
        (1 - 1 / (p.m : ℝ)) ^
          (GeneratedBlockChoiceAverages.incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  have hfactor := generatedProcessedGuardFutureEventWithSide_measure p s ids rewards
    C_star C_h eta A hA b hcompleted hnotStopped
    (GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u)
    {q | q = z} Set.univ MeasurableSet.univ
  have hprofile := profileProbability_focalIsolationPrivateId p b i a u
  have hAtoms : GeneratedBlockGuardLaw.targetGuardAtoms p {q | q = z} = {z} := by
    ext q
    simp [GeneratedBlockGuardLaw.targetGuardAtoms]
  have htarget :
      (∑ q ∈ GeneratedBlockGuardLaw.targetGuardAtoms p {q | q = z},
        1 / (p.K : ℝ)) = 1 / (p.K : ℝ) := by
    rw [hAtoms]
    simp
  have hpId : BootstrapBlockConstruction.privateIdProbability p u =
      1 / (A_id p : ℝ) := by
    simp [BootstrapBlockConstruction.privateIdProbability]
  have hinc : GeneratedBlockChoiceAverages.incomingCount p b =
      (GeneratedBlockGuardLaw.sourceIncomingFinset p b).card := rfl
  rw [supportChoiceTargetCellWithSide, hfactor, hprofile, htarget, hpId, hinc]
  simp [GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
    CompleteRowStoppingLaw.futureArrayLaw]

/-- Restricting the retained-side factorization to a prefix cell is exactly
the causal-prefix/boundary cell on original coordinates. -/
theorem supportChoiceTargetCell_prefix_measure (p : Parameters)
    (s : Fin (n_boot p)) (E : Set (SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a z : Fin p.K) (u : Fin (A_id p)) :
    GeneratedBlockStartLaw.originalCoordinatesLaw p
      (supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta
        (sourcePrefixSideCell p s E) b hcompleted hnotStopped i a z u) =
      GeneratedBlockStartLaw.originalCoordinatesLaw p
        (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) *
      ENNReal.ofReal (((BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a /
          (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
        (1 - 1 / (p.m : ℝ)) ^
          (GeneratedBlockChoiceAverages.incomingCount p b - 1)) *
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  rw [supportChoiceTargetCellWithSide_measure p s ids rewards C_star C_h eta
    (sourcePrefixSideCell p s E) (measurableSet_sourcePrefixSideCell p s E hE)
    b hcompleted hnotStopped i a z u]
  congr 1

private theorem actualProfile_eq_descriptorDraws
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (e : GeneratedBlockStartLaw.OriginalCoordinates p)
    (draws : PrivateSourceStreams.BlockDrawProfile p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b)
    (hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
      b.weight_ge_one e.2 = draws) :
    GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
      b hcompleted hnotStopped e = fun j => draws
        (BootstrapPhysicalInput.sourceFollowerIndex p j.1) := by
  rw [GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile
    p s ids rewards C_star C_h eta b hcompleted hnotStopped e hboundary]
  funext j
  change GeneratedBlockGuardLaw.sourceRestrictedProfile p b
    (GeneratedBlockDrawLaw.generatedCurrentBlockProfile p s b e.2) j = _
  change BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
    b.weight_ge_one e.2 (BootstrapPhysicalInput.sourceFollowerIndex p j.1) = _
  exact congrFun hdraws (BootstrapPhysicalInput.sourceFollowerIndex p j.1)

private theorem blockStartGuard_iff_processedFields
    (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (i : GeneratedBlockChoiceAverages.Incoming p b) (a z : Fin p.K)
    (u : Fin (A_id p)) (e : GeneratedBlockStartLaw.OriginalCoordinates p)
    (d : GeneratedBootstrapRoundLaw.Descriptor p)
    (hboundary : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards
      C_star C_h eta e = b) (hdb : d.1 = b)
    (hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
      b.weight_ge_one e.2 = d.2.1)
    (htarget : GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards
      C_star C_h eta b hcompleted hnotStopped e = d.2.2.1) :
    GeneratedStayBlockTower.blockStartGuard ids rewards (s := s) i.1 a z u
        (some d) ↔
      GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta
          b hcompleted hnotStopped e ∈
        GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard p b i a u ∧
      GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards C_star C_h eta
        b hcompleted hnotStopped e = z ∧ z ≠ a := by
  have hprofile := actualProfile_eq_descriptorDraws s ids rewards C_star C_h eta
    b hcompleted hnotStopped e d.2.1 hboundary hdraws
  simp only [GeneratedStayBlockTower.blockStartGuard,
    GeneratedStayConditionalMean.inputOfDescriptor,
    GeneratedBlockGuardLaw.focalIsolationPrivateIdGuard,
    GeneratedBlockGuardLaw.focalIsolationGuard, Set.mem_setOf_eq, hdb, htarget]
  constructor
  · rintro ⟨hi, ha, hh, hu, ht, hza, hother⟩
    have hpi := congrFun hprofile i
    refine ⟨⟨⟨?_, ⟨?_, ?_⟩⟩, ?_⟩, ⟨ht, hza⟩⟩
    · rw [hpi]
      exact ha
    · rw [hpi]
      exact hh
    · intro j hji
      have hjiVal : j.1 ≠ i.1 := by
        intro h
        apply hji
        exact Subtype.ext h
      let k : {k // k ∈ ReferenceInitializationRun.uninformed d.1} :=
        ⟨j.1, by simpa [hdb] using j.2⟩
      have hi' : i.1 ∈ ReferenceInitializationRun.uninformed d.1 := by
        simpa [hdb] using hi
      have hki : k ≠ ⟨i.1, hi'⟩ := by
        intro h
        apply hjiVal
        have hkval : j.1 = i.1 := by
          have hv := congrArg
            (fun x : {k // k ∈ ReferenceInitializationRun.uninformed d.1} => x.1) h
          simpa [k] using hv
        exact hkval
      rw [congrFun hprofile j]
      exact hother k hki
    · rw [hpi]
      exact hu
  · rintro ⟨⟨⟨ha, hh, hother⟩, hu⟩, ⟨ht, hza⟩⟩
    have hpi := congrFun hprofile i
    rw [hpi] at ha hh hu
    refine ⟨i.2, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using ha
    · refine ⟨?_, ?_⟩
      · simpa using hh
      · refine ⟨?_, ?_⟩
        · simpa using hu
        · refine ⟨?_, ?_⟩
          · simpa using ht
          · refine ⟨hza, ?_⟩
            intro k hki
            let j : GeneratedBlockChoiceAverages.Incoming p b :=
              ⟨k.1, by simpa [hdb] using k.2⟩
            have hji : j ≠ i := by
              intro h
              apply hki
              have hval : k.1 = i.1 := by
                have hv := congrArg (fun x : GeneratedBlockChoiceAverages.Incoming p b => x.1) h
                simpa [j] using hv
              exact Subtype.ext hval
            have hj := hother j hji
            rw [congrFun hprofile j] at hj
            exact hj

/-- A source-choice cell under an arbitrary prefix restriction lies inside
the accepted physical block-start event for its target and private ID. -/
theorem supportChoiceTargetCell_prefix_subset_blockStartEvent
    (p : Parameters) (s : Fin (n_boot p)) (E : Set (SourcePrefix p s))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a z : Fin p.K) (u : Fin (A_id p)) (hza : z ≠ a) :
    supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta
        (sourcePrefixSideCell p s E) b hcompleted hnotStopped i a z u ⊆
      sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b ∩
        GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
          (s := s) i.1 a z u := by
  intro e he
  rcases he with ⟨hside, hevent⟩
  rcases hevent with ⟨hb, hprofile, htarget, hfuture, _, _⟩
  have hprefix : GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e ∈ E :=
    (analysisSide_sourcePrefixSideCell_iff p s E e).mp hside
  have hrun : ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b := by
    simpa [GeneratedBlockStartLaw.boundaryAtOriginal,
      GeneratedBlockDrawLaw.generatedBoundary, GeneratedBlockDrawLaw.fixedReferenceInput,
      GeneratedBootstrapBlockFiltrationRepair.referenceInput, GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using hb
  have hrunStopped : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
      s.val).crossing = none := by rw [hrun]; exact hnotStopped
  have hdescriptorNe : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta
      s (GeneratedStayBlockTower.blockStartRound p s) e ≠ none := by
    intro hd
    have hcross := (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards
      C_star C_h eta s (GeneratedStayBlockTower.blockStartRound p s) e).mp hd
    exact hcross hrunStopped
  cases hd : GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e with
  | none => exact (hdescriptorNe hd).elim
  | some d =>
    have hrec := GeneratedStayConditionalMean.actualDescriptor_reconstructs_source_block
      p ids rewards C_star C_h eta (s := s)
      (t := GeneratedStayBlockTower.blockStartRound p s) e d hd
    dsimp only at hrec
    rcases hrec with ⟨hrunD, hrem, hdrawsRaw, htargetRaw, _, hnext⟩
    have hdb : d.1 = b := hrunD.symm.trans hrun
    have hdraws : BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
        b.weight_ge_one e.2 = d.2.1 := by
      rw [hnext, hrun] at hdrawsRaw
      simpa [GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]
        using hdrawsRaw
    have htargetD : GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards
        C_star C_h eta b hcompleted hnotStopped e = d.2.2.1 := by
      cases hrun
      simpa [GeneratedBlockGuardLaw.actualProcessedTarget,
        GeneratedBlockDrawLaw.generatedPhysicalBlockTarget,
        GeneratedBlockDrawLaw.fixedReferenceInput, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates] using htargetRaw
    have htargetEq : GeneratedBlockGuardLaw.actualProcessedTarget p s ids rewards
        C_star C_h eta b hcompleted hnotStopped e = z := by
      simpa using htarget
    have hguard := (blockStartGuard_iff_processedFields s ids rewards C_star C_h eta b
      hcompleted hnotStopped i a z u e d hb hdb hdraws htargetD).2
        ⟨hprofile, htargetEq, hza⟩
    have hstart : e ∈ GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
        (s := s) i.1 a z u := by
      simpa [GeneratedStayBlockTower.blockStartEvent, hd] using hguard
    exact ⟨⟨hprefix, hb⟩, hstart⟩

private theorem supportedIDZeroCount_div16_eq_blockStartCoefficient
    (p : Parameters) (s : Fin (n_boot p)) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) (u : Fin (A_id p)) :
    supportedIDZeroCount p s ids rewards a u / 16 =
      GeneratedStayBlockTower.blockStartGainCoefficient ids rewards (s := s) a u := by
  unfold supportedIDZeroCount GeneratedStayBlockTower.blockStartGainCoefficient
    GeneratedBlockChoiceAverages.roundedSupportChi GeneratedStayBlockTower.sourceChi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpositive :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    rw [RealRewardGridCount.realRewardGridValue]
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast (show (0 : ℕ) < (rewards t a).val ↔ 0 < (rewards t a).val by rfl)
  simp [GeneratedBlockChoiceAverages.roundedSupportChi,
    GeneratedStayBlockTower.sourceChi, hpositive]

/-- The accepted physical tower localized to an arbitrary measurable
causal-prefix cell and one original block-start choice cell. Its lower mass is
provided by the source-prefix-restricted choice factorization above, so it
remains meaningful on null prefix cells. -/
theorem actualBlockGain_setIntegral_ge_prefixCell (p : Parameters)
    (s : Fin (n_boot p)) (E : Set (SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (i : GeneratedBlockChoiceAverages.Incoming p b)
    (a z : Fin p.K) (u : Fin (A_id p)) (hza : z ≠ a) :
    (supportedIDZeroCount p s ids rewards a u / 16) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real
          (supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta
            (sourcePrefixSideCell p s E) b hcompleted hnotStopped i a z u) ≤
      ∫ e in sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b ∩
          GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
            (s := s) i.1 a z u,
        GeneratedStayBlockTower.actualBlockGain ids rewards C_star C_h eta
          (s := s) i.1 e ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  let A := sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b ∩
    GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
      (s := s) i.1 a z u
  let : MeasurableSpace (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :=
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val
  have hprefix : Measurable (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) :=
    comap_measurable _
  have hrun := GeneratedBootstrapBlockFiltrationRepair.measurable_run p s.val ids rewards
    C_star C_h eta
  have hrunEq : (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
      ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        s.val) = GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta := by
    funext e
    rfl
  have hcellBoundary :
      @MeasurableSet (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
        (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val)
        (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) := by
    change MeasurableSet ({e | GeneratedBootstrapBlockFiltrationRepair.sourcePrefix
      p s.val e ∈ E} ∩ {e | GeneratedBlockStartLaw.boundaryAtOriginal p s
        ids rewards C_star C_h eta e = b})
    exact (hE.preimage hprefix).inter <| by
      rw [← hrunEq]
      exact (measurableSet_singleton b).preimage hrun
  have hfil : GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val ≤
      GeneratedBootstrapFiltration.analysisFiltration p
        (GeneratedStayBlockTower.blockStartRound p s).val := by
    have hstartEq : GeneratedStayBlockTower.blockStartRound p s =
        GeneratedDownBlockBoundaryMean.blockStartRound s := by
      apply Fin.ext
      rfl
    rw [hstartEq, GeneratedDownBlockBoundaryMean.blockStartRound_is_elapsed s]
    exact GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_analysis_at_elapsed
      p s.val
  have hA : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (GeneratedStayBlockTower.blockStartRound p s).val] A := by
    exact MeasurableSet.inter ((MeasurableSpace.le_def.mp hfil)
      (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) hcellBoundary)
      (GeneratedStayBlockTower.blockStartEvent_measurable ids rewards C_star C_h eta
        (s := s) i.1 a z u)
  have hTower := GeneratedStayBlockTower.actualBlockGain_setIntegral_ge_on_blockStartEvent
    ids rewards C_star C_h eta (s := s) i.1 a z u A hA
    (by intro e he; exact he.2)
  have hcoeff := supportedIDZeroCount_div16_eq_blockStartCoefficient p s ids rewards a u
  have hTower' : GeneratedStayBlockTower.blockStartGainCoefficient ids rewards
        (s := s) a u *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      ∫ e in A, GeneratedStayBlockTower.actualBlockGain ids rewards C_star C_h eta
        (s := s) i.1 e ∂GeneratedBootstrapRoundLaw.originalLaw p := by
    simpa [A, GeneratedStayBlockTower.blockStartGainCoefficient] using hTower
  have hcellSubset := supportChoiceTargetCell_prefix_subset_blockStartEvent p s E
    ids rewards C_star C_h eta b hcompleted hnotStopped i a z u hza
  have hmass : (GeneratedBootstrapRoundLaw.originalLaw p).real
        (supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta
          (sourcePrefixSideCell p s E) b hcompleted hnotStopped i a z u) ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
    apply measureReal_mono (μ := GeneratedBootstrapRoundLaw.originalLaw p) hcellSubset
  have hcoeffNonneg : 0 ≤ supportedIDZeroCount p s ids rewards a u / 16 := by
    exact div_nonneg
      (GeneratedBlockChoiceAverages.supportedIDZeroCount_nonneg p s ids rewards a u)
      (by norm_num)
  calc
    _ ≤ (supportedIDZeroCount p s ids rewards a u / 16) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A :=
      mul_le_mul_of_nonneg_left hmass hcoeffNonneg
    _ ≤ ∫ e in A, GeneratedStayBlockTower.actualBlockGain ids rewards C_star C_h eta
        (s := s) i.1 e ∂GeneratedBootstrapRoundLaw.originalLaw p := by
      rw [hcoeff]
      exact hTower'

end Bandits.Support.GeneratedBootstrapImportanceMean

end
