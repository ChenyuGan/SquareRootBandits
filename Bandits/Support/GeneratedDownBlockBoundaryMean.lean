/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedDownConditionalMean
public import Bandits.Support.GeneratedBlockGuardLaw
public import Bandits.Support.GeneratedBlockStartLaw
public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.GeneratedBootstrapMonitor

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual generated DOWN block means on boundary atoms

For one genuine generated block, this file sums the existing one-round
conditional-mean theorem on the actual calendar block. The tower step is
localized to an actual processed-boundary atom intersected with its actual
all-incoming-inactive profile guard; the accepted guard law then averages the
original activity coordinates without conditioning on boundary mass.

This proves unnormalized bounds on boundary atoms. Extending the localization
to arbitrary causal block-prefix events remains a separate obligation for the
new block-filtration module.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:638-682` and
`sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBootstrapFiltration
open Bandits.Support.GeneratedDownConditionalMean
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.GeneratedBlockGuardLaw
open Bandits.Support.GeneratedBootstrapMonitor
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.GeneratedDownBlockBoundaryMean

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-! ## The actual rounded support and generated block sum -/

/-- The source support count is the literal count of positive rounded rewards
on the existing clipped calendar block. -/
def roundedPositiveCount (p : Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) : ℝ :=
  ∑ t ∈ calendarBlock p s, if (0 : Fin (D p + 1)) < rewards t a then 1 else 0

theorem roundedPositiveCount_eq_rewardSupportCount (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    roundedPositiveCount p s rewards a =
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
  unfold roundedPositiveCount BootstrapDownCountMean.rewardSupportCount
  apply Finset.sum_congr rfl
  intro t ht
  unfold BootstrapDownCountMean.rewardSupport
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos :
      (0 : ℝ) < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        (0 : Fin (D p + 1)) < rewards t a := by
    rw [RealRewardGridCount.realRewardGridValue]
    constructor
    · intro h
      have hv : (0 : ℝ) < ((rewards t a).val : ℝ) :=
        (div_pos_iff_of_pos_right hD).mp h
      exact_mod_cast hv
    · intro h
      have hn : (0 : ℕ) < (rewards t a).val := by exact_mod_cast h
      have hn' : (0 : ℝ) < ((rewards t a).val : ℝ) := by exact_mod_cast hn
      exact (div_pos_iff_of_pos_right hD).2 hn'
  by_cases h : (0 : Fin (D p + 1)) < rewards t a
  · simp [h, hpos]
  · simp [h, hpos]

/-- The existing generated current-round test, summed over every actual
calendar round in block `s`. `none` remains the accepted analytic zero. -/
def downBlockTest (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) : Coordinates p → ℝ := fun e =>
  ∑ t ∈ calendarBlock p s,
    GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
      (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a) e

theorem measurable_downBlockTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) : Measurable (downBlockTest p ids rewards C_star C_h eta s a) := by
  unfold downBlockTest
  apply Finset.measurable_sum
  intro t ht
  have hd := GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta s t ht
  have hd' := hd.mono (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) le_rfl
  have hc := GeneratedBootstrapFiltration.measurable_current_succ p t
  have hc' := hc.mono
    (GeneratedBootstrapFiltration.analysisFiltration_le p (t.val + 1)) le_rfl
  exact (GeneratedDownConditionalMean.measurable_downPositiveCurrentTest ids rewards s t a).comp
    (hd'.prodMk hc')

theorem integrable_downBlockTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) :
    Integrable (downBlockTest p ids rewards C_star C_h eta s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  unfold downBlockTest
  apply integrable_finsetSum
  intro t ht
  exact GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
    C_star C_h eta s t ht a

theorem downBlockTest_nonneg_le_boot (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) :
    0 ≤ downBlockTest p ids rewards C_star C_h eta s a e ∧
      downBlockTest p ids rewards C_star C_h eta s a e ≤ B_boot p := by
  unfold downBlockTest
  constructor
  · apply Finset.sum_nonneg
    intro t ht
    have hu := GeneratedDownConditionalMean.downPositiveCurrentTest_unit_bounds
      ids rewards s t a
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e,
        GeneratedBootstrapRoundLaw.current p t e)
    simpa only [GeneratedBootstrapFiltration.testValue] using hu.1
  · calc
      _ ≤ ∑ t ∈ calendarBlock p s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have hu := GeneratedDownConditionalMean.downPositiveCurrentTest_unit_bounds
          ids rewards s t a
          (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e,
            GeneratedBootstrapRoundLaw.current p t e)
        simpa only [GeneratedBootstrapFiltration.testValue] using hu.2
      _ = ((calendarBlock p s).card : ℝ) := by simp
      _ ≤ (B_boot p : ℝ) := by
        exact_mod_cast BootstrapDimensions.calendarBlock_card_le_B_boot p s

/-! ## The zero-based block boundary is a round-past cutoff -/

theorem blockStart_lt_horizon (s : Fin (n_boot p)) :
    s.val * B_boot p < p.T := by
  obtain ⟨t, ht⟩ := BootstrapDimensions.calendarBlock_nonempty p s
  have h := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht
  exact lt_of_le_of_lt h.1 t.isLt

/-- The first zero-based calendar round of the existing block. -/
def blockStartRound (s : Fin (n_boot p)) : Fin p.T :=
  ⟨s.val * B_boot p, blockStart_lt_horizon (p := p) s⟩

theorem blockStartRound_mem (s : Fin (n_boot p)) :
    blockStartRound s ∈ calendarBlock p s := by
  apply (BootstrapDimensions.mem_calendarBlock_iff p s (blockStartRound s)).2
  constructor
  · exact le_rfl
  · obtain ⟨t, ht⟩ := BootstrapDimensions.calendarBlock_nonempty p s
    exact ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).1.trans_lt
      ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).2

theorem blockStartRound_is_elapsed (s : Fin (n_boot p)) :
    (blockStartRound s).val = ReferenceInitializationRun.elapsed p s.val := by
  simp only [blockStartRound, Fin.val_mk, ReferenceInitializationRun.elapsed]
  exact (Nat.min_eq_right (Nat.le_of_lt (blockStart_lt_horizon (p := p) s))).symm

/-- Source-indexing the block's first round adds one to its zero-based
boundary index. Its conditional expectation therefore uses filtration index
`k0`, since the source past is `alpha - 1`. -/
theorem blockStart_sourceClockIndex (s : Fin (n_boot p)) :
    GeneratedBootstrapFiltration.sourceClockIndex p (blockStartRound s) =
      s.val * B_boot p + 1 := by
  rfl

/-- The actual original-coordinate atom at boundary `b`. -/
def boundaryEvent (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) : Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  {e | GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b}

private def boundaryFromRoundPast (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (e₀ : Coordinates p) (w : Past p (blockStartRound s)) :
    ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.run
    (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta
      (GeneratedBootstrapRoundLaw.complete p (blockStartRound s) e₀ w)) s.val

private theorem measurable_boundaryFromRoundPast (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (e₀ : Coordinates p) :
    Measurable (boundaryFromRoundPast (p := p) ids rewards C_star C_h eta s e₀) := by
  change Measurable (fun w : Past p (blockStartRound s) =>
    ReferenceInitializationRun.run
      (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, GeneratedBootstrapRoundLaw.complete p (blockStartRound s) e₀ w)) s.val)
  exact (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards s.val).comp
    (measurable_const.prodMk
      (GeneratedBootstrapRoundLaw.measurable_complete p (blockStartRound s) e₀))

private theorem boundaryAtOriginal_eq_roundPast (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (e₀ e : Coordinates p) :
    GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e =
      boundaryFromRoundPast (p := p) ids rewards C_star C_h eta s e₀
        (GeneratedBootstrapRoundLaw.past p (blockStartRound s) e) := by
  have hpast := GeneratedBootstrapRoundLaw.runPrefixInputEq_of_past_eq
    ids rewards C_star C_h eta s (blockStartRound s) (blockStartRound_mem s)
    e (GeneratedBootstrapRoundLaw.complete p (blockStartRound s) e₀
      (GeneratedBootstrapRoundLaw.past p (blockStartRound s) e))
    (by rw [GeneratedBootstrapRoundLaw.past_complete])
  change ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val =
    ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta
        (GeneratedBootstrapRoundLaw.complete p (blockStartRound s) e₀
          (GeneratedBootstrapRoundLaw.past p (blockStartRound s) e))) s.val
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq _ _ _ hpast

theorem measurableSet_boundaryEvent_at_blockStart (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (blockStartRound s).val]
      (boundaryEvent ids rewards C_star C_h eta s b) := by
  rw [GeneratedBootstrapFiltration.analysisFiltration_at p (blockStartRound s)]
  obtain ⟨e₀⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure
    (GeneratedBootstrapRoundLaw.originalLaw p)
  have hfactor :
      (fun e : Coordinates p =>
        GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e) =
      boundaryFromRoundPast (p := p) ids rewards C_star C_h eta s e₀ ∘
        GeneratedBootstrapRoundLaw.past p (blockStartRound s) := by
    funext e
    exact (boundaryAtOriginal_eq_roundPast (p := p) ids rewards C_star C_h eta s e₀ e)
  have hf := measurable_boundaryFromRoundPast (p := p) ids rewards C_star C_h eta s e₀
  have hset : MeasurableSet
      (boundaryFromRoundPast (p := p) ids rewards C_star C_h eta s e₀ ⁻¹' {b}) :=
    (measurableSet_singleton b).preimage hf
  change MeasurableSet[MeasurableSpace.comap
    (GeneratedBootstrapRoundLaw.past p (blockStartRound s)) inferInstance]
      ((fun e : Coordinates p =>
        GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e) ⁻¹' {b})
  rw [hfactor]
  exact ⟨_, hset, rfl⟩

/-! ## The actual inactive guard on the processed boundary -/

/-- The processed boundary atom intersected with the actual incoming-profile
all-inactive guard, with the accepted entire-future-row guard retained. -/
def allInactiveBoundaryEvent (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) : Set (GeneratedBlockStartLaw.OriginalCoordinates p) :=
  GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards C_star C_h eta
    b hcompleted hnotStopped (GeneratedBlockGuardLaw.allIncomingInactiveGuard p b)
    Set.univ Set.univ

private theorem descriptor_processed_on_boundary (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b)
    (t : Fin p.T) :
    GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
      some (b, (BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
        b.weight_ge_one e.2,
        ((ReferenceInitializationRun.physical
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt)).target,
          BootstrapPhysicalBlock.run
            (ReferenceInitializationRun.physical
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
              (by rw [hcompleted]; exact s.isLt)) t.val))) := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  have hrun : ReferenceInitializationRun.run x s.val = b := by
    change ReferenceInitializationRun.run x s.val = b at hb
    exact hb
  have h : b.completed < n_boot p := by
    simp [hcompleted]
  have hnext : ReferenceInitializationRun.nextBlock b h = s := by
    apply Fin.ext
    exact hcompleted
  have hprofile : BootstrapPhysicalInput.currentBlockDrawProfile p
      (ReferenceInitializationRun.nextBlock b h) b.numerators b.weight_ge_one x.coordinates =
      BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators b.weight_ge_one x.coordinates := by
    rw [hnext]
  rw [GeneratedBootstrapRoundLaw.descriptor, hrun]
  simp only [GeneratedBootstrapRoundLaw.descriptorAtBoundary, hnotStopped, ite_true,
    dite_eq_left h]
  apply congrArg some
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hprofile
    · apply Prod.ext <;> rfl

private theorem startGuard_iff_actualProfileGuard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
          (blockStartRound s) e) = true ↔
      GeneratedBlockGuardLaw.actualProcessedProfile p s ids rewards C_star C_h eta b
        hcompleted hnotStopped e ∈ GeneratedBlockGuardLaw.allIncomingInactiveGuard p b := by
  have hdesc := descriptor_processed_on_boundary ids rewards C_star C_h eta s b
    hcompleted hnotStopped e hb (blockStartRound s)
  rw [hdesc]
  rw [GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile p s ids rewards
    C_star C_h eta b hcompleted hnotStopped e hb]
  simp [GeneratedDownConditionalMean.processedAllInactive,
    GeneratedDownConditionalMean.descriptorAllInactive,
    GeneratedBlockGuardLaw.allIncomingInactiveGuard,
    GeneratedBlockGuardLaw.sourceRestrictedProfile,
    BootstrapPhysicalInput.currentBlockDrawProfile,
    GeneratedBlockDrawLaw.generatedCurrentBlockProfile]

private theorem allInactiveBoundaryEvent_eq_inter_startGuard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) :
    allInactiveBoundaryEvent ids rewards C_star C_h eta s b hcompleted hnotStopped =
      boundaryEvent ids rewards C_star C_h eta s b ∩
        {e | GeneratedDownConditionalMean.processedAllInactive
          (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
            (blockStartRound s) e) = true} := by
  ext e
  constructor
  · intro he
    have he' := he
    simp only [allInactiveBoundaryEvent, GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
      Set.mem_ofPred_eq, Set.mem_univ] at he'
    rcases he' with ⟨hb, hprofile, _, _, _, _⟩
    refine ⟨hb, ?_⟩
    exact (startGuard_iff_actualProfileGuard ids rewards C_star C_h eta s b
      hcompleted hnotStopped e hb).2 hprofile
  · rintro ⟨hb, hguard⟩
    have hprofile := (startGuard_iff_actualProfileGuard ids rewards C_star C_h eta s b
      hcompleted hnotStopped e hb).1 hguard
    have hfieldsProfile := GeneratedBlockGuardLaw.actualProcessedProfile_eq_generatedProfile
      p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
    have hfieldsTarget := GeneratedBlockGuardLaw.actualProcessedTarget_eq_generatedTarget
      p s ids rewards C_star C_h eta b hcompleted hnotStopped e hb
    simp only [allInactiveBoundaryEvent, GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent,
      Set.mem_ofPred_eq, Set.mem_univ]
    exact ⟨hb, hprofile, trivial, trivial, hfieldsProfile, hfieldsTarget⟩

theorem measurableSet_allInactiveBoundaryEvent_at_blockStart (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) :
    MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (blockStartRound s).val]
      (allInactiveBoundaryEvent ids rewards C_star C_h eta s b hcompleted hnotStopped) := by
  rw [allInactiveBoundaryEvent_eq_inter_startGuard]
  have hB := measurableSet_boundaryEvent_at_blockStart (p := p) ids rewards C_star C_h eta s b
  have ht := blockStartRound_mem (p := p) s
  have hguard := GeneratedDownConditionalMean.actual_allInactiveGuard_measurable
    ids rewards C_star C_h eta s (blockStartRound s) ht
  have hguardSet : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p
      (blockStartRound s).val]
      {e | GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
          (blockStartRound s) e) = true} := by
    exact (measurableSet_singleton true).preimage hguard
  exact hB.inter hguardSet

private theorem processedAllInactive_persists (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b)
    (hstart : GeneratedDownConditionalMean.processedAllInactive
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
        (blockStartRound s) e) = true) :
    ∀ t ∈ calendarBlock p s,
      GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true := by
  intro t ht
  have hdesc := descriptor_processed_on_boundary ids rewards C_star C_h eta s b
    hcompleted hnotStopped e hb t
  have hstartDesc := descriptor_processed_on_boundary ids rewards C_star C_h eta s b
    hcompleted hnotStopped e hb (blockStartRound s)
  rw [hstartDesc] at hstart
  rw [hdesc]
  simpa [GeneratedDownConditionalMean.processedAllInactive,
    GeneratedDownConditionalMean.descriptorAllInactive] using hstart

/-- The block-start inactivity test is the same actual incoming profile used
by every generated descriptor in the processed block. -/
theorem processedAllInactive_persists_on_block (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b)
    (hstart : GeneratedDownConditionalMean.processedAllInactive
      (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s
        (blockStartRound s) e) = true) :
    ∀ t ∈ calendarBlock p s,
      GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true :=
  processedAllInactive_persists ids rewards C_star C_h eta s b hcompleted hnotStopped e hb hstart

/-! ## Pointwise identity with the actual run and monitor -/

/-- On the actual processed boundary atom, the generated sum is exactly the
sum of the actual coordinator `downArm` indicators on the whole clipped block.
The descriptor reconstruction includes all rounds through a launch-triggering
block's last update. -/
theorem downBlockTest_eq_downArm_sum_on_boundary (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    downBlockTest p ids rewards C_star C_h eta s a e =
      ∑ t ∈ calendarBlock p s,
        if ReferenceInitializationRun.downArm
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) t = some a then 1 else 0 := by
  unfold downBlockTest
  apply Finset.sum_congr rfl
  intro t ht
  have hdesc := descriptor_processed_on_boundary ids rewards C_star C_h eta s b
    hcompleted hnotStopped e hb t
  have hbridge := GeneratedDownConditionalMean.actual_downPositive_descriptor_bridge
    ids rewards C_star C_h eta s t a e b
    (BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators b.weight_ge_one e.2)
    ((ReferenceInitializationRun.physical
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
      (by rw [hcompleted]; exact s.isLt)).target)
    (BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
        (by rw [hcompleted]; exact s.isLt)) t.val) hdesc
  rcases hbridge with ⟨_, _, _, _, _, _, _, htest⟩
  exact htest

private theorem real_calendar_downArm_sum_eq_nat_cast (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (a : Fin p.K) :
    (∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
      if ReferenceInitializationRun.downArm x b h t = some a then (1 : ℝ) else 0) =
    ((∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
      if ReferenceInitializationRun.downArm x b h t = some a then (1 : ℕ) else 0 : ℕ) : ℝ) := by
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Casting the finite indicator sum identifies `Z_s(a)` with the accepted
actual monitor's per-arm `historyBlockCount`. -/
theorem downBlockTest_eq_historyBlockCount_on_boundary (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (e : Coordinates p)
    (hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    downBlockTest p ids rewards C_star C_h eta s a e =
      (GeneratedBootstrapMonitor.historyBlockCount
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        (ReferenceInitializationRun.elapsed p (b.completed + 1))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        (ReferenceInitializationRun.extendedHistory
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) (coordinator p.two_le_m))
        (ReferenceInitializationRun.nextBlock b (by rw [hcompleted]; exact s.isLt))
        (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd
          b (by rw [hcompleted]; exact s.isLt)]) a : ℝ) := by
  have hnext : ReferenceInitializationRun.nextBlock b
      (by rw [hcompleted]; exact s.isLt) = s := by
    apply Fin.ext
    exact hcompleted
  have hcal : calendarBlock p s = calendarBlock p
      (ReferenceInitializationRun.nextBlock b (by rw [hcompleted]; exact s.isLt)) := by
    rw [hnext]
  rw [downBlockTest_eq_downArm_sum_on_boundary ids rewards C_star C_h eta s a b
    hcompleted hnotStopped e hb]
  calc
    _ = (∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b
          (by rw [hcompleted]; exact s.isLt)),
        if ReferenceInitializationRun.downArm
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) t = some a then (1 : ℝ) else 0) := by
      rw [hcal]
    _ = ((∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b
          (by rw [hcompleted]; exact s.isLt)),
        if ReferenceInitializationRun.downArm
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) t = some a then (1 : ℕ) else 0 : ℕ) : ℝ) :=
      real_calendar_downArm_sum_eq_nat_cast _ _ _ _
    _ = (GeneratedBootstrapMonitor.historyBlockCount
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        (ReferenceInitializationRun.elapsed p (b.completed + 1))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        (ReferenceInitializationRun.extendedHistory
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) (coordinator p.two_le_m))
        (ReferenceInitializationRun.nextBlock b (by rw [hcompleted]; exact s.isLt))
        (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd
          b (by rw [hcompleted]; exact s.isLt)]) a : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ))
        (GeneratedDownConditionalMean.downArm_calendar_sum_eq_historyBlockCount
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) a)

/-- The cast block count is precisely the increment in the actual accepted
per-arm coordinator counter, including the first overflow update. -/
theorem updatedCounters_eq_old_add_historyBlockCount (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (_hnotStopped : b.crossing = none)
    (e : Coordinates p)
    (_hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b) :
    ReferenceInitializationRun.updatedCounters
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
        (by rw [hcompleted]; exact s.isLt) a =
      b.counters a + GeneratedBootstrapMonitor.historyBlockCount
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        (ReferenceInitializationRun.elapsed p (b.completed + 1))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        (ReferenceInitializationRun.extendedHistory
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b
          (by rw [hcompleted]; exact s.isLt) (coordinator p.two_le_m))
        (ReferenceInitializationRun.nextBlock b (by rw [hcompleted]; exact s.isLt))
        (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd
          b (by rw [hcompleted]; exact s.isLt)]) a := by
  rw [ReferenceInitializationRun.updatedCounters_eq_credit_fold]
  simp only [BootstrapLaunchMonitor.creditCounter, zero_add]
  rw [GeneratedDownConditionalMean.downArm_calendar_sum_eq_historyBlockCount]

/-- If the actual stopped run has already crossed, every calendar test is the
accepted descriptor `none` zero. No physical postlaunch trace is supplied. -/
theorem downBlockTest_eq_zero_when_stopped (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p)
    (hstopped : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing ≠ none) :
    downBlockTest p ids rewards C_star C_h eta s a e = 0 := by
  unfold downBlockTest
  apply Finset.sum_eq_zero
  intro t ht
  have hnone := (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff
    ids rewards C_star C_h eta s t e).2 hstopped
  simp [GeneratedBootstrapFiltration.testValue,
    GeneratedDownConditionalMean.downPositiveCurrentTest, hnone]

/-! ## The tower step on a genuine past event -/

private theorem setIntegral_round_lower_on_inactive (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (a : Fin p.K)
    (A : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A)
    (hguard : ∀ e ∈ A,
      GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true) :
    (GeneratedDownConditionalMean.rewardSupport rewards t a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      ∫ e in A,
        GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a) e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  let f := GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
    (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a)
  have hf : Integrable f (GeneratedBootstrapRoundLaw.originalLaw p) :=
    GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
      C_star C_h eta s t ht a
  have hce := GeneratedDownConditionalMean.actual_downPositive_condExp_lower_on_allInactive
    ids rewards C_star C_h eta s t ht a
  have hAambient : MeasurableSet A :=
    (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) A hA
  have hceRestrict :
      (fun _ : Coordinates p => GeneratedDownConditionalMean.rewardSupport rewards t a /
        (16 * (p.K : ℝ))) ≤ᵐ[(GeneratedBootstrapRoundLaw.originalLaw p).restrict A]
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f := by
    change ∀ᵐ e ∂(GeneratedBootstrapRoundLaw.originalLaw p).restrict A,
      GeneratedDownConditionalMean.rewardSupport rewards t a / (16 * (p.K : ℝ)) ≤
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
    apply (ae_restrict_iff' (μ := GeneratedBootstrapRoundLaw.originalLaw p)
      (s := A) hAambient).2
    filter_upwards [hce] with e he hmem
    exact he (hguard e hmem)
  have hcei : Integrable
      (condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f)
      (GeneratedBootstrapRoundLaw.originalLaw p) := integrable_condExp
  have hconstInt : IntegrableOn
      (fun _ : Coordinates p => GeneratedDownConditionalMean.rewardSupport rewards t a /
        (16 * (p.K : ℝ))) A (GeneratedBootstrapRoundLaw.originalLaw p) := by
    exact (integrable_const _).integrableOn
  have hceOn : IntegrableOn
      (fun e : Coordinates p => condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e) A
      (GeneratedBootstrapRoundLaw.originalLaw p) := hcei.integrableOn
  have hmono := setIntegral_mono_ae_restrict
    hconstInt hceOn hceRestrict
  have hmono' :
      ∫ e in A, (GeneratedDownConditionalMean.rewardSupport rewards t a /
        (16 * (p.K : ℝ))) ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      ∫ e in A, condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono
  calc
    (GeneratedDownConditionalMean.rewardSupport rewards t a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A =
      ∫ e in A, (GeneratedDownConditionalMean.rewardSupport rewards t a /
        (16 * (p.K : ℝ))) ∂GeneratedBootstrapRoundLaw.originalLaw p := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
          ring
    _ ≤ ∫ e in A,
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono'
    _ = ∫ e in A, f e ∂GeneratedBootstrapRoundLaw.originalLaw p :=
      setIntegral_condExp (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) hf hA

private theorem setIntegral_round_upper (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (a : Fin p.K)
    (A : Set (Coordinates p))
    (hA : MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A) :
    ∫ e in A,
        GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
          (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a) e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      (GeneratedDownConditionalMean.rewardSupport rewards t a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
  let f := GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
    (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a)
  have hf : Integrable f (GeneratedBootstrapRoundLaw.originalLaw p) :=
    GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
      C_star C_h eta s t ht a
  have hce := GeneratedDownConditionalMean.actual_downPositive_condExp_upper
    ids rewards C_star C_h eta s t ht a
  have hAambient : MeasurableSet A :=
    (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) A hA
  have hceRestrict :
      condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f ≤ᵐ[
          (GeneratedBootstrapRoundLaw.originalLaw p).restrict A]
        fun _ => GeneratedDownConditionalMean.rewardSupport rewards t a / (p.K : ℝ) := by
    change ∀ᵐ e ∂(GeneratedBootstrapRoundLaw.originalLaw p).restrict A,
      condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e ≤
        GeneratedDownConditionalMean.rewardSupport rewards t a / (p.K : ℝ)
    apply (ae_restrict_iff' (μ := GeneratedBootstrapRoundLaw.originalLaw p)
      (s := A) hAambient).2
    filter_upwards [hce] with e he hmem
    exact he
  have hcei : Integrable
      (condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f)
      (GeneratedBootstrapRoundLaw.originalLaw p) := integrable_condExp
  have hceOn : IntegrableOn
      (fun e : Coordinates p => condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e) A
      (GeneratedBootstrapRoundLaw.originalLaw p) := hcei.integrableOn
  have hconstInt : IntegrableOn
      (fun _ : Coordinates p => GeneratedDownConditionalMean.rewardSupport rewards t a /
        (p.K : ℝ)) A (GeneratedBootstrapRoundLaw.originalLaw p) := by
    exact (integrable_const _).integrableOn
  have hmono := setIntegral_mono_ae_restrict
    hceOn hconstInt hceRestrict
  have hmono' :
      ∫ e in A, condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
        (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      ∫ e in A, (GeneratedDownConditionalMean.rewardSupport rewards t a /
        (p.K : ℝ)) ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono
  calc
    _ = ∫ e in A,
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p) f e
        ∂GeneratedBootstrapRoundLaw.originalLaw p :=
      (setIntegral_condExp (GeneratedBootstrapFiltration.analysisFiltration_le p t.val) hf hA).symm
    _ ≤ ∫ e in A, (GeneratedDownConditionalMean.rewardSupport rewards t a /
        (p.K : ℝ)) ∂GeneratedBootstrapRoundLaw.originalLaw p := hmono'
    _ = (GeneratedDownConditionalMean.rewardSupport rewards t a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
          ring

private theorem integrable_downBlockTestOn (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (A : Set (Coordinates p)) :
    IntegrableOn (downBlockTest p ids rewards C_star C_h eta s a) A
      (GeneratedBootstrapRoundLaw.originalLaw p) :=
  (integrable_downBlockTest ids rewards C_star C_h eta s a).integrableOn

private theorem setIntegral_downBlockTest_eq_sum (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (A : Set (Coordinates p)) :
    ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p =
      ∑ t ∈ calendarBlock p s,
        ∫ e in A,
          GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
            (GeneratedDownConditionalMean.downPositiveCurrentTest ids rewards s t a) e
          ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  unfold downBlockTest
  rw [integral_finsetSum]
  intro t ht
  exact (GeneratedDownConditionalMean.integrable_downPositiveCurrentTest ids rewards
    C_star C_h eta s t ht a).integrableOn

private theorem rewardSupport_nonneg (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : 0 ≤ GeneratedDownConditionalMean.rewardSupport rewards t a := by
  unfold GeneratedDownConditionalMean.rewardSupport BootstrapDownCountMean.rewardSupport
  split_ifs <;> norm_num

private theorem rewardSupportCount_nonneg (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    0 ≤ BootstrapDownCountMean.rewardSupportCount p s rewards a := by
  unfold BootstrapDownCountMean.rewardSupportCount
  apply Finset.sum_nonneg
  intro t ht
  exact rewardSupport_nonneg rewards t a

private theorem setIntegral_downBlockTest_lower_on_guard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (A : Set (Coordinates p))
    (hA : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A)
    (hguard : ∀ e ∈ A, ∀ t ∈ calendarBlock p s,
      GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true) :
    (BootstrapDownCountMean.rewardSupportCount p s rewards a / (16 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A ≤
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  have hsum := setIntegral_downBlockTest_eq_sum ids rewards C_star C_h eta s a A
  rw [hsum]
  rw [BootstrapDownCountMean.rewardSupportCount, Finset.sum_div]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  exact setIntegral_round_lower_on_inactive ids rewards C_star C_h eta s t ht a A
    (hA t ht) (fun e he => hguard e he t ht)

private theorem setIntegral_downBlockTest_upper (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (A : Set (Coordinates p))
    (hA : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A) :
    ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      (BootstrapDownCountMean.rewardSupportCount p s rewards a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
  have hsum := setIntegral_downBlockTest_eq_sum ids rewards C_star C_h eta s a A
  rw [hsum]
  rw [BootstrapDownCountMean.rewardSupportCount, Finset.sum_div]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  exact setIntegral_round_upper ids rewards C_star C_h eta s t ht a A (hA t ht)

/-! ## Averaging the original activity coins after the tower step -/

private theorem allInactiveBoundary_mass_ge_quarter (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none) :
    (1 / 4 : ℝ) * (GeneratedBootstrapRoundLaw.originalLaw p).real
        (boundaryEvent ids rewards C_star C_h eta s b) ≤
      (GeneratedBootstrapRoundLaw.originalLaw p).real
        (allInactiveBoundaryEvent ids rewards C_star C_h eta s b hcompleted hnotStopped) := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let q : ℝ := (1 - 1 / (p.m : ℝ)) ^
    (GeneratedBlockGuardLaw.sourceIncomingFinset p b).card
  have hqquarter : (1 / 4 : ℝ) ≤ q := by
    dsimp [q]
    exact GeneratedBlockGuardLaw.allIncomingInactive_probability_ge_quarter p b
  have hqnonneg : 0 ≤ q := le_trans (by norm_num) hqquarter
  have hjoint := GeneratedBlockGuardLaw.allIncomingInactive_joint_future_law
    p s ids rewards C_star C_h eta b hcompleted hnotStopped Set.univ MeasurableSet.univ
  have hExact : μ (allInactiveBoundaryEvent ids rewards C_star C_h eta s b
      hcompleted hnotStopped) =
      μ (boundaryEvent ids rewards C_star C_h eta s b) * ENNReal.ofReal q := by
    change GeneratedBlockStartLaw.originalCoordinatesLaw p
        (GeneratedBlockGuardLaw.generatedProcessedGuardFutureEvent p s ids rewards
          C_star C_h eta b hcompleted hnotStopped
          (GeneratedBlockGuardLaw.allIncomingInactiveGuard p b) Set.univ Set.univ) = _
    rw [hjoint]
    simp [μ, q, boundaryEvent, GeneratedBlockStartLaw.originalCoordinatesLaw,
      GeneratedBootstrapRoundLaw.originalLaw]
  have hreal : μ.real (allInactiveBoundaryEvent ids rewards C_star C_h eta s b
      hcompleted hnotStopped) =
      μ.real (boundaryEvent ids rewards C_star C_h eta s b) * q := by
    change ENNReal.toReal (μ (allInactiveBoundaryEvent ids rewards C_star C_h eta s b
      hcompleted hnotStopped)) =
      ENNReal.toReal (μ (boundaryEvent ids rewards C_star C_h eta s b)) * q
    rw [hExact, ENNReal.toReal_mul, ENNReal.toReal_ofReal hqnonneg]
  calc
    (1 / 4 : ℝ) * μ.real (boundaryEvent ids rewards C_star C_h eta s b) ≤
        q * μ.real (boundaryEvent ids rewards C_star C_h eta s b) :=
      mul_le_mul_of_nonneg_right hqquarter MeasureTheory.measureReal_nonneg
    _ = μ.real (allInactiveBoundaryEvent ids rewards C_star C_h eta s b
        hcompleted hnotStopped) := by rw [hreal]; ring

/-- The two unnormalized actual generated coordinator DOWN-positive block
expectation bounds on a genuine processed boundary atom. The lower step first
uses the round-past tower on the actual all-inactive guard and only then
averages the original block activity coins through the accepted guard law.
No boundary-mass positivity or event-mass division is assumed. -/
theorem boundary_atom_expectation_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none) :
    (roundedPositiveCount p s rewards a / (64 * (p.K : ℝ))) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real
          (boundaryEvent ids rewards C_star C_h eta s b) ≤
      ∫ e in boundaryEvent ids rewards C_star C_h eta s b,
        downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ∧
    ∫ e in boundaryEvent ids rewards C_star C_h eta s b,
        downBlockTest p ids rewards C_star C_h eta s a e
        ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
      (roundedPositiveCount p s rewards a / (p.K : ℝ)) *
        (GeneratedBootstrapRoundLaw.originalLaw p).real
          (boundaryEvent ids rewards C_star C_h eta s b) := by
  rw [roundedPositiveCount_eq_rewardSupportCount s rewards a]
  let B := boundaryEvent ids rewards C_star C_h eta s b
  let A := allInactiveBoundaryEvent ids rewards C_star C_h eta s b hcompleted hnotStopped
  have hBstart := measurableSet_boundaryEvent_at_blockStart (p := p)
    ids rewards C_star C_h eta s b
  have hAstart := measurableSet_allInactiveBoundaryEvent_at_blockStart (p := p)
    ids rewards C_star C_h eta s b hcompleted hnotStopped
  have hB : MeasurableSet B :=
    (GeneratedBootstrapFiltration.analysisFiltration_le p
      (blockStartRound s).val) B hBstart
  have hAB : A ⊆ B := by
    intro e he
    have he' : e ∈ allInactiveBoundaryEvent ids rewards C_star C_h eta s b
        hcompleted hnotStopped := by simpa [A] using he
    rw [allInactiveBoundaryEvent_eq_inter_startGuard] at he'
    exact he'.1
  have hAAt : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] A := by
    intro t ht
    have hmon := (GeneratedBootstrapFiltration.analysisFiltration p).mono
      ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).1
    exact hmon A hAstart
  have hBAt : ∀ t ∈ calendarBlock p s,
      MeasurableSet[GeneratedBootstrapFiltration.analysisFiltration p t.val] B := by
    intro t ht
    have hmon := (GeneratedBootstrapFiltration.analysisFiltration p).mono
      ((BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht).1
    exact hmon B hBstart
  have hguard : ∀ e ∈ A, ∀ t ∈ calendarBlock p s,
      GeneratedDownConditionalMean.processedAllInactive
        (GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e) = true := by
    intro e he t ht
    have he' : e ∈ allInactiveBoundaryEvent ids rewards C_star C_h eta s b
        hcompleted hnotStopped := by simpa [A] using he
    rw [allInactiveBoundaryEvent_eq_inter_startGuard] at he'
    exact processedAllInactive_persists_on_block ids rewards C_star C_h eta s b
      hcompleted hnotStopped e he'.1 he'.2 t ht
  have hLowerA := setIntegral_downBlockTest_lower_on_guard ids rewards C_star C_h eta
    s a A hAAt hguard
  have hAtoB :
      ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
          ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
        ∫ e in B, downBlockTest p ids rewards C_star C_h eta s a e
          ∂GeneratedBootstrapRoundLaw.originalLaw p := by
    apply setIntegral_mono_set (integrable_downBlockTestOn ids rewards C_star C_h eta s a B)
    · change ∀ᵐ e ∂(GeneratedBootstrapRoundLaw.originalLaw p).restrict B,
        0 ≤ downBlockTest p ids rewards C_star C_h eta s a e
      apply (ae_restrict_iff' hB).2
      filter_upwards with e he
      exact (downBlockTest_nonneg_le_boot ids rewards C_star C_h eta s a e).1
    · exact Filter.Eventually.of_forall (fun e he => hAB he)
  have hUpperB := setIntegral_downBlockTest_upper ids rewards C_star C_h eta s a B hBAt
  have hquarter := allInactiveBoundary_mass_ge_quarter ids rewards C_star C_h eta s b
    hcompleted hnotStopped
  have hSnonneg := rewardSupportCount_nonneg s rewards a
  have hcNonneg :
      0 ≤ BootstrapDownCountMean.rewardSupportCount p s rewards a /
        (16 * (p.K : ℝ)) := by
    positivity
  have hscale :
      (BootstrapDownCountMean.rewardSupportCount p s rewards a / (64 * (p.K : ℝ))) *
          (GeneratedBootstrapRoundLaw.originalLaw p).real B ≤
        (BootstrapDownCountMean.rewardSupportCount p s rewards a / (16 * (p.K : ℝ))) *
          (GeneratedBootstrapRoundLaw.originalLaw p).real A := by
    calc
      _ = (BootstrapDownCountMean.rewardSupportCount p s rewards a /
            (16 * (p.K : ℝ))) *
          ((1 / 4 : ℝ) * (GeneratedBootstrapRoundLaw.originalLaw p).real B) := by
            have hK : (p.K : ℝ) ≠ 0 := (Nat.cast_pos.mpr (K_pos p)).ne'
            field_simp [hK]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hquarter hcNonneg
  constructor
  · calc
      (BootstrapDownCountMean.rewardSupportCount p s rewards a / (64 * (p.K : ℝ))) *
          (GeneratedBootstrapRoundLaw.originalLaw p).real B ≤
        (BootstrapDownCountMean.rewardSupportCount p s rewards a / (16 * (p.K : ℝ))) *
          (GeneratedBootstrapRoundLaw.originalLaw p).real A := hscale
      _ ≤ ∫ e in A, downBlockTest p ids rewards C_star C_h eta s a e
          ∂GeneratedBootstrapRoundLaw.originalLaw p := hLowerA
      _ ≤ ∫ e in B, downBlockTest p ids rewards C_star C_h eta s a e
          ∂GeneratedBootstrapRoundLaw.originalLaw p := hAtoB
  · exact hUpperB

/-- A zero-mass boundary atom has zero restricted block expectation. This
explicitly covers the zero-mass case without dividing by the atom's measure. -/
theorem integral_eq_zero_of_boundary_mass_zero (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (hmass : (GeneratedBootstrapRoundLaw.originalLaw p).real
      (boundaryEvent ids rewards C_star C_h eta s b) = 0) :
    ∫ e in boundaryEvent ids rewards C_star C_h eta s b,
      downBlockTest p ids rewards C_star C_h eta s a e
      ∂GeneratedBootstrapRoundLaw.originalLaw p = 0 := by
  have hbounds := boundary_atom_expectation_bounds ids rewards C_star C_h eta s a b
    hcompleted hnotStopped
  rcases hbounds with ⟨hlower, hupper⟩
  rw [hmass] at hlower hupper
  simp only [mul_zero] at hlower hupper
  exact le_antisymm hupper hlower

theorem boundary_atom_support_is_literal_rounded_count (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    BootstrapDownCountMean.rewardSupportCount p s rewards a =
      roundedPositiveCount p s rewards a :=
  (roundedPositiveCount_eq_rewardSupportCount s rewards a).symm

end Bandits.Support.GeneratedDownBlockBoundaryMean

end
