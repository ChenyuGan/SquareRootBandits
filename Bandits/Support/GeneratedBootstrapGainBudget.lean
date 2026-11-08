/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapPotential
public import Bandits.Support.BootstrapDownCountMean
public import Bandits.Support.BootstrapStartupCostScale

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Generated bootstrap full-gain budget

For the actual stopped initialization run, this module derives the support
domination of full physical stay gain and charges each block either to its
productive indicator or to the original latent activity indicator. The
productive indicator uses the block's pre-block enabled flag, so a block that
completes a declaration or launches remains included. The activity indicator
continues to use the original private block draw after stopping.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:588-589,623-625`
and `sources/zip4/manuscript/07_public_setup.tex:68-109`.

The exported prefix estimate is the deterministic gain-budget input for the
future `GeneratedUninformedPrefixSupport` assembly. Its probability estimates
and the final regret theorem are separate obligations.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators

namespace Bandits.Support.GeneratedBootstrapGainBudget

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The actual pre-block boundary at bootstrap opportunity `s`. -/
def boundaryAt (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) : ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.run x s.val

/-- The actual analysis block at opportunity `s`, including its pre-block
enabled flag and the held arm supplied to the existing weight updater. -/
def blockAt (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) : BootstrapWeightPotential.Block p.K (B_boot p) :=
  GeneratedBootstrapPotential.actualBlock x i s

/-- The full physical stay gain of the actual stopped run at opportunity `s`.
It includes all positive stays in a block that completes or launches. -/
def fullStayGainAt (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) : ℕ :=
  GeneratedBootstrapPotential.actualStoppedFullStayGain x i s

/-- Literal rounded-reward support count on the clipped calendar block. -/
def rewardSupportCountAt (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (a : Fin p.K) : ℝ :=
  BootstrapDownCountMean.rewardSupportCount p s x.rewards a

/-- The literal bootstrap startup threshold for this run's public constant. -/
def startupThreshold (x : ReferenceInitializationRun.Input p) : ℕ :=
  BootstrapStartupCostScale.h_boot x.C_h p

/-- Original block draw for follower `i`, read from the actual boundary
numerators and the original labelled private coordinate, including after the
physical process has stopped. -/
def latentBlockProfileAt (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) :
    PrivateSourceStreams.BlockDraw p :=
  PrivateSourceStreams.blockDrawProfileMap p (boundaryAt x s).numerators
    (boundaryAt x s).weight_ge_one (x.coordinates.1.1 s)
    (BootstrapPhysicalInput.sourceFollowerIndex p i)

/-- The real-valued zero-one indicator of the original latent activity field. -/
def latentActivityIndicator (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) : ℝ :=
  if (latentBlockProfileAt x i s).1 then 1 else 0

/-- The productive zero-one indicator: the actual pre-block analysis block is
enabled and its held arm has support at least the literal startup threshold. -/
def productiveIndicator (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) : ℝ :=
  if (blockAt x i s).enabled = true ∧
      (startupThreshold x : ℝ) ≤
        rewardSupportCountAt x s (blockAt x i s).held
  then 1 else 0

/-- The positive rounded-reward rounds on one actual calendar block and arm. -/
def positiveRewardRounds (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t =>
    0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a)

/-- The real support count is exactly the cast cardinality of its positive
rounded-reward rounds. -/
theorem rewardSupportCountAt_eq_positiveRewardRounds_card
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (a : Fin p.K) :
    rewardSupportCountAt x s a =
      (positiveRewardRounds s x.rewards a).card := by
  unfold rewardSupportCountAt positiveRewardRounds
    BootstrapDownCountMean.rewardSupportCount BootstrapDownCountMean.rewardSupport
  rw [Finset.sum_boole]

/-- Every physical stay round with positive feedback lies in the positive
rounded-reward support of the held arm. On an active ID-zero round, the
existing action rule plays the held arm; positive feedback then forces its
reward entry to be positive. -/
theorem physicalStayRounds_subset_positiveRewardRounds
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (hactive : v.active j = true) :
    BootstrapPhysicalBlock.physicalStayRounds v j ⊆
      positiveRewardRounds s v.rewards (v.held j) := by
  classical
  intro t ht
  change t ∈ (calendarBlock p s).filter
    (fun t => v.ids (v.privateId j) t = false ∧
      0 < BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)) at ht
  rcases Finset.mem_filter.mp ht with ⟨hcalendar, hid, hfeedback⟩
  have haction :
      BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) = v.held j := by
    calc
      _ = BootstrapPhysicalBlock.followerAction v t j :=
        BootstrapPhysicalBlock.actions_follower v (BootstrapPhysicalBlock.run v t.val) t j
      _ = BootstrapPhysicalBlock.uninformedAction v t j := by
        simp only [BootstrapPhysicalBlock.followerAction, dite_eq_left j.property]
      _ = v.held j := BootstrapPhysicalBlock.uninformedAction_stay v t j hactive hid
  have hfree : FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t)
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) :=
    FiniteBanditModel.collisionFreeFor_of_playerFeedback_pos
      _ _ _ hfeedback
  have hfeedback_eq :
      BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) =
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (v.rewards t (v.held j)) := by
    simp [BootstrapPhysicalBlock.feedback, FiniteBanditModel.playerFeedback,
      hfree, haction]
  have hrewards :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (v.rewards t (v.held j)) := by
    rw [← hfeedback_eq]
    exact hfeedback
  exact Finset.mem_filter.mpr ⟨hcalendar, hrewards⟩

/-- Each real support count is nonnegative. -/
theorem rewardSupportCountAt_nonneg
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (a : Fin p.K) : 0 ≤ rewardSupportCountAt x s a := by
  unfold rewardSupportCountAt BootstrapDownCountMean.rewardSupportCount
    BootstrapDownCountMean.rewardSupport
  apply Finset.sum_nonneg
  intro t ht
  split_ifs <;> norm_num

/-- The original activity indicator always lies in the unit interval. -/
theorem latentActivityIndicator_mem_unitInterval
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) : latentActivityIndicator x i s ∈ Set.Icc (0 : ℝ) 1 := by
  unfold latentActivityIndicator
  split_ifs <;> norm_num

/-- The original activity indicator is nonnegative, even when its draw is
continued after physical stopping. -/
theorem latentActivityIndicator_nonneg
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) : 0 ≤ latentActivityIndicator x i s :=
  (latentActivityIndicator_mem_unitInterval x i s).1

/-- The actual full stay gain is bounded by the actual rounded-reward support
on the analysis block's held arm. No support domination is assumed. -/
theorem fullStayGainAt_le_rewardSupportCount
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    (fullStayGainAt x i s : ℝ) ≤
      rewardSupportCountAt x s (blockAt x i s).held := by
  classical
  let b := ReferenceInitializationRun.run x s.val
  by_cases hcross : b.crossing = none
  · have hcrossRun :
        (ReferenceInitializationRun.run x s.val).crossing = none := by
      simpa [boundaryAt, b] using hcross
    by_cases hinformed : i ∈ ReferenceInitializationRun.uninformed b
    · have hcompleted :=
        GeneratedBootstrapPotential.completed_eq_of_no_crossing x s.val s.isLt.le hcross
      have hprocessed : b.completed < n_boot p := by
        change (ReferenceInitializationRun.run x s.val).completed < n_boot p
        rw [hcompleted]
        exact s.isLt
      have hnext : ReferenceInitializationRun.nextBlock b hprocessed = s := by
        apply Fin.ext
        dsimp [ReferenceInitializationRun.nextBlock]
        exact hcompleted
      let j : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i, hinformed⟩
      have hinformedRun : i ∈ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run x s.val) := by
        simpa [boundaryAt, b] using hinformed
      let v : BootstrapPhysicalBlock.Input p (ReferenceInitializationRun.nextBlock b hprocessed) :=
        ReferenceInitializationRun.physical x b hprocessed
      have hgain : fullStayGainAt x i s =
          BootstrapPhysicalBlock.physicalStayGain v j := by
        simp only [fullStayGainAt, GeneratedBootstrapPotential.actualStoppedFullStayGain,
          hcrossRun, hinformedRun]
        rfl
      have hheldLatent : (blockAt x i s).held =
          GeneratedBootstrapPotential.actualLatentHeldArm x b s i :=
        GeneratedBootstrapPotential.actualBlock_held_eq_actualLatentHeldArm x i s
      have hphysicalHeld :=
        GeneratedBootstrapPotential.physical_held_eq_actualLatentHeldArm x b hprocessed j
      unfold GeneratedBootstrapPotential.actualLatentHeldArm at hphysicalHeld
      have hcoordinate : x.coordinates.1.1
          (ReferenceInitializationRun.nextBlock b hprocessed) =
            x.coordinates.1.1 s := congrArg (fun q => x.coordinates.1.1 q) hnext
      rw [hcoordinate] at hphysicalHeld
      have hphysicalHeld' : v.held j =
          GeneratedBootstrapPotential.actualLatentHeldArm x b s i := by
        unfold GeneratedBootstrapPotential.actualLatentHeldArm
        simpa [v, j] using hphysicalHeld
      have hheld : (blockAt x i s).held = v.held j := by
        exact hheldLatent.trans hphysicalHeld'.symm
      by_cases hactive : v.active j = true
      · have hsubsetAtNext := physicalStayRounds_subset_positiveRewardRounds v j hactive
        have hsubset : BootstrapPhysicalBlock.physicalStayRounds v j ⊆
            positiveRewardRounds s x.rewards (v.held j) := by
          simpa [v, ReferenceInitializationRun.physical,
            BootstrapPhysicalInput.blockInput, hnext] using hsubsetAtNext
        have hsupport := rewardSupportCountAt_eq_positiveRewardRounds_card
          x s (blockAt x i s).held
        rw [hheld] at hsupport
        calc
          (fullStayGainAt x i s : ℝ) =
              (BootstrapPhysicalBlock.physicalStayGain v j : ℝ) := by rw [hgain]
          _ = (BootstrapPhysicalBlock.physicalStayRounds v j).card := by
            simp [BootstrapPhysicalBlock.physicalStayGain, hactive]
          _ ≤ (positiveRewardRounds s x.rewards (v.held j)).card := by
            exact_mod_cast Finset.card_le_card hsubset
          _ = rewardSupportCountAt x s (blockAt x i s).held := by
            rw [hheld]
            exact hsupport.symm
      · rw [hgain]
        simp [BootstrapPhysicalBlock.physicalStayGain, hactive]
        exact rewardSupportCountAt_nonneg x s (blockAt x i s).held
    · have hinformedRun : i ∉ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run x s.val) := by
        simpa [boundaryAt, b] using hinformed
      simp [fullStayGainAt, GeneratedBootstrapPotential.actualStoppedFullStayGain,
        hcrossRun, hinformedRun]
      exact rewardSupportCountAt_nonneg x s (blockAt x i s).held
  · have hnotcrossRun :
        (ReferenceInitializationRun.run x s.val).crossing ≠ none := by
      simpa [boundaryAt, b] using hcross
    simp [fullStayGainAt, GeneratedBootstrapPotential.actualStoppedFullStayGain,
      hnotcrossRun]
    exact rewardSupportCountAt_nonneg x s (blockAt x i s).held

/-- If the generated analysis block is enabled, its physical activity field is
the original latent activity draw at that opportunity. -/
theorem latentBlockProfileAt_active_eq_true_of_blockAt_enabled
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) (henabled : (blockAt x i s).enabled = true) :
    (latentBlockProfileAt x i s).1 = true := by
  classical
  let b := ReferenceInitializationRun.run x s.val
  by_cases hcross : b.crossing = none
  · have hcrossRun :
        (ReferenceInitializationRun.run x s.val).crossing = none := by
      simpa [boundaryAt, b] using hcross
    by_cases hinformed : i ∈ ReferenceInitializationRun.uninformed b
    · have hcompleted :=
        GeneratedBootstrapPotential.completed_eq_of_no_crossing x s.val s.isLt.le hcross
      have hprocessed : b.completed < n_boot p := by
        change (ReferenceInitializationRun.run x s.val).completed < n_boot p
        rw [hcompleted]
        exact s.isLt
      have hnext : ReferenceInitializationRun.nextBlock b hprocessed = s := by
        apply Fin.ext
        dsimp [ReferenceInitializationRun.nextBlock]
        exact hcompleted
      let j : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i, hinformed⟩
      have hActualEnabled :
          (GeneratedBootstrapPotential.actualBlock x i s).enabled = true := by
        simpa only [blockAt] using henabled
      have hweightEnabled :
          (ReferenceInitializationRun.weightInput x b hprocessed j).enabled = true := by
        have hblock := GeneratedBootstrapPotential.actualBlock_eq_weightInput
          x i s hcross hinformed
        rw [hblock] at hActualEnabled
        exact hActualEnabled
      have htraceEnabled :
          BootstrapBlockConstruction.blockEnabled
            (BootstrapTruePrefixController.observationTrace
              (ReferenceInitializationRun.physical x b hprocessed) j false)
            (ReferenceInitializationRun.nextBlock b hprocessed) = true := by
        change (ReferenceInitializationRun.weightInput x b hprocessed j).enabled = true
        exact hweightEnabled
      have htraceParts := htraceEnabled
      simp only [BootstrapBlockConstruction.blockEnabled, Bool.and_eq_true] at htraceParts
      have htraceActive :
          (BootstrapTruePrefixController.observationTrace
            (ReferenceInitializationRun.physical x b hprocessed) j false).active
            (ReferenceInitializationRun.nextBlock b hprocessed) = true := htraceParts.1
      have hphysicalActive :
          (ReferenceInitializationRun.physical x b hprocessed).active j = true := by
        simpa [BootstrapTruePrefixController.observationTrace,
          BootstrapPhysicalBlock.observationTrace] using htraceActive
      have hdraw := ReferenceInitializationRun.physical_own_block_draw x b hprocessed j
      have hdrawActive :
          (ReferenceInitializationRun.physical x b hprocessed).active j =
            (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
              (x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b hprocessed))
              (BootstrapPhysicalInput.sourceFollowerIndex p j.val)).1 := by
        simpa only [Prod.fst] using congrArg (fun q => q.1) hdraw
      have hprofile : (latentBlockProfileAt x i s).1 =
          (ReferenceInitializationRun.physical x b hprocessed).active j := by
        have hcoordinate : x.coordinates.1.1
            (ReferenceInitializationRun.nextBlock b hprocessed) =
              x.coordinates.1.1 s := congrArg (fun q => x.coordinates.1.1 q) hnext
        rw [hcoordinate] at hdrawActive
        simpa [latentBlockProfileAt, boundaryAt, b, j] using hdrawActive.symm
      rw [hphysicalActive] at hprofile
      exact hprofile
    · have hnotinformedRun : i ∉ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run x s.val) := by
        simpa [boundaryAt, b] using hinformed
      have hdisabled : (blockAt x i s).enabled = false := by
        simp [blockAt, GeneratedBootstrapPotential.actualBlock,
          hcrossRun, hnotinformedRun]
      rw [hdisabled] at henabled
      cases henabled
  · have hnotcrossRun :
        (ReferenceInitializationRun.run x s.val).crossing ≠ none := by
      simpa [boundaryAt, b] using hcross
    have hdisabled : (blockAt x i s).enabled = false := by
      simp [blockAt, GeneratedBootstrapPotential.actualBlock, hnotcrossRun]
    rw [hdisabled] at henabled
    cases henabled

/-- The productive indicator is dominated by the original latent activity
indicator, including after later stopping because the latter retains its draw. -/
theorem productiveIndicator_le_latentActivityIndicator
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    productiveIndicator x i s ≤ latentActivityIndicator x i s := by
  by_cases hproductive : (blockAt x i s).enabled = true ∧
      (startupThreshold x : ℝ) ≤
        rewardSupportCountAt x s (blockAt x i s).held
  · have hactive := latentBlockProfileAt_active_eq_true_of_blockAt_enabled
      x i s hproductive.1
    simp [productiveIndicator, latentActivityIndicator, hproductive, hactive]
  · simp [productiveIndicator, hproductive]
    exact latentActivityIndicator_nonneg x i s

/-- The actual full-gain budget for one block. A productive block is charged
at most `B_boot`; every other enabled block has gain below the startup
threshold and is charged to its original latent activity. -/
theorem fullStayGainAt_le_indicatorBudget
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    (fullStayGainAt x i s : ℝ) ≤
      (B_boot p : ℝ) * productiveIndicator x i s +
        (startupThreshold x : ℝ) *
          latentActivityIndicator x i s := by
  by_cases hproductive : (blockAt x i s).enabled = true ∧
      (startupThreshold x : ℝ) ≤
        rewardSupportCountAt x s (blockAt x i s).held
  · have hP : productiveIndicator x i s = 1 := by
      simp [productiveIndicator, hproductive]
    have hA : latentActivityIndicator x i s = 1 := by
      have hPA := productiveIndicator_le_latentActivityIndicator x i s
      have hA_le : latentActivityIndicator x i s ≤ 1 := by
        exact (latentActivityIndicator_mem_unitInterval x i s).2
      rw [hP] at hPA
      linarith
    have hgain_eq : fullStayGainAt x i s = (blockAt x i s).gain := by
      have heffective := GeneratedBootstrapPotential.actualBlock_effectiveGain_eq_actualStoppedFullStayGain
        x i s
      have hEnabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = true := by
        simpa only [blockAt] using hproductive.1
      rw [BootstrapWeightPotential.effectiveGain] at heffective
      rw [hEnabled] at heffective
      simpa [fullStayGainAt, blockAt] using heffective.symm
    rw [hP, hA, hgain_eq]
    have hgain_le : ((blockAt x i s).gain : ℝ) ≤ (B_boot p : ℝ) :=
      Nat.cast_le.mpr (blockAt x i s).gain_le
    have hB_nonneg : 0 ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
    have hh_nonneg : 0 ≤ (startupThreshold x : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  · have hP : productiveIndicator x i s = 0 := by
      simp [productiveIndicator, hproductive]
    by_cases henabled : (blockAt x i s).enabled = true
    · have hA : latentActivityIndicator x i s = 1 :=
        by
          have hactive := latentBlockProfileAt_active_eq_true_of_blockAt_enabled
            x i s henabled
          simp [latentActivityIndicator, hactive]
      have hnotthreshold :
          ¬ ((startupThreshold x : ℝ) ≤
            rewardSupportCountAt x s (blockAt x i s).held) := by
        intro hthreshold
        exact hproductive ⟨henabled, hthreshold⟩
      have hsupport_lt :
          rewardSupportCountAt x s (blockAt x i s).held <
            (startupThreshold x : ℝ) :=
        lt_of_not_ge hnotthreshold
      have hgain_support := fullStayGainAt_le_rewardSupportCount x i s
      rw [hP, hA]
      linarith
    · cases hblockEnabled : (blockAt x i s).enabled with
      | false =>
          have hgain_zero : fullStayGainAt x i s = 0 := by
            have heffective :=
              (GeneratedBootstrapPotential.actualBlock_effectiveGain_eq_actualStoppedFullStayGain
                x i s).symm
            have hEnabled :
                (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
              simpa only [blockAt] using hblockEnabled
            rw [BootstrapWeightPotential.effectiveGain] at heffective
            rw [hEnabled] at heffective
            simpa [fullStayGainAt] using heffective
          have hA_nonneg := latentActivityIndicator_nonneg x i s
          simp only [hP, hgain_zero, Nat.cast_zero, mul_zero, zero_add]
          exact mul_nonneg (Nat.cast_nonneg _) hA_nonneg
      | true => exact (henabled hblockEnabled).elim

/-- For every prefix of the actual stopped initialization run, total full
stay gain is charged by the actual productive blocks and the original latent
activity draws. This deterministic budget is ready for the future
`GeneratedUninformedPrefixSupport` probability assembly. -/
theorem fullStayGain_prefix_budget
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p) :
    (∑ s : Fin r,
      (fullStayGainAt x i ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) ≤
      (B_boot p : ℝ) *
        (∑ s : Fin r, productiveIndicator x i ⟨s.val, s.isLt.trans_le hr⟩) +
      (startupThreshold x : ℝ) *
        (∑ s : Fin r, latentActivityIndicator x i ⟨s.val, s.isLt.trans_le hr⟩) := by
  calc
    (∑ s : Fin r,
        (fullStayGainAt x i ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) ≤
        ∑ s : Fin r,
          ((B_boot p : ℝ) * productiveIndicator x i ⟨s.val, s.isLt.trans_le hr⟩ +
            (startupThreshold x : ℝ) *
              latentActivityIndicator x i ⟨s.val, s.isLt.trans_le hr⟩) :=
      Finset.sum_le_sum fun s hs => fullStayGainAt_le_indicatorBudget x i _
    _ = (B_boot p : ℝ) *
          (∑ s : Fin r, productiveIndicator x i ⟨s.val, s.isLt.trans_le hr⟩) +
        (startupThreshold x : ℝ) *
          (∑ s : Fin r, latentActivityIndicator x i ⟨s.val, s.isLt.trans_le hr⟩) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end Bandits.Support.GeneratedBootstrapGainBudget

end
