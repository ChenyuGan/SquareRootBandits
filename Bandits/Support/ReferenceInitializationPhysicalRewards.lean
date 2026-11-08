/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.ActualReferenceInitializationBlock

import Mathlib.Algebra.BigOperators.Fin

/-!
# Physical rewards in the generated initialization history

Sources: `sources/zip4/manuscript/01_introduction.tex:20-36`,
`sources/zip4/manuscript/07_public_setup.tex:27-114,123-164`,
`sources/zip4/manuscript/08_main_theorem.tex:26-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

This module projects cumulative observed reward from the existing stopped
reference producer. It proves the generated history's physical feedback law,
reward append and range facts, input-coordinate measurability, and the original
source pullback. A padded absent log slot is used only as a measurability
encoding by the imported boundary code; no absent slot is a physical round.
These results do not construct complete reference execution or prove a
postlaunch observable, source law, independence, startup estimate, or regret
theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.BootstrapPhysicalBlock
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceInitializationPhysicalRewards

private abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The sum of the actual stored scalar feedback over the generated physical
prefix. There are no terms for rounds outside `elapsed p b.completed`.
Sources: `01_introduction.tex:30-36` and `07_public_setup.tex:63-94`. -/
def boundaryReward (p : Parameters) (b : ReferenceInitializationRun.Boundary p) : ℝ :=
  ∑ u : Fin (ReferenceInitializationRun.elapsed p b.completed),
    ∑ i : Fin p.m, ((b.history i u).2).val.val

/-- The generated prefix's total observed reward is nonnegative and at most
one unit per player and generated round. The bound is valid for every
well-typed boundary because each stored `Observation` is already in `[0,1]`. -/
theorem boundaryReward_bounds (p : Parameters) (b : ReferenceInitializationRun.Boundary p) :
    boundaryReward p b ∈ Set.Icc 0
      ((p.m : ℝ) * (ReferenceInitializationRun.elapsed p b.completed : ℝ)) := by
  have hvalue (u : Fin (ReferenceInitializationRun.elapsed p b.completed)) (i : Fin p.m) :
      ((b.history i u).2).val.val ∈ Set.Icc (0 : ℝ) 1 :=
    (b.history i u).2.val.property
  constructor
  · unfold boundaryReward
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro i hi
    exact (hvalue u i).1
  · unfold boundaryReward
    calc
      (∑ u : Fin (ReferenceInitializationRun.elapsed p b.completed),
          ∑ i : Fin p.m, ((b.history i u).2).val.val)
          ≤ ∑ u : Fin (ReferenceInitializationRun.elapsed p b.completed), ∑ i : Fin p.m, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro u hu
            apply Finset.sum_le_sum
            intro i hi
            exact (hvalue u i).2
      _ = (ReferenceInitializationRun.elapsed p b.completed : ℝ) * (p.m : ℝ) := by simp
      _ = (p.m : ℝ) * (ReferenceInitializationRun.elapsed p b.completed : ℝ) := mul_comm _ _

/-- The empty initial boundary contains no physical reward. -/
theorem boundaryReward_initial (p : Parameters) :
    boundaryReward p (ReferenceInitializationRun.initial p) = 0 := by
  unfold boundaryReward
  apply Finset.sum_eq_zero
  intro u hu
  have hlen : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.initial p).completed = 0 := by
    simp [ReferenceInitializationRun.initial, ReferenceInitializationRun.elapsed]
  have hfalse : u.val < 0 := by
    rw [← hlen]
    exact u.isLt
  omega

/-- The new contribution in a genuine finish is exactly the simultaneous
feedback sum from that same physical block, at its actual calendar rounds.
The block-offset `u` maps to `blockRound p (nextBlock b h) u`, whose value is
`blockStart + u.val`; this also covers the clipped final block. -/
theorem boundaryReward_finishBlock (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) :
    boundaryReward p (ReferenceInitializationRun.finishBlock x b h) = boundaryReward p b +
      ∑ u : Fin (ReferencePrelaunchPhysicalReplay.blockLength p (ReferenceInitializationRun.nextBlock b h)),
        ∑ i : Fin p.m,
          BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical x b h)
            (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h)
              (ReferencePrelaunchPhysicalReplay.blockRound p (ReferenceInitializationRun.nextBlock b h) u).val)
            (ReferencePrelaunchPhysicalReplay.blockRound p (ReferenceInitializationRun.nextBlock b h) u) i := by
  let s := ReferenceInitializationRun.nextBlock b h
  let v := ReferenceInitializationRun.physical x b h
  let n := ReferenceInitializationRun.elapsed p b.completed
  let q := ReferencePrelaunchPhysicalReplay.blockLength p s
  have hlen : ReferenceInitializationRun.elapsed p (b.completed + 1) = n + q := by
    dsimp [n, q, s]
    rw [ReferenceInitializationRun.elapsed_succ_eq_blockEnd, ReferencePrelaunchPhysicalReplay.blockEnd_eq_start_add_length,
      ReferenceInitializationRun.elapsed_eq_blockStart]
  let f : Fin (ReferenceInitializationRun.elapsed p (b.completed + 1)) → ℝ := fun t =>
    ∑ i : Fin p.m, (((ReferenceInitializationRun.finishBlock x b h).history i t).2).val.val
  let g : Fin (n + q) → ℝ := fun t => f (Fin.cast hlen.symm t)
  have hreindex : (∑ t : Fin (ReferenceInitializationRun.elapsed p (b.completed + 1)), f t) =
      ∑ t : Fin (n + q), g t := by
    exact Fintype.sum_equiv (finCongr hlen) f g (by intro t; rfl)
  unfold boundaryReward
  change (∑ t : Fin (ReferenceInitializationRun.elapsed p (b.completed + 1)), f t) = _
  rw [hreindex, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hidx : Fin.cast hlen.symm (Fin.castAdd q t) =
        ⟨t.val, Nat.lt_of_lt_of_le t.isLt (ReferenceInitializationRun.elapsed_mono p (Nat.le_succ _))⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd]
    change f (Fin.cast hlen.symm (Fin.castAdd q t)) = _
    dsimp [f, g]
    rw [hidx]
    change ∑ i : Fin p.m,
        (((ReferenceInitializationRun.extendedHistory x b h i
          ⟨t.val, Nat.lt_of_lt_of_le t.isLt (ReferenceInitializationRun.elapsed_mono p (Nat.le_succ _))⟩).2).val.val) = _
    simp only [ReferenceInitializationRun.extendedHistory_prefix]
  · apply Finset.sum_congr rfl
    intro u hu
    have hidx : Fin.cast hlen.symm (Fin.natAdd n u) = ReferencePrelaunchPhysicalReplay.blockEmbed u := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, ReferencePrelaunchPhysicalReplay.blockEmbed]
      have hn : n = ReferencePrelaunchPhysicalReplay.blockStart p s := by
        dsimp [n, s]
        exact ReferenceInitializationRun.elapsed_eq_blockStart b h
      rw [hn]
    change f (Fin.cast hlen.symm (Fin.natAdd n u)) = _
    dsimp [f, g]
    rw [hidx]
    change ∑ i : Fin p.m,
        (((ReferenceInitializationRun.extendedHistory x b h i (ReferencePrelaunchPhysicalReplay.blockEmbed u)).2).val.val) = _
    simp only [ReferenceInitializationRun.extendedHistory_block]
    simp only [ReferenceInitializationRun.ownEntry, ReferenceInitializationRun.ownObservation]

/-- A stopped run opportunity carries the reward unchanged. This holds at all
later `r`, without a bound by the bootstrap horizon. -/
theorem boundaryReward_advance_stopped (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (hc : b.crossing.isSome = true) :
    boundaryReward p (ReferenceInitializationRun.advance x b) = boundaryReward p b := by
  rw [ReferenceInitializationRun.advance_of_crossing x b hc]

/-- An exhausted boundary also carries the reward unchanged. -/
theorem boundaryReward_advance_exhausted (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : n_boot p ≤ b.completed) :
    boundaryReward p (ReferenceInitializationRun.advance x b) = boundaryReward p b := by
  rw [ReferenceInitializationRun.advance_of_exhausted x b h]

/-- The complete `run` recursion has exactly the stopped, exhausted and true
finish cases. The finish case appends the physical feedback of its current
block, including all players and the clipped final block. -/
theorem boundaryReward_run_succ (x : ReferenceInitializationRun.Input p) (r : ℕ) :
    boundaryReward p (ReferenceInitializationRun.run x (r + 1)) =
      if (ReferenceInitializationRun.run x r).crossing.isSome then boundaryReward p (ReferenceInitializationRun.run x r)
      else if h : (ReferenceInitializationRun.run x r).completed < n_boot p then
        boundaryReward p (ReferenceInitializationRun.run x r) +
          ∑ u : Fin (ReferencePrelaunchPhysicalReplay.blockLength p (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x r) h)),
            ∑ i : Fin p.m,
              BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r) h)
                (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r) h)
                  (ReferencePrelaunchPhysicalReplay.blockRound p (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x r) h) u).val)
                (ReferencePrelaunchPhysicalReplay.blockRound p (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x r) h) u) i
      else boundaryReward p (ReferenceInitializationRun.run x r) := by
  rw [ReferenceInitializationRun.run_succ]
  by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
  · rw [ReferenceInitializationRun.advance_of_crossing x _ hc]
    simp [hc]
  · have hn : (ReferenceInitializationRun.run x r).crossing = none := by
      cases he : (ReferenceInitializationRun.run x r).crossing <;> simp_all
    by_cases h : (ReferenceInitializationRun.run x r).completed < n_boot p
    · rw [ReferenceInitializationRun.advance_of_no_crossing x _ hn h, boundaryReward_finishBlock]
      simp [hc, h]
    · rw [ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt h)]
      simp [hc, h]

/-- Every actual `run` history entry is the feedback dictated by the whole
generated simultaneous arm profile and the same indexed reward row. This
identity is asserted only on histories produced by `ReferenceInitializationRun.run`; no arbitrary
boundary is supplied with a physics premise. -/
theorem run_history_physicalFeedback (x : ReferenceInitializationRun.Input p) :
    ∀ r (u : Fin (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run x r).completed)) (i : Fin p.m),
      ((ReferenceInitializationRun.run x r).history i u).2.val.val =
        if FiniteBanditModel.collisionFreeFor
            (fun j => ((ReferenceInitializationRun.run x r).history j u).1) i then
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (x.rewards ⟨u.val,
              Nat.lt_of_lt_of_le u.isLt
                (ReferenceInitializationRun.elapsed_le_T p
                  (ReferenceInitializationRun.run x r).completed)⟩
              (((ReferenceInitializationRun.run x r).history i u).1))
        else 0 := by
  intro r
  induction r with
  | zero =>
      intro u i
      have hlen : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x 0).completed = 0 := by
        simp [ReferenceInitializationRun.run_zero, ReferenceInitializationRun.initial,
          ReferenceInitializationRun.elapsed]
      rw [hlen] at u
      exact Fin.elim0 u
  | succ r ih =>
      rw [ReferenceInitializationRun.run_succ]
      by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
      · rw [ReferenceInitializationRun.advance_of_crossing x _ hc]
        exact ih
      · have hn : (ReferenceInitializationRun.run x r).crossing = none := by
          cases he : (ReferenceInitializationRun.run x r).crossing <;> simp_all
        by_cases h : (ReferenceInitializationRun.run x r).completed < n_boot p
        · rw [ReferenceInitializationRun.advance_of_no_crossing x _ hn h]
          intro u i
          let b := ReferenceInitializationRun.run x r
          let s := ReferenceInitializationRun.nextBlock b h
          let v := ReferenceInitializationRun.physical x b h
          have hlen : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.finishBlock x b h).completed =
              ReferenceInitializationRun.elapsed p b.completed +
                ReferencePrelaunchPhysicalReplay.blockLength p s := by
            change ReferenceInitializationRun.elapsed p (b.completed + 1) = _
            rw [ReferenceInitializationRun.elapsed_succ_eq_blockEnd, ReferencePrelaunchPhysicalReplay.blockEnd_eq_start_add_length,
              ReferenceInitializationRun.elapsed_eq_blockStart]
          have huBound : u.val < ReferenceInitializationRun.elapsed p b.completed +
              ReferencePrelaunchPhysicalReplay.blockLength p s := by
            rw [← hlen]
            exact u.isLt
          by_cases hu : u.val < ReferenceInitializationRun.elapsed p b.completed
          · let old : Fin (ReferenceInitializationRun.elapsed p b.completed) := ⟨u.val, by
              exact hu⟩
            have hidx : u = ⟨old.val,
                Nat.lt_of_lt_of_le old.isLt (ReferenceInitializationRun.elapsed_mono p (Nat.le_succ _))⟩ := by
              apply Fin.ext
              rfl
            have hprefix (j : Fin p.m) :
                (ReferenceInitializationRun.finishBlock x b h).history j u = b.history j old := by
              rw [hidx]
              exact ReferenceInitializationRun.extendedHistory_prefix x b h j old
            have hprofile : (fun j : Fin p.m => ((ReferenceInitializationRun.finishBlock x b h).history j u).1) =
                fun j => (b.history j old).1 := by
              funext j
              exact congrArg Prod.fst (hprefix j)
            rw [hprefix i, hprofile]
            have hrewardIndex :
                (⟨u.val, Nat.lt_of_lt_of_le u.isLt
                  (ReferenceInitializationRun.elapsed_le_T p
                    (ReferenceInitializationRun.finishBlock x b h).completed)⟩ : Fin p.T) =
                  ⟨old.val, Nat.lt_of_lt_of_le old.isLt
                    (ReferenceInitializationRun.elapsed_le_T p b.completed)⟩ := by
              apply Fin.ext
              rfl
            rw [hrewardIndex]
            simpa [b] using ih old i
          · have huLower : ReferenceInitializationRun.elapsed p b.completed ≤ u.val :=
              Nat.le_of_not_gt hu
            let offset : Fin (ReferencePrelaunchPhysicalReplay.blockLength p s) :=
              ⟨u.val - ReferenceInitializationRun.elapsed p b.completed, by
                omega⟩
            have hstart : ReferenceInitializationRun.elapsed p b.completed =
                ReferencePrelaunchPhysicalReplay.blockStart p s := by
              dsimp [s]
              exact ReferenceInitializationRun.elapsed_eq_blockStart b h
            have hidx : u = ReferencePrelaunchPhysicalReplay.blockEmbed offset := by
              apply Fin.ext
              change u.val = ReferencePrelaunchPhysicalReplay.blockStart p s + offset.val
              dsimp [offset]
              rw [hstart]
              omega
            let t : Fin p.T := ⟨u.val,
              Nat.lt_of_lt_of_le u.isLt (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))⟩
            have htime : ReferencePrelaunchPhysicalReplay.blockRound p s offset = t := by
              apply Fin.ext
              rw [ReferencePrelaunchPhysicalReplay.blockRound_val]
              dsimp [offset, t]
              rw [hstart]
              omega
            have hrewardIndex :
                (⟨u.val, Nat.lt_of_lt_of_le u.isLt
                  (ReferenceInitializationRun.elapsed_le_T p
                    (ReferenceInitializationRun.finishBlock x b h).completed)⟩ : Fin p.T) = t := by
              apply Fin.ext
              rfl
            have hentry (j : Fin p.m) :
                (ReferenceInitializationRun.finishBlock x b h).history j u = ReferenceInitializationRun.ownEntry v j t := by
              change ReferenceInitializationRun.extendedHistory x b h j u = _
              rw [hidx, ReferenceInitializationRun.extendedHistory_block, htime]
            have hprofile :
                (fun j : Fin p.m => ((ReferenceInitializationRun.finishBlock x b h).history j u).1) =
                  BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t := by
              funext j
              rw [hentry j]
              rfl
            have hfeedback :
                ((ReferenceInitializationRun.finishBlock x b h).history i u).2.val.val =
                  BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t i := by
              rw [hentry i]
              rfl
            rw [hfeedback, hprofile]
            rw [hrewardIndex]
            have haction :
                ((ReferenceInitializationRun.finishBlock x b h).history i u).1 =
                  (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t) i :=
              congrArg (fun profile => profile i) hprofile
            rw [haction]
            change BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t i =
              if FiniteBanditModel.collisionFreeFor
                  (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t) i then
                RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (x.rewards t ((BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t) i))
              else 0
            change FiniteBanditModel.playerFeedback
                (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t)
                (fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (v.rewards t a)) i = _
            have hreward : v.rewards t = x.rewards t := rfl
            rw [hreward]
            by_cases hfree : FiniteBanditModel.collisionFreeFor
                (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t) i
            · simp [FiniteBanditModel.playerFeedback, hfree]
            · simp [FiniteBanditModel.playerFeedback, hfree]
        · rw [ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          exact ih

/-- The terminal reference boundary's generated reward; a literal output
projection of the existing `ReferenceInitializationRun.output`. -/
def outputBoundaryReward (p : Parameters) (x : ReferenceInitializationRun.Input p) : ℝ :=
  boundaryReward p (ReferenceInitializationRun.output x)

/-- Terminal output reward is bounded by `m` times its actual elapsed prefix,
and therefore by `m*T`. -/
theorem outputBoundaryReward_bounds (p : Parameters) (x : ReferenceInitializationRun.Input p) :
    outputBoundaryReward p x ∈
        Set.Icc 0 ((p.m : ℝ) * (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed : ℝ)) ∧
      outputBoundaryReward p x ≤ (p.m : ℝ) * (p.T : ℝ) := by
  have hbound := boundaryReward_bounds p (ReferenceInitializationRun.output x)
  refine ⟨hbound, ?_⟩
  exact le_trans hbound.2 (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (ReferenceInitializationRun.elapsed_le_T p (ReferenceInitializationRun.output x).completed)) (Nat.cast_nonneg _))

/-- A no-crossing output has exactly `T` generated physical entries. Its
padded physical log has no absent suffix, so its reward has no fabricated tail. -/
theorem output_no_crossing_has_exactly_T_entries (p : Parameters) (x : ReferenceInitializationRun.Input p)
    (hc : (ReferenceInitializationRun.output x).crossing = none) :
    ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = p.T ∧
      ∀ (i : Fin p.m) (t : Fin p.T),
        ReferenceInitializationMeasurability.boundaryLog p (ReferenceInitializationRun.output x) i t ≠ none := by
  have he : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = p.T := by
    exact ReferenceInitializationRun.output_elapsed_of_no_crossing x hc
  refine ⟨he, ?_⟩
  intro i t hnone
  have hpad := (ReferenceInitializationMeasurability.boundaryLog_eq_none_iff p (ReferenceInitializationRun.output x) i t).mp hnone
  rw [he] at hpad
  exact (Nat.not_le_of_gt t.isLt) hpad

/-- Every run reward projection is Borel measurable on the full original
`InputCoordinates` product. The imported measurable boundary key encodes its
entire dependent history; countability is not imposed on rows or private data. -/
theorem measurable_boundaryReward_run (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (r : ℕ) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      boundaryReward p
        (ReferenceInitializationRun.run (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z) r)) := by
  exact (measurable_of_countable (boundaryReward p)).comp
    (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards r)

/-- The output reward projection is measurable on the same whole-coordinate
product, with the actual terminal `ReferenceInitializationRun.output`. -/
theorem measurable_outputBoundaryReward (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      outputBoundaryReward p
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)) := by
  change Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
    boundaryReward p (ReferenceInitializationRun.output (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)))
  exact (measurable_of_countable (boundaryReward p)).comp
    (ReferenceInitializationMeasurability.measurable_output p C_star C_h eta rewards)

/-- Original-source specialization of the generated physical feedback law,
using the same source-selected row, original `J`, all published rows and all
original private coordinates. -/
theorem source_reference_output_physicalFeedback
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : ActiveFollowerDownAcceptance.RateInput p)
    (u : Fin (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)) (i : Fin p.m) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    (b.history i u).2.val.val =
      if FiniteBanditModel.collisionFreeFor (fun j => (b.history j u).1) i then
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (x.rewards ⟨u.val,
            Nat.lt_of_lt_of_le u.isLt (ReferenceInitializationRun.elapsed_le_T p b.completed)⟩
            ((b.history i u).1))
      else 0 := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  exact run_history_physicalFeedback x (n_boot p) u i

/-- Original-source terminal reward has the same `m*elapsed ≤ m*T` bound. -/
theorem source_reference_output_reward_bound
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : ActiveFollowerDownAcceptance.RateInput p) :
    outputBoundaryReward p (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) ∈
        Set.Icc 0 ((p.m : ℝ) *
          (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed : ℝ)) ∧
      outputBoundaryReward p (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) ≤
        (p.m : ℝ) * (p.T : ℝ) :=
  outputBoundaryReward_bounds p (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)

/-- Pull back output reward measurability to the original complete published
rows and original `SourceInput`. The finite selected index is exactly the
existing source `J`; its coordinate and the entire row family remain in the
domain, with no resampling or finite replacement of continuous rows. -/
theorem measurable_source_reference_outputBoundaryReward
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : ActiveFollowerDownAcceptance.RateInput p) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      outputBoundaryReward p (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) := by
  let J : BootstrapPrivateRoundStreams.SourceInput p → Fin (ConstructorDimensions.M p) :=
    ActualInitializationPhysicalStep.selectedRowIndex p
  have hJ : Measurable J := by
    dsimp [J, ActualInitializationPhysicalStep.selectedRowIndex]
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hselectedRow : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p => source.1.2 (J source)) := by
    have hbranch : ∀ j : Fin (ConstructorDimensions.M p),
        Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p => source.1.2 j) := by
      intro j
      exact (CompletePublicTable.measurable_completeRowProjection p j).comp
        (measurable_snd.comp measurable_fst)
    exact (measurable_from_prod_countable_right
      (f := fun v : Fin (ConstructorDimensions.M p) × BootstrapPrivateRoundStreams.SourceInput p =>
        v.2.1.2 v.1)
      hbranch).comp (hJ.prodMk measurable_id)
  have hcoordinates : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        (source.1.1, (source.1.2 (J source), source.2))) := by
    exact (measurable_fst.comp measurable_fst).prodMk
      (hselectedRow.prodMk measurable_snd)
  have houtput := measurable_outputBoundaryReward p C_star C_h rate.eta rewards
  have hrewrite :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        outputBoundaryReward p (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) =
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        outputBoundaryReward p
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta rewards
            (source.1.1, (source.1.2 (J source), source.2)))) := by
    funext source
    rfl
  rw [hrewrite]
  exact houtput.comp hcoordinates

end Bandits.Support.ReferenceInitializationPhysicalRewards

end
