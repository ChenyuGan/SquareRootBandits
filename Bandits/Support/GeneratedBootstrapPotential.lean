/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapWeightPotential
public import Bandits.Support.BootstrapBlockConstruction
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.ReferenceInitializationRun

import Lean.Elab.Tactic.Omega

/-!
# Generated stopped bootstrap weight potential

The finite analysis input is built from the actual deterministic
`ReferenceInitializationRun.run`, with no supplied observation trace or
schedule. On a processed block before declaration, it reuses the run's exact
`weightInput`, including the complete block stay feedback. A prior declaration
or launch contributes a disabled analysis block. Source: `07_public_setup.tex`
lines 27-38 and 90-114, and `appendix_b_communication.tex` lines 512-570.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedBootstrapPotential

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActiveRoundActions
open scoped Classical

variable {p : Parameters}

/-- A held-arm value obtained from this run boundary's exact numerator vector
and this opportunity's existing labelled scalar. It may fill the ignored arm
field of a disabled analysis block; it does not choose a physical action. -/
def actualLatentHeldArm (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (s : Fin (n_boot p))
    (i : Follower p.m) : Fin p.K :=
  (Bandits.Support.PrivateSourceStreams.blockDrawProfileMap p b.numerators
    b.weight_ge_one (x.coordinates.1.1 s)
    (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i)).2.1

/-- A boundary with no launch has completed exactly the opportunity index.
This is obtained from the actual recursion's progress theorem. -/
theorem completed_eq_of_no_crossing (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r ≤ n_boot p) (hc : (ReferenceInitializationRun.run x r).crossing = none) :
    (ReferenceInitializationRun.run x r).completed = r := by
  have h := ReferenceInitializationRun.run_progress x r hr
  cases h with
  | inl hcross => simp [hc] at hcross
  | inr hcompleted => exact hcompleted

/-- Exact scalar-derived held-arm field on a genuine incoming physical block.
This also covers an inactive block, whose gain is effectively zero. -/
theorem physical_held_eq_actualLatentHeldArm
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) :
    (ReferenceInitializationRun.physical x b h).held i =
      actualLatentHeldArm x b (ReferenceInitializationRun.nextBlock b h) i.val := by
  have hdraw := ReferenceInitializationRun.physical_own_block_draw x b h i
  have hheld := congrArg (fun d : Bandits.Support.PrivateSourceStreams.BlockDraw p => d.2.1) hdraw
  simpa only [actualLatentHeldArm] using hheld

/-- The existing run weight input retains the actual scalar-derived held arm
on active and inactive incoming blocks. -/
theorem weightInput_held_eq_actualLatentHeldArm
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) :
    (ReferenceInitializationRun.weightInput x b h i).held =
      actualLatentHeldArm x b (ReferenceInitializationRun.nextBlock b h) i.val := by
  change (ReferenceInitializationRun.physical x b h).held i = _
  exact physical_held_eq_actualLatentHeldArm x b h i

/-- The actual analysis input for opportunity `s`. It uses exactly the
run-produced weight input when this opportunity is processed and the follower
is uninformed. Otherwise it disables the accepted block updater, retaining an
ignored latent arm field. The disabled field is never a physical action. -/
def actualBlock (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) :
    BootstrapWeightPotential.Block p.K (B_boot p) :=
  let b := ReferenceInitializationRun.run x s.val
  if hc : b.crossing = none then
    if hi : i ∈ ReferenceInitializationRun.uninformed b then
      ReferenceInitializationRun.weightInput x b
        (by
          have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
          rw [hcompleted]
          exact s.isLt)
        ⟨i, hi⟩
    else ⟨false, actualLatentHeldArm x b s i, 0, Nat.zero_le _⟩
  else ⟨false, actualLatentHeldArm x b s i, 0, Nat.zero_le _⟩

/-- The chronological finite input list, with exactly one entry per source
bootstrap opportunity. -/
def actualBlocks (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) : List (BootstrapWeightPotential.Block p.K (B_boot p)) :=
  List.ofFn (actualBlock x i)

theorem actualBlocks_length (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) : (actualBlocks x i).length = n_boot p := by
  simp only [actualBlocks, List.length_ofFn]

theorem actualBlocks_get (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) :
    (actualBlocks x i)[s.val]'(by simp [actualBlocks]) = actualBlock x i s := by
  simp only [actualBlocks, List.getElem_ofFn]

private theorem actualBlocks_getList (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) :
    (actualBlocks x i).get ⟨s.val, by rw [actualBlocks_length]; exact s.isLt⟩ =
      actualBlock x i s := by
  simp [actualBlocks]

/-- The preblock numerator state generated by the actual stopped recursion is
the state used by the importance gain at this opportunity. -/
noncomputable def actualImportance (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) : ℝ :=
  BootstrapWeightPotential.importance (b_N p)
    ((ReferenceInitializationRun.run x s.val).numerators
      (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i))
    (actualBlock x i s) a

/-- Full stay gain on processed blocks while this follower is uninformed,
including all positive stays after a declaration has been saved within the
block. It is zero on inactive, informed, and postlaunch opportunities. -/
noncomputable def actualStoppedFullStayGain
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) : ℕ :=
  let b := ReferenceInitializationRun.run x s.val
  if hc : b.crossing = none then
    if hi : i ∈ ReferenceInitializationRun.uninformed b then
      BootstrapPhysicalBlock.physicalStayGain
        (ReferenceInitializationRun.physical x b
          (by
            have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
            rw [hcompleted]
            exact s.isLt))
        ⟨i, hi⟩
    else 0
  else 0

/-- A nonlaunch boundary at opportunity `s` is the actual preblock state, and
its successor processes exactly that block (including a first crossing). -/
theorem run_processes_opportunity (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p))
    (hc : (ReferenceInitializationRun.run x s.val).crossing = none) :
    (ReferenceInitializationRun.run x s.val).completed = s.val ∧
      (ReferenceInitializationRun.run x s.val).completed < n_boot p ∧
      ReferenceInitializationRun.run x (s.val + 1) =
        ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x s.val)
          (by
            have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
            rw [hcompleted]
            exact s.isLt) := by
  have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
  have hlt : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
    rw [hcompleted]
    exact s.isLt
  refine ⟨hcompleted, hlt, ?_⟩
  rw [ReferenceInitializationRun.run_succ,
    ReferenceInitializationRun.advance_of_no_crossing x _ hc hlt]

/-- On a processed uninformed block the adapter is exactly the existing
`ReferenceInitializationRun.weightInput`, with its actual incoming numerator
state, activity, held arm, private ID, and full physical feedback. -/
theorem actualBlock_eq_weightInput (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p))
    (hc : (ReferenceInitializationRun.run x s.val).crossing = none)
    (hi : i ∈ ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val)) :
    actualBlock x i s =
      ReferenceInitializationRun.weightInput x (ReferenceInitializationRun.run x s.val)
        (by
          have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
          rw [hcompleted]
          exact s.isLt)
        ⟨i, hi⟩ := by
  simp [actualBlock, hc, hi]

/-- A previously declared or forced follower's later analysis block is
 disabled by the actual activation state. -/
theorem actualBlock_disabled_of_activated (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p))
    (ha : (ReferenceInitializationRun.run x s.val).activation i ≠ none) :
    (actualBlock x i s).enabled = false := by
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · have hi : i ∉ ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val) := by
      intro hm
      exact ha ((ReferenceInitializationRun.mem_uninformed
        (ReferenceInitializationRun.run x s.val) i).mp hm)
    simp [actualBlock, hc, hi]
  · simp [actualBlock, hc]

/-- No postlaunch opportunity is processed or given an enabled analysis block. -/
theorem actualBlock_disabled_after_launch (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p))
    (hc : (ReferenceInitializationRun.run x s.val).crossing.isSome = true) :
    (actualBlock x i s).enabled = false := by
  cases hcross : (ReferenceInitializationRun.run x s.val).crossing with
  | none => simp [hcross] at hc
  | some c => simp [actualBlock, hcross]

/-- Replacing the ignored arm field of a disabled generated entry changes
neither its effective gain nor the literal numerator update. -/
theorem actualBlock_disabled_arm_irrelevant (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (s : Fin (n_boot p))
    (hdisabled : (actualBlock x i s).enabled = false) (held' : Fin p.K)
    (n : Fin p.K → ℕ) :
    BootstrapWeightPotential.effectiveGain (actualBlock x i s) =
        BootstrapWeightPotential.effectiveGain
          ({ actualBlock x i s with held := held' } : BootstrapWeightPotential.Block p.K (B_boot p)) ∧
      BootstrapWeightPotential.next (b_N p) n (actualBlock x i s) =
        BootstrapWeightPotential.next (b_N p) n
          ({ actualBlock x i s with held := held' } : BootstrapWeightPotential.Block p.K (B_boot p)) := by
  have hignored :
      ({ actualBlock x i s with held := held' } : BootstrapWeightPotential.Block p.K (B_boot p)).enabled =
        false := by
    simp only [hdisabled]
  exact BootstrapBlockConstruction.disabled_private_values_irrelevant
    (actualBlock x i s) _ hdisabled hignored n

/-- The held arm in every list entry is the exact latent arm derived from the
same current weight numerators and labelled block scalar. Inactive incoming
blocks keep this field even though their effective gain is zero. -/
theorem actualBlock_held_eq_actualLatentHeldArm
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    (actualBlock x i s).held =
      actualLatentHeldArm x (ReferenceInitializationRun.run x s.val) s i := by
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · by_cases hi : i ∈ ReferenceInitializationRun.uninformed
        (ReferenceInitializationRun.run x s.val)
    · have hcompleted := completed_eq_of_no_crossing x s.val s.isLt.le hc
      have hlt : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
        rw [hcompleted]
        exact s.isLt
      have hnext : ReferenceInitializationRun.nextBlock
          (ReferenceInitializationRun.run x s.val) hlt = s := Fin.ext hcompleted
      have hweight := weightInput_held_eq_actualLatentHeldArm x _ hlt ⟨i, hi⟩
      rw [hnext] at hweight
      have hblock := actualBlock_eq_weightInput x i s hc hi
      exact (congrArg BootstrapWeightPotential.Block.held hblock).trans hweight
    · simp [actualBlock, hc, hi]
  · simp [actualBlock, hc]

/-- The input updater's effective gain equals the literal physical full-stay
gain on processed uninformed blocks and is zero otherwise. -/
theorem actualBlock_effectiveGain_eq_actualStoppedFullStayGain
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    BootstrapWeightPotential.effectiveGain (actualBlock x i s) =
      actualStoppedFullStayGain x i s := by
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · by_cases hi : i ∈ ReferenceInitializationRun.uninformed
        (ReferenceInitializationRun.run x s.val)
    · rw [actualBlock_eq_weightInput x i s hc hi]
      rw [ReferenceInitializationRun.weightInput_full_gain]
      simp only [actualStoppedFullStayGain, hc, hi]
      rfl
    · simp [actualBlock, actualStoppedFullStayGain, hc, hi,
        BootstrapWeightPotential.effectiveGain]
  · simp [actualBlock, actualStoppedFullStayGain, hc,
      BootstrapWeightPotential.effectiveGain]

/-- Every prefix list fold is the exact numerator state of the generated run.
The proof follows `run` and `finishBlock`; it assumes no supplied schedule and
does not use this equality as an input to the adapter. -/
theorem actual_listNumerators_eq_run (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (r : ℕ) (hr : r ≤ n_boot p) :
    BootstrapWeightPotential.listNumerators (b_N p) (actualBlocks x i) r =
      (ReferenceInitializationRun.run x r).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  induction r with
  | zero =>
      simp [BootstrapWeightPotential.listNumerators,
        ReferenceInitializationRun.run, ReferenceInitializationRun.initial]
  | succ r ih =>
      have hlt : r < n_boot p := by omega
      rw [BootstrapWeightPotential.listNumerators_succ (actualBlocks x i) r (by
        rw [actualBlocks_length]
        exact hlt)]
      rw [ih (by omega), actualBlocks_get x i ⟨r, hlt⟩]
      by_cases hc : (ReferenceInitializationRun.run x r).crossing = none
      · have hcompleted := completed_eq_of_no_crossing x r (by omega) hc
        have hproc : (ReferenceInitializationRun.run x r).completed < n_boot p := by
          rw [hcompleted]
          exact hlt
        by_cases hi : i ∈ ReferenceInitializationRun.uninformed
            (ReferenceInitializationRun.run x r)
        · rw [actualBlock_eq_weightInput x i ⟨r, hlt⟩ hc hi]
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hc hproc]
          change BootstrapWeightPotential.next (b_N p)
              ((ReferenceInitializationRun.run x r).numerators
                (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i))
              (ReferenceInitializationRun.weightInput x
                (ReferenceInitializationRun.run x r) hproc ⟨i, hi⟩) =
            ReferenceInitializationRun.updatedNumerators x
              (ReferenceInitializationRun.run x r) hproc
                (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i)
          have hupdate := ReferenceInitializationRun.updatedNumerators_incoming
            x (ReferenceInitializationRun.run x r) hproc ⟨i, hi⟩
          exact hupdate.symm
        · have hdisabled : (actualBlock x i ⟨r, hlt⟩).enabled = false := by
            simp [actualBlock, hc, hi]
          have hnext := BootstrapWeightPotential.next_disabled
            (b := b_N p) ((ReferenceInitializationRun.run x r).numerators
              (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i))
            (actualBlock x i ⟨r, hlt⟩) hdisabled
          rw [hnext, ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hc hproc]
          change (ReferenceInitializationRun.run x r).numerators
              (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) =
            ReferenceInitializationRun.updatedNumerators x
              (ReferenceInitializationRun.run x r) hproc
                (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i)
          have hindex : Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i = i :=
            Fin.ext rfl
          rw [hindex]
          simp [ReferenceInitializationRun.updatedNumerators, hi]
      · have hsome : (ReferenceInitializationRun.run x r).crossing.isSome = true := by
          cases hcross : (ReferenceInitializationRun.run x r).crossing with
          | none => simp [hcross] at hc
          | some c => rfl
        have hdisabled := actualBlock_disabled_after_launch x i ⟨r, hlt⟩ hsome
        have hnext := BootstrapWeightPotential.next_disabled
          (b := b_N p) ((ReferenceInitializationRun.run x r).numerators
            (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i))
          (actualBlock x i ⟨r, hlt⟩) hdisabled
        rw [hnext, ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_crossing x _ hsome]

/-- Once a follower has become informed, the generated recursion preserves
that activation at every later boundary through the finite horizon. -/
theorem activation_persistent (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) {r q : ℕ} (hrq : r ≤ q) (hq : q ≤ n_boot p)
    (ha : (ReferenceInitializationRun.run x r).activation i ≠ none) :
    (ReferenceInitializationRun.run x q).activation i ≠ none := by
  induction q generalizing r ha with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      exact ha
  | succ q ih =>
      by_cases heq : r = q + 1
      · simpa [heq] using ha
      · have hrq' : r ≤ q := by omega
        have hq' : q ≤ n_boot p := by omega
        have ha' := ih hrq' hq' ha
        by_cases hc : (ReferenceInitializationRun.run x q).crossing.isSome = true
        · rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_crossing x _ hc]
          exact ha'
        · have hcNone : (ReferenceInitializationRun.run x q).crossing = none := by
            cases hcross : (ReferenceInitializationRun.run x q).crossing <;>
              simp_all only [Option.isSome_some, not_true_eq_false]
          have hprog := ReferenceInitializationRun.run_progress x q (by omega)
          have hcompleted : (ReferenceInitializationRun.run x q).completed = q :=
            hprog.resolve_left hc
          have hlt : (ReferenceInitializationRun.run x q).completed < n_boot p := by
            rw [hcompleted]
            omega
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hcNone hlt]
          cases hactivation : (ReferenceInitializationRun.run x q).activation i with
          | none => simp [hactivation] at ha'
          | some a =>
              rw [ReferenceInitializationRun.activated_activation x _ hlt i a hactivation]
              exact Option.some_ne_none _

/-- From the first boundary where a follower is activated, subsequent generated
numerators are frozen. The activation block's preceding full update remains in
the state by `finishBlock` and the exact fold identity below. -/
theorem numerators_succ_eq_after_activation
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p))
    (ha : (ReferenceInitializationRun.run x s.val).activation i ≠ none) :
    (ReferenceInitializationRun.run x (s.val + 1)).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) =
      (ReferenceInitializationRun.run x s.val).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  have hfoldS := actual_listNumerators_eq_run x i s.val s.isLt.le
  have hfoldNext := actual_listNumerators_eq_run x i (s.val + 1) (by omega)
  rw [← hfoldNext, ← hfoldS]
  rw [BootstrapWeightPotential.listNumerators_succ (actualBlocks x i) s.val (by
    rw [actualBlocks_length]
    exact s.isLt)]
  rw [actualBlocks_get x i s]
  have hdisabled := actualBlock_disabled_of_activated x i s ha
  exact BootstrapWeightPotential.next_disabled
    (b := b_N p) (BootstrapWeightPotential.listNumerators (b_N p) (actualBlocks x i) s.val)
    (actualBlock x i s) hdisabled

theorem numerators_frozen_after_activation (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) {r q : ℕ} (hrq : r ≤ q) (hq : q ≤ n_boot p)
    (ha : (ReferenceInitializationRun.run x r).activation i ≠ none) :
    (ReferenceInitializationRun.run x q).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) =
      (ReferenceInitializationRun.run x r).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  induction q generalizing r ha with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      rfl
  | succ q ih =>
      by_cases heq : r = q + 1
      · subst r
        rfl
      · have hrq' : r ≤ q := by omega
        have hq' : q ≤ n_boot p := by omega
        have hactQ := activation_persistent x i hrq' hq' ha
        have hprev := ih hrq' hq' ha
        have hs : q < n_boot p := by omega
        let s : Fin (n_boot p) := ⟨q, hs⟩
        have hstep := numerators_succ_eq_after_activation x i s (by simpa [s] using hactQ)
        simpa [s] using hstep.trans hprev

/-- At and after an actual launch crossing, the run recursion stutters; every
later analysis block is disabled, so no new physical observations or weight
updates are introduced by this adapter. -/
theorem numerators_frozen_after_launch (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) {r q : ℕ} (hrq : r ≤ q) (_hq : q ≤ n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing.isSome = true) :
    (ReferenceInitializationRun.run x q).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) =
      (ReferenceInitializationRun.run x r).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  have hrun := ReferenceInitializationRun.run_stops_at_crossing x r (q - r) hc
  have hqeq : r + (q - r) = q := by omega
  calc
    (ReferenceInitializationRun.run x q).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) =
      (ReferenceInitializationRun.run x (r + (q - r))).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) := by rw [hqeq]
    _ = (ReferenceInitializationRun.run x r).numerators
        (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i) :=
      congrArg (fun b : ReferenceInitializationRun.Boundary p =>
        b.numerators (Bandits.Support.BootstrapPhysicalInput.sourceFollowerIndex p i)) hrun

/-- Every disabled analysis block has zero stopped importance, independent of
its ignored held arm. -/
theorem actualImportance_eq_zero_of_disabled
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p)) (hdisabled : (actualBlock x i s).enabled = false)
    (a : Fin p.K) : actualImportance x i s a = 0 := by
  simp only [actualImportance, BootstrapWeightPotential.importance, hdisabled,
    Bool.false_eq_true, false_and, ↓reduceIte]

/-- Importance is frozen to zero after a follower has declared or been forced
into its activated state. -/
theorem actualImportance_eq_zero_of_activated
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p))
    (ha : (ReferenceInitializationRun.run x s.val).activation i ≠ none)
    (a : Fin p.K) : actualImportance x i s a = 0 := by
  have hdisabled := actualBlock_disabled_of_activated x i s ha
  exact actualImportance_eq_zero_of_disabled x i s hdisabled a

/-- Importance is zero after the coordinator's first launch crossing. -/
theorem actualImportance_eq_zero_after_launch
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (s : Fin (n_boot p))
    (hc : (ReferenceInitializationRun.run x s.val).crossing.isSome = true)
    (a : Fin p.K) : actualImportance x i s a = 0 := by
  have hdisabled := actualBlock_disabled_after_launch x i s hc
  exact actualImportance_eq_zero_of_disabled x i s hdisabled a

/-- The deterministic weight comparison for this actual run, simultaneously
for every arm and every opportunity prefix. All dimensions and numeric side
conditions come from the source constructor definitions. -/
theorem actual_run_finite_bootstrap_potential_bound
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    (∑ s : Fin r, actualImportance x i ⟨s.val, s.isLt.trans_le hr⟩ a) ≤
      4 * (∑ s : Fin r,
        (actualStoppedFullStayGain x i ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) +
        8 * p.K * B_boot p * Real.log (p.K : ℝ) := by
  have hNb : N p ≤ 2 ^ b_N p := by
    simpa only [ConstructorDimensions.D] using
      (ConstructorDimensions.N_lt_D p).le
  have hbound := BootstrapWeightPotential.finite_bootstrap_potential_bound
    (ConstructorDimensions.K_pos p) (BootstrapDimensions.B_boot_pos p)
    (BootstrapDimensions.twentyFour_le_N p) (BootstrapDimensions.K_mul_B_boot_le_N p)
    hNb (actualBlocks x i) r (by
      rw [actualBlocks_length]
      exact hr) a
  have himportance (s : Fin r) :
      BootstrapWeightPotential.importance (b_N p)
        (BootstrapWeightPotential.listNumerators (b_N p) (actualBlocks x i) s.val)
        ((actualBlocks x i).get ⟨s.val, lt_of_lt_of_le s.isLt (by
          rw [actualBlocks_length]
          exact hr)⟩) a = actualImportance x i ⟨s.val, s.isLt.trans_le hr⟩ a := by
    rw [actual_listNumerators_eq_run x i s.val (s.isLt.le.trans hr)]
    have hget := actualBlocks_getList x i ⟨s.val, s.isLt.trans_le hr⟩
    rw [hget]
    rfl
  have hgain (s : Fin r) :
      (BootstrapWeightPotential.effectiveGain
        ((actualBlocks x i).get ⟨s.val, lt_of_lt_of_le s.isLt (by
          rw [actualBlocks_length]
          exact hr)⟩) : ℝ) =
        (actualStoppedFullStayGain x i ⟨s.val, s.isLt.trans_le hr⟩ : ℝ) := by
    have hget := actualBlocks_getList x i ⟨s.val, s.isLt.trans_le hr⟩
    rw [hget, actualBlock_effectiveGain_eq_actualStoppedFullStayGain]
  simpa only [himportance, hgain] using hbound

end Bandits.Support.GeneratedBootstrapPotential

end
