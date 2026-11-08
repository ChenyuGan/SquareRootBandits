/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapWeightPotential
public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedBootstrapPotential
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Process.Adapted

import Lean.Elab.Tactic.Omega

/-!
# Adapted actual bootstrap importance gains

The observable here is the actual generated importance gain on the original
complete-row/private-coordinate law.  At opportunity `s` it is measurable in
the accepted causal source prefix at time `s.val + 1`.  The prefix retains the
current block's source triple and target, all calendar entries in the clipped
block, and all original player-round scalars read there; the separate `J`
scalar stays excluded exactly as in `sourcePrefix`.

The gain is the full accepted `actualImportance`, so a completing block keeps
all its stay feedback after a declaration.  No conditional freshness, mean,
product, activation, or support assertion is proved here.  Sources:
`sources/zip4/manuscript/appendix_b_communication.tex:533-585` and
`sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open scoped Classical

namespace Bandits.Support.GeneratedImportanceGainAdaptedness

variable (p : Bandits.Support.ConstructorDimensions.Parameters)

/-- The literal importance gain of the accepted generated run on the original
coordinate law, with all public parameters fixed before the coordinates. -/
def actualImportanceObservable
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : ℝ :=
  GeneratedBootstrapPotential.actualImportance
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e) i s a

/-- The source label of the current block triple is strictly inside the next
source prefix, including at the final opportunity. -/
theorem sourcePrefix_current_block_triple
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e).2.1
      ⟨s, by omega⟩ = e.2.1.1 s := rfl

/-- The coordinator target scalar for the current opportunity is in the same
next source prefix. -/
theorem sourcePrefix_current_target
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e).2.2.1
      ⟨s, by omega⟩ = e.2.2.2 s := rfl

/-- Every calendar entry in the current clipped block is present by boundary
`s + 1`.  The `min T` endpoint in `calendarBlock` includes a shortened last
block without a separate horizon case. -/
theorem calendarBlock_round_in_next_sourcePrefix
    (s : Fin (n_boot p)) (t : Fin p.T)
    (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    t.val < ReferenceInitializationRun.elapsed p (s.val + 1) := by
  have h := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht
  simpa only [ReferenceInitializationRun.elapsed] using h.2

/-- The complete original calendar entry at any round of the current block
is a coordinate of its next source prefix. -/
theorem sourcePrefix_current_calendar_entry
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (t : Fin p.T) (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e).1
      ⟨t, calendarBlock_round_in_next_sourcePrefix p s t ht⟩ =
        ((fun u => e.1.1 u t), e.1.2 t) := rfl

/-- Every player's original round scalar read in the current clipped block is
present in the next source prefix. -/
theorem sourcePrefix_current_player_round_scalar
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (i : Fin p.m) (t : Fin p.T)
    (ht : t ∈ BootstrapDimensions.calendarBlock p s) :
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e).2.2.2
      ⟨(i, t), calendarBlock_round_in_next_sourcePrefix p s t ht⟩ =
        e.2.2.1 (i, t) := rfl

/-- The scale used by the later bounded-observable consumer. -/
def scaledActualImportanceObservable
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : ℝ :=
  actualImportanceObservable p ids rewards C_star C_h eta i s a e /
    (2 * (p.K : ℝ) * B_boot p)

/-- Proof-side decomposition by the actual incoming run boundary.  This is
not a second process or a supplied trace; on a generated boundary it agrees
with `actualImportance` by the accepted run and updater definitions. -/
private def fixedBoundaryImportance
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : ℝ :=
  if _hc : b.crossing = none then
    if hi : i ∈ ReferenceInitializationRun.uninformed b then
      if h : b.completed < n_boot p then
        BootstrapWeightPotential.importance (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i))
          (ReferenceInitializationRun.weightInput
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) b h ⟨i, hi⟩) a
      else 0
    else 0
  else 0

private theorem measurable_fixedBoundaryImportance
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a : Fin p.K) :
    Measurable (fixedBoundaryImportance p ids rewards C_star C_h eta b i a) := by
  by_cases hc : b.crossing = none
  · by_cases hi : i ∈ ReferenceInitializationRun.uninformed b
    · by_cases h : b.completed < n_boot p
      · let i' : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i, hi⟩
        let draws := ReferenceInitializationMeasurability.blockDrawCode p
          (ReferenceInitializationRun.nextBlock b h)
          (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one
        let inputAt := fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
          ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, e)
        have hcoords : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
            (ids, e)) := measurable_const.prodMk measurable_id
        have hdraws : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
            draws (ids, e)) :=
          (ReferenceInitializationMeasurability.measurable_blockDrawCode p
            (ReferenceInitializationRun.nextBlock b h)
            (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one).comp hcoords
        have hactive : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
            (draws (ids, e)).1 i') :=
          (measurable_pi_apply i').comp (measurable_fst.comp hdraws)
        have hheld : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
            (draws (ids, e)).2.1 i') :=
          (measurable_pi_apply i').comp
            ((measurable_fst.comp measurable_snd).comp hdraws)
        have hgain : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
            (ReferenceInitializationRun.weightInput (inputAt e) b h i').gain) := by
          change Measurable
            ((fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              (ReferenceInitializationRun.weightInput
                (ReferenceInitializationMeasurability.inputOfCoordinates
                  p C_star C_h eta rewards z) b h i').gain) ∘
              (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p => (ids, e)))
          exact (ReferenceInitializationMeasurability.measurable_weightGain_at_fixedBoundary
            p C_star C_h eta rewards b h i').comp hcoords
        let inputReads : GeneratedBootstrapBlockFiltrationRepair.Coordinates p →
            Bool × (Fin p.K × ℕ) := fun e =>
          ((draws (ids, e)).1 i',
            ((draws (ids, e)).2.1 i',
              (ReferenceInitializationRun.weightInput (inputAt e) b h i').gain))
        have hreads : Measurable inputReads := hactive.prodMk (hheld.prodMk hgain)
        let readImportance : Bool × (Fin p.K × ℕ) → ℝ := fun v =>
          if v.1 = true ∧ v.2.1 = a then
            (v.2.2 : ℝ) / BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i)) a
          else 0
        have hmap : Measurable readImportance := measurable_of_countable readImportance
        have hreadEq : fixedBoundaryImportance p ids rewards C_star C_h eta b i a =
            readImportance ∘ inputReads := by
          funext e
          have hfields := ReferenceInitializationMeasurability.weightInput_fields
            (inputAt e) b h i'
          have hactiveEq :
              (ReferenceInitializationRun.weightInput (inputAt e) b h i').enabled =
                (draws (ids, e)).1 i' := by
            rw [hfields.1]
            rfl
          have hheldEq :
              (ReferenceInitializationRun.weightInput (inputAt e) b h i').held =
                (draws (ids, e)).2.1 i' := by
            rw [hfields.2.1]
            rfl
          simp only [fixedBoundaryImportance, dite_eq_left hc, dite_eq_left hi,
            dite_eq_left h,
            Function.comp_apply, inputReads]
          change BootstrapWeightPotential.importance (b_N p)
            (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i))
            (ReferenceInitializationRun.weightInput (inputAt e) b h i') a =
              readImportance ((draws (ids, e)).1 i',
                ((draws (ids, e)).2.1 i',
                  (ReferenceInitializationRun.weightInput (inputAt e) b h i').gain))
          unfold BootstrapWeightPotential.importance
          unfold readImportance
          rw [hactiveEq, hheldEq]
        rw [hreadEq]
        exact hmap.comp hreads
      · have hzero : fixedBoundaryImportance p ids rewards C_star C_h eta b i a =
            fun _ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p => 0 := by
          funext e
          unfold fixedBoundaryImportance
          rw [dite_eq_left hc, dite_eq_left hi, dite_eq_right h]
        rw [hzero]
        exact measurable_const
    · have hzero : fixedBoundaryImportance p ids rewards C_star C_h eta b i a =
          fun _ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p => 0 := by
        funext e
        unfold fixedBoundaryImportance
        rw [dite_eq_left hc, dite_eq_right hi]
      rw [hzero]
      exact measurable_const
  · have hzero : fixedBoundaryImportance p ids rewards C_star C_h eta b i a =
        fun _ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p => 0 := by
      funext e
      unfold fixedBoundaryImportance
      rw [dite_eq_right hc]
    rw [hzero]
    exact measurable_const

private theorem weightInput_eq_of_boundary_eq
    (x : ReferenceInitializationRun.Input p)
    (b₁ b₂ : ReferenceInitializationRun.Boundary p) (hb : b₁ = b₂)
    (h₁ : b₁.completed < n_boot p) (h₂ : b₂.completed < n_boot p)
    (i : Follower p.m)
    (hi₁ : i ∈ ReferenceInitializationRun.uninformed b₁)
    (hi₂ : i ∈ ReferenceInitializationRun.uninformed b₂) :
    ReferenceInitializationRun.weightInput x b₁ h₁ ⟨i, hi₁⟩ =
      ReferenceInitializationRun.weightInput x b₂ h₂ ⟨i, hi₂⟩ := by
  cases hb
  rfl

private theorem actualImportance_eq_fixedBoundaryImportance
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e =
      fixedBoundaryImportance p ids rewards C_star C_h eta
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val) i a e := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  change GeneratedBootstrapPotential.actualImportance x i s a = _
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · have hcompleted := GeneratedBootstrapPotential.completed_eq_of_no_crossing
      x s.val s.isLt.le hc
    have hlt : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    by_cases hi : i ∈ ReferenceInitializationRun.uninformed
        (ReferenceInitializationRun.run x s.val)
    · have hblock := GeneratedBootstrapPotential.actualBlock_eq_weightInput x i s hc hi
      unfold GeneratedBootstrapPotential.actualImportance
      rw [hblock]
      simp [fixedBoundaryImportance, hc, hi, hlt, x]
    · have hdisabled :
          (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
        simp [GeneratedBootstrapPotential.actualBlock, hc, hi]
      rw [GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
        x i s hdisabled a]
      simp [fixedBoundaryImportance, hc, hi, x]
  · have hdisabled :
        (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
      simp [GeneratedBootstrapPotential.actualBlock, hc]
    rw [GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
      x i s hdisabled a]
    simp [fixedBoundaryImportance, hc, x]

/-- The actual observable is Borel measurable on the original ambient
complete-row/private-coordinate space. -/
theorem actualImportance_measurable
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    Measurable (actualImportanceObservable p ids rewards C_star C_h eta i s a) := by
  let incomingRun := fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
    ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      s.val
  have hrun : Measurable incomingRun := by
    have h := GeneratedBootstrapBlockFiltrationRepair.measurable_run
      p s.val ids rewards C_star C_h eta
    exact h.mono (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p s.val)
      (by rfl)
  have hbranches : ∀ b : ReferenceInitializationRun.Boundary p,
      Measurable (fixedBoundaryImportance p ids rewards C_star C_h eta b i a) := by
    intro b
    exact measurable_fixedBoundaryImportance p ids rewards C_star C_h eta b i a
  have hjoint : Measurable (fun v : ReferenceInitializationRun.Boundary p ×
      GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        fixedBoundaryImportance p ids rewards C_star C_h eta v.1 i a v.2) := by
    exact measurable_from_prod_countable_right hbranches
  have hcompose : Measurable (fun e =>
      fixedBoundaryImportance p ids rewards C_star C_h eta (incomingRun e) i a e) := by
    exact hjoint.comp (hrun.prodMk measurable_id)
  have hfactor : actualImportanceObservable p ids rewards C_star C_h eta i s a =
      fun e => fixedBoundaryImportance p ids rewards C_star C_h eta (incomingRun e) i a e := by
    funext e
    exact actualImportance_eq_fixedBoundaryImportance p ids rewards C_star C_h eta i s a e
  rw [hfactor]
  exact hcompose

/-- Equal causal prefixes at `s + 1` give the same actual importance gain.
The incoming generated run agrees by restriction to prefix `s`; the current
block updater agrees by the accepted `weightInput_prefix_eq`, whose physical
prefix argument covers the full clipped block including its last round. -/
theorem actualImportance_eq_of_sourcePrefix_eq
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e f : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (h : GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e =
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) f) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e =
      actualImportanceObservable p ids rewards C_star C_h eta i s a f := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  let y := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta f
  have hrestrict := congrArg
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict p s.val (s.val + 1) (by omega)) h
  have hprev : GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e =
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val f := by
    rw [GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict_sourcePrefix
      p s.val (s.val + 1) (by omega) e,
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict_sourcePrefix
      p s.val (s.val + 1) (by omega) f] at hrestrict
    exact hrestrict
  have hp := GeneratedBootstrapBlockFiltrationRepair.runPrefixInputEq_of_sourcePrefix_eq
    p (s.val + 1) ids rewards C_star C_h eta e f h
  have hb := GeneratedBootstrapBlockFiltrationRepair.run_eq_of_sourcePrefix_eq
    p s.val ids rewards C_star C_h eta e f hprev
  change GeneratedBootstrapPotential.actualImportance x i s a =
    GeneratedBootstrapPotential.actualImportance y i s a
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · have hcY : (ReferenceInitializationRun.run y s.val).crossing = none := by
      rw [← hb]
      exact hc
    have hcompleted := GeneratedBootstrapPotential.completed_eq_of_no_crossing
      x s.val s.isLt.le hc
    have hlt : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    have htime : (ReferenceInitializationRun.run x s.val).completed < s.val + 1 := by
      rw [hcompleted]
      omega
    by_cases hi : i ∈ ReferenceInitializationRun.uninformed
        (ReferenceInitializationRun.run x s.val)
    · have hiY : i ∈ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run y s.val) := by
        rw [← hb]
        exact hi
      let i' : {j // j ∈ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run x s.val)} := ⟨i, hi⟩
      have hcompletedY :
          (ReferenceInitializationRun.run y s.val).completed = s.val := by
        rw [← hb]
        exact hcompleted
      have hltY : (ReferenceInitializationRun.run y s.val).completed < n_boot p := by
        rw [hcompletedY]
        exact s.isLt
      have hweight := ReferenceInitializationPrefixInvariance.weightInput_prefix_eq
        x y (ReferenceInitializationRun.run x s.val) hlt htime hp i'
      have hnums :
          (ReferenceInitializationRun.run x s.val).numerators
              (BootstrapPhysicalInput.sourceFollowerIndex p i) =
            (ReferenceInitializationRun.run y s.val).numerators
              (BootstrapPhysicalInput.sourceFollowerIndex p i) := by
        rw [hb]
      have hblockY := GeneratedBootstrapPotential.actualBlock_eq_weightInput y i s hcY hiY
      have hblockY' : GeneratedBootstrapPotential.actualBlock y i s =
          ReferenceInitializationRun.weightInput y
            (ReferenceInitializationRun.run x s.val) hlt i' := by
        rw [hblockY]
        exact weightInput_eq_of_boundary_eq p y
          (ReferenceInitializationRun.run y s.val)
          (ReferenceInitializationRun.run x s.val) hb.symm hltY hlt i hiY hi
      have hblockX := GeneratedBootstrapPotential.actualBlock_eq_weightInput x i s hc hi
      unfold GeneratedBootstrapPotential.actualImportance
      rw [hblockX, hblockY', hnums, hweight]
    · have hiY : i ∉ ReferenceInitializationRun.uninformed
          (ReferenceInitializationRun.run y s.val) := by
        intro hm
        apply hi
        rw [← hb] at hm
        exact hm
      have hdisabledX :
          (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
        simp [GeneratedBootstrapPotential.actualBlock, hc, hi]
      have hdisabledY :
          (GeneratedBootstrapPotential.actualBlock y i s).enabled = false := by
        simp [GeneratedBootstrapPotential.actualBlock, hcY, hiY]
      rw [GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
        x i s hdisabledX a,
        GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
          y i s hdisabledY a]
  · have hcY : (ReferenceInitializationRun.run y s.val).crossing ≠ none := by
      intro hnone
      apply hc
      rw [hb]
      exact hnone
    have hdisabledX :
        (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
      simp [GeneratedBootstrapPotential.actualBlock, hc]
    have hdisabledY :
        (GeneratedBootstrapPotential.actualBlock y i s).enabled = false := by
      have hsome : (ReferenceInitializationRun.run y s.val).crossing.isSome = true := by
        cases hcross : (ReferenceInitializationRun.run y s.val).crossing with
        | none => exact (hcY hcross).elim
        | some value => rfl
      exact GeneratedBootstrapPotential.actualBlock_disabled_after_launch y i s hsome
    rw [GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
      x i s hdisabledX a,
      GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled
        y i s hdisabledY a]

/-- The accepted measurable completion gives an actual section of the source
prefix, and the gain is constant on its fibers. -/
theorem actualImportance_factors_through_sourcePrefix
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e₀ e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e =
      actualImportanceObservable p ids rewards C_star C_h eta i s a
        (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p (s.val + 1) e₀
          (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e)) := by
  apply actualImportance_eq_of_sourcePrefix_eq p ids rewards C_star C_h eta i s a
  exact (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix_completeSourcePrefix
    p (s.val + 1) e₀ (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e)).symm

/-- Adaptedness uses precisely the accepted causal block filtration, with
source opportunity `s` represented at natural time `s.val + 1`. -/
theorem actualImportance_measurable_boundary
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (actualImportanceObservable p ids rewards C_star C_h eta i s a) := by
  let r := s.val + 1
  let e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p :=
    Classical.choice (nonempty_of_isProbabilityMeasure (GeneratedBootstrapRoundLaw.originalLaw p))
  let prefixSection : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r → ℝ := fun q =>
    actualImportanceObservable p ids rewards C_star C_h eta i s a
      (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p r e₀ q)
  have hsection : Measurable prefixSection := by
    exact (actualImportance_measurable p ids rewards C_star C_h eta i s a).comp
      (GeneratedBootstrapBlockFiltrationRepair.measurable_completeSourcePrefix p r e₀)
  have hprefix :
      @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
        (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r)
        (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p r) inferInstance
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r) :=
    comap_measurable (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r)
  have hfactor : actualImportanceObservable p ids rewards C_star C_h eta i s a =
      prefixSection ∘ GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r := by
    funext e
    exact actualImportance_factors_through_sourcePrefix p ids rewards C_star C_h eta
      i s a e₀ e
  change @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
    (MeasurableSpace.comap (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r) inferInstance)
    inferInstance (actualImportanceObservable p ids rewards C_star C_h eta i s a)
  rw [hfactor]
  exact hsection.comp hprefix

/-- The same gain is ambient measurable on the original coordinate carrier. -/
theorem actualImportance_measurable_ambient
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    Measurable (actualImportanceObservable p ids rewards C_star C_h eta i s a) :=
  actualImportance_measurable p ids rewards C_star C_h eta i s a

/-- The actual importance gain is nonnegative by the accepted update bound. -/
theorem actualImportance_nonneg
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    0 ≤ actualImportanceObservable p ids rewards C_star C_h eta i s a e := by
  exact BootstrapWeightPotential.importance_nonneg (ConstructorDimensions.K_pos p)
    ((ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val).numerators
      (BootstrapPhysicalInput.sourceFollowerIndex p i))
    (GeneratedBootstrapPotential.actualBlock
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) i s) a

/-- The actual importance gain is bounded by `2*K*B_boot` on every original
coordinate, with no exceptional-coordinate qualification. -/
theorem actualImportance_le
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e ≤
      2 * (p.K : ℝ) * B_boot p := by
  exact BootstrapWeightPotential.importance_le (ConstructorDimensions.K_pos p)
    ((ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) s.val).numerators
      (BootstrapPhysicalInput.sourceFollowerIndex p i))
    (GeneratedBootstrapPotential.actualBlock
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) i s) a

/-- The source-normalized gain lies pointwise in `[0,1]`. -/
theorem scaledActualImportance_mem_Icc
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    scaledActualImportanceObservable p ids rewards C_star C_h eta i s a e ∈ Set.Icc 0 1 := by
  have hden : (0 : ℝ) < 2 * (p.K : ℝ) * B_boot p := by
    have hK : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hB : (0 : ℝ) < (B_boot p : ℝ) :=
      Nat.cast_pos.mpr (BootstrapDimensions.B_boot_pos p)
    positivity
  constructor
  · exact div_nonneg (actualImportance_nonneg p ids rewards C_star C_h eta i s a e) hden.le
  · apply (div_le_iff₀ hden).mpr
    simpa only [one_mul] using actualImportance_le p ids rewards C_star C_h eta i s a e

/-- The scaled observable remains ambient measurable. -/
theorem scaledActualImportance_measurable
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    Measurable (scaledActualImportanceObservable p ids rewards C_star C_h eta i s a) := by
  exact (actualImportance_measurable p ids rewards C_star C_h eta i s a).div_const _

/-- Bounded actual gains are integrable under the original probability law. -/
theorem actualImportance_integrable_originalLaw
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    Integrable (actualImportanceObservable p ids rewards C_star C_h eta i s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply Integrable.mono_nonneg (integrable_const (2 * (p.K : ℝ) * B_boot p))
    ((actualImportance_measurable p ids rewards C_star C_h eta i s a).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun e =>
      actualImportance_nonneg p ids rewards C_star C_h eta i s a e
  · exact Filter.Eventually.of_forall fun e =>
      actualImportance_le p ids rewards C_star C_h eta i s a e

/-- The scaled bounded observable is integrable under the original law too. -/
theorem scaledActualImportance_integrable_originalLaw
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (s : Fin (n_boot p)) (a : Fin p.K) :
    Integrable (scaledActualImportanceObservable p ids rewards C_star C_h eta i s a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply Integrable.mono_nonneg (integrable_const (1 : ℝ))
    ((scaledActualImportance_measurable p ids rewards C_star C_h eta i s a).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun e =>
      (scaledActualImportance_mem_Icc p ids rewards C_star C_h eta i s a e).1
  · exact Filter.Eventually.of_forall fun e =>
      (scaledActualImportance_mem_Icc p ids rewards C_star C_h eta i s a e).2

/-- Nat-indexed stopped analytical observable: opportunity `s` is placed at
time `s.val + 1`, time zero and times after the finite horizon being zero. -/
def actualImportanceProcess
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) (n : ℕ)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : ℝ :=
  if hn : n = 0 then 0
  else if hle : n ≤ n_boot p then
    actualImportanceObservable p ids rewards C_star C_h eta i
      ⟨n - 1, by omega⟩ a e
  else 0

/-- Exact shift: source opportunity `s` is the process value at `s.val + 1`. -/
theorem actualImportanceProcess_at_opportunity
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) (s : Fin (n_boot p))
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceProcess p ids rewards C_star C_h eta i a (s.val + 1) e =
      actualImportanceObservable p ids rewards C_star C_h eta i s a e := by
  have hn : s.val + 1 ≠ 0 := by omega
  have hle : s.val + 1 ≤ n_boot p := by omega
  simp only [actualImportanceProcess, dite_eq_right hn, dite_eq_left hle]
  congr 1

theorem actualImportanceProcess_zero_at_zero
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceProcess p ids rewards C_star C_h eta i a 0 e = 0 := by
  simp [actualImportanceProcess]

theorem actualImportanceProcess_zero_after_horizon
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) (n : ℕ) (hn : n_boot p < n)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    actualImportanceProcess p ids rewards C_star C_h eta i a n e = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hnotle : ¬ n ≤ n_boot p := by omega
  simp [actualImportanceProcess, hn0, hnotle]

/-- The process is Mathlib-adapted to the exact accepted causal
block-boundary filtration. -/
theorem actualImportanceProcess_adapted
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) :
    MeasureTheory.Adapted (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (fun n e => actualImportanceProcess p ids rewards C_star C_h eta i a n e) := by
  intro n
  change @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
    (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p n) inferInstance
    (fun e => actualImportanceProcess p ids rewards C_star C_h eta i a n e)
  by_cases hn0 : n = 0
  · subst n
    simp only [actualImportanceProcess]
    exact measurable_const
  · by_cases hle : n ≤ n_boot p
    · let s : Fin (n_boot p) := ⟨n - 1, by omega⟩
      have htime : s.val + 1 = n := by
        dsimp [s]
        omega
      have hs := actualImportance_measurable_boundary p ids rewards C_star C_h eta i s a
      rw [htime] at hs
      have heq : (fun e => actualImportanceProcess p ids rewards C_star C_h eta i a n e) =
          actualImportanceObservable p ids rewards C_star C_h eta i s a := by
        funext e
        rw [← htime]
        exact actualImportanceProcess_at_opportunity p ids rewards C_star C_h eta i a s e
      rw [heq]
      exact hs
    · have hnotle : ¬ n ≤ n_boot p := hle
      simp only [actualImportanceProcess, dite_eq_right hn0, dite_eq_right hnotle]
      exact measurable_const

/-- The finite process prefix is exactly the accepted finite sum, with source
opportunities `0,...,r-1` mapped to process times `1,...,r`.  In particular,
the final observed block is retained. -/
theorem actualImportanceProcess_sum_eq_actual_run_sum
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) (r : ℕ) (hr : r ≤ n_boot p)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (∑ t : Fin r,
      actualImportanceProcess p ids rewards C_star C_h eta i a (t.val + 1) e) =
      (∑ s : Fin r, GeneratedBootstrapPotential.actualImportance
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) i
          ⟨s.val, s.isLt.trans_le hr⟩ a) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hs : t.val < n_boot p := t.isLt.trans_le hr
  simpa only [actualImportanceObservable] using
    actualImportanceProcess_at_opportunity p ids rewards C_star C_h eta i a
      ⟨t.val, hs⟩ e

/-- The shifted process prefix inherits the accepted actual-run finite
bootstrap potential bound without dropping any processed opportunity. -/
theorem actualImportanceProcess_sum_le_actual_run_finite_bootstrap_potential_bound
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Follower p.m) (a : Fin p.K) (r : ℕ) (hr : r ≤ n_boot p)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (∑ t : Fin r,
      actualImportanceProcess p ids rewards C_star C_h eta i a (t.val + 1) e) ≤
      4 * (∑ s : Fin r,
        (GeneratedBootstrapPotential.actualStoppedFullStayGain
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) i
          ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) +
        8 * p.K * B_boot p * Real.log (p.K : ℝ) := by
  rw [actualImportanceProcess_sum_eq_actual_run_sum p ids rewards C_star C_h eta i a r hr e]
  exact GeneratedBootstrapPotential.actual_run_finite_bootstrap_potential_bound
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
    i r hr a

end Bandits.Support.GeneratedImportanceGainAdaptedness

end
