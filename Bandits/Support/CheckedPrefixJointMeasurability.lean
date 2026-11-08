/-
Copyright (c) 2026 The Bandits Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CheckedPrefixSampler
public import Bandits.Support.PrefixSamplerLaw
public import Bandits.Support.PrefixSetSampler
public import Bandits.Support.ContinuousControlSlice
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Joint measurability of the checked prefix sampler

The sampler and its checks are the literal operations of
`Bandits.Support.CheckedPrefixSampler`. Raw masses range over the ordinary
product Borel space on the existing finite set carrier, and scalar inputs range
over the original half-open cube.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-12,66-77`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-22`, and
`sources/zip4/manuscript/06_interruptions.tex:30-35`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CheckedPrefixJointMeasurability

open MeasureTheory
open PrefixSetSampler
open CheckedPrefixSampler
open PrefixSamplerLaw
open ContinuousControlSlice

variable {K m : ℕ}

/-- The original raw real mass function space, with its product Borel sigma algebra. -/
abbrev RawMass (K m : ℕ) := SetCarrier K m → ℝ

local instance (K m : ℕ) : DecidableEq (PrefixState K m) := Classical.decEq _

noncomputable local instance (K m : ℕ) : Fintype (PrefixState K m) := by
  classical
  refine Fintype.ofEquiv (Finset (SetCarrier K m) × (Fin K → Option Bool)) ?_
  exact
    { toFun := fun state => ⟨state.1, state.2⟩
      invFun := fun state => (state.candidates, state.decisions)
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }

local instance (K m : ℕ) : MeasurableSpace (SetCarrier K m) := ⊤
local instance (K m : ℕ) : DiscreteMeasurableSpace (SetCarrier K m) :=
  ⟨fun _ => trivial⟩
local instance (K m : ℕ) : MeasurableSpace (PrefixState K m) := ⊤
local instance (K m : ℕ) : DiscreteMeasurableSpace (PrefixState K m) :=
  ⟨fun _ => trivial⟩
local instance (K m : ℕ) : MeasurableSpace (PrefixRun K m) := ⊤
local instance (K m : ℕ) : DiscreteMeasurableSpace (PrefixRun K m) :=
  ⟨fun _ => trivial⟩
local instance (K m : ℕ) : MeasurableSpace (Result K m) := ⊤
local instance (K m : ℕ) : DiscreteMeasurableSpace (Result K m) :=
  ⟨fun _ => trivial⟩

private theorem measurable_on_finite_right {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [Fintype β] [DiscreteMeasurableSpace β] (f : α × β → γ)
    (hf : ∀ b, Measurable (fun a => f (a, b))) : Measurable f := by
  intro s hs
  have hpre : f ⁻¹' s = ⋃ b : β, ((fun a => f (a, b)) ⁻¹' s) ×ˢ {b} := by
    ext x
    rcases x with ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨b, h, rfl⟩
    · rintro ⟨c, h, rfl⟩
      exact h
  rw [hpre]
  exact MeasurableSet.iUnion fun b => (hf b hs).prod (measurableSet_singleton b)

/-- For a fixed finite prefix state, its raw total mass is measurable in all
real candidate masses. -/
theorem measurable_rawStateMass (state : PrefixState K m) :
    Measurable (fun mass : RawMass K m => rawStateMass mass state) := by
  unfold rawStateMass PrefixMassPartition.totalMass
  exact Finset.measurable_fun_sum state.candidates
    (fun s hs => measurable_pi_apply s)

/-- For a fixed finite prefix state and arm, its raw included mass is measurable
in all real candidate masses. -/
theorem measurable_rawIncludedMass (state : PrefixState K m) (arm : Fin K) :
    Measurable (fun mass : RawMass K m => rawIncludedMass mass state arm) := by
  unfold rawIncludedMass PrefixMassPartition.includedMass
  exact Finset.measurable_fun_sum _ (fun s hs => measurable_pi_apply s)

/-- Raw total mass is jointly measurable in the raw mass function and the
existing finite prefix state. -/
theorem measurable_rawStateMass_joint :
    Measurable (fun p : RawMass K m × PrefixState K m =>
      rawStateMass p.1 p.2) := by
  apply measurable_on_finite_right
  intro state
  exact measurable_rawStateMass state

/-- Raw included mass is jointly measurable in raw masses and the existing
finite prefix state, for each next arm. -/
theorem measurable_rawIncludedMass_joint (arm : Fin K) :
    Measurable (fun p : RawMass K m × PrefixState K m =>
      rawIncludedMass p.1 p.2 arm) := by
  apply measurable_on_finite_right
  intro state
  exact measurable_rawIncludedMass state arm

/-- The complete checked scalar step is jointly measurable in arbitrary raw
real masses and its scalar input. All denominator, probability-range, and
strict-threshold branches are the original checked operation. -/
theorem measurable_checkedStep_joint (state : PrefixState K m) (arm : Fin K) :
    Measurable (fun p : RawMass K m × UnitScalar =>
      checkedStep p.1 p.2 state arm) := by
  classical
  let W : RawMass K m × UnitScalar → ℝ := fun p => rawStateMass p.1 state
  let Win : RawMass K m × UnitScalar → ℝ := fun p => rawIncludedMass p.1 state arm
  let ratio : RawMass K m × UnitScalar → ℝ := fun p => Win p / W p
  let value : RawMass K m × UnitScalar → ℝ := fun p => p.2.1
  have hW : Measurable W := (measurable_rawStateMass state).comp measurable_fst
  have hWin : Measurable Win := (measurable_rawIncludedMass state arm).comp measurable_fst
  have hratio : Measurable ratio := hWin.div hW
  have hvalue : Measurable value := measurable_subtype_coe.comp measurable_snd
  have hdenom : MeasurableSet {p | 0 < W p} := measurableSet_lt measurable_const hW
  have hratioLow : MeasurableSet {p | 0 ≤ ratio p} :=
    measurableSet_le measurable_const hratio
  have hratioHigh : MeasurableSet {p | ratio p ≤ 1} :=
    measurableSet_le hratio measurable_const
  have hthreshold : Measurable (fun p => value p * W p) :=
    measurable_mul.comp (hvalue.prodMk hW)
  have hbranch : MeasurableSet {p | Win p > value p * W p} := by
    simpa only [gt_iff_lt] using measurableSet_lt hthreshold hWin
  have hbranchMap : Measurable (fun p =>
      if Win p > value p * W p then
        PrefixRun.ready
          ⟨state.candidates.filter (fun s => arm ∈ s.1),
            Function.update state.decisions arm (some true)⟩
      else
        PrefixRun.ready
          ⟨state.candidates.filter (fun s => arm ∉ s.1),
            Function.update state.decisions arm (some false)⟩) :=
    Measurable.ite hbranch measurable_const measurable_const
  have hratioHighMap : Measurable (fun p =>
      if ratio p ≤ 1 then
        (if Win p > value p * W p then
          PrefixRun.ready
            ⟨state.candidates.filter (fun s => arm ∈ s.1),
              Function.update state.decisions arm (some true)⟩
        else
          PrefixRun.ready
            ⟨state.candidates.filter (fun s => arm ∉ s.1),
              Function.update state.decisions arm (some false)⟩)
      else PrefixRun.failed arm .probabilityAboveOne) :=
    Measurable.ite hratioHigh hbranchMap measurable_const
  have hratioLowMap : Measurable (fun p =>
      if 0 ≤ ratio p then
        (if ratio p ≤ 1 then
          (if Win p > value p * W p then
            PrefixRun.ready
              ⟨state.candidates.filter (fun s => arm ∈ s.1),
                Function.update state.decisions arm (some true)⟩
          else
            PrefixRun.ready
              ⟨state.candidates.filter (fun s => arm ∉ s.1),
                Function.update state.decisions arm (some false)⟩)
        else PrefixRun.failed arm .probabilityAboveOne)
      else PrefixRun.failed arm .probabilityBelowZero) :=
    Measurable.ite hratioLow hratioHighMap measurable_const
  have htotal : Measurable (fun p =>
      if 0 < W p then
        (if 0 ≤ ratio p then
          (if ratio p ≤ 1 then
            (if Win p > value p * W p then
              PrefixRun.ready
                ⟨state.candidates.filter (fun s => arm ∈ s.1),
                  Function.update state.decisions arm (some true)⟩
            else
              PrefixRun.ready
                ⟨state.candidates.filter (fun s => arm ∉ s.1),
                  Function.update state.decisions arm (some false)⟩)
          else PrefixRun.failed arm .probabilityAboveOne)
        else PrefixRun.failed arm .probabilityBelowZero)
      else PrefixRun.failed arm .nonPositiveNormalizer) :=
    Measurable.ite hdenom hratioLowMap measurable_const
  simpa only [checkedStep, W, Win, ratio, value, dite_eq_ite] using htotal

/-- A fixed prior `PrefixRun` transition remains jointly measurable as the raw
mass function varies. -/
theorem measurable_checkedTransitionAt_joint (arm : Fin K) (run : PrefixRun K m) :
    Measurable (fun p : RawMass K m × UnitScalar =>
      checkedTransition p.1 arm (run, p.2)) := by
  cases run with
  | failed failedArm reason => exact measurable_const
  | ready state => exact measurable_checkedStep_joint state arm

/-- The literal transition is jointly measurable in raw masses, a scalar, and
the actual finite prior run code. -/
theorem measurable_checkedTransition_joint (arm : Fin K) :
    Measurable (fun p : (RawMass K m × UnitScalar) × PrefixRun K m =>
      checkedTransition p.1.1 arm (p.2, p.1.2)) := by
  classical
  apply measurable_to_countable'
  intro output
  have hpre :
      (fun p : (RawMass K m × UnitScalar) × PrefixRun K m =>
        checkedTransition p.1.1 arm (p.2, p.1.2)) ⁻¹' {output} =
      ⋃ run : PrefixRun K m,
        ((fun p : RawMass K m × UnitScalar =>
          checkedTransition p.1 arm (run, p.2)) ⁻¹' {output}) ×ˢ {run} := by
    ext x
    rcases x with ⟨⟨mass, value⟩, run⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨run, h, rfl⟩
    · rintro ⟨prior, h, rfl⟩
      exact h
  rw [hpre]
  exact MeasurableSet.iUnion fun run =>
    ((measurableSet_singleton output).preimage
      (measurable_checkedTransitionAt_joint arm run)).prod
        (measurableSet_singleton run)

/-- The recursive checked prefix is jointly measurable in the raw mass
function and the whole original `K`-coordinate scalar cube. -/
theorem measurable_runCheckedPrefix_joint :
    ∀ n (hn : n ≤ K),
      Measurable (fun p : RawMass K m × (Fin K → UnitScalar) =>
        runCheckedPrefix p.1 p.2 n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact measurable_const
  | succ n ih =>
      intro hn
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      let arm : Fin K := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev := ih hn'
      have hcoord : Measurable (fun p : RawMass K m × (Fin K → UnitScalar) =>
          p.2 arm) := (measurable_pi_apply arm).comp measurable_snd
      change Measurable (fun p : RawMass K m × (Fin K → UnitScalar) =>
        checkedTransition p.1 arm
          (runCheckedPrefix p.1 p.2 n hn', p.2 arm))
      exact (measurable_checkedTransition_joint arm).comp
        ((measurable_fst.prodMk hcoord).prodMk hprev)

/-- The existing checked finite prefix sampler is jointly Borel measurable in
arbitrary raw real masses and the genuine scalar cube, including all failure
outputs and its final carrier check. -/
theorem measurable_checkedSample_joint :
    Measurable (fun p : RawMass K m × (Fin K → UnitScalar) =>
      checkedSample p.1 p.2) := by
  have hfinish : Measurable (finishOutput (K := K) (m := m)) :=
    Measurable.of_discrete
  exact hfinish.comp (measurable_runCheckedPrefix_joint K le_rfl)

/-- Joint measurability after composing the raw masses and the original full
`K+1` assignment vector on any measurable base space. The sampler consumes the
actual `prefixValues` projection, leaving the final assignment coordinate in
the public input vector. -/
theorem measurable_checkedSample_comp_assignment {X : Type*} [MeasurableSpace X]
    (mass : X → RawMass K m) (hmass : Measurable mass)
    (assignment : X → Fin (K + 1) → ContinuousControlSlice.Scalar)
    (hassignment : Measurable assignment) :
    Measurable (fun x =>
      checkedSample (mass x) (PrefixSamplerLaw.prefixValues (assignment x))) := by
  exact measurable_checkedSample_joint.comp
    (hmass.prodMk ((PrefixSamplerLaw.measurable_prefixValues K).comp hassignment))

end Bandits.Support.CheckedPrefixJointMeasurability

end
