/-
Copyright (c) 2026 The Bandits Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PrefixSamplerLaw
public import Bandits.Support.CanonicalAssignmentVector
public import Bandits.Support.RecordedCorrectedWindow

/-!
# Checked finite prefix sampler

The sampler consumes the literal real mass on supported `m`-sets. It checks
each current denominator and each resulting scalar probability immediately
before the corresponding division and threshold comparison. Its operational
state is the accepted `PrefixState`.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-12,66-77`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-22`, and
`sources/zip4/manuscript/06_interruptions.tex:30-35`.
-/

public section

noncomputable section

namespace Bandits.Support.CheckedPrefixSampler

open PrefixSetSampler
open PrefixSamplerLaw
open MeasureTheory
open scoped BigOperators ENNReal

/-- The first failed local check in the source sampler. -/
inductive FailureReason where
  | nonPositiveNormalizer
  | probabilityBelowZero
  | probabilityAboveOne
  | outputOutsideCarrier
  deriving DecidableEq

instance : Fintype FailureReason where
  elems := {.nonPositiveNormalizer, .probabilityBelowZero,
    .probabilityAboveOne, .outputOutsideCarrier}
  complete reason := by cases reason <;> simp

local instance (K m : ℕ) : DecidableEq (PrefixState K m) := Classical.decEq _

noncomputable local instance (K m : ℕ) : Fintype (PrefixState K m) := by
  classical
  refine Fintype.ofEquiv (Finset (SetCarrier K m) × (Fin K → Option Bool)) ?_
  exact
    { toFun := fun state => ⟨state.1, state.2⟩
      invFun := fun state => (state.candidates, state.decisions)
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }

/-- A checked intermediate prefix, retaining the accepted operational state. -/
inductive PrefixRun (K m : ℕ) where
  | failed (arm : Fin K) (reason : FailureReason)
  | ready (state : PrefixState K m)
  deriving DecidableEq, Fintype

/-- The checked final output. `none` arm denotes only the post-prefix output
carrier check; every denominator or probability failure carries its arm. -/
inductive Result (K m : ℕ) where
  | failed (arm : Option (Fin K)) (reason : FailureReason)
  | sampled (set : SetCarrier K m)
  deriving DecidableEq, Fintype

local instance resultMeasurableSpace (K m : ℕ) : MeasurableSpace (Result K m) := ⊤
local instance resultDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (Result K m) := ⟨fun _ => trivial⟩
local instance prefixRunMeasurableSpace (K m : ℕ) : MeasurableSpace (PrefixRun K m) := ⊤
local instance prefixRunDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (PrefixRun K m) := ⟨fun _ => trivial⟩
local instance carrierMeasurableSpace (K m : ℕ) :
    MeasurableSpace (SetCarrier K m) := ⊤
local instance carrierDiscreteMeasurableSpace (K m : ℕ) :
    DiscreteMeasurableSpace (SetCarrier K m) := ⟨fun _ => trivial⟩

private theorem measurable_if_const {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] (p : α → Prop) [DecidablePred p]
    (a b : β) (hp : MeasurableSet {x | p x}) :
    Measurable (fun x => if p x then a else b) := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · apply measurable_to_countable'
    intro y
    by_cases hya : y = a
    · subst y
      have hba : b ≠ a := fun h => hab h.symm
      have hpre : (fun x => if p x then a else b) ⁻¹' {a} = {x | p x} := by
        ext x
        by_cases hpx : p x <;> simp [hpx, hba]
      rw [hpre]
      exact hp
    · by_cases hyb : y = b
      · subst y
        have hpre : (fun x => if p x then a else b) ⁻¹' {b} = {x | ¬ p x} := by
          ext x
          by_cases hpx : p x <;> simp [hpx, hab]
        rw [hpre]
        exact hp.compl
      · have hpre : (fun x => if p x then a else b) ⁻¹' {y} = ∅ := by
          ext x
          have hya' : a ≠ y := fun h => hya h.symm
          have hyb' : b ≠ y := fun h => hyb h.symm
          by_cases hpx : p x <;> simp [hpx, hya', hyb']
        rw [hpre]
        exact MeasurableSet.empty

/-- The literal total mass of the current candidate support, with no global
normalization or sign condition on the supplied raw mass. -/
@[expose] def rawStateMass {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) : ℝ :=
  PrefixMassPartition.totalMass state.candidates mass

/-- The literal current mass among candidates containing the next arm. -/
@[expose] def rawIncludedMass {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) (arm : Fin K) : ℝ :=
  PrefixMassPartition.includedMass state.candidates mass (fun s => arm ∈ s.1)

/-- Sum over the inclusion-filter branch is exactly the tested included mass. -/
theorem rawStateMass_filter_in {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) (arm : Fin K) :
    PrefixMassPartition.totalMass
        (state.candidates.filter (fun s => arm ∈ s.1)) mass =
      rawIncludedMass mass state arm := by
  simp [rawIncludedMass, PrefixMassPartition.totalMass,
    PrefixMassPartition.includedMass, Finset.sum_filter]

/-- Sum over the exclusion-filter branch is exactly the complementary mass. -/
theorem rawStateMass_filter_out {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) (arm : Fin K) :
    PrefixMassPartition.totalMass
        (state.candidates.filter (fun s => arm ∉ s.1)) mass =
      PrefixMassPartition.excludedMass state.candidates mass
        (fun s => arm ∈ s.1) := by
  simp [PrefixMassPartition.totalMass, PrefixMassPartition.excludedMass,
    Finset.sum_filter]

/-- One literal checked scalar operation. The division occurs only in the
positive-normalizer branch, and the comparison uses the source's strict
`Win > V * W` rule after the computed ratio has passed both domain checks. -/
@[expose] def checkedStep {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state : PrefixState K m) (arm : Fin K) :
    PrefixRun K m := by
  if hW : 0 < rawStateMass mass state then
    if hlow : 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state then
      if hup : rawIncludedMass mass state arm / rawStateMass mass state ≤ 1 then
        if hbranch : rawIncludedMass mass state arm > value.1 * rawStateMass mass state then
          exact .ready
            ⟨state.candidates.filter (fun s => arm ∈ s.1),
              Function.update state.decisions arm (some true)⟩
        else
          exact .ready
            ⟨state.candidates.filter (fun s => arm ∉ s.1),
              Function.update state.decisions arm (some false)⟩
      else exact .failed arm .probabilityAboveOne
    else exact .failed arm .probabilityBelowZero
  else exact .failed arm .nonPositiveNormalizer

/-- One transition of the finite checked machine, separated from its coordinate
projection for the measurability proof. -/
@[expose] def checkedTransition {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (arm : Fin K) : PrefixRun K m × UnitScalar → PrefixRun K m
  | (.failed failedArm reason, _) => .failed failedArm reason
  | (.ready state, value) => checkedStep mass value state arm

/-- A fixed-state scalar transition is measurable by its strict half-interval
branch; failed states are constant and do not inspect the scalar. -/
theorem measurable_checkedTransitionAt {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (arm : Fin K) (run : PrefixRun K m) :
    Measurable (fun value : UnitScalar =>
      checkedTransition mass arm (run, value)) := by
  classical
  cases run with
  | failed failedArm reason => exact measurable_const
  | ready state =>
      by_cases hW : 0 < rawStateMass mass state
      · by_cases hlow : 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state
        · by_cases hup : rawIncludedMass mass state arm / rawStateMass mass state ≤ 1
          · have hbranch : MeasurableSet {value : UnitScalar |
                rawIncludedMass mass state arm >
                  value.1 * rawStateMass mass state} := by
              simpa only [gt_iff_lt] using
                (measurableSet_lt
                  (measurable_subtype_coe.mul_const (rawStateMass mass state))
                  measurable_const)
            have hpiece : Measurable (fun value : UnitScalar =>
                if rawIncludedMass mass state arm >
                    value.1 * rawStateMass mass state then
                  PrefixRun.ready
                    ⟨state.candidates.filter (fun s => arm ∈ s.1),
                      Function.update state.decisions arm (some true)⟩
                else
                  PrefixRun.ready
                    ⟨state.candidates.filter (fun s => arm ∉ s.1),
                      Function.update state.decisions arm (some false)⟩) := by
              exact measurable_if_const _ _ _ hbranch
            simpa [checkedTransition, checkedStep, hW, hlow, hup] using hpiece
          · simp [checkedTransition, checkedStep, hW, hlow, hup]
        · simp [checkedTransition, checkedStep, hW, hlow]
      · simp [checkedTransition, checkedStep, hW]

/-- The transition on a finite prior code and one continuous scalar is
measurable. Its fibers are countable unions of discrete-code slices crossed
with scalar half-intervals. -/
theorem measurable_checkedTransition {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (arm : Fin K) :
    Measurable (checkedTransition mass arm) := by
  classical
  apply measurable_to_countable'
  intro output
  have hfiber : (checkedTransition mass arm) ⁻¹' {output} =
      ⋃ run : PrefixRun K m,
        ({run} : Set (PrefixRun K m)) ×ˢ
          ((fun value : UnitScalar => checkedTransition mass arm (run, value)) ⁻¹'
            {output}) := by
    ext x
    rcases x with ⟨run, value⟩
    simp [checkedTransition]
  rw [hfiber]
  exact MeasurableSet.iUnion fun run =>
    (measurableSet_singleton run).prod
      ((measurableSet_singleton output).preimage
        (measurable_checkedTransitionAt mass arm run))

/-- Recursively perform arms `0, ..., n-1` in source order. A prior failure is
returned directly, so later scalar coordinates are never inspected. -/
@[expose] def runCheckedPrefix {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (values : Fin K → UnitScalar) : (n : ℕ) → n ≤ K → PrefixRun K m
  | 0, _ => .ready (initialState K m)
  | n + 1, hn =>
      let prev := runCheckedPrefix mass values n (Nat.le_trans (Nat.le_succ n) hn)
      checkedTransition mass ⟨n, Nat.lt_of_succ_le hn⟩
        (prev, values ⟨n, Nat.lt_of_succ_le hn⟩)

/-- Check the actual included-arm output against the supported `m`-set
carrier. The successful output is that set itself, with its proved carrier
membership; there is no witness choice or fallback set. -/
@[expose] def finishOutput {K m : ℕ} (run : PrefixRun K m) : Result K m :=
  match run with
  | .failed arm reason => .failed (some arm) reason
  | .ready state =>
      let output := (Finset.univ : Finset (Fin K)).filter
        (fun i => state.decisions i = some true)
      if houtput : output ∈ (Finset.univ : Finset (Fin K)).powersetCard m then
        .sampled ⟨output, houtput⟩
      else .failed none .outputOutsideCarrier

/-- Run all `K` checked steps and return the actual carrier-checked output. -/
@[expose] def checkedSample {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (values : Fin K → UnitScalar) : Result K m :=
  finishOutput (runCheckedPrefix mass values K le_rfl)

/-- The recursive checked prefix is measurable as a function on the original
product of `K` continuous scalar coordinates. -/
theorem measurable_runCheckedPrefix {K m : ℕ}
    (mass : SetCarrier K m → ℝ) :
    ∀ n (hn : n ≤ K),
      Measurable (fun values : Fin K → UnitScalar =>
        runCheckedPrefix mass values n hn) := by
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
      have hcoord : Measurable (fun values : Fin K → UnitScalar => values arm) :=
        measurable_pi_apply arm
      change Measurable (fun values : Fin K → UnitScalar =>
        checkedTransition mass arm
          (runCheckedPrefix mass values n hn', values arm))
      exact (measurable_checkedTransition mass arm).comp
        (hprev.prodMk hcoord)

/-- The final carrier-check operation is measurable because its finite input
code has the discrete sigma algebra. -/
theorem measurable_finishOutput {K m : ℕ} :
    Measurable (finishOutput (K := K) (m := m)) :=
  Measurable.of_discrete

/-- Raw checked output measurability on the original continuous `K`-coordinate
cube. Each recursive transition uses only finite measurable inequalities. -/
theorem measurable_checkedSample {K m : ℕ} (mass : SetCarrier K m → ℝ) :
    Measurable (checkedSample (K := K) (m := m) mass) := by
  exact measurable_finishOutput.comp
    (measurable_runCheckedPrefix mass K le_rfl)

/-- The inclusion branch equation for one checked step. -/
theorem checkedStep_ready_in {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state : PrefixState K m) (arm : Fin K)
    (hW : 0 < rawStateMass mass state)
    (hlow : 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state)
    (hup : rawIncludedMass mass state arm / rawStateMass mass state ≤ 1)
    (hbranch : rawIncludedMass mass state arm > value.1 * rawStateMass mass state) :
    checkedStep mass value state arm = .ready
      ⟨state.candidates.filter (fun s => arm ∈ s.1),
        Function.update state.decisions arm (some true)⟩ := by
  simp [checkedStep, hW, hlow, hup, hbranch]

/-- The exclusion branch equation, including equality at the threshold. -/
theorem checkedStep_ready_out {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state : PrefixState K m) (arm : Fin K)
    (hW : 0 < rawStateMass mass state)
    (hlow : 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state)
    (hup : rawIncludedMass mass state arm / rawStateMass mass state ≤ 1)
    (hbranch : ¬ rawIncludedMass mass state arm > value.1 * rawStateMass mass state) :
    checkedStep mass value state arm = .ready
      ⟨state.candidates.filter (fun s => arm ∉ s.1),
        Function.update state.decisions arm (some false)⟩ := by
  simp [checkedStep, hW, hlow, hup, hbranch]

/-- The denominator check has priority over both scalar-domain checks. -/
theorem checkedStep_nonpositive_normalizer {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (value : UnitScalar)
    (state : PrefixState K m) (arm : Fin K)
    (hW : ¬ 0 < rawStateMass mass state) :
    checkedStep mass value state arm = .failed arm .nonPositiveNormalizer := by
  simp [checkedStep, hW]

/-- A negative computed ratio fails before the Bernoulli comparison. -/
theorem checkedStep_probability_below_zero {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (value : UnitScalar)
    (state : PrefixState K m) (arm : Fin K)
    (hW : 0 < rawStateMass mass state)
    (hlow : ¬ 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state) :
    checkedStep mass value state arm = .failed arm .probabilityBelowZero := by
  simp [checkedStep, hW, hlow]

/-- A computed ratio above one fails before the Bernoulli comparison. -/
theorem checkedStep_probability_above_one {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (value : UnitScalar)
    (state : PrefixState K m) (arm : Fin K)
    (hW : 0 < rawStateMass mass state)
    (hlow : 0 ≤ rawIncludedMass mass state arm / rawStateMass mass state)
    (hup : ¬ rawIncludedMass mass state arm / rawStateMass mass state ≤ 1) :
    checkedStep mass value state arm = .failed arm .probabilityAboveOne := by
  simp [checkedStep, hW, hlow, hup]

/-- The state mass after a successful inclusion test is precisely `Win`. -/
theorem checkedStep_stateMass_in {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) (arm : Fin K) :
    PrefixMassPartition.totalMass
        (state.candidates.filter (fun s => arm ∈ s.1)) mass =
      rawIncludedMass mass state arm :=
  rawStateMass_filter_in mass state arm

/-- The state mass after a successful exclusion test is the complementary
filtered mass, equal to `W - Win` by the finite partition identity. -/
theorem checkedStep_stateMass_out {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (state : PrefixState K m) (arm : Fin K) :
    PrefixMassPartition.totalMass
        (state.candidates.filter (fun s => arm ∉ s.1)) mass =
      rawStateMass mass state - rawIncludedMass mass state arm := by
  rw [rawStateMass_filter_out]
  exact PrefixMassPartition.excludedMass_eq_totalMass_sub_includedMass
    state.candidates mass (fun s => arm ∈ s.1)

/-- Any successful scalar test leaves positive mass in its chosen branch.
This uses only the checks actually performed at that step, and does not assume
individual raw set masses are nonnegative. -/
theorem checkedStep_chosenMass_pos {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state next : PrefixState K m) (arm : Fin K)
    (hstep : checkedStep mass value state arm = .ready next) :
    0 < rawStateMass mass next := by
  unfold checkedStep at hstep
  split_ifs at hstep with hW hlow hup hbranch
  · cases hstep
    change 0 < PrefixMassPartition.totalMass
      (state.candidates.filter (fun s => arm ∈ s.1)) mass
    rw [rawStateMass_filter_in]
    have hW' : 0 < PrefixMassPartition.totalMass state.candidates mass := by
      simpa [rawStateMass] using hW
    have hWin : PrefixMassPartition.includedMass state.candidates mass
        (fun s => arm ∈ s.1) >
          value.1 * PrefixMassPartition.totalMass state.candidates mass := by
      simpa [rawIncludedMass, rawStateMass] using hbranch
    have hmul : 0 ≤ value.1 * PrefixMassPartition.totalMass state.candidates mass :=
      mul_nonneg value.2.1 hW'.le
    change 0 < PrefixMassPartition.includedMass state.candidates mass
      (fun s => arm ∈ s.1)
    exact lt_of_le_of_lt hmul hWin
  · cases hstep
    change 0 < PrefixMassPartition.totalMass
      (state.candidates.filter (fun s => arm ∉ s.1)) mass
    rw [rawStateMass_filter_out]
    rw [PrefixMassPartition.excludedMass_eq_totalMass_sub_includedMass]
    have hW' : 0 < PrefixMassPartition.totalMass state.candidates mass := by
      simpa [rawStateMass] using hW
    have hbranch' : PrefixMassPartition.includedMass state.candidates mass
        (fun s => arm ∈ s.1) ≤
          value.1 * PrefixMassPartition.totalMass state.candidates mass := by
      exact le_of_not_gt (by simpa [rawIncludedMass, rawStateMass] using hbranch)
    have hmul : value.1 * PrefixMassPartition.totalMass state.candidates mass <
        PrefixMassPartition.totalMass state.candidates mass := by
      have := mul_lt_mul_of_pos_right value.2.2 hW'
      simpa only [one_mul] using this
    exact sub_pos.mpr (lt_of_le_of_lt hbranch' hmul)

/-- A ready result records that the denominator and both probability bounds
were checked before its comparison. -/
theorem checkedStep_tests_of_ready {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state next : PrefixState K m) (arm : Fin K)
    (hstep : checkedStep mass value state arm = .ready next) :
    0 < rawStateMass mass state ∧
      0 ≤ rawIncludedMass mass state arm / rawStateMass mass state ∧
      rawIncludedMass mass state arm / rawStateMass mass state ≤ 1 := by
  unfold checkedStep at hstep
  split_ifs at hstep with hW hlow hup hbranch
  · exact ⟨hW, hlow, hup⟩
  · exact ⟨hW, hlow, hup⟩

/-- A ready step records a decision at its arm and leaves every other decision
unchanged. -/
theorem checkedStep_decisions_of_ready {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state next : PrefixState K m) (arm : Fin K)
    (hstep : checkedStep mass value state arm = .ready next) :
    next.decisions arm ≠ none ∧
      ∀ j, j ≠ arm → next.decisions j = state.decisions j := by
  unfold checkedStep at hstep
  split_ifs at hstep with hW hlow hup hbranch
  · cases hstep
    constructor
    · simp [Function.update_self]
    · intro j hj
      simp [Function.update_of_ne hj]
  · cases hstep
    constructor
    · simp [Function.update_self]
    · intro j hj
      simp [Function.update_of_ne hj]

/-- A successful checked branch is exactly the appropriate finite filter and
decision update, with equality taking the exclusion branch. -/
theorem checkedStep_candidates_exact {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (value : UnitScalar) (state next : PrefixState K m) (arm : Fin K)
    (hstep : checkedStep mass value state arm = .ready next)
    (hstate : ∀ s, s ∈ state.candidates ↔
      agrees_with_recorded_decisions state.decisions s)
    (hfresh : state.decisions arm = none) :
    ∀ s, s ∈ next.candidates ↔
      agrees_with_recorded_decisions next.decisions s := by
  unfold checkedStep at hstep
  split_ifs at hstep with hW hlow hup hbranch
  · cases hstep
    intro s
    simp only [Finset.mem_filter]
    rw [agrees_with_recorded_decisions_update_true _ _ _ hfresh, ← hstate s]
  · cases hstep
    intro s
    simp only [Finset.mem_filter]
    rw [agrees_with_recorded_decisions_update_false _ _ _ hfresh, ← hstate s]

/-- A successful recursive stage is exactly a successful prior state followed
by one checked arm transition. -/
theorem runCheckedPrefix_ready_succ {K m : ℕ} (mass : SetCarrier K m → ℝ)
    (values : Fin K → UnitScalar) (n : ℕ) (hn : n + 1 ≤ K)
    (state : PrefixState K m)
    (hrun : runCheckedPrefix mass values (n + 1) hn = .ready state) :
    ∃ prev : PrefixState K m,
      runCheckedPrefix mass values n (Nat.le_trans (Nat.le_succ n) hn) = .ready prev ∧
      checkedStep mass (values ⟨n, Nat.lt_of_succ_le hn⟩) prev
        ⟨n, Nat.lt_of_succ_le hn⟩ = .ready state := by
  cases hprev : runCheckedPrefix mass values n
      (Nat.le_trans (Nat.le_succ n) hn) with
  | failed arm reason =>
      simp [runCheckedPrefix, checkedTransition, hprev] at hrun
  | ready prev =>
      refine ⟨prev, rfl, ?_⟩
      simpa [runCheckedPrefix, checkedTransition, hprev] using hrun

/-- Every successful prefix retains the exact recorded-decision filter
invariant and has a decision precisely on the arms already tested. Every
nonempty successful prefix also has positive raw candidate mass. -/
theorem runCheckedPrefix_ready_specs {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (state : PrefixState K m),
      runCheckedPrefix mass values n hn = .ready state →
        (∀ s, s ∈ state.candidates ↔
          agrees_with_recorded_decisions state.decisions s) ∧
        (∀ i, i.1 < n → state.decisions i ≠ none) ∧
        (∀ i, n ≤ i.1 → state.decisions i = none) ∧
        (n = 0 ∨ 0 < rawStateMass mass state) := by
  intro n
  induction n with
  | zero =>
      intro hn state hrun
      simp only [runCheckedPrefix] at hrun
      cases hrun
      refine ⟨?_, ?_, ?_, Or.inl rfl⟩
      · intro s
        simp [initialState, agrees_with_recorded_decisions]
      · intro i hi
        omega
      · intro i hi
        simp [initialState]
  | succ n ih =>
      intro hn state hrun
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      obtain ⟨prev, hprev, hstep⟩ :=
        runCheckedPrefix_ready_succ mass values n hn state hrun
      have hprevSpec := ih hn' prev hprev
      have hfresh : prev.decisions ⟨n, Nat.lt_of_succ_le hn⟩ = none :=
        hprevSpec.2.2.1 ⟨n, Nat.lt_of_succ_le hn⟩ le_rfl
      have hconsistent := checkedStep_candidates_exact mass
        (values ⟨n, Nat.lt_of_succ_le hn⟩) prev state ⟨n, Nat.lt_of_succ_le hn⟩
        hstep hprevSpec.1 hfresh
      have hdecision := checkedStep_decisions_of_ready mass
        (values ⟨n, Nat.lt_of_succ_le hn⟩) prev state
        ⟨n, Nat.lt_of_succ_le hn⟩ hstep
      have hpos := checkedStep_chosenMass_pos mass
        (values ⟨n, Nat.lt_of_succ_le hn⟩) prev state
        ⟨n, Nat.lt_of_succ_le hn⟩ hstep
      refine ⟨hconsistent, ?_, ?_, Or.inr hpos⟩
      · intro i hi
        by_cases hieq : i = (⟨n, Nat.lt_of_succ_le hn⟩ : Fin K)
        · subst i
          exact hdecision.1
        · rw [hdecision.2 i hieq]
          have hvalne : i.1 ≠ n := by
            intro hval
            apply hieq
            exact Fin.ext hval
          exact hprevSpec.2.1 i (by omega)
      · intro i hi
        have hne : i ≠ (⟨n, Nat.lt_of_succ_le hn⟩ : Fin K) := by
          intro heq
          have hval : i.1 = n := by simpa using congrArg Fin.val heq
          omega
        rw [hdecision.2 i hne]
        exact hprevSpec.2.2.1 i (by omega)

/-- The accepted normalized sampler's bounds make every checked step pass and
make its state exactly the existing `prefixStep`. -/
theorem checkedStep_eq_prefixStep {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (arm : Fin K)
    (hW : 0 < stateMass μ state) :
    checkedStep μ.weight (values arm) state arm =
      .ready (prefixStep μ values state arm) := by
  have hbounds := state_included_mass_bounds μ state arm
  have hratio : 0 ≤ stateIncludedMass μ state arm / stateMass μ state ∧
      stateIncludedMass μ state arm / stateMass μ state ≤ 1 := by
    constructor
    · exact div_nonneg hbounds.1 hW.le
    · exact (div_le_one hW).mpr hbounds.2
  by_cases hbranch : stateIncludedMass μ state arm >
      (values arm).1 * stateMass μ state
  · have hW' : 0 < rawStateMass μ.weight state := by
      simpa [rawStateMass, stateMass] using hW
    have hlow : 0 ≤ rawIncludedMass μ.weight state arm / rawStateMass μ.weight state := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hratio.1
    have hup : rawIncludedMass μ.weight state arm / rawStateMass μ.weight state ≤ 1 := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hratio.2
    have hbranch' : rawIncludedMass μ.weight state arm >
        (values arm).1 * rawStateMass μ.weight state := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hbranch
    rw [checkedStep_ready_in μ.weight (values arm) state arm hW' hlow hup hbranch']
    simp [prefixStep, hbranch]
  · have hW' : 0 < rawStateMass μ.weight state := by
      simpa [rawStateMass, stateMass] using hW
    have hlow : 0 ≤ rawIncludedMass μ.weight state arm / rawStateMass μ.weight state := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hratio.1
    have hup : rawIncludedMass μ.weight state arm / rawStateMass μ.weight state ≤ 1 := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hratio.2
    have hbranch' : ¬ rawIncludedMass μ.weight state arm >
        (values arm).1 * rawStateMass μ.weight state := by
      simpa [rawIncludedMass, rawStateMass, stateIncludedMass, stateMass] using hbranch
    rw [checkedStep_ready_out μ.weight (values arm) state arm hW' hlow hup hbranch']
    simp [prefixStep, hbranch]

/-- On accepted normalized mass, every checked prefix succeeds and computes
exactly the existing recursive prefix state. -/
theorem runCheckedPrefix_eq_prefix {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K),
      runCheckedPrefix μ.weight values n hn = .ready (runPrefix μ values n hn) := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
      intro hn
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      rw [runCheckedPrefix, ih hn']
      have hW : 0 < stateMass μ (runPrefix μ values n hn') := by
        exact run_prefix_mass_pos μ values n hn'
      change checkedStep μ.weight (values ⟨n, Nat.lt_of_succ_le hn⟩)
          (runPrefix μ values n hn') ⟨n, Nat.lt_of_succ_le hn⟩ =
        .ready (prefixStep μ values (runPrefix μ values n hn')
          ⟨n, Nat.lt_of_succ_le hn⟩)
      exact checkedStep_eq_prefixStep μ values _ _ hW

/-- Checked failures are prefix-local: changing coordinates at or after `n`
cannot change the result after the first `n` arm tests. -/
theorem runCheckedPrefix_prefix_independent {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values other : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K),
      (∀ i, i.1 < n → values i = other i) →
      runCheckedPrefix mass values n hn = runCheckedPrefix mass other n hn := by
  intro n
  induction n with
  | zero => intro hn h; rfl
  | succ n ih =>
      intro hn h
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      have hprev := ih hn' (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      change checkedTransition mass ⟨n, Nat.lt_of_succ_le hn⟩
          (runCheckedPrefix mass values n hn', values ⟨n, Nat.lt_of_succ_le hn⟩) =
        checkedTransition mass ⟨n, Nat.lt_of_succ_le hn⟩
          (runCheckedPrefix mass other n hn', other ⟨n, Nat.lt_of_succ_le hn⟩)
      rw [hprev]
      cases hrun : runCheckedPrefix mass other n hn' with
      | failed arm reason => simp [checkedTransition]
      | ready state =>
          have hcoord := h ⟨n, Nat.lt_of_succ_le hn⟩ (Nat.lt_succ_self n)
          simp [checkedTransition, hcoord]

/-- Once an earlier prefix has failed, the next recursive arm preserves that
first failure verbatim, without reading its scalar coordinate. -/
theorem runCheckedPrefix_failure_short_circuit {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar)
    (n : ℕ) (hn : n + 1 ≤ K) (arm : Fin K) (reason : FailureReason)
    (hfail : runCheckedPrefix mass values n (Nat.le_trans (Nat.le_succ n) hn) =
      .failed arm reason) :
    runCheckedPrefix mass values (n + 1) hn = .failed arm reason := by
  change checkedTransition mass ⟨n, Nat.lt_of_succ_le hn⟩
      (runCheckedPrefix mass values n
        (Nat.le_trans (Nat.le_succ n) hn), values ⟨n, Nat.lt_of_succ_le hn⟩) =
    .failed arm reason
  rw [hfail]
  rfl

/-- A positive mass on the final consistent candidate set proves that the
included-arm decision set is an actual supported `m`-set. -/
theorem final_included_arms_mem_carrier {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (state : PrefixState K m)
    (hpos : 0 < rawStateMass mass state)
    (hconsistent : ∀ s, s ∈ state.candidates ↔
      agrees_with_recorded_decisions state.decisions s)
    (hcomplete : ∀ i : Fin K, ∃ b, state.decisions i = some b) :
    (Finset.univ.filter (fun i : Fin K => state.decisions i = some true)) ∈
      (Finset.univ : Finset (Fin K)).powersetCard m := by
  have hnonempty : state.candidates.Nonempty := by
    by_contra hempty
    have hempty' : state.candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hz : rawStateMass mass state = 0 := by
      simp [rawStateMass, hempty', PrefixMassPartition.totalMass]
    rw [hz] at hpos
    exact (lt_irrefl 0 hpos)
  obtain ⟨s, hs⟩ := hnonempty
  have hagree := hconsistent s |>.mp hs
  have hvalue := agrees_with_recorded_decisions_value_eq_included_arms
    state.decisions s hcomplete hagree
  simpa [hvalue] using s.2

/-- Decision consistency and completion identify at most one candidate
supported set. -/
theorem final_candidate_unique {K m : ℕ}
    (state : PrefixState K m)
    (hconsistent : ∀ s, s ∈ state.candidates ↔
      agrees_with_recorded_decisions state.decisions s)
    (hcomplete : ∀ i : Fin K, ∃ b, state.decisions i = some b)
    (s t : SetCarrier K m) (hs : s ∈ state.candidates)
    (ht : t ∈ state.candidates) : s = t := by
  apply Subtype.ext
  apply Finset.ext
  intro i
  obtain ⟨b, hb⟩ := hcomplete i
  have hsa := (hconsistent s).mp hs i b hb
  have hta := (hconsistent t).mp ht i b hb
  exact hsa.trans hta.symm

/-- A successful full checked run with at least one arm has positive final
candidate mass. Positivity follows from its successful first scalar test and
the positive chosen-branch invariant. -/
theorem full_run_state_mass_pos {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (hK : 0 < K)
    (hfull : runCheckedPrefix mass values K le_rfl = .ready state) :
    0 < rawStateMass mass state := by
  have hspec := runCheckedPrefix_ready_specs mass values K le_rfl state hfull
  rcases hspec.2.2.2 with hzero | hpos
  · omega
  · exact hpos

/-- A successful full checked run has exactly one actual supported candidate
set. Both existence and uniqueness are proved from positive mass, the complete
decision record, and candidate/filter consistency. -/
theorem full_run_candidate_unique {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (hK : 0 < K)
    (hfull : runCheckedPrefix mass values K le_rfl = .ready state) :
    ∃! s : SetCarrier K m, s ∈ state.candidates := by
  have hspec := runCheckedPrefix_ready_specs mass values K le_rfl state hfull
  have hpos := full_run_state_mass_pos mass values state hK hfull
  have hcomplete : ∀ i : Fin K, ∃ b, state.decisions i = some b := by
    intro i
    have hi := hspec.2.1 i i.2
    cases hdecision : state.decisions i with
    | none => exact (hi hdecision).elim
    | some b => exact ⟨b, rfl⟩
  have hnonempty : state.candidates.Nonempty := by
    by_contra hempty
    have hempty' : state.candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hz : rawStateMass mass state = 0 := by
      simp [rawStateMass, hempty', PrefixMassPartition.totalMass]
    rw [hz] at hpos
    exact (lt_irrefl 0 hpos)
  obtain ⟨s, hs⟩ := hnonempty
  refine ⟨s, hs, ?_⟩
  intro t ht
  symm
  exact final_candidate_unique state hspec.1 hcomplete s t hs ht

/-- On every successful full raw run with `K > 0`, the checked output-domain
test succeeds and returns the actual included-arm set. -/
theorem full_state_output_supported {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (hK : 0 < K)
    (hfull : runCheckedPrefix mass values K le_rfl = .ready state) :
    (Finset.univ.filter (fun i : Fin K => state.decisions i = some true)) ∈
      (Finset.univ : Finset (Fin K)).powersetCard m := by
  have hspec := runCheckedPrefix_ready_specs mass values K le_rfl state hfull
  have hpos := full_run_state_mass_pos mass values state hK hfull
  have hcomplete : ∀ i : Fin K, ∃ b, state.decisions i = some b := by
    intro i
    have hi := hspec.2.1 i i.2
    cases hdecision : state.decisions i with
    | none => exact (hi hdecision).elim
    | some b => exact ⟨b, rfl⟩
  exact final_included_arms_mem_carrier mass state hpos hspec.1 hcomplete

/-- The source output check is discharged by the full-run invariants, and the
returned set is the finite set of arms whose recorded decision is inclusion. -/
theorem checkedSample_eq_actual_full_output {K m : ℕ}
    (mass : SetCarrier K m → ℝ) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (hK : 0 < K)
    (hfull : runCheckedPrefix mass values K le_rfl = .ready state) :
    checkedSample mass values = Result.sampled
      ⟨Finset.univ.filter (fun i : Fin K => state.decisions i = some true),
        full_state_output_supported mass values state hK hfull⟩ := by
  rw [checkedSample, hfull]
  have hmem := full_state_output_supported mass values state hK hfull
  have hcard := (Finset.mem_powersetCard.mp hmem).2
  simp [finishOutput, hcard]

/-- The normalized checked sampler returns the same supported set as the
accepted sampler for every scalar vector. -/
theorem checkedSample_eq_sample {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    checkedSample μ.weight values = Result.sampled (sample μ values) := by
  have hr := runCheckedPrefix_eq_prefix μ values K le_rfl
  rw [checkedSample, hr]
  have hmem : includedArms μ values ∈
      (Finset.univ : Finset (Fin K)).powersetCard m := included_arms_mem_carrier μ values
  have houtput : (Finset.univ.filter
      (fun i : Fin K => (runAll μ values).decisions i = some true)) ∈
        (Finset.univ : Finset (Fin K)).powersetCard m := by
    simpa [PrefixSetSampler.includedArms] using hmem
  change finishOutput (.ready (runAll μ values)) = Result.sampled (sample μ values)
  simp only [finishOutput, houtput]
  apply congrArg Result.sampled
  apply Subtype.ext
  rfl

/-- Every scalar check succeeds at each actual normalized prefix state. -/
theorem normalized_checks_success {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    runCheckedPrefix μ.weight values K le_rfl = .ready (runAll μ values) := by
  simpa [runAll] using runCheckedPrefix_eq_prefix μ values K le_rfl

/-- Checked success is a definitional refinement of the accepted sample, so
the entire-vector pushforward retains all `K+1` source coordinates, including
the untouched orientation coordinate. -/
theorem assignmentLaw_map_checkedSample {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) :
    (ContinuousControlSlice.assignmentLaw K).map
        (fun v => checkedSample μ.weight (prefixValues v)) =
      ((massPMF μ).toMeasure).map (fun s => Result.sampled s) := by
  have heq : (fun v : Fin (K + 1) → ContinuousControlSlice.Scalar =>
      checkedSample μ.weight (prefixValues v)) =
      fun v => Result.sampled (sample μ (prefixValues v)) := by
    funext v
    exact checkedSample_eq_sample μ (prefixValues v)
  rw [heq, ← Function.comp_def Result.sampled
      (fun v : Fin (K + 1) → ContinuousControlSlice.Scalar =>
        sample μ (prefixValues v)),
    ← Measure.map_map Measurable.of_discrete
      (measurable_sample_prefixValues μ), assignmentLaw_map_sample]

/-- Atom law transported from the accepted full-vector sample law by computed
equality, with no checked-success premise in the probability statement. -/
theorem assignmentLaw_checkedSample_singleton {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (s : SetCarrier K m) :
    ContinuousControlSlice.assignmentLaw K
      {v | checkedSample μ.weight (prefixValues v) = Result.sampled s} =
      ENNReal.ofReal (μ.weight s) := by
  have hset : {v : Fin (K + 1) → ContinuousControlSlice.Scalar |
      checkedSample μ.weight (prefixValues v) = Result.sampled s} =
      {v | sample μ (prefixValues v) = s} := by
    ext v
    change checkedSample μ.weight (prefixValues v) = Result.sampled s ↔
      sample μ (prefixValues v) = s
    rw [checkedSample_eq_sample μ]
    simp
  rw [hset, assignmentLaw_sample_singleton]

/-- Actual product-weight specialization used by the canonical assignment
vector. The source positive-weight hypotheses are those of the accepted
producer, not extra assumptions of the checker. -/
theorem productQ_checked_sampler_law {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (w : Fin K → ℝ) (hw : ∀ i, 0 < w i) :
    (ContinuousControlSlice.assignmentLaw K).map
        (fun v => checkedSample
          (CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw).weight
          (prefixValues v)) =
      ((massPMF (CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw)).toMeasure).map
        (fun s => Result.sampled s) :=
  assignmentLaw_map_checkedSample
    (CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw)

/-- The canonical product-weight producer retains each exact output atom. -/
theorem productQ_checked_sampler_singleton {K m : ℕ}
    (hm : 2 ≤ m) (hmK : m < K) (w : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (s : SetCarrier K m) :
    ContinuousControlSlice.assignmentLaw K
      {v | checkedSample
        (CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw).weight
        (prefixValues v) = Result.sampled s} =
      ENNReal.ofReal
        ((CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw).weight s) :=
  assignmentLaw_checkedSample_singleton
    (CanonicalAssignmentVector.productQNormalizedMass hm hmK w hw) s

/-- Actual corrected-window specialization on its supplied logical queue
path. This is a finite-law refinement only; it asserts no physical-history
interpretation of the supplied rounds. -/
theorem actualCorrected_checked_sampler_law
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length) :
    (ContinuousControlSlice.assignmentLaw p.K).map
        (fun x => checkedSample
          (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
          (prefixValues x)) =
      ((massPMF
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)).toMeasure).map
        (fun s => Result.sampled s) :=
  assignmentLaw_map_checkedSample
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv)

/-- The corrected logical-queue producer retains each exact output atom. -/
theorem actualCorrected_checked_sampler_singleton
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (s : SetCarrier p.K p.m) :
    ContinuousControlSlice.assignmentLaw p.K
      {x | checkedSample
        (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight
        (prefixValues x) = Result.sampled s} =
      ENNReal.ofReal
        ((RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv).weight s) :=
  assignmentLaw_checkedSample_singleton
    (RecordedCorrectedWindow.actualPrefixSamplerMass p q hcap rounds u v hu huv hv) s

end Bandits.Support.CheckedPrefixSampler

end
