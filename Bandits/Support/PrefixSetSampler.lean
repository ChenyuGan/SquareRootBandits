/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Bandits.Support.PrefixMassPartition

/-!
# Deterministic finite prefix set sampler

This module formalizes only the deterministic prefix inclusion algorithm and
its finite-support invariants. The sampler uses one literal scalar in `[0,1)`
per arm and the strict inclusion test from
`sources/zip4/manuscript/appendix_a_local_protocol.tex:77`; the scalar
coordinates are listed in
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`.
It proves no product-uniform pushforward law, orientation coupling, or
application-specific normalization.
-/

public section
noncomputable section

namespace Bandits.Support.PrefixSetSampler

/-- The genuine finite carrier of degree-`m` subsets of the `K` arms. -/
abbrev SetCarrier (K m : ℕ) :=
  {s : Finset (Fin K) // s ∈ (Finset.univ : Finset (Fin K)).powersetCard m}

/-- A scalar coordinate with the source's half-open unit interval domain. -/
abbrev UnitScalar := {v : ℝ // 0 ≤ v ∧ v < 1}

/-- A real-valued normalized finite mass on the actual degree-`m` carrier. -/
structure NormalizedMass (K m : ℕ) (hm : m ≤ K) where
  weight : SetCarrier K m → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum_eq_one :
    PrefixMassPartition.totalMass (Finset.univ : Finset (SetCarrier K m)) weight = 1

/-- The operational state after some prefix tests. `none` marks an arm not yet
tested; `some true` and `some false` record its inclusion and exclusion
decisions. -/
structure PrefixState (K m : ℕ) where
  candidates : Finset (SetCarrier K m)
  decisions : Fin K → Option Bool

/-- Candidate sets agree with every inclusion decision already recorded. -/
@[expose] def agrees_with_recorded_decisions {K m : ℕ}
    (decisions : Fin K → Option Bool) (s : SetCarrier K m) : Prop :=
  ∀ i b, decisions i = some b → (i ∈ s.1 ↔ b = true)

/-- Initial state: every degree-`m` set remains possible and no arm is tested. -/
@[expose] def initialState (K m : ℕ) : PrefixState K m :=
  ⟨Finset.univ, fun _ => none⟩

/-- Total mass in the current candidate support. -/
@[expose] def stateMass {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (state : PrefixState K m) : ℝ :=
  PrefixMassPartition.totalMass state.candidates μ.weight

/-- Current candidate mass among sets containing the next arm. -/
@[expose] def stateIncludedMass {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (state : PrefixState K m) (i : Fin K) : ℝ :=
  PrefixMassPartition.includedMass state.candidates μ.weight (fun s => i ∈ s.1)

/-- One deterministic threshold test. Equality is sent to the exclusion
branch because acceptance is the strict comparison `Win > v * W`. -/
@[expose] def prefixStep {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K) : PrefixState K m :=
  if stateIncludedMass μ state i > (values i).1 * stateMass μ state then
    ⟨state.candidates.filter (fun s => i ∈ s.1),
      Function.update state.decisions i (some true)⟩
  else
    ⟨state.candidates.filter (fun s => i ∉ s.1),
      Function.update state.decisions i (some false)⟩

/-- The state after testing arms `0, ..., n-1`, by recursion on the prefix
length. The recursive call computes the previous state; no trace or branch
equations are supplied as input. -/
@[expose] def runPrefix {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    (n : ℕ) → n ≤ K → PrefixState K m
  | 0, _ => initialState K m
  | n + 1, hn =>
      prefixStep μ values
        (runPrefix μ values n (Nat.le_trans (Nat.le_succ n) hn))
        ⟨n, Nat.lt_of_succ_le hn⟩

/-- The state after all `K` arm tests, in increasing `Fin K` order. -/
@[expose] def runAll {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) : PrefixState K m :=
  runPrefix μ values K le_rfl

/-- The literal included-arm finset recorded by the completed deterministic run. -/
@[expose] def includedArms {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) : Finset (Fin K) :=
  (Finset.univ : Finset (Fin K)).filter
    (fun i => (runAll μ values).decisions i = some true)

theorem state_mass_step_eq {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K) :
    stateMass μ (prefixStep μ values state i) =
      if stateIncludedMass μ state i > (values i).1 * stateMass μ state then
        stateIncludedMass μ state i
      else
        PrefixMassPartition.excludedMass state.candidates μ.weight (fun s => i ∈ s.1) := by
  unfold prefixStep stateMass stateIncludedMass
  split_ifs <;> rfl

theorem state_included_mass_bounds {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (state : PrefixState K m) (i : Fin K) :
    0 ≤ stateIncludedMass μ state i ∧
      stateIncludedMass μ state i ≤ stateMass μ state := by
  exact PrefixMassPartition.includedMass_bounds state.candidates μ.weight
    (fun s => i ∈ s.1) (fun s _ => μ.weight_nonneg s)

theorem prefix_step_branch_mass_pos {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K) (hW : 0 < stateMass μ state) :
    if stateIncludedMass μ state i > (values i).1 * stateMass μ state then
      0 < stateIncludedMass μ state i
    else
      0 < PrefixMassPartition.excludedMass state.candidates μ.weight
        (fun s => i ∈ s.1) := by
  have hbranches := PrefixMassPartition.thresholdBranches_have_positive_mass
    state.candidates μ.weight (fun s => i ∈ s.1) (values i).1 hW
    (values i).2.1 (values i).2.2
  by_cases h : stateIncludedMass μ state i > (values i).1 * stateMass μ state
  · simp [h]
    exact hbranches.1 h
  · simp [h]
    exact hbranches.2 h

theorem prefix_step_threshold_equality_excludes {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K) (hW : 0 < stateMass μ state)
    (heq : stateIncludedMass μ state i = (values i).1 * stateMass μ state) :
    (prefixStep μ values state i).decisions =
        Function.update state.decisions i (some false) ∧
      (prefixStep μ values state i).candidates =
        state.candidates.filter (fun s => i ∉ s.1) ∧
      0 < PrefixMassPartition.excludedMass state.candidates μ.weight
        (fun s => i ∈ s.1) := by
  have hpositive := PrefixMassPartition.thresholdEquality_goes_to_excluded
    state.candidates μ.weight (fun s => i ∈ s.1) (values i).1 hW
    (values i).2.1 (values i).2.2 heq
  constructor
  · simp [prefixStep, heq]
  constructor
  · simp [prefixStep, heq]
  · exact hpositive

theorem prefix_step_mass_pos {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K) (hW : 0 < stateMass μ state) :
    0 < stateMass μ (prefixStep μ values state i) := by
  by_cases h : stateIncludedMass μ state i > (values i).1 * stateMass μ state
  · simpa [state_mass_step_eq, h] using
      (prefix_step_branch_mass_pos μ values state i hW)
  · simpa [state_mass_step_eq, h] using
      (prefix_step_branch_mass_pos μ values state i hW)

theorem agrees_with_recorded_decisions_update_true {K m : ℕ}
    (decisions : Fin K → Option Bool) (i : Fin K) (s : SetCarrier K m)
    (hfresh : decisions i = none) :
    agrees_with_recorded_decisions (Function.update decisions i (some true)) s ↔
      agrees_with_recorded_decisions decisions s ∧ i ∈ s.1 := by
  constructor
  · intro hagree
    constructor
    · intro j b hj
      by_cases hji : j = i
      · subst j
        rw [hfresh] at hj
        cases hj
      · have hdec : Function.update decisions i (some true) j = some b := by
          simpa [Function.update_of_ne hji] using hj
        have h := hagree j b hdec
        simpa [Function.update_of_ne hji] using h
    · have hi := hagree i true (by simp [Function.update_self])
      simpa using hi
  · rintro ⟨hagree, hi⟩ j b hj
    by_cases hji : j = i
    · subst j
      simp [Function.update_self] at hj
      subst b
      simpa using hi
    · have hdec : decisions j = some b := by
        simpa [Function.update_of_ne hji] using hj
      exact hagree j b hdec

theorem agrees_with_recorded_decisions_update_false {K m : ℕ}
    (decisions : Fin K → Option Bool) (i : Fin K) (s : SetCarrier K m)
    (hfresh : decisions i = none) :
    agrees_with_recorded_decisions (Function.update decisions i (some false)) s ↔
      agrees_with_recorded_decisions decisions s ∧ i ∉ s.1 := by
  constructor
  · intro hagree
    constructor
    · intro j b hj
      by_cases hji : j = i
      · subst j
        rw [hfresh] at hj
        cases hj
      · have hdec : Function.update decisions i (some false) j = some b := by
          simpa [Function.update_of_ne hji] using hj
        have h := hagree j b hdec
        simpa [Function.update_of_ne hji] using h
    · have hi := hagree i false (by simp [Function.update_self])
      simpa using hi
  · rintro ⟨hagree, hi⟩ j b hj
    by_cases hji : j = i
    · subst j
      simp [Function.update_self] at hj
      subst b
      simpa using hi
    · have hdec : decisions j = some b := by
        simpa [Function.update_of_ne hji] using hj
      exact hagree j b hdec

theorem prefix_step_candidates_exact {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar)
    (state : PrefixState K m) (i : Fin K)
    (hstate : ∀ s, s ∈ state.candidates ↔
      agrees_with_recorded_decisions state.decisions s)
    (hfresh : state.decisions i = none) :
    ∀ s, s ∈ (prefixStep μ values state i).candidates ↔
      agrees_with_recorded_decisions (prefixStep μ values state i).decisions s := by
  intro s
  unfold prefixStep
  split_ifs with h
  · simp only [Finset.mem_filter]
    rw [agrees_with_recorded_decisions_update_true _ _ _ hfresh, ← hstate s]
  · simp only [Finset.mem_filter]
    rw [agrees_with_recorded_decisions_update_false _ _ _ hfresh, ← hstate s]

theorem run_prefix_decision_none_after {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (i : Fin K), n ≤ i.1 →
      (runPrefix μ values n hn).decisions i = none := by
  intro n
  induction n with
  | zero =>
      intro hn i hi
      rfl
  | succ n ih =>
      intro hn i hi
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      have hne : (⟨n, Nat.lt_of_succ_le hn⟩ : Fin K) ≠ i := by
        intro heq
        have hval : n = i.1 := by simpa using congrArg Fin.val heq
        omega
      simp only [runPrefix, prefixStep]
      split_ifs <;> simp only [Function.update_of_ne hne.symm]
      <;> exact ih hn' i (Nat.le_trans (Nat.le_succ n) hi)

theorem run_prefix_decisions_recorded_before {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (i : Fin K), i.1 < n →
      (runPrefix μ values n hn).decisions i ≠ none := by
  intro n
  induction n with
  | zero =>
      intro hn i hi
      omega
  | succ n ih =>
      intro hn i hi
      by_cases hin : i.1 < n
      · have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
        have hne : (⟨n, Nat.lt_of_succ_le hn⟩ : Fin K) ≠ i := by
          intro heq
          have hval : n = i.1 := by simpa using congrArg Fin.val heq
          omega
        simp only [runPrefix, prefixStep]
        split_ifs <;> simp [Function.update_of_ne hne.symm] <;> exact ih hn' i hin
      · have heq : i.1 = n := by omega
        have hi' : i = (⟨n, Nat.lt_of_succ_le hn⟩ : Fin K) := Fin.ext heq
        subst i
        simp only [runPrefix, prefixStep]
        split_ifs <;> simp [Function.update_self]

theorem run_prefix_candidates_agree {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (s : SetCarrier K m),
      s ∈ (runPrefix μ values n hn).candidates ↔
        agrees_with_recorded_decisions (runPrefix μ values n hn).decisions s := by
  intro n
  induction n with
  | zero =>
      intro hn s
      simp [runPrefix, initialState, agrees_with_recorded_decisions]
  | succ n ih =>
      intro hn s
      let prev : PrefixState K m :=
        runPrefix μ values n (Nat.le_trans (Nat.le_succ n) hn)
      let i : Fin K := ⟨n, Nat.lt_of_succ_le hn⟩
      have hfresh : prev.decisions i = none := by
        exact run_prefix_decision_none_after μ values n
          (Nat.le_trans (Nat.le_succ n) hn) i le_rfl
      have hprev : ∀ x, x ∈ prev.candidates ↔
          agrees_with_recorded_decisions prev.decisions x := by
        intro x
        exact ih (Nat.le_trans (Nat.le_succ n) hn) x
      have hstep := prefix_step_candidates_exact μ values prev i hprev hfresh s
      simpa [runPrefix, prev, i] using hstep

theorem agrees_with_recorded_decisions_iff_prefix {K m : ℕ}
    (n : ℕ) (decisions : Fin K → Option Bool) (s : SetCarrier K m)
    (hbefore : ∀ i, i.1 < n → decisions i ≠ none)
    (hafter : ∀ i, n ≤ i.1 → decisions i = none) :
    agrees_with_recorded_decisions decisions s ↔
      ∀ i, i.1 < n → (i ∈ s.1 ↔ decisions i = some true) := by
  constructor
  · intro hagree i hi
    cases hdec : decisions i with
    | none => exact (hbefore i hi hdec).elim
    | some b =>
        have hmem := hagree i b hdec
        simpa [hdec] using hmem
  · intro hprefix i b hdec
    by_cases hi : i.1 < n
    · have hmem := hprefix i hi
      simpa [hdec] using hmem
    · have hlarge : n ≤ i.1 := by omega
      rw [hafter i hlarge] at hdec
      cases hdec

theorem run_prefix_candidates_match_prefix {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (s : SetCarrier K m),
      s ∈ (runPrefix μ values n hn).candidates ↔
        ∀ i, i.1 < n →
          (i ∈ s.1 ↔ (runPrefix μ values n hn).decisions i = some true) := by
  intro n hn s
  rw [run_prefix_candidates_agree μ values n hn s]
  exact agrees_with_recorded_decisions_iff_prefix n
    (runPrefix μ values n hn).decisions s
    (fun i hi => run_prefix_decisions_recorded_before μ values n hn i hi)
    (fun i hi => run_prefix_decision_none_after μ values n hn i hi)

theorem run_prefix_mass_pos {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K), 0 < stateMass μ (runPrefix μ values n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      change 0 < PrefixMassPartition.totalMass
        (Finset.univ : Finset (SetCarrier K m)) μ.weight
      rw [μ.weight_sum_eq_one]
      norm_num
  | succ n ih =>
      intro hn
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      have hprev := ih hn'
      simpa [runPrefix] using
        prefix_step_mass_pos μ values (runPrefix μ values n hn')
          ⟨n, Nat.lt_of_succ_le hn⟩ hprev

theorem run_prefix_included_mass_bounds {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n ≤ K) (i : Fin K),
      0 ≤ stateIncludedMass μ (runPrefix μ values n hn) i ∧
        stateIncludedMass μ (runPrefix μ values n hn) i ≤
          stateMass μ (runPrefix μ values n hn) := by
  intro n hn i
  exact state_included_mass_bounds μ (runPrefix μ values n hn) i

theorem run_prefix_next_branch_mass_pos {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    ∀ n (hn : n < K),
      let state := runPrefix μ values n (Nat.le_of_lt hn)
      let i : Fin K := ⟨n, hn⟩
      if stateIncludedMass μ state i > (values i).1 * stateMass μ state then
        0 < stateIncludedMass μ state i
      else
        0 < PrefixMassPartition.excludedMass state.candidates μ.weight
          (fun s => i ∈ s.1) := by
  intro n hn
  dsimp
  exact prefix_step_branch_mass_pos μ values
    (runPrefix μ values n (Nat.le_of_lt hn)) ⟨n, hn⟩
    (run_prefix_mass_pos μ values n (Nat.le_of_lt hn))

theorem agrees_with_recorded_decisions_iff_included_arms {K m : ℕ}
    (decisions : Fin K → Option Bool) (s : SetCarrier K m)
    (hcomplete : ∀ i, ∃ b, decisions i = some b) :
    agrees_with_recorded_decisions decisions s ↔
      ∀ i, i ∈ s.1 ↔ i ∈ (Finset.univ : Finset (Fin K)).filter
        (fun j => decisions j = some true) := by
  constructor
  · intro hagree i
    rcases hcomplete i with ⟨b, hb⟩
    have hmem := hagree i b hb
    simpa [Finset.mem_filter, hb] using hmem
  · intro hagree i b hb
    have hmem := hagree i
    simpa [Finset.mem_filter, hb] using hmem

theorem run_all_decision_complete {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) (i : Fin K) :
    ∃ b, (runAll μ values).decisions i = some b := by
  cases h : (runAll μ values).decisions i with
  | none =>
      have hrecorded : (runAll μ values).decisions i ≠ none := by
        simpa [runAll] using
          run_prefix_decisions_recorded_before μ values K le_rfl i i.2
      exact (hrecorded h).elim
  | some b => exact ⟨b, rfl⟩

theorem run_all_candidates_nonempty {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    (runAll μ values).candidates.Nonempty := by
  have hpos : 0 < stateMass μ (runAll μ values) := by
    simpa [runAll] using run_prefix_mass_pos μ values K le_rfl
  by_contra hempty
  have hzero : stateMass μ (runAll μ values) = 0 := by
    change PrefixMassPartition.totalMass (runAll μ values).candidates μ.weight = 0
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp [PrefixMassPartition.totalMass]
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos)

theorem agrees_with_recorded_decisions_value_eq_included_arms {K m : ℕ}
    (decisions : Fin K → Option Bool) (s : SetCarrier K m)
    (hcomplete : ∀ i, ∃ b, decisions i = some b)
    (hagree : agrees_with_recorded_decisions decisions s) :
    s.1 = (Finset.univ : Finset (Fin K)).filter
      (fun i => decisions i = some true) := by
  ext i
  exact (agrees_with_recorded_decisions_iff_included_arms decisions s hcomplete).1
    hagree i

theorem included_arms_mem_carrier {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    includedArms μ values ∈ (Finset.univ : Finset (Fin K)).powersetCard m := by
  rcases run_all_candidates_nonempty μ values with ⟨s, hs⟩
  have hagree := (run_prefix_candidates_agree μ values K le_rfl s).1 hs
  have hcomplete : ∀ i, ∃ b, (runAll μ values).decisions i = some b :=
    run_all_decision_complete μ values
  have hvalue := agrees_with_recorded_decisions_value_eq_included_arms
    (runAll μ values).decisions s hcomplete hagree
  change includedArms μ values ∈ (Finset.univ : Finset (Fin K)).powersetCard m
  have hvalue' : s.1 = includedArms μ values := by
    simpa [includedArms] using hvalue
  rw [← hvalue']
  exact s.2

/-- The deterministic sampler's output is the constructed included-arm set,
packaged in the genuine degree-`m` set carrier. -/
@[expose] def sample {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) : SetCarrier K m :=
  ⟨includedArms μ values, included_arms_mem_carrier μ values⟩

theorem sample_val {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    (sample μ values).1 = includedArms μ values := rfl

theorem sample_card {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    (sample μ values).1.card = m :=
  (Finset.mem_powersetCard.mp (sample μ values).2).2

theorem run_all_candidates_eq_singleton {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    (runAll μ values).candidates = {sample μ values} := by
  ext s
  simp only [Finset.mem_singleton]
  constructor
  · intro hs
    have hagree := (run_prefix_candidates_agree μ values K le_rfl s).1 hs
    have hcomplete : ∀ i, ∃ b, (runAll μ values).decisions i = some b :=
      run_all_decision_complete μ values
    have hvalue := agrees_with_recorded_decisions_value_eq_included_arms
      (runAll μ values).decisions s hcomplete hagree
    apply Subtype.ext
    simpa [sample, includedArms] using hvalue
  · rintro rfl
    apply (run_prefix_candidates_agree μ values K le_rfl (sample μ values)).2
    intro i b hb
    have hb' : (runAll μ values).decisions i = some b := by
      simpa [runAll] using hb
    change i ∈ includedArms μ values ↔ b = true
    simp only [includedArms, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hb']
    simp

theorem run_all_mass_eq_sample_weight {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    stateMass μ (runAll μ values) = μ.weight (sample μ values) := by
  unfold stateMass
  rw [run_all_candidates_eq_singleton μ values]
  simp [PrefixMassPartition.totalMass]

theorem sample_weight_pos {K m : ℕ} {hm : m ≤ K}
    (μ : NormalizedMass K m hm) (values : Fin K → UnitScalar) :
    0 < μ.weight (sample μ values) := by
  rw [← run_all_mass_eq_sample_weight μ values]
  simpa [runAll] using run_prefix_mass_pos μ values K le_rfl

end Bandits.Support.PrefixSetSampler

end
