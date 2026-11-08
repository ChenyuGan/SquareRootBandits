/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.CompletePublicTable
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Pi

/-!
# False-forward-slice private prefix passing

This module formalizes one finite false-row, one-ID, one-block prefix tester.
Eligibility is selected from private randomness before and independently of
the numerical forward slice. It does not model the full reference policy.

Source: `appendix_b_communication.tex:294-338` and
`07_public_setup.tex:25-38`.
-/

public section

open MeasureTheory
open ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.ForwardPrefixSlice

/-- A numerical forward slice for one false-row, identification-index pair. -/
abbrev ForwardSlice (p : ConstructorDimensions.Parameters) := Fin p.T → Bool

/-- Labels for distinct false-row and identification-index slices. -/
abbrev SliceLabel (p : ConstructorDimensions.Parameters) :=
  Fin (ConstructorDimensions.M p) × Fin (BootstrapDimensions.A_id p)

/-- A chronological prefix contains exactly the first `min n length` eligible times. -/
@[expose] def prefixCount {α : Type*} (times : List α) (n : ℕ) : ℕ :=
  min n times.length

/-- The permanent mismatch flag after scanning the first `n` eligible times. -/
@[expose] def prefixEverMismatch {α : Type*} (times : List α) (bit : α → Bool)
    (n : ℕ) : Bool :=
  decide (∃ t, t ∈ times.take n ∧ bit t = false)

/-- The prefix scan state records its count and whether any mismatch has occurred. -/
@[expose] def prefixScanState {α : Type*} (times : List α) (bit : α → Bool)
    (n : ℕ) : ℕ × Bool :=
  (prefixCount times n, prefixEverMismatch times bit n)

/-- A prefix passes when its count reaches the quota and its permanent mismatch flag is clear. -/
@[expose] def prefixPasses {α : Type*} (times : List α) (bit : α → Bool)
    (quota : ℕ) : Prop :=
  ∃ n, n ≤ times.length ∧ quota ≤ (prefixScanState times bit n).1 ∧
    (prefixScanState times bit n).2 = false

theorem prefixEverMismatch_eq_false_iff {α : Type*} (times : List α) (bit : α → Bool)
    (n : ℕ) :
    prefixEverMismatch times bit n = false ↔ ∀ t ∈ times.take n, bit t = true := by
  simp [prefixEverMismatch]

theorem prefixPasses_iff_first_quota {α : Type*} (times : List α) (bit : α → Bool)
    {quota : ℕ} :
    prefixPasses times bit quota ↔
      quota ≤ times.length ∧ ∀ t ∈ times.take quota, bit t = true := by
  constructor
  · rintro ⟨n, hn, hcount, hmismatch⟩
    have hquota_n : quota ≤ n := by
      simpa [prefixScanState, prefixCount, Nat.min_eq_left hn] using hcount
    have hnoMismatch := (prefixEverMismatch_eq_false_iff times bit n).1 hmismatch
    refine ⟨hquota_n.trans hn, ?_⟩
    intro t ht
    apply hnoMismatch t
    have htake : (times.take n).take quota = times.take quota := by
      rw [List.take_take, Nat.min_eq_left hquota_n]
    rw [← htake] at ht
    exact (List.take_sublist _ _).subset ht
  · rintro ⟨hlen, hfirst⟩
    refine ⟨quota, hlen, ?_, ?_⟩
    · simp [prefixScanState, prefixCount, Nat.min_eq_left hlen]
    · exact (prefixEverMismatch_eq_false_iff times bit quota).2 hfirst

theorem q_dec_pos (p : ConstructorDimensions.Parameters) :
    0 < BootstrapDimensions.q_dec p := by
  rw [BootstrapDimensions.q_dec]
  have hL : 0 < BootstrapDimensions.L0 p := by
    have h := BootstrapDimensions.two_mul_b_N_le_L0 p
    have hb := ConstructorDimensions.b_N_pos p
    omega
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hL)
    (ConstructorDimensions.b_N_pos p)

/-- The source Bernoulli parameter is the probability of a true forward bit. -/
@[expose] noncomputable def forwardTrueProbability (p : ConstructorDimensions.Parameters) : ℝ :=
  1 - 1 / (BootstrapDimensions.L0 p : ℝ)

theorem forwardTrueProbability_nonneg (p : ConstructorDimensions.Parameters) :
    0 ≤ forwardTrueProbability p := by
  rw [forwardTrueProbability]
  have hL : 1 ≤ BootstrapDimensions.L0 p := by
    have := BootstrapDimensions.two_mul_b_N_le_L0 p
    have := ConstructorDimensions.b_N_pos p
    omega
  have hL' : (1 : ℝ) ≤ (BootstrapDimensions.L0 p : ℝ) := by exact_mod_cast hL
  have hLpos : 0 < (BootstrapDimensions.L0 p : ℝ) := by positivity
  rw [sub_nonneg]
  exact (div_le_one hLpos).2 hL'

theorem forwardTrueProbability_le_exp_bound (p : ConstructorDimensions.Parameters) :
    forwardTrueProbability p ^ BootstrapDimensions.q_dec p ≤
      Real.exp (-8 * (ConstructorDimensions.b_N p : ℝ)) := by
  have hL : 1 ≤ BootstrapDimensions.L0 p := by
    have := BootstrapDimensions.two_mul_b_N_le_L0 p
    have := ConstructorDimensions.b_N_pos p
    omega
  have ht : (1 : ℝ) ≤ (BootstrapDimensions.q_dec p : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (q_dec_pos p))
  have hdiv := Real.one_sub_div_pow_le_exp_neg (n := BootstrapDimensions.q_dec p)
    (t := 8 * (ConstructorDimensions.b_N p : ℝ)) (by
      rw [BootstrapDimensions.q_dec]
      have hb : 0 < (ConstructorDimensions.b_N p : ℝ) := by
        exact_mod_cast ConstructorDimensions.b_N_pos p
      have hLreal : (1 : ℝ) ≤ (BootstrapDimensions.L0 p : ℝ) := by exact_mod_cast hL
      rw [Nat.cast_mul, Nat.cast_mul]
      calc
        8 * (ConstructorDimensions.b_N p : ℝ) =
            (8 * (ConstructorDimensions.b_N p : ℝ)) * 1 := by ring
        _ ≤ (8 * (ConstructorDimensions.b_N p : ℝ)) *
              (BootstrapDimensions.L0 p : ℝ) :=
          mul_le_mul_of_nonneg_left hLreal (by positivity)
        _ = 8 * (BootstrapDimensions.L0 p : ℝ) *
              (ConstructorDimensions.b_N p : ℝ) := by ring)
  have hratio :
      (1 : ℝ) - (8 * (ConstructorDimensions.b_N p : ℝ)) /
        (BootstrapDimensions.q_dec p : ℝ) = forwardTrueProbability p := by
    rw [BootstrapDimensions.q_dec, Nat.cast_mul, Nat.cast_mul]
    rw [forwardTrueProbability]
    have hb0 : (ConstructorDimensions.b_N p : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast ConstructorDimensions.b_N_pos p)
    have hL0 : (BootstrapDimensions.L0 p : ℝ) ≠ 0 := by positivity
    field_simp [hb0, hL0]
    ring
  rw [hratio] at hdiv
  simpa only [neg_mul] using hdiv

/-- A private-randomness-selected set of eligible times in one calendar block.
The choice function has no forward-slice argument. -/
structure EligibleListFunction (p : ConstructorDimensions.Parameters)
    (s : Fin (BootstrapDimensions.n_boot p)) (Ω : Type*) [MeasurableSpace Ω] where
  choose : Ω → Finset (Fin p.T)
  choose_subset : ∀ ω, choose ω ⊆ BootstrapDimensions.calendarBlock p s
  measurable_choose : Measurable choose

/-- Sort the selected times into chronological order. -/
@[expose] noncomputable def chronologicalEligibleTimes
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω) :
    List (Fin p.T) := (E.choose ω).sort

theorem chronologicalEligibleTimes_nodup
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω) :
    (chronologicalEligibleTimes E ω).Nodup :=
  Finset.sort_nodup _ _

theorem chronologicalEligibleTimes_sorted
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω) :
    (chronologicalEligibleTimes E ω).SortedLT :=
  Finset.sortedLT_sort _

theorem chronologicalEligibleTimes_mem_calendarBlock
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω)
    {t : Fin p.T} (ht : t ∈ chronologicalEligibleTimes E ω) :
    t ∈ BootstrapDimensions.calendarBlock p s := by
  exact E.choose_subset ω ((Finset.mem_sort _).1 ht)

/-- The literal passing event for the sorted private eligible times and a supplied slice. -/
@[expose] def privatePrefixPasses {p : ConstructorDimensions.Parameters}
    {s : Fin (BootstrapDimensions.n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (E : EligibleListFunction p s Ω) (ω : Ω) (slice : ForwardSlice p) : Prop :=
  prefixPasses (chronologicalEligibleTimes E ω) slice (BootstrapDimensions.q_dec p)

theorem privatePrefixPasses_iff_first_q
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω)
    (slice : ForwardSlice p) :
    privatePrefixPasses E ω slice ↔
      BootstrapDimensions.q_dec p ≤ (chronologicalEligibleTimes E ω).length ∧
        ∀ t ∈ (chronologicalEligibleTimes E ω).take (BootstrapDimensions.q_dec p),
          slice t = true := by
  exact prefixPasses_iff_first_quota _ _ (quota := BootstrapDimensions.q_dec p)

/-- The set of private outcomes for which a fixed numerical slice passes. -/
@[expose] def privatePrefixPassSet {p : ConstructorDimensions.Parameters}
    {s : Fin (BootstrapDimensions.n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (E : EligibleListFunction p s Ω) (slice : ForwardSlice p) : Set Ω :=
  {ω | privatePrefixPasses E ω slice}

theorem measurableSet_privatePrefixPassSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω)
    (slice : ForwardSlice p) : MeasurableSet (privatePrefixPassSet E slice) := by
  classical
  let test : Finset (Fin p.T) → Bool := fun selected =>
    decide (prefixPasses (selected.sort) slice (BootstrapDimensions.q_dec p))
  have htest : Measurable test := measurable_of_finite test
  have hdec : Measurable (test ∘ E.choose) := htest.comp E.measurable_choose
  have hset : privatePrefixPassSet E slice = (test ∘ E.choose) ⁻¹' {true} := by
    ext ω
    simp [privatePrefixPassSet, privatePrefixPasses, test, Function.comp_def,
      chronologicalEligibleTimes]
  rw [hset]
  exact hdec (measurableSet_singleton true)

/-- The private passing probability as a literal integral of the indicator. -/
@[expose] noncomputable def integratedPrivatePassing
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (slice : ForwardSlice p) : ℝ :=
  ∫ ω, (privatePrefixPassSet E slice).indicator (fun _ => (1 : ℝ)) ω ∂P

theorem integratedPrivatePassing_eq_measureReal
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (slice : ForwardSlice p) :
    integratedPrivatePassing P E slice = P.real (privatePrefixPassSet E slice) := by
  change (∫ ω, (privatePrefixPassSet E slice).indicator 1 ω ∂P) = _
  exact integral_indicator_one (measurableSet_privatePrefixPassSet E slice)

theorem integratedPrivatePassing_nonneg
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (slice : ForwardSlice p) :
    0 ≤ integratedPrivatePassing P E slice := by
  rw [integratedPrivatePassing_eq_measureReal]
  positivity

theorem integratedPrivatePassing_le_one
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (slice : ForwardSlice p) :
    integratedPrivatePassing P E slice ≤ 1 := by
  rw [integratedPrivatePassing_eq_measureReal]
  exact measureReal_le_one

theorem measurable_integratedPrivatePassing
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) :
    Measurable (integratedPrivatePassing P E) := by
  classical
  exact measurable_of_finite _

/-- Probability that a fixed ID-coordinate slice is one on every time in a finite set. -/
theorem forwardRow_allTrue_probability_finset (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (times : Finset (Fin p.T)) :
    (CompletePublicTable.forwardRowMeasure p).real
      {x | ∀ t ∈ times, x u t = true} =
        forwardTrueProbability p ^ times.card := by
  classical
  let f : Fin p.T → CompletePublicTable.ForwardRow p → Bool := fun t x => x u t
  have hmap : Function.Injective (fun t : Fin p.T =>
      (u, t) : Fin p.T → Fin (BootstrapDimensions.A_id p) × Fin p.T) := by
    intro t r h
    exact congrArg Prod.snd h
  have hindep : iIndepFun f (CompletePublicTable.forwardRowMeasure p) := by
    change iIndepFun (fun t x => CompletePublicTable.forwardRowCoordinate p u t x)
      (CompletePublicTable.forwardRowMeasure p)
    exact (CompletePublicTable.iIndepFun_forwardRowCoordinate p).precomp hmap
  let phi : Bool → ℝ := fun b => if b = true then 1 else 0
  have hphi : Measurable phi := measurable_of_finite phi
  have hcoordMeas : ∀ t : Fin p.T,
      AEMeasurable (f t) (CompletePublicTable.forwardRowMeasure p) := by
    intro t
    exact CompletePublicTable.measurable_forwardRowCoordinate p u t |>.aemeasurable
  have hphiComp : ∀ t : Fin p.T,
      AEStronglyMeasurable phi ((CompletePublicTable.forwardRowMeasure p).map (f t)) := by
    intro t
    change AEStronglyMeasurable phi
      ((CompletePublicTable.forwardRowMeasure p).map
        (CompletePublicTable.forwardRowCoordinate p u t))
    rw [CompletePublicTable.forwardRowCoordinate_map p u t]
    exact hphi.aestronglyMeasurable
  let psi : Fin p.T → Bool → ℝ := fun t b => if t ∈ times then phi b else 1
  have hpsi : ∀ t : Fin p.T,
      AEStronglyMeasurable (psi t) ((CompletePublicTable.forwardRowMeasure p).map (f t)) := by
    intro t
    by_cases ht : t ∈ times
    · simpa [psi, ht] using hphiComp t
    · simpa [psi, ht] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : Bool => (1 : ℝ))
            ((CompletePublicTable.forwardRowMeasure p).map (f t)))
  have hprod := hindep.integral_fun_prod_comp hcoordMeas hpsi
  have hprodFun (x : CompletePublicTable.ForwardRow p) :
      (∏ t : Fin p.T, psi t (f t x)) =
        Set.indicator ({x | ∀ t ∈ times, x u t = true} :
          Set (CompletePublicTable.ForwardRow p)) (fun _ => (1 : ℝ)) x := by
    let event : Fin p.T → Set (CompletePublicTable.ForwardRow p) :=
      fun t => {y | f t y = true}
    change (∏ t : Fin p.T,
      (if t ∈ times then phi (f t x) else 1)) = _
    rw [Finset.prod_ite_mem]
    simp only [Finset.univ_inter]
    have hfactor (t : Fin p.T) :
        phi (f t x) = Set.indicator (event t) (fun _ => (1 : ℝ)) x := by
      cases h : f t x <;> simp [phi, event, f, h]
    simp_rw [hfactor]
    rw [prod_indicator_const_apply]
    simp [event, f, Set.indicator_apply, Set.mem_iInter]
  have hset : MeasurableSet
      ({x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true}) := by
    rw [show ({x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} :
        Set (CompletePublicTable.ForwardRow p)) =
          ⋂ t : times, {x | x u t.1 = true} by
        ext x
        simp [Set.mem_iInter]]
    apply MeasurableSet.iInter
    intro t
    exact measurableSet_preimage
      (CompletePublicTable.measurable_forwardRowCoordinate p u t.1)
      (measurableSet_singleton true)
  rw [← integral_indicator_one hset]
  calc
    ∫ x, ({x | ∀ t ∈ times, x u t = true} :
        Set (CompletePublicTable.ForwardRow p)).indicator (fun _ => (1 : ℝ)) x
        ∂CompletePublicTable.forwardRowMeasure p
      = ∫ x, ∏ t : Fin p.T, psi t (f t x) ∂CompletePublicTable.forwardRowMeasure p := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => (hprodFun x).symm)
    _ = ∏ t : Fin p.T,
          ∫ x, psi t (f t x) ∂CompletePublicTable.forwardRowMeasure p := hprod
    _ = forwardTrueProbability p ^ times.card := by
      have hsingle (t : Fin p.T) :
          (∫ x, psi t (f t x) ∂CompletePublicTable.forwardRowMeasure p) =
            if t ∈ times then forwardTrueProbability p else 1 := by
        by_cases ht : t ∈ times
        · have hpsi_t : psi t = phi := by
            funext b
            exact ite_eq_left ht
          rw [hpsi_t, ite_eq_left ht]
          calc
            (∫ x, phi (f t x) ∂CompletePublicTable.forwardRowMeasure p) =
                ∫ x, (CompletePublicTable.forwardRowCoordinate p u t ⁻¹' {true}).indicator
                  (fun _ : CompletePublicTable.ForwardRow p => (1 : ℝ)) x
                  ∂CompletePublicTable.forwardRowMeasure p := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun x => by
                      simp [phi, f, CompletePublicTable.forwardRowCoordinate,
                        Set.indicator_apply]
            _ = forwardTrueProbability p := by
              rw [integral_indicator_const 1 (measurableSet_preimage
                (CompletePublicTable.measurable_forwardRowCoordinate p u t)
                (measurableSet_singleton true))]
              simp only [smul_eq_mul, mul_one]
              rw [show (CompletePublicTable.forwardRowMeasure p).real
                  (CompletePublicTable.forwardRowCoordinate p u t ⁻¹' {true}) =
                  (CompletePublicTable.forwardRowMeasure p).real
                    {x | CompletePublicTable.forwardRowCoordinate p u t x = true} by
                    congr 1]
              rw [CompletePublicTable.forwardRowCoordinate_true_mass]
              rw [forwardTrueProbability]
        · simp [psi, ht]
      rw [Finset.prod_congr rfl (fun t _ => hsingle t)]
      rw [Finset.prod_ite_mem]
      simp [Finset.prod_const, forwardTrueProbability]

theorem measurableSet_forwardRow_allTrue (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (times : Finset (Fin p.T)) :
    MeasurableSet {x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} := by
  rw [show ({x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} :
      Set (CompletePublicTable.ForwardRow p)) =
        ⋂ t : times, {x | x u t.1 = true} by
      ext x
      simp [Set.mem_iInter]]
  apply MeasurableSet.iInter
  intro t
  exact measurableSet_preimage
    (CompletePublicTable.measurable_forwardRowCoordinate p u t.1)
    (measurableSet_singleton true)

theorem measurableSet_forwardRow_allTrue_list (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (times : List (Fin p.T)) :
    MeasurableSet {x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} := by
  rw [show ({x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} :
      Set (CompletePublicTable.ForwardRow p)) =
        {x | ∀ t ∈ times.toFinset, x u t = true} by
      ext x
      simp]
  exact measurableSet_forwardRow_allTrue p u times.toFinset

theorem forwardRow_allTrue_probability_list (p : ConstructorDimensions.Parameters)
    (u : Fin (BootstrapDimensions.A_id p)) (times : List (Fin p.T)) (hnodup : times.Nodup) :
    (CompletePublicTable.forwardRowMeasure p).real
      {x | ∀ t ∈ times, x u t = true} = forwardTrueProbability p ^ times.length := by
  rw [show ({x : CompletePublicTable.ForwardRow p | ∀ t ∈ times, x u t = true} :
      Set (CompletePublicTable.ForwardRow p)) =
        {x | ∀ t ∈ times.toFinset, x u t = true} by
      ext x
      simp]
  rw [forwardRow_allTrue_probability_finset, List.toFinset_card_of_nodup hnodup]

/-- For one fixed eligible list, the false-slice passing probability is exactly
`p^q` when at least `q` distinct entries are eligible, and zero otherwise. -/
theorem privatePassing_slice_integral
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω]
    (E : EligibleListFunction p s Ω) (ω : Ω) (u : Fin (BootstrapDimensions.A_id p)) :
    (∫ x : CompletePublicTable.ForwardRow p,
      ({x | privatePrefixPasses E ω (fun t => x u t)} :
        Set (CompletePublicTable.ForwardRow p)).indicator
        (fun _ => (1 : ℝ)) x ∂CompletePublicTable.forwardRowMeasure p) =
      (if BootstrapDimensions.q_dec p ≤ (chronologicalEligibleTimes E ω).length
        then (1 : ℝ) else 0) *
          forwardTrueProbability p ^ BootstrapDimensions.q_dec p := by
  classical
  let times := chronologicalEligibleTimes E ω
  let q := BootstrapDimensions.q_dec p
  change (∫ x : CompletePublicTable.ForwardRow p,
      ({x | privatePrefixPasses E ω (fun t => x u t)} :
        Set (CompletePublicTable.ForwardRow p)).indicator (fun _ => (1 : ℝ)) x
        ∂CompletePublicTable.forwardRowMeasure p) =
      (if q ≤ times.length then (1 : ℝ) else 0) * forwardTrueProbability p ^ q
  by_cases hq : q ≤ times.length
  · have hset :
        {x : CompletePublicTable.ForwardRow p | privatePrefixPasses E ω (fun t => x u t)} =
          {x | ∀ t ∈ times.take q, x u t = true} := by
      ext x
      change prefixPasses times (fun t => x u t) q ↔ _
      rw [prefixPasses_iff_first_quota]
      simp [times, q, hq]
    rw [hset]
    rw [integral_indicator_const 1 (measurableSet_forwardRow_allTrue_list p u (times.take q))]
    simp only [smul_eq_mul, mul_one]
    rw [forwardRow_allTrue_probability_list p u (times.take q)
      (List.Nodup.sublist (List.take_sublist q times) (chronologicalEligibleTimes_nodup E ω))]
    simp [List.length_take, hq]
  · have hset :
        {x : CompletePublicTable.ForwardRow p | privatePrefixPasses E ω (fun t => x u t)} =
          ∅ := by
      ext x
      change prefixPasses times (fun t => x u t) q ↔ _
      rw [prefixPasses_iff_first_quota]
      simp [times, q, hq]
    rw [hset]
    simp [q, hq]

/-- The private and numerical slice variables used by the one-context tester. -/
@[expose] def jointPrivatePrefixPassSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω)
    (u : Fin (BootstrapDimensions.A_id p)) :
    Set (Ω × CompletePublicTable.ForwardRow p) :=
  {z | privatePrefixPasses E z.1 (fun t => z.2 u t)}

theorem measurableSet_jointPrivatePrefixPassSet
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω)
    (u : Fin (BootstrapDimensions.A_id p)) :
    MeasurableSet (jointPrivatePrefixPassSet E u) := by
  classical
  let input : Ω × CompletePublicTable.ForwardRow p →
      Finset (Fin p.T) × ForwardSlice p :=
    fun z => (E.choose z.1, fun t => z.2 u t)
  let test : Finset (Fin p.T) × ForwardSlice p → Bool := fun pair =>
    decide (prefixPasses (pair.1.sort) pair.2 (BootstrapDimensions.q_dec p))
  have hchoose : Measurable (fun z : Ω × CompletePublicTable.ForwardRow p => E.choose z.1) :=
    E.measurable_choose.comp measurable_fst
  have hslice : Measurable (fun z : Ω × CompletePublicTable.ForwardRow p =>
      fun t => z.2 u t) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (CompletePublicTable.measurable_forwardRowCoordinate p u t).comp measurable_snd
  have hinput : Measurable input := Measurable.prodMk hchoose hslice
  have htest : Measurable test := measurable_of_finite test
  have hdec : Measurable (test ∘ input) := htest.comp hinput
  have hset : jointPrivatePrefixPassSet E u = (test ∘ input) ⁻¹' {true} := by
    ext z
    simp [jointPrivatePrefixPassSet, test, input, privatePrefixPasses,
      chronologicalEligibleTimes, Function.comp_def]
  rw [hset]
  exact hdec (measurableSet_singleton true)

/-- The private quota weight in the source average over eligible lists. -/
@[expose] noncomputable def privateQuotaSuccessWeight
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω) : ℝ :=
  (if BootstrapDimensions.q_dec p ≤ (chronologicalEligibleTimes E ω).length
    then (1 : ℝ) else 0) *
      forwardTrueProbability p ^ BootstrapDimensions.q_dec p

theorem measurableSet_privateQuotaEvent
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) :
    MeasurableSet {ω | BootstrapDimensions.q_dec p ≤
      (chronologicalEligibleTimes E ω).length} := by
  classical
  let test : Finset (Fin p.T) → Bool := fun selected =>
    decide (BootstrapDimensions.q_dec p ≤ selected.sort.length)
  have htest : Measurable test := measurable_of_finite test
  have hdec : Measurable (test ∘ E.choose) := htest.comp E.measurable_choose
  have hset : {ω | BootstrapDimensions.q_dec p ≤
      (chronologicalEligibleTimes E ω).length} = (test ∘ E.choose) ⁻¹' {true} := by
    ext ω
    simp [test, Function.comp_def, chronologicalEligibleTimes]
  rw [hset]
  exact hdec (measurableSet_singleton true)

/-- Fubini gives the exact private-list expectation of the forward-slice passing probability. -/
theorem integratedPrivatePassing_mean_eq_privateExpectation
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (u : Fin (BootstrapDimensions.A_id p)) :
    (∫ x : CompletePublicTable.ForwardRow p,
      integratedPrivatePassing P E (fun t => x u t)
        ∂CompletePublicTable.forwardRowMeasure p) =
      ∫ ω, privateQuotaSuccessWeight E ω ∂P := by
  let f : Ω → CompletePublicTable.ForwardRow p → ℝ := fun ω x =>
    (jointPrivatePrefixPassSet E u).indicator (fun _ => (1 : ℝ)) (ω, x)
  have hf : Integrable (Function.uncurry f)
      (P.prod (CompletePublicTable.forwardRowMeasure p)) := by
    change Integrable ((jointPrivatePrefixPassSet E u).indicator
      (fun _ => (1 : ℝ))) (P.prod (CompletePublicTable.forwardRowMeasure p))
    exact (integrable_const 1).indicator (measurableSet_jointPrivatePrefixPassSet E u)
  calc
    (∫ x : CompletePublicTable.ForwardRow p,
      integratedPrivatePassing P E (fun t => x u t)
        ∂CompletePublicTable.forwardRowMeasure p) =
      ∫ x, ∫ ω, f ω x ∂P ∂CompletePublicTable.forwardRowMeasure p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => rfl
    _ = ∫ ω, ∫ x, f ω x ∂CompletePublicTable.forwardRowMeasure p ∂P :=
      (integral_integral_swap (f := f) hf).symm
    _ = ∫ ω, privateQuotaSuccessWeight E ω ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        calc
          (∫ x, f ω x ∂CompletePublicTable.forwardRowMeasure p) =
              ∫ x, ({x | privatePrefixPasses E ω (fun t => x u t)} :
                Set (CompletePublicTable.ForwardRow p)).indicator
                  (fun _ => (1 : ℝ)) x ∂CompletePublicTable.forwardRowMeasure p := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun x => rfl
          _ = privateQuotaSuccessWeight E ω := by
                simpa [privateQuotaSuccessWeight] using
                  (privatePassing_slice_integral E ω u)

theorem integratedPrivatePassing_mean_le_first_q_power
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (u : Fin (BootstrapDimensions.A_id p)) :
    (∫ x : CompletePublicTable.ForwardRow p,
      integratedPrivatePassing P E (fun t => x u t)
        ∂CompletePublicTable.forwardRowMeasure p) ≤
      forwardTrueProbability p ^ BootstrapDimensions.q_dec p := by
  rw [integratedPrivatePassing_mean_eq_privateExpectation]
  change (∫ ω, (if BootstrapDimensions.q_dec p ≤
      (chronologicalEligibleTimes E ω).length then (1 : ℝ) else 0) *
        forwardTrueProbability p ^ BootstrapDimensions.q_dec p ∂P) ≤ _
  have hindicator :
      (fun ω : Ω => (if BootstrapDimensions.q_dec p ≤
          (chronologicalEligibleTimes E ω).length then (1 : ℝ) else 0)) =
        (fun ω => ({ω | BootstrapDimensions.q_dec p ≤
          (chronologicalEligibleTimes E ω).length} : Set Ω).indicator
            (fun _ => (1 : ℝ)) ω) := by
    funext ω
    simp [Set.indicator_apply]
  rw [integral_mul_const, hindicator,
    integral_indicator_const 1 (measurableSet_privateQuotaEvent E)]
  simp only [smul_eq_mul, mul_one]
  have hp : 0 ≤ forwardTrueProbability p ^ BootstrapDimensions.q_dec p :=
    pow_nonneg (forwardTrueProbability_nonneg p) _
  calc
    P.real {ω | BootstrapDimensions.q_dec p ≤
        (chronologicalEligibleTimes E ω).length} *
          forwardTrueProbability p ^ BootstrapDimensions.q_dec p
      ≤ 1 * forwardTrueProbability p ^ BootstrapDimensions.q_dec p :=
        mul_le_mul_of_nonneg_right measureReal_le_one hp
    _ = forwardTrueProbability p ^ BootstrapDimensions.q_dec p := by ring

/-- The family of full time slices, indexed by actual false-row and ID labels. -/
abbrev SliceFamily (p : ConstructorDimensions.Parameters) :=
  SliceLabel p → ForwardSlice p

/-- The one-slice marginal law inherited from the full forward-bit product law. -/
@[expose] noncomputable def forwardSliceMeasure (p : ConstructorDimensions.Parameters) :
    Measure (ForwardSlice p) :=
  Measure.pi (fun _ : Fin p.T => CompletePublicTable.forwardBitLaw p)

instance forwardSliceMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (forwardSliceMeasure p) := by
  dsimp [forwardSliceMeasure]
  infer_instance

/-- Extract all `(false row, ID)` slices from the existing complete forward family. -/
@[expose] def forwardSliceFamily (p : ConstructorDimensions.Parameters)
    (x : CompletePublicTable.ForwardFamily p) : SliceFamily p :=
  fun label t => x label.1 label.2 t

/-- Extract one slice at a literal `(false row, ID)` label. -/
@[expose] def forwardSliceAt (p : ConstructorDimensions.Parameters)
    (label : SliceLabel p) (x : CompletePublicTable.ForwardFamily p) : ForwardSlice p :=
  fun t => x label.1 label.2 t

private theorem nestedPi₂_flatten_law {ι κ γ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace γ] (ν : Measure γ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => ν))).map
      (fun x : ι → κ → γ => fun ij : ι × κ => x ij.1 ij.2) =
        Measure.pi (fun _ : ι × κ => ν) := by
  classical
  let flatten : (ι → κ → γ) → (ι × κ → γ) := fun x ij => x ij.1 ij.2
  have hflatten : Measurable flatten := by
    apply measurable_pi_iff.mpr
    intro ij
    exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hflatten.aemeasurable (MeasurableSet.univ_pi hs)]
  have hpre : flatten ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    simp [flatten, Set.mem_pi]
  rw [hpre]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type' (fun i j => ν (s (i, j)))).symm

theorem measurable_forwardSliceFamily (p : ConstructorDimensions.Parameters) :
    Measurable (forwardSliceFamily p) := by
  apply measurable_pi_iff.mpr
  intro label
  apply measurable_pi_iff.mpr
  intro t
  exact CompletePublicTable.measurable_forwardCoordinate p label.1 label.2 t

/-- Re-grouping the accepted flattened full-family law gives independent complete slices. -/
theorem forwardSliceFamily_map_eq_product (p : ConstructorDimensions.Parameters) :
    (CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceFamily p) =
      Measure.pi (fun _ : SliceLabel p => forwardSliceMeasure p) := by
  classical
  let groupCoord := SliceLabel p × Fin p.T
  let fullCoord := Fin (ConstructorDimensions.M p) ×
    Fin (BootstrapDimensions.A_id p) × Fin p.T
  let coordEquiv : groupCoord ≃ fullCoord :=
    Equiv.prodAssoc (Fin (ConstructorDimensions.M p))
      (Fin (BootstrapDimensions.A_id p)) (Fin p.T)
  let reindex : (fullCoord → Bool) → (groupCoord → Bool) :=
    fun z ij => z (coordEquiv ij)
  let curry : (groupCoord → Bool) ≃ᵐ SliceFamily p :=
    MeasurableEquiv.curry (SliceLabel p) (Fin p.T) Bool
  have hreindex :
      (Measure.pi (fun _ : fullCoord => CompletePublicTable.forwardBitLaw p)).map reindex =
        Measure.pi (fun _ : groupCoord => CompletePublicTable.forwardBitLaw p) := by
    change (Measure.pi (fun _ : fullCoord => CompletePublicTable.forwardBitLaw p)).map
      (MeasurableEquiv.piCongrLeft (fun _ : groupCoord => Bool) coordEquiv.symm) = _
    exact Measure.pi_map_piCongrLeft coordEquiv.symm
      (fun _ : groupCoord => CompletePublicTable.forwardBitLaw p)
  have htargetFlat :
      (Measure.pi (fun _ : SliceLabel p => forwardSliceMeasure p)).map curry.symm =
        Measure.pi (fun _ : groupCoord => CompletePublicTable.forwardBitLaw p) := by
    change (Measure.pi (fun _ : SliceLabel p =>
        Measure.pi (fun _ : Fin p.T => CompletePublicTable.forwardBitLaw p))).map
          (fun f : SliceFamily p => fun coord : groupCoord => f coord.1 coord.2) = _
    exact nestedPi₂_flatten_law (ι := SliceLabel p) (κ := Fin p.T)
      (ν := CompletePublicTable.forwardBitLaw p)
  have hactualFlat :
      ((CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceFamily p)).map curry.symm =
        Measure.pi (fun _ : groupCoord => CompletePublicTable.forwardBitLaw p) := by
    have hfun :
        (fun x : CompletePublicTable.ForwardFamily p => curry.symm (forwardSliceFamily p x)) =
          fun x => reindex (CompletePublicTable.forwardFamilyFlatten p x) := by
      funext x
      ext ij
      change forwardSliceFamily p x ij.1 ij.2 =
        (CompletePublicTable.forwardFamilyFlatten p x) (coordEquiv ij)
      rcases ij with ⟨⟨v, u⟩, t⟩
      rfl
    calc
      ((CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceFamily p)).map curry.symm =
          (CompletePublicTable.forwardFamilyMeasure p).map
            (fun x => curry.symm (forwardSliceFamily p x)) := by
              rw [Measure.map_map curry.symm.measurable
                (measurable_forwardSliceFamily p)]
              rfl
      _ = (CompletePublicTable.forwardFamilyMeasure p).map
            (fun x => reindex (CompletePublicTable.forwardFamilyFlatten p x)) := by rw [hfun]
      _ = ((CompletePublicTable.forwardFamilyMeasure p).map
            (CompletePublicTable.forwardFamilyFlatten p)).map reindex := by
              rw [Measure.map_map (by
                apply measurable_pi_iff.mpr
                intro ij
                exact measurable_pi_apply (coordEquiv ij))
                (CompletePublicTable.measurable_forwardFamilyFlatten p)]
              rfl
      _ = Measure.pi (fun _ : groupCoord => CompletePublicTable.forwardBitLaw p) := by
            rw [CompletePublicTable.forwardFamily_flatten_law]
            exact hreindex
  apply curry.symm.measurableEmbedding.map_injective
  exact hactualFlat.trans htargetFlat.symm

theorem measurable_forwardSliceAt (p : ConstructorDimensions.Parameters)
    (label : SliceLabel p) :
    Measurable (forwardSliceAt p label) := by
  apply measurable_pi_iff.mpr
  intro t
  exact CompletePublicTable.measurable_forwardCoordinate p label.1 label.2 t

/-- The complete forward slices at distinct literal labels are independent. -/
theorem iIndepFun_forwardSlices (p : ConstructorDimensions.Parameters) :
    iIndepFun (fun label : SliceLabel p => forwardSliceAt p label)
      (CompletePublicTable.forwardFamilyMeasure p) := by
  have hmeas : ∀ label : SliceLabel p,
      AEMeasurable (forwardSliceAt p label) (CompletePublicTable.forwardFamilyMeasure p) := by
    intro label
    exact (measurable_forwardSliceAt p label).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  change (CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceFamily p) =
    Measure.pi (fun label : SliceLabel p =>
      (CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceAt p label))
  rw [forwardSliceFamily_map_eq_product]
  congr 1
  funext label
  symm
  calc
    (CompletePublicTable.forwardFamilyMeasure p).map (forwardSliceAt p label) =
        (Measure.pi (fun _ : SliceLabel p => forwardSliceMeasure p)).map
          (fun f : SliceFamily p => f label) := by
            have hfun : forwardSliceAt p label =
                (fun f : SliceFamily p => f label) ∘ forwardSliceFamily p := by
              funext x
              rfl
            rw [hfun, ← Measure.map_map (measurable_pi_apply label)
              (measurable_forwardSliceFamily p), forwardSliceFamily_map_eq_product]
    _ = forwardSliceMeasure p :=
      (measurePreserving_eval
        (fun _ : SliceLabel p => forwardSliceMeasure p) label).map_eq

/-- Integrating the private tester separately on each fixed label preserves slice independence. -/
theorem iIndepFun_integratedPrivatePassing_family
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) :
    iIndepFun
      (fun label x => integratedPrivatePassing P (E label) (forwardSliceAt p label x))
      (CompletePublicTable.forwardFamilyMeasure p) := by
  exact (iIndepFun_forwardSlices p).comp
    (fun label slice => integratedPrivatePassing P (E label) slice)
    (fun label => measurable_integratedPrivatePassing P (E label))

/-- Fubini's private-list mean for a slice in the full forward-family law. -/
theorem integratedPrivatePassing_family_mean_eq_privateExpectation
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (label : SliceLabel p) :
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) =
      ∫ ω, privateQuotaSuccessWeight E ω ∂P := by
  let projection : CompletePublicTable.ForwardFamily p → CompletePublicTable.ForwardRow p :=
    fun x => x label.1
  let g : CompletePublicTable.ForwardRow p → ℝ := fun row =>
    integratedPrivatePassing P E (fun t => row label.2 t)
  have hprojection : Measurable projection := measurable_pi_apply label.1
  have hg : Measurable g := by
    apply (measurable_integratedPrivatePassing P E).comp
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply t).comp (measurable_pi_apply label.2)
  have hmap :
      (CompletePublicTable.forwardFamilyMeasure p).map projection =
        CompletePublicTable.forwardRowMeasure p :=
    CompletePublicTable.map_forwardRowProjection p label.1
  have hgmap : AEStronglyMeasurable g
      ((CompletePublicTable.forwardFamilyMeasure p).map projection) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  calc
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) =
      ∫ row, g row ∂(CompletePublicTable.forwardFamilyMeasure p).map projection := by
        symm
        exact integral_map hprojection.aemeasurable hgmap
    _ = ∫ row, g row ∂CompletePublicTable.forwardRowMeasure p := by rw [hmap]
    _ = ∫ ω, privateQuotaSuccessWeight E ω ∂P :=
      integratedPrivatePassing_mean_eq_privateExpectation P E label.2

theorem privateQuotaSuccessWeight_eq_indicator
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (E : EligibleListFunction p s Ω) (ω : Ω) :
    privateQuotaSuccessWeight E ω =
      ({ω | BootstrapDimensions.q_dec p ≤
        (chronologicalEligibleTimes E ω).length} : Set Ω).indicator
          (fun _ => (1 : ℝ)) ω *
        (1 - 1 / (BootstrapDimensions.L0 p : ℝ)) ^ BootstrapDimensions.q_dec p := by
  by_cases hquota : BootstrapDimensions.q_dec p ≤
      (chronologicalEligibleTimes E ω).length
  · simp [privateQuotaSuccessWeight, forwardTrueProbability, hquota]
  · simp [privateQuotaSuccessWeight, forwardTrueProbability, hquota]

/-- The full-family slice mean in the source's explicit quota-indicator form. -/
theorem integratedPrivatePassing_family_mean_eq_quota_indicator
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (label : SliceLabel p) :
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) =
      ∫ ω,
        ({ω | BootstrapDimensions.q_dec p ≤
          (chronologicalEligibleTimes E ω).length} : Set Ω).indicator
            (fun _ => (1 : ℝ)) ω *
          (1 - 1 / (BootstrapDimensions.L0 p : ℝ)) ^ BootstrapDimensions.q_dec p ∂P := by
  rw [integratedPrivatePassing_family_mean_eq_privateExpectation P E label]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => privateQuotaSuccessWeight_eq_indicator E ω

theorem integratedPrivatePassing_family_mean_le_first_q_power
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (label : SliceLabel p) :
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) ≤
      forwardTrueProbability p ^ BootstrapDimensions.q_dec p := by
  calc
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) =
      ∫ ω, privateQuotaSuccessWeight E ω ∂P :=
        integratedPrivatePassing_family_mean_eq_privateExpectation P E label
    _ = ∫ row : CompletePublicTable.ForwardRow p,
          integratedPrivatePassing P E (fun t => row label.2 t)
            ∂CompletePublicTable.forwardRowMeasure p :=
          (integratedPrivatePassing_mean_eq_privateExpectation P E label.2).symm
    _ ≤ forwardTrueProbability p ^ BootstrapDimensions.q_dec p :=
      integratedPrivatePassing_mean_le_first_q_power P E label.2

theorem integratedPrivatePassing_family_mean_le_exp_bound
    {p : ConstructorDimensions.Parameters} {s : Fin (BootstrapDimensions.n_boot p)}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : EligibleListFunction p s Ω) (label : SliceLabel p) :
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) ≤
      Real.exp (-8 * (ConstructorDimensions.b_N p : ℝ)) := by
  calc
    (∫ x : CompletePublicTable.ForwardFamily p,
      integratedPrivatePassing P E (forwardSliceAt p label x)
        ∂CompletePublicTable.forwardFamilyMeasure p) ≤
        forwardTrueProbability p ^ BootstrapDimensions.q_dec p :=
      integratedPrivatePassing_family_mean_le_first_q_power P E label
    _ ≤ Real.exp (-8 * (ConstructorDimensions.b_N p : ℝ)) :=
      forwardTrueProbability_le_exp_bound p

end Bandits.Support.ForwardPrefixSlice

end
