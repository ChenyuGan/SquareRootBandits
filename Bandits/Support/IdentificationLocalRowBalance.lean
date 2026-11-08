/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.CompletePublicTable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Identification local row balance

This module defines the literal per-identification-row balance event on each
bootstrap calendar block and proves its fixed-interval and whole-row failure
probability bounds. The row maps retain their full ID-coordinate laws, including
independence for distinct ID labels. Source: `appendix_b_communication.tex:193-203,215-231`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.IdentificationLocalRowBalance

open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open ProbabilityTheory

/-- Natural endpoints from the first offset of a block through its clipped stop.
The stop endpoint is included so half-open intervals can include the final
calendar round and can represent the empty interval at the block start. -/
abbrev BlockEndpoint (p : Parameters) (s : Fin (n_boot p)) :=
  {a : ℕ // s.val * B_boot p ≤ a ∧ a ≤ min p.T ((s.val + 1) * B_boot p)}

/-- A deterministic binary support on the calendar times of a block. -/
abbrev BlockSupport (p : Parameters) (s : Fin (n_boot p)) :=
  {x : Finset (Fin p.T) // x ⊆ calendarBlock p s}

/-- The half-open interval between two block endpoints, clipped to the actual
calendar block. Equal endpoints give the empty interval. -/
@[expose] noncomputable def calendarInterval (p : Parameters) (s : Fin (n_boot p))
    (a b : BlockEndpoint p s) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t => a.val ≤ t.val ∧ t.val < b.val

/-- Membership in a block interval records both its calendar and endpoint
conditions, including the clipped stop of the final block. -/
theorem mem_calendarInterval_iff (p : Parameters) (s : Fin (n_boot p))
    (a b : BlockEndpoint p s) (t : Fin p.T) :
    t ∈ calendarInterval p s a b ↔
      s.val * B_boot p ≤ t.val ∧
      t.val < min p.T ((s.val + 1) * B_boot p) ∧
      a.val ≤ t.val ∧ t.val < b.val := by
  simp only [calendarInterval, Finset.mem_filter]
  rw [BootstrapDimensions.mem_calendarBlock_iff]
  constructor
  · rintro ⟨⟨hstart, hstop⟩, hleft, hright⟩
    exact ⟨hstart, hstop, hleft, hright⟩
  · rintro ⟨hstart, hstop, hleft, hright⟩
    exact ⟨⟨hstart, hstop⟩, hleft, hright⟩

/-- A nonempty half-open calendar interval indexed by its actual start and a
positive length at most `B_boot`; filtering clips it to this block. -/
@[expose] noncomputable def calendarIntervalFromStartLength
    (p : Parameters) (s : Fin (n_boot p))
    (t : Fin p.T) (k : Fin (B_boot p)) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun q =>
    t.val ≤ q.val ∧ q.val < t.val + k.val + 1

/-- The number of supported calendar times in an interval. -/
@[expose] def localBalanceSupportCount {n : ℕ} (D x : Finset (Fin n)) : ℕ :=
  (D ∩ x).card

/-- The number of supported times whose ID bit in one row equals `e`. -/
@[expose] def localBalanceIDCount {n : ℕ} (D x : Finset (Fin n)) (e : Bool)
    (row : Fin n → Bool) : ℕ :=
  ((D ∩ x).filter fun t => row t = e).card

/-- The literal source inequality for one complete ID row, simultaneously over
all half-open intervals (including empty intervals) and both bits. -/
@[expose] noncomputable def localBalanceRowPredicate
    (p : Parameters) (s : Fin (n_boot p))
    (x : BlockSupport p s) (row : Fin p.T → Bool) : Prop :=
  ∀ a b : BlockEndpoint p s, a.val ≤ b.val → ∀ e : Bool,
    ((localBalanceIDCount (calendarInterval p s a b) x.1 e row : ℕ) : ℝ) ≥
      (localBalanceSupportCount (calendarInterval p s a b) x.1 : ℝ) / 3 -
        8 * (b_N p : ℝ)

/-- The local-balance event for fixed block, deterministic support, and ID label. -/
@[expose] noncomputable def localBalanceRowEvent
    (p : Parameters) (s : Fin (n_boot p))
    (x : BlockSupport p s) (u : Fin (A_id p)) : Set (IDArray p) :=
  {id | localBalanceRowPredicate p s x (id u)}

/-- Failure of the fixed-set, fixed-bit source inequality for one ID label. -/
@[expose] noncomputable def localBalanceFixedIntervalFailureEvent (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u : Fin (A_id p))
    (D : Finset (Fin p.T)) (e : Bool) : Set (IDArray p) :=
  {id |
    ((localBalanceIDCount D x.1 e (id u) : ℕ) : ℝ) <
      (localBalanceSupportCount D x.1 : ℝ) / 3 - 8 * (b_N p : ℝ)}

/-- Every subset of the finite ID-array carrier is measurable. -/
theorem measurableSet_localBalanceRowEvent (p : Parameters) (s : Fin (n_boot p))
    (x : BlockSupport p s) (u : Fin (A_id p)) :
    MeasurableSet (localBalanceRowEvent p s x u) := by
  classical
  exact (Set.toFinite _).measurableSet

/-- Every fixed-interval failure event is measurable. -/
theorem measurableSet_localBalanceFixedIntervalFailureEvent (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u : Fin (A_id p))
    (D : Finset (Fin p.T)) (e : Bool) :
    MeasurableSet (localBalanceFixedIntervalFailureEvent p s x u D e) := by
  classical
  exact (Set.toFinite _).measurableSet

/-- The MGF factor from the source estimate is at most one for every support
size. Its cube base is exactly `54/64`. -/
theorem localBalance_mgf_factor_power_le_one (n : ℕ) :
    ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)) ^ n ≤ 1 := by
  let q : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)
  have hq0 : 0 ≤ q := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have hqCube : q ^ 3 = 54 / 64 := by
    dsimp [q]
    have hroot : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
      calc
        ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 =
            (2 : ℝ) ^ ((1 / 3 : ℝ) * 3) :=
          (Real.rpow_mul_natCast (by norm_num) (1 / 3 : ℝ) 3).symm
        _ = 2 := by norm_num
    rw [mul_pow, hroot]
    norm_num
  have hq1 : q ≤ 1 := by
    by_contra h
    have hle : 1 ≤ q := le_of_lt (lt_of_not_ge h)
    have hfactor : 0 ≤ (q - 1) * (q ^ 2 + q + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hidentity : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    nlinarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      q ^ n * q ≤ 1 * 1 :=
        mul_le_mul ih hq1 (by positivity) (by positivity)
      _ = 1 := by ring

private noncomputable def localBalanceMgfFactor (e bit : Bool) : ℝ :=
  if bit = e then (2 : ℝ) ^ (-1 : ℝ) else 1

private noncomputable def localBalanceMgf {n : ℕ} (S : Finset (Fin n)) (e : Bool)
    (row : Fin n → Bool) : ℝ :=
  ∏ t, if t ∈ S then localBalanceMgfFactor e (row t) else 1

private theorem localBalanceMgf_eq_count {n : ℕ} (S : Finset (Fin n)) (e : Bool)
    (row : Fin n → Bool) :
    localBalanceMgf S e row =
      (2 : ℝ) ^ (-(((S.filter fun t => row t = e).card : ℕ) : ℝ)) := by
  classical
  simp only [localBalanceMgf, Finset.prod_ite_mem_eq, localBalanceMgfFactor]
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  exact (Real.rpow_mul_natCast (by norm_num) (-1 : ℝ)
    ((S.filter fun t => row t = e).card)).symm.trans (by congr 1; ring)

private theorem integral_localBalanceMgf_row {n : ℕ} (S : Finset (Fin n)) (e : Bool) :
    (∫ row : Fin n → Bool, localBalanceMgf S e row ∂
      Measure.pi (fun _ : Fin n => fairBitLaw)) = (3 / 4 : ℝ) ^ S.card := by
  classical
  have hbit : ∀ e : Bool,
      (∫ bit : Bool, localBalanceMgfFactor e bit ∂fairBitLaw) = (3 / 4 : ℝ) := by
    intro e
    rw [fairBitLaw, ProbabilityTheory.integral_bernoulliMeasure]
    cases e <;> norm_num [localBalanceMgfFactor, fairBitParameter]
  have hfactor : ∀ t : Fin n,
      (∫ bit : Bool,
        (if t ∈ S then localBalanceMgfFactor e bit else 1) ∂fairBitLaw) =
          if t ∈ S then (3 / 4 : ℝ) else 1 := by
    intro t
    by_cases ht : t ∈ S
    · simpa [ht] using hbit e
    · simp only [if_neg ht]
      rw [integral_const]
      have hmass : fairBitLaw.real Set.univ = 1 := by
        rw [Measure.real, measure_univ, ENNReal.toReal_one]
      rw [hmass]
      simp
  change (∫ row : Fin n → Bool,
      ∏ t : Fin n, (if t ∈ S then localBalanceMgfFactor e (row t) else 1)
        ∂Measure.pi (fun _ : Fin n => fairBitLaw)) = _
  rw [integral_fintype_prod_eq_prod (f := fun t bit =>
    if t ∈ S then localBalanceMgfFactor e bit else 1)]
  simp_rw [hfactor]
  simp only [Finset.prod_ite_mem_eq, Finset.prod_const]

private theorem integral_localBalanceMgf (p : Parameters) (u : Fin (A_id p))
    (S : Finset (Fin p.T)) (e : Bool) :
    (∫ id : IDArray p, localBalanceMgf S e (id u) ∂idArrayMeasure p) =
      (3 / 4 : ℝ) ^ S.card := by
  change (∫ id : (u : Fin (A_id p)) → Fin p.T → Bool,
      localBalanceMgf S e (id u) ∂
        Measure.pi (fun _ : Fin (A_id p) =>
          Measure.pi (fun _ : Fin p.T => fairBitLaw))) = _
  rw [MeasureTheory.integral_comp_eval (i := u)
    (MeasureTheory.AEStronglyMeasurable.of_discrete)]
  exact integral_localBalanceMgf_row S e

/-- The exact Markov/MGF estimate for a fixed interval and bit. The MGF factor
is `(2^(1/3) * 3/4)^supportCount`, whose cube is `54/64 < 1`. -/
theorem localBalance_fixed_interval_bit_mgf_bound (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u : Fin (A_id p))
    (D : Finset (Fin p.T)) (e : Bool) :
    (idArrayMeasure p).real (localBalanceFixedIntervalFailureEvent p s x u D e) ≤
      (2 : ℝ) ^ (-8 * (b_N p : ℝ)) *
      ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)) ^
          localBalanceSupportCount D x.1 := by
  classical
  let S := D ∩ x.1
  let n := localBalanceSupportCount D x.1
  let d : ℝ := (n : ℝ) / 3 - 8 * (b_N p : ℝ)
  let threshold : ℝ := (2 : ℝ) ^ d
  let g : IDArray p → ℝ := fun id => threshold * localBalanceMgf S e (id u)
  have hthreshold : 0 ≤ threshold := by
    dsimp [threshold]
    exact Real.rpow_nonneg (by norm_num) _
  have hmgf_nonneg : ∀ row : Fin p.T → Bool, 0 ≤ localBalanceMgf S e row := by
    intro row
    unfold localBalanceMgf
    apply Finset.prod_nonneg
    intro t ht
    by_cases hmem : t ∈ S
    · simp only [hmem, ↓reduceIte]
      unfold localBalanceMgfFactor
      split_ifs <;> positivity
    · simp only [hmem, ↓reduceIte]
      norm_num
  have hInt : (∫ id, g id ∂idArrayMeasure p) =
      threshold * (3 / 4 : ℝ) ^ S.card := by
    dsimp [g]
    rw [integral_const_mul]
    exact congrArg (fun r : ℝ => threshold * r)
      (integral_localBalanceMgf p u S e)
  have hMarkov :
      (idArrayMeasure p) (localBalanceFixedIntervalFailureEvent p s x u D e) ≤
        ENNReal.ofReal (∫ id, g id ∂idArrayMeasure p) := by
    apply (Integrable.of_finite : Integrable g (idArrayMeasure p)).measure_le_integral
    · exact ae_of_all _ (fun id => mul_nonneg hthreshold (hmgf_nonneg (id u)))
    · intro id hid
      change ((localBalanceIDCount D x.1 e (id u) : ℕ) : ℝ) < d at hid
      have hcount :
          localBalanceIDCount D x.1 e (id u) = (S.filter fun t => id u t = e).card := by
        rfl
      rw [hcount] at hid
      have hMgf := localBalanceMgf_eq_count S e (id u)
      have hExp : 0 < d - (((S.filter fun t => id u t = e).card : ℕ) : ℝ) := by
        linarith
      change 1 ≤ threshold * localBalanceMgf S e (id u)
      rw [hMgf, show threshold = (2 : ℝ) ^ d by rfl]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.one_le_rpow (by norm_num)
      linarith
  rw [hInt] at hMarkov
  have hThresholdIdentity :
      threshold * (3 / 4 : ℝ) ^ S.card =
        (2 : ℝ) ^ (-8 * (b_N p : ℝ)) *
          ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)) ^ S.card := by
    have hpow : (2 : ℝ) ^ ((S.card : ℝ) / 3) =
        ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ S.card := by
      calc
        (2 : ℝ) ^ ((S.card : ℝ) / 3) =
            (2 : ℝ) ^ ((1 / 3 : ℝ) * (S.card : ℝ)) := by congr 1; ring
        _ = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ (S.card : ℝ) :=
          Real.rpow_mul (by norm_num) _ _
        _ = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ S.card := Real.rpow_natCast _ _
    have hsplit : threshold =
        (2 : ℝ) ^ ((S.card : ℝ) / 3) *
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
      dsimp [threshold]
      rw [show d = (S.card : ℝ) / 3 - 8 * (b_N p : ℝ) by rfl,
        sub_eq_add_neg, Real.rpow_add (by norm_num)]
      congr 1
      ring_nf
    rw [hsplit, hpow]
    calc
      ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ S.card *
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) * (3 / 4 : ℝ) ^ S.card =
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) *
            (((2 : ℝ) ^ (1 / 3 : ℝ)) ^ S.card * (3 / 4 : ℝ) ^ S.card) := by ring
      _ = (2 : ℝ) ^ (-8 * (b_N p : ℝ)) *
            ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)) ^ S.card := by
          rw [← mul_pow]
  have hprobReal :
      (idArrayMeasure p).real (localBalanceFixedIntervalFailureEvent p s x u D e) ≤
        threshold * (3 / 4 : ℝ) ^ S.card := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMarkov
    calc
      (idArrayMeasure p).real (localBalanceFixedIntervalFailureEvent p s x u D e) =
          ((idArrayMeasure p)
            (localBalanceFixedIntervalFailureEvent p s x u D e)).toReal := by
              rfl
      _ ≤ (ENNReal.ofReal (threshold * (3 / 4 : ℝ) ^ S.card)).toReal := by
            simpa [hInt] using h
      _ = threshold * (3 / 4 : ℝ) ^ S.card :=
            ENNReal.toReal_ofReal (by positivity)
  rw [hThresholdIdentity] at hprobReal
  exact hprobReal

/-- The source fixed-interval probability estimate, with its exact MGF factor. -/
theorem localBalance_fixed_interval_bit_failure_probability (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u : Fin (A_id p))
    (D : Finset (Fin p.T)) (e : Bool) :
    (idArrayMeasure p).real (localBalanceFixedIntervalFailureEvent p s x u D e) ≤
      (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
  have h := localBalance_fixed_interval_bit_mgf_bound p s x u D e
  have hq : ((2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ)) ^
      localBalanceSupportCount D x.1 ≤ 1 := by
    exact localBalance_mgf_factor_power_le_one _
  have hbase : 0 ≤ (2 : ℝ) ^ (-8 * (b_N p : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  simpa using h.trans (mul_le_mul_of_nonneg_left hq hbase)

/-- The full ID-array rows are mutually independent under the nested product law. -/
theorem iIndepFun_idArrayRows (p : Parameters) :
    iIndepFun (fun u : Fin (A_id p) => fun id : IDArray p => id u)
      (idArrayMeasure p) := by
  change iIndepFun (fun u (id : Fin (A_id p) → Fin p.T → Bool) => id u)
      (Measure.pi (fun _ : Fin (A_id p) =>
        Measure.pi (fun _ : Fin p.T => fairBitLaw)))
  exact iIndepFun_pi (fun _ => aemeasurable_id)

/-- The fixed block/support local-balance row events are mutually independent.
This exposes the distinct ID-row coordinate decomposition for later consumers. -/
theorem iIndepSet_localBalanceRowEvent (p : Parameters) (s : Fin (n_boot p))
    (x : BlockSupport p s) :
    iIndepSet (fun u : Fin (A_id p) => localBalanceRowEvent p s x u)
      (idArrayMeasure p) := by
  classical
  rw [iIndepSet_iff_meas_biInter
    (f := fun u : Fin (A_id p) => localBalanceRowEvent p s x u)
    (μ := idArrayMeasure p)
    (fun u => measurableSet_localBalanceRowEvent p s x u)]
  intro S
  have h := (iIndepFun_idArrayRows p).measure_inter_preimage_eq_mul
    (S := S)
    (sets := fun _ : Fin (A_id p) =>
      {row : Fin p.T → Bool | localBalanceRowPredicate p s x row})
    (by
      intro u hu
      exact (Set.toFinite _).measurableSet)
  simpa [localBalanceRowEvent] using h

/-- Two different ID labels have independent local-balance events. -/
theorem indepSet_distinct_localBalanceRowEvent (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u v : Fin (A_id p)) (huv : u ≠ v) :
    IndepSet (localBalanceRowEvent p s x u) (localBalanceRowEvent p s x v)
    (idArrayMeasure p) := by
  rw [indepSet_iff_measure_inter_eq_mul (μ := idArrayMeasure p)
    (measurableSet_localBalanceRowEvent p s x u)
    (measurableSet_localBalanceRowEvent p s x v)]
  have h := (iIndepSet_localBalanceRowEvent p s x).meas_biInter (insert u {v})
  simpa [huv] using h

/-- A union bound over actual nonempty intervals and both ID bits proves the
fixed-row failure probability bound. The event itself still quantifies over
empty intervals, whose inequality holds deterministically. -/
theorem localBalanceRowEvent_failure_probability_le (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) (u : Fin (A_id p)) :
    (idArrayMeasure p).real (localBalanceRowEvent p s x u)ᶜ ≤
      2 * (B_boot p : ℝ) ^ 2 * (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
  classical
  let choices : Finset (Fin p.T × Fin (B_boot p)) :=
    (calendarBlock p s).product Finset.univ
  let indices : Finset ((Fin p.T × Fin (B_boot p)) × Bool) :=
    choices.product Finset.univ
  let failure (i : (Fin p.T × Fin (B_boot p)) × Bool) : Set (IDArray p) :=
    localBalanceFixedIntervalFailureEvent p s x u
      (calendarIntervalFromStartLength p s i.1.1 i.1.2) i.2
  have hcover : (localBalanceRowEvent p s x u)ᶜ ⊆ ⋃ i ∈ indices, failure i := by
    intro id hid
    have hbad : ¬ localBalanceRowPredicate p s x (id u) := by
      simpa [localBalanceRowEvent] using hid
    unfold localBalanceRowPredicate at hbad
    push Not at hbad
    rcases hbad with ⟨a, b, hab, e, hfail⟩
    have hlt : a.val < b.val := by
      by_contra hnot
      have heq : a.val = b.val := by omega
      have habEq : a = b := Subtype.ext heq
      subst b
      have hinterval : calendarInterval p s a a = ∅ := by
        ext q
        simp only [calendarInterval, Finset.mem_filter, Finset.notMem_empty]
        constructor
        · rintro ⟨_, hq⟩
          exact False.elim (by omega)
        · intro hq
          cases hq
      rw [hinterval] at hfail
      simp [localBalanceIDCount, localBalanceSupportCount] at hfail
      have hb : (0 : ℝ) ≤ (b_N p : ℝ) := by positivity
      nlinarith [hb]
    have hbStop : b.val ≤ min p.T ((s.val + 1) * B_boot p) := b.property.2
    have haStop : a.val < min p.T ((s.val + 1) * B_boot p) :=
      lt_of_lt_of_le hlt hbStop
    let t : Fin p.T :=
      ⟨a.val, lt_of_lt_of_le haStop (Nat.min_le_left _ _)⟩
    have htblock : t ∈ calendarBlock p s := by
      rw [BootstrapDimensions.mem_calendarBlock_iff]
      exact ⟨a.property.1, by omega⟩
    have hspan : b.val - a.val ≤ B_boot p := by
      have hstart := a.property.1
      have hcard :
          min p.T ((s.val + 1) * B_boot p) - s.val * B_boot p ≤ B_boot p := by
        rw [← calendarBlock_card p s]
        exact calendarBlock_card_le_B_boot p s
      omega
    let k : Fin (B_boot p) := ⟨b.val - a.val - 1, by omega⟩
    have hendpoint : t.val + k.val + 1 = b.val := by
      dsimp [t, k]
      omega
    have hinterval :
        calendarIntervalFromStartLength p s t k = calendarInterval p s a b := by
      ext q
      simp only [calendarIntervalFromStartLength, calendarInterval, Finset.mem_filter]
      constructor
      · rintro ⟨hq, hstart, hstop⟩
        exact ⟨hq, hstart, by rw [← hendpoint]; exact hstop⟩
      · rintro ⟨hq, hstart, hstop⟩
        exact ⟨hq, hstart, by rw [hendpoint]; exact hstop⟩
    have hchoice : id ∈ failure ((t, k), e) := by
      change ((localBalanceIDCount
        (calendarIntervalFromStartLength p s t k) x.1 e (id u) : ℕ) : ℝ) < _
      change ((localBalanceIDCount
        (calendarInterval p s a b) x.1 e (id u) : ℕ) : ℝ) < _ at hfail
      rw [hinterval]
      exact hfail
    have hmem : ((t, k), e) ∈ indices := by
      simp [indices, choices, htblock]
    simp only [Set.mem_iUnion]
    exact ⟨((t, k), e), hmem, hchoice⟩
  have hmono :
      (idArrayMeasure p).real (localBalanceRowEvent p s x u)ᶜ ≤
        (idArrayMeasure p).real (⋃ i ∈ indices, failure i) := by
    have hmeasure := measure_mono (μ := idArrayMeasure p) hcover
    have hfinite : idArrayMeasure p (⋃ i ∈ indices, failure i) ≠ ∞ := by
      exact (measure_lt_top (idArrayMeasure p) _).ne
    exact ENNReal.toReal_mono hfinite hmeasure
  have hsum :
      (∑ i ∈ indices, (idArrayMeasure p).real (failure i)) ≤
        ∑ i ∈ indices, (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact localBalance_fixed_interval_bit_failure_probability p s x u
      (calendarIntervalFromStartLength p s i.1.1 i.1.2) i.2
  have hcard : indices.card ≤ 2 * B_boot p ^ 2 := by
    have hcardEq : indices.card = (calendarBlock p s).card * B_boot p * 2 := by
      simp [indices, choices, Finset.card_product]
    rw [hcardEq]
    have hblock := calendarBlock_card_le_B_boot p s
    nlinarith
  calc
    (idArrayMeasure p).real (localBalanceRowEvent p s x u)ᶜ ≤
        (idArrayMeasure p).real (⋃ i ∈ indices, failure i) := hmono
    _ ≤ ∑ i ∈ indices, (idArrayMeasure p).real (failure i) :=
        measureReal_biUnion_finset_le indices failure
    _ ≤ ∑ i ∈ indices, (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := hsum
    _ = (indices.card : ℝ) * (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * B_boot p ^ 2 : ℕ) * (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 2 * (B_boot p : ℝ) ^ 2 * (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
        push_cast
        ring

end Bandits.Support.IdentificationLocalRowBalance

end
