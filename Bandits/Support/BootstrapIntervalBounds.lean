/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-horizon interval clocks

Source motivation: `sources/zip4/manuscript/appendix_b_communication.tex:247–292`.
The conditional means below are literally conditional expectations. The clocks
use finite prefix sums, and freeze after the deterministic horizon. This is
internal probability infrastructure, not a manuscript or startup closure claim.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ProbabilityTheory ENNReal

namespace Bandits.Support.BootstrapIntervalBounds

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℕ m} {X : ℕ → Ω → ℝ}
  {α T : ℕ}

/-- The predictable conditional mean, with no independent mean parameter. -/
noncomputable def conditionalMean (P : Measure Ω) (F : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P[X t | F (t - 1)]

/-- The sum over `[α, min n T]`, written using a finite prefix to make both
the empty initial interval and the constant continuation explicit. -/
noncomputable def intervalSum (Y : ℕ → Ω → ℝ) (α T n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range (n + 1), if α ≤ t ∧ t ≤ T then Y t ω else 0

/-- The exponential clock with real tilt `θ`. The choices `-1` and `1`
are exactly the two clocks in the source. -/
noncomputable def intervalClock (P : Measure Ω) (F : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (α T : ℕ) (θ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (θ * intervalSum X α T n ω -
    (Real.exp θ - 1) * intervalSum (conditionalMean P F X) α T n ω)

omit [IsProbabilityMeasure P] in
theorem conditionalMean_stronglyMeasurable (t : ℕ) :
    StronglyMeasurable[F (t - 1)] (conditionalMean P F X t) :=
  stronglyMeasurable_condExp

omit [IsProbabilityMeasure P] in
theorem conditionalMean_integrable (t : ℕ) :
    Integrable (conditionalMean P F X t) P :=
  integrable_condExp

omit [IsProbabilityMeasure P] in
theorem conditionalMean_predictable : IsStronglyPredictable F (conditionalMean P F X) := by
  apply IsStronglyPredictable.iff_measurable_add_one.mpr
  constructor
  · exact conditionalMean_stronglyMeasurable 0
  · intro n
    simpa only [Nat.add_sub_cancel] using
      (conditionalMean_stronglyMeasurable (P := P) (F := F) (X := X) (n + 1))

theorem integrable_of_unit_bounds {Y : Ω → ℝ} (hY : StronglyMeasurable Y)
    (hb : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ 1) : Integrable Y P := by
  refine (integrable_const (1 : ℝ)).mono' hY.aestronglyMeasurable ?_
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2

theorem conditionalMean_unit_bounds {t : ℕ}
    (hX : StronglyMeasurable[F t] (X t))
    (hb : ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) :
    ∀ᵐ ω ∂P, 0 ≤ conditionalMean P F X t ω ∧ conditionalMean P F X t ω ≤ 1 := by
  have hi := integrable_of_unit_bounds (hX.mono (F.le t)) hb
  have h0 : 0 ≤ᵐ[P] X t := hb.mono fun _ h => h.1
  have h1 : X t ≤ᵐ[P] fun _ => (1 : ℝ) := hb.mono fun _ h => h.2
  have hu := condExp_mono (m := F (t - 1)) hi (integrable_const 1) h1
  rw [condExp_const (F.le (t - 1))] at hu
  filter_upwards [condExp_nonneg (m := F (t - 1)) h0, hu] with ω hω0 hω1
  exact ⟨hω0, hω1⟩

/-- The chord bound for the exponential on the unit interval. -/
theorem exp_mul_le_chord (θ x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (θ * x) ≤ 1 + (Real.exp θ - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ θ)
    (sub_nonneg.mpr hx1) hx0 (sub_add_cancel 1 x)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc
    Real.exp (θ * x) = Real.exp (x * θ) := by rw [mul_comm]
    _ ≤ 1 - x + x * Real.exp θ := h
    _ = _ := by ring

theorem exp_mul_integrable {Y : Ω → ℝ} (hY : StronglyMeasurable Y)
    (hb : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ 1) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * Y ω)) P := by
  refine (integrable_const (Real.exp |θ|)).mono'
    ((Real.continuous_exp.comp_stronglyMeasurable (hY.const_mul θ)).aestronglyMeasurable) ?_
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    θ * Y ω ≤ |θ| * Y ω := mul_le_mul_of_nonneg_right (le_abs_self θ) hω.1
    _ ≤ |θ| := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hω.2 (abs_nonneg θ)

/-- Conditional convexity, derived from the actual conditional expectation.
There is no conditional moment or exponential-clock premise. -/
theorem condExp_exp_mul_le {t : ℕ}
    (hX : StronglyMeasurable[F t] (X t))
    (hb : ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) (θ : ℝ) :
    P[(fun ω => Real.exp (θ * X t ω)) | F (t - 1)] ≤ᵐ[P]
      fun ω => Real.exp ((Real.exp θ - 1) * conditionalMean P F X t ω) := by
  have hi := integrable_of_unit_bounds (hX.mono (F.le t)) hb
  have he := exp_mul_integrable (hX.mono (F.le t)) hb θ
  have hc : Integrable (fun ω => 1 + (Real.exp θ - 1) * X t ω) P :=
    (integrable_const 1).add (hi.const_mul _)
  have hm := condExp_mono (m := F (t - 1)) he hc
    (hb.mono fun ω hω => exp_mul_le_chord θ (X t ω) hω.1 hω.2)
  have ha := condExp_add (integrable_const (1 : ℝ)) (hi.const_mul (Real.exp θ - 1))
    (F (t - 1))
  have hs := condExp_smul (μ := P) (Real.exp θ - 1) (X t) (F (t - 1))
  rw [condExp_const (F.le (t - 1))] at ha
  filter_upwards [hm, ha, hs] with ω hmω haω hsω
  calc
    _ ≤ P[(fun ω => 1 + (Real.exp θ - 1) * X t ω) | F (t - 1)] ω := hmω
    _ = 1 + (Real.exp θ - 1) * conditionalMean P F X t ω := by
      change _ = 1 + (Real.exp θ - 1) * P[X t | F (t - 1)] ω
      simpa only [Pi.add_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        haω.trans (congrArg (fun z : ℝ => 1 + z) hsω)
    _ ≤ _ := by
      simpa only [add_comm] using
        Real.add_one_le_exp ((Real.exp θ - 1) * conditionalMean P F X t ω)

theorem condExp_exp_neg_le {t : ℕ} (hX : StronglyMeasurable[F t] (X t))
    (hb : ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) :
    P[(fun ω => Real.exp (-X t ω)) | F (t - 1)] ≤ᵐ[P]
      fun ω => Real.exp (-(1 - Real.exp (-1)) * conditionalMean P F X t ω) := by
  simpa only [neg_one_mul, neg_sub] using condExp_exp_mul_le hX hb (-1)

theorem condExp_exp_le {t : ℕ} (hX : StronglyMeasurable[F t] (X t))
    (hb : ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) :
    P[(fun ω => Real.exp (X t ω)) | F (t - 1)] ≤ᵐ[P]
      fun ω => Real.exp ((Real.exp 1 - 1) * conditionalMean P F X t ω) := by
  simpa only [one_mul] using condExp_exp_mul_le hX hb 1

theorem intervalSum_succ (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    intervalSum Y α T (n + 1) ω = intervalSum Y α T n ω +
      if α ≤ n + 1 ∧ n + 1 ≤ T then Y (n + 1) ω else 0 := by
  exact sum_range_succ _ _

theorem intervalSum_initial (Y : ℕ → Ω → ℝ) (hα : 1 ≤ α) (ω : Ω) :
    intervalSum Y α T (α - 1) ω = 0 := by
  apply sum_eq_zero
  intro t ht
  have ht' := mem_range.mp ht
  rw [ite_eq_right]
  omega

theorem intervalSum_eq_sum_Icc (Y : ℕ → Ω → ℝ) {n : ℕ} (hn : n ≤ T) (ω : Ω) :
    intervalSum Y α T n ω = ∑ t ∈ Icc α n, Y t ω := by
  classical
  have hf : (range (n + 1)).filter (fun t => α ≤ t ∧ t ≤ T) = Icc α n := by
    ext t
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  unfold intervalSum
  rw [← sum_filter, hf]

theorem intervalSum_stronglyMeasurable {Y : ℕ → Ω → ℝ}
    (hY : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (Y t)) (n : ℕ) :
    StronglyMeasurable[F n] (intervalSum Y α T n) := by
  classical
  apply Finset.stronglyMeasurable_fun_sum
  intro t ht
  by_cases ha : α ≤ t ∧ t ≤ T
  · simp only [ite_eq_left ha]
    exact (hY t ha.1 ha.2).mono (F.mono (by have := mem_range.mp ht; omega))
  · simp only [ite_eq_right ha]
    exact stronglyMeasurable_const

omit [IsProbabilityMeasure P] in
theorem intervalSum_unit_bounds {Y : ℕ → Ω → ℝ}
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ Y t ω ∧ Y t ω ≤ 1) (n : ℕ) :
    ∀ᵐ ω ∂P, 0 ≤ intervalSum Y α T n ω ∧ intervalSum Y α T n ω ≤ (n + 1 : ℕ) := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ t, α ≤ t → t ≤ T → 0 ≤ Y t ω ∧ Y t ω ≤ 1 := by
    apply ae_all_iff.mpr
    intro t
    by_cases ha : α ≤ t ∧ t ≤ T
    · filter_upwards [hb t ha.1 ha.2] with ω hω
      exact fun _ _ => hω
    · exact ae_of_all _ fun _ h1 h2 => (ha ⟨h1, h2⟩).elim
  filter_upwards [hall] with ω hω
  constructor
  · apply sum_nonneg
    intro t _
    split_ifs with ha
    · exact (hω t ha.1 ha.2).1
    · exact le_rfl
  · calc
      _ ≤ ∑ _t ∈ range (n + 1), (1 : ℝ) := by
        apply sum_le_sum
        intro t _
        split_ifs with ha
        · exact (hω t ha.1 ha.2).2
        · exact zero_le_one
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]

omit [IsProbabilityMeasure P] in
theorem intervalClock_pos (θ : ℝ) (n : ℕ) (ω : Ω) :
    0 < intervalClock P F X α T θ n ω :=
  Real.exp_pos _

omit [IsProbabilityMeasure P] in
theorem intervalClock_initial (hα : 1 ≤ α) (θ : ℝ) :
    intervalClock P F X α T θ (α - 1) = fun _ => 1 := by
  funext ω
  simp only [intervalClock, intervalSum_initial X hα,
    intervalSum_initial (conditionalMean P F X) hα, mul_zero, sub_self, Real.exp_zero]

omit [IsProbabilityMeasure P] in
theorem intervalClock_stronglyAdapted
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t)) (θ : ℝ) :
    StronglyAdapted F (intervalClock P F X α T θ) := by
  intro n
  have hm : StronglyMeasurable[F n] (intervalSum (conditionalMean P F X) α T n) :=
    intervalSum_stronglyMeasurable (fun t _ _ =>
      (conditionalMean_stronglyMeasurable t).mono (F.mono (Nat.sub_le t 1))) n
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((intervalSum_stronglyMeasurable hX n).const_mul θ).sub (hm.const_mul _))

theorem intervalClock_integrable
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (θ : ℝ) (n : ℕ) : Integrable (intervalClock P F X α T θ n) P := by
  have hm := intervalSum_unit_bounds
    (fun t h1 h2 => conditionalMean_unit_bounds (hX t h1 h2) (hb t h1 h2)) n
  have hx := intervalSum_unit_bounds hb n
  refine (integrable_const
    (Real.exp ((|θ| + |Real.exp θ - 1|) * (n + 1 : ℕ)))).mono'
    (((intervalClock_stronglyAdapted hX θ n).mono (F.le n)).aestronglyMeasurable) ?_
  filter_upwards [hx, hm] with ω hxω hmω
  rw [Real.norm_eq_abs, abs_of_pos (intervalClock_pos θ n ω)]
  apply Real.exp_le_exp.mpr
  have hθ : θ * intervalSum X α T n ω ≤ |θ| * (n + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self θ) hxω.1).trans
      (mul_le_mul_of_nonneg_left hxω.2 (abs_nonneg θ))
  have hc : -(Real.exp θ - 1) * intervalSum (conditionalMean P F X) α T n ω ≤
      |Real.exp θ - 1| * (n + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_right (neg_le_abs _) hmω.1).trans
      (mul_le_mul_of_nonneg_left hmω.2 (abs_nonneg _))
  nlinarith only [hθ, hc]

/-- The actual finite-prefix exponential clocks are supermartingales.
Only adaptedness and almost-everywhere unit bounds are inputs. -/
theorem intervalClock_supermartingale
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (θ : ℝ) : Supermartingale (intervalClock P F X α T θ) F P := by
  have had := intervalClock_stronglyAdapted (P := P) hX θ
  have hi := intervalClock_integrable hX hb θ
  apply supermartingale_nat had hi
  intro n
  by_cases ha : α ≤ n + 1 ∧ n + 1 ≤ T
  · let c := Real.exp θ - 1
    let q : Ω → ℝ := fun ω => Real.exp
      (θ * intervalSum X α T n ω - c * intervalSum (conditionalMean P F X) α T n ω -
        c * conditionalMean P F X (n + 1) ω)
    have hmu : StronglyMeasurable[F n] (conditionalMean P F X (n + 1)) := by
      simpa only [Nat.add_sub_cancel] using
        (conditionalMean_stronglyMeasurable (P := P) (F := F) (X := X) (n + 1))
    have hms : StronglyMeasurable[F n] (intervalSum (conditionalMean P F X) α T n) :=
      intervalSum_stronglyMeasurable (fun t _ _ =>
        (conditionalMean_stronglyMeasurable t).mono (F.mono (Nat.sub_le t 1))) n
    have hq : StronglyMeasurable[F n] q :=
      Real.continuous_exp.comp_stronglyMeasurable
        ((((intervalSum_stronglyMeasurable hX n).const_mul θ).sub
          (hms.const_mul c)).sub (hmu.const_mul c))
    have hrec : intervalClock P F X α T θ (n + 1) =
        q * (fun ω => Real.exp (θ * X (n + 1) ω)) := by
      funext ω
      dsimp only [intervalClock, q, Pi.mul_apply]
      simp only [intervalSum_succ, ite_eq_left ha]
      rw [← Real.exp_add]
      congr 1
      dsimp only [c]
      ring
    have hprod : Integrable (q * (fun ω => Real.exp (θ * X (n + 1) ω))) P :=
      hrec ▸ hi (n + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left hq hprod
      (exp_mul_integrable ((hX (n + 1) ha.1 ha.2).mono (F.le _)) (hb _ ha.1 ha.2) θ)
    have hmgf := condExp_exp_mul_le (hX (n + 1) ha.1 ha.2) (hb _ ha.1 ha.2) θ
    simp only [Nat.add_sub_cancel] at hmgf
    rw [hrec]
    filter_upwards [hpull, hmgf] with ω hpω hmω
    calc
      _ = q ω * P[(fun ω => Real.exp (θ * X (n + 1) ω)) | F n] ω := hpω
      _ ≤ q ω * Real.exp (c * conditionalMean P F X (n + 1) ω) :=
        mul_le_mul_of_nonneg_left hmω (Real.exp_nonneg _)
      _ = intervalClock P F X α T θ n ω := by
        dsimp only [q, intervalClock]
        rw [← Real.exp_add]
        congr 1
        dsimp only [c]
        ring
  · have hrec : intervalClock P F X α T θ (n + 1) = intervalClock P F X α T θ n := by
      funext ω
      simp only [intervalClock, intervalSum_succ, ite_eq_right ha, add_zero]
    rw [hrec, condExp_of_stronglyMeasurable (F.le n) (had n) (hi n)]

/-- The source lower clock, with coefficient `κ = 1 - exp(-1)`. -/
noncomputable def Lminus (P : Measure Ω) (F : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (α T : ℕ) : ℕ → Ω → ℝ :=
  intervalClock P F X α T (-1)

/-- The source upper clock, with coefficient `exp(1) - 1`. -/
noncomputable def Lplus (P : Measure Ω) (F : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (α T : ℕ) : ℕ → Ω → ℝ :=
  intervalClock P F X α T 1

omit [IsProbabilityMeasure P] in
theorem Lminus_eq_exp {n : ℕ} (hn : n ≤ T) (ω : Ω) :
    Lminus P F X α T n ω = Real.exp
      ((1 - Real.exp (-1)) * (∑ t ∈ Icc α n, conditionalMean P F X t ω) -
        ∑ t ∈ Icc α n, X t ω) := by
  simp only [Lminus, intervalClock, intervalSum_eq_sum_Icc X hn,
    intervalSum_eq_sum_Icc (conditionalMean P F X) hn]
  congr 1
  ring

omit [IsProbabilityMeasure P] in
theorem Lplus_eq_exp {n : ℕ} (hn : n ≤ T) (ω : Ω) :
    Lplus P F X α T n ω = Real.exp
      ((∑ t ∈ Icc α n, X t ω) -
        (Real.exp 1 - 1) * (∑ t ∈ Icc α n, conditionalMean P F X t ω)) := by
  simp only [Lplus, intervalClock, intervalSum_eq_sum_Icc X hn,
    intervalSum_eq_sum_Icc (conditionalMean P F X) hn, one_mul]

omit [IsProbabilityMeasure P] in
theorem Lminus_nonneg (n : ℕ) (ω : Ω) : 0 ≤ Lminus P F X α T n ω :=
  (intervalClock_pos (-1) n ω).le

omit [IsProbabilityMeasure P] in
theorem Lplus_nonneg (n : ℕ) (ω : Ω) : 0 ≤ Lplus P F X α T n ω :=
  (intervalClock_pos 1 n ω).le

omit [IsProbabilityMeasure P] in
theorem Lminus_initial (hα : 1 ≤ α) : Lminus P F X α T (α - 1) = fun _ => 1 :=
  intervalClock_initial hα (-1)

omit [IsProbabilityMeasure P] in
theorem Lplus_initial (hα : 1 ≤ α) : Lplus P F X α T (α - 1) = fun _ => 1 :=
  intervalClock_initial hα 1

theorem Lminus_supermartingale
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) :
    Supermartingale (Lminus P F X α T) F P :=
  intervalClock_supermartingale hX hb (-1)

theorem Lplus_supermartingale
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) :
    Supermartingale (Lplus P F X α T) F P :=
  intervalClock_supermartingale hX hb 1

/-- A finite strict crossing event, including both endpoints. -/
def clockCrossing (L : ℕ → Ω → ℝ) (a b : ℕ) (c : ℝ) : Set Ω :=
  {ω | ∃ n ∈ Set.Icc a b, c < L n ω}

theorem clockCrossing_measurable {L : ℕ → Ω → ℝ}
    (hL : StronglyAdapted F L) (a b : ℕ) (c : ℝ) :
    MeasurableSet (clockCrossing L a b c) := by
  classical
  simp only [clockCrossing, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ∈ Set.Icc a b
  · simpa only [hn, true_and] using
      (measurableSet_lt measurable_const ((hL n).mono (F.le n)).measurable :
        MeasurableSet {ω | c < L n ω})
  · simp only [hn, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

/-- Localized finite maximal estimate for a nonnegative supermartingale
initially one. The proof stops at the first crossing and applies optional
stopping to the negated supermartingale. In particular, it does not apply a
nonnegative *submartingale* maximal inequality to a supermartingale. -/
theorem localized_supermartingale_maximal {L : ℕ → Ω → ℝ} {a b : ℕ}
    (hL : Supermartingale L F P) (hnonneg : ∀ n ω, 0 ≤ L n ω)
    (hab : a ≤ b) (hinit : L a = fun _ => 1) {c : ℝ} (hc : 0 < c)
    {A : Set Ω} (hA : MeasurableSet[F a] A) :
    P.real (A ∩ clockCrossing L a b c) ≤ c⁻¹ * P.real A := by
  classical
  let τ : Ω → WithTop ℕ := fun ω => WithTop.some (hittingBtwn L (Set.Ioi c) a b ω)
  let Z : Ω → ℝ := fun ω => L (hittingBtwn L (Set.Ioi c) a b ω) ω
  have hτ : IsStoppingTime F τ :=
    hL.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ioi
  have hτlo (ω : Ω) : WithTop.some a ≤ τ ω := by
    change WithTop.some a ≤ WithTop.some (hittingBtwn L (Set.Ioi c) a b ω)
    exact WithTop.coe_le_coe.mpr (le_hittingBtwn hab ω)
  have hτhi (ω : Ω) : τ ω ≤ WithTop.some b := by
    change WithTop.some (hittingBtwn L (Set.Ioi c) a b ω) ≤ WithTop.some b
    exact WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have hZeq : stoppedValue L τ = Z := by
    funext ω
    simp only [stoppedValue, τ, WithTop.untopA, WithTop.untopD_coe, Z]
  have hZi : Integrable Z P := by
    rw [← hZeq]
    exact integrable_stoppedValue ℕ hτ hL.integrable hτhi
  have hneg := hL.neg.stoppedProcess hτ
  have hstart : stoppedProcess (-L) τ a = fun _ => (-1 : ℝ) := by
    funext ω
    rw [stoppedProcess_eq_of_le (u := -L) (i := a) (hτlo ω)]
    simp only [Pi.neg_apply, hinit]
  have hend : stoppedProcess (-L) τ b = -Z := by
    funext ω
    rw [stoppedProcess_eq_of_ge (u := -L) (i := b) (hτhi ω)]
    simp only [τ, WithTop.untopA, WithTop.untopD_coe, Pi.neg_apply, Z]
  have hopt := hneg.setIntegral_le hab hA
  rw [hstart, hend] at hopt
  have hZA : ∫ ω in A, Z ω ∂P ≤ P.real A := by
    simpa only [Pi.neg_apply, integral_neg, setIntegral_const, smul_eq_mul,
      mul_neg_one, mul_one, neg_le_neg_iff] using hopt
  have hAm : MeasurableSet A := F.le a A hA
  have hBm := clockCrossing_measurable hL.stronglyAdapted a b c
  have hABm := hAm.inter hBm
  have hcross : ∀ ω ∈ clockCrossing L a b c, c ≤ Z ω := by
    intro ω hω
    exact (hittingBtwn_mem_set (u := L) (s := Set.Ioi c) hω).le
  have hlower : c * P.real (A ∩ clockCrossing L a b c) ≤
      ∫ ω in A ∩ clockCrossing L a b c, Z ω ∂P := by
    calc
      _ = ∫ _ω in A ∩ clockCrossing L a b c, c ∂P := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := setIntegral_mono_on (integrable_const c).integrableOn hZi.integrableOn
        hABm (fun ω hω => hcross ω hω.2)
  have hsub : ∫ ω in A ∩ clockCrossing L a b c, Z ω ∂P ≤ ∫ ω in A, Z ω ∂P :=
    setIntegral_mono_set hZi.integrableOn
      (ae_of_all _ fun ω => hnonneg _ ω)
      (ae_of_all _ fun _ hω => hω.1)
  have hbound := hlower.trans (hsub.trans hZA)
  exact (le_inv_mul_iff₀ hc).mpr hbound

/-- Localized crossing bound for clocks constructed from the actual means. -/
theorem intervalClock_localized_maximal
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (θ ℓ : ℝ)
    {A : Set Ω} (hA : MeasurableSet[F (α - 1)] A) :
    P.real (A ∩ clockCrossing (intervalClock P F X α T θ) (α - 1) T (Real.exp ℓ)) ≤
      Real.exp (-ℓ) * P.real A := by
  rw [Real.exp_neg]
  exact localized_supermartingale_maximal (intervalClock_supermartingale hX hb θ)
    (fun n ω => (intervalClock_pos θ n ω).le) (by omega)
    (intervalClock_initial hα θ) (Real.exp_pos ℓ) hA

/-- Conversion of localized probabilities to the usual almost-sure conditional
probability, represented literally by the conditional expectation of an indicator. -/
theorem condExp_indicator_le_of_localized {a : ℕ} {B : Set Ω} (hB : MeasurableSet B)
    {c : ℝ}
    (hlocal : ∀ A : Set Ω, MeasurableSet[F a] A → P.real (A ∩ B) ≤ c * P.real A) :
    P[B.indicator (fun _ => (1 : ℝ)) | F a] ≤ᵐ[P] fun _ => c := by
  have hi : Integrable (B.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hB
  have hsm : StronglyMeasurable[F a] (P[B.indicator (fun _ => (1 : ℝ)) | F a]) :=
    stronglyMeasurable_condExp
  apply ae_of_ae_trim (F.le a)
  apply ae_le_of_forall_setIntegral_le (integrable_condExp.trim (F.le a) hsm)
    (integrable_const c)
  intro A hA _
  rw [← setIntegral_trim (F.le a) hsm hA,
    ← setIntegral_trim (F.le a) stronglyMeasurable_const hA,
    setIntegral_condExp (F.le a) hi hA, setIntegral_indicator hB,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  exact hlocal A hA

/-- Complementary form of the preceding conversion. -/
theorem condExp_indicator_ge_of_localized_compl {a : ℕ} {G : Set Ω}
    (hG : MeasurableSet G) {c : ℝ}
    (hlocal : ∀ A : Set Ω, MeasurableSet[F a] A → P.real (A ∩ Gᶜ) ≤ c * P.real A) :
    (fun _ => 1 - c) ≤ᵐ[P] P[G.indicator (fun _ => (1 : ℝ)) | F a] := by
  have hbound := condExp_indicator_le_of_localized hG.compl hlocal
  have heq : G.indicator (fun _ => (1 : ℝ)) =
      (fun _ => (1 : ℝ)) - Gᶜ.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    by_cases hω : ω ∈ G <;> simp only [Pi.sub_apply, Set.indicator_apply,
      Set.mem_compl_iff, hω, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
      sub_zero, sub_self]
  have hsub := condExp_sub (μ := P) (integrable_const (1 : ℝ))
    ((integrable_const (1 : ℝ)).indicator hG.compl) (F a)
  rw [condExp_const (F.le a)] at hsub
  rw [heq]
  filter_upwards [hbound, hsub] with ω hbω hsω
  rw [hsω]
  exact sub_le_sub_left hbω 1

/-- Simultaneous lower interval event, with the empty and post-horizon sums
governed by the exposed `intervalSum` formula. -/
def lowerGood (P : Measure Ω) (F : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (α T : ℕ) (ℓ : ℝ) : Set Ω :=
  {ω | ∀ n ∈ Set.Icc α T, intervalSum (conditionalMean P F X) α T n ω / 2 - ℓ ≤
    intervalSum X α T n ω}

/-- Simultaneous upper interval event. -/
def upperGood (P : Measure Ω) (F : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (α T : ℕ) (ℓ : ℝ) : Set Ω :=
  {ω | ∀ n ∈ Set.Icc α T, intervalSum X α T n ω ≤
    2 * intervalSum (conditionalMean P F X) α T n ω + ℓ}

omit [IsProbabilityMeasure P] in
theorem lowerGood_measurable
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t)) (ℓ : ℝ) :
    MeasurableSet (lowerGood P F X α T ℓ) := by
  have hms (n : ℕ) : Measurable (intervalSum (conditionalMean P F X) α T n) :=
    ((intervalSum_stronglyMeasurable (fun t _ _ =>
      (conditionalMean_stronglyMeasurable t).mono (F.mono (Nat.sub_le t 1))) n).mono
        (F.le n)).measurable
  simp only [lowerGood, Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_le (((hms n).div_const 2).sub_const ℓ)
      (((intervalSum_stronglyMeasurable hX n).mono (F.le n)).measurable)

omit [IsProbabilityMeasure P] in
theorem upperGood_measurable
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t)) (ℓ : ℝ) :
    MeasurableSet (upperGood P F X α T ℓ) := by
  have hms (n : ℕ) : Measurable (intervalSum (conditionalMean P F X) α T n) :=
    ((intervalSum_stronglyMeasurable (fun t _ _ =>
      (conditionalMean_stronglyMeasurable t).mono (F.mono (Nat.sub_le t 1))) n).mono
        (F.le n)).measurable
  simp only [upperGood, Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_le (((intervalSum_stronglyMeasurable hX n).mono (F.le n)).measurable)
      (((hms n).const_mul 2).add_const ℓ)

/-- The source lower failure is almost surely a strict crossing of the
constructed lower supermartingale. -/
theorem lower_failure_subset_crossing_ae
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) (ℓ : ℝ) :
    (lowerGood P F X α T ℓ)ᶜ ≤ᵐ[P]
      clockCrossing (Lminus P F X α T) (α - 1) T (Real.exp ℓ) := by
  have hall : ∀ᵐ ω ∂P, ∀ n, 0 ≤ intervalSum (conditionalMean P F X) α T n ω := by
    apply ae_all_iff.mpr
    intro n
    exact (intervalSum_unit_bounds
      (fun t h1 h2 => conditionalMean_unit_bounds (hX t h1 h2) (hb t h1 h2)) n).mono
        (fun _ h => h.1)
  filter_upwards [hall] with ω hμ hfail
  obtain ⟨n, hn⟩ := not_forall.mp hfail
  obtain ⟨hnI, hnfail⟩ := not_imp.mp hn
  refine ⟨n, ⟨(Nat.sub_le α 1).trans hnI.1, hnI.2⟩, ?_⟩
  apply Real.exp_lt_exp.mpr
  have hbad := lt_of_not_ge hnfail
  nlinarith only [hbad, hμ n, Real.exp_neg_one_lt_half]

theorem upper_failure_subset_crossing_ae
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1) (ℓ : ℝ) :
    (upperGood P F X α T ℓ)ᶜ ≤ᵐ[P]
      clockCrossing (Lplus P F X α T) (α - 1) T (Real.exp ℓ) := by
  have hall : ∀ᵐ ω ∂P, ∀ n, 0 ≤ intervalSum (conditionalMean P F X) α T n ω := by
    apply ae_all_iff.mpr
    intro n
    exact (intervalSum_unit_bounds
      (fun t h1 h2 => conditionalMean_unit_bounds (hX t h1 h2) (hb t h1 h2)) n).mono
        (fun _ h => h.1)
  filter_upwards [hall] with ω hμ hfail
  obtain ⟨n, hn⟩ := not_forall.mp hfail
  obtain ⟨hnI, hnfail⟩ := not_imp.mp hn
  refine ⟨n, ⟨(Nat.sub_le α 1).trans hnI.1, hnI.2⟩, ?_⟩
  apply Real.exp_lt_exp.mpr
  have hbad := lt_of_not_ge hnfail
  nlinarith only [hbad, hμ n, Real.exp_one_lt_three]

theorem lower_failure_localized
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ)
    {A : Set Ω} (hA : MeasurableSet[F (α - 1)] A) :
    P.real (A ∩ (lowerGood P F X α T ℓ)ᶜ) ≤ Real.exp (-ℓ) * P.real A := by
  have hsub := lower_failure_subset_crossing_ae hX hb ℓ
  have hm : P (A ∩ (lowerGood P F X α T ℓ)ᶜ) ≤
      P (A ∩ clockCrossing (Lminus P F X α T) (α - 1) T (Real.exp ℓ)) := by
    apply measure_mono_ae
    filter_upwards [hsub] with ω hω hmem
    exact ⟨hmem.1, hω hmem.2⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hm).trans
    (intervalClock_localized_maximal hX hb hα hαT (-1) ℓ hA)

theorem upper_failure_localized
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ)
    {A : Set Ω} (hA : MeasurableSet[F (α - 1)] A) :
    P.real (A ∩ (upperGood P F X α T ℓ)ᶜ) ≤ Real.exp (-ℓ) * P.real A := by
  have hsub := upper_failure_subset_crossing_ae hX hb ℓ
  have hm : P (A ∩ (upperGood P F X α T ℓ)ᶜ) ≤
      P (A ∩ clockCrossing (Lplus P F X α T) (α - 1) T (Real.exp ℓ)) := by
    apply measure_mono_ae
    filter_upwards [hsub] with ω hω hmem
    exact ⟨hmem.1, hω hmem.2⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hm).trans
    (intervalClock_localized_maximal hX hb hα hαT 1 ℓ hA)

/-- Conditional lower estimate, simultaneously for every endpoint in `[α,T]`. -/
theorem lower_conditional_probability
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ) :
    (fun _ => 1 - Real.exp (-ℓ)) ≤ᵐ[P]
      P[(lowerGood P F X α T ℓ).indicator (fun _ => (1 : ℝ)) | F (α - 1)] :=
  condExp_indicator_ge_of_localized_compl (lowerGood_measurable hX ℓ)
    (fun _ hA => lower_failure_localized hX hb hα hαT ℓ hA)

/-- Conditional upper estimate, separately from the lower estimate, and
simultaneously for every endpoint in `[α,T]`. -/
theorem upper_conditional_probability
    (hX : ∀ t, α ≤ t → t ≤ T → StronglyMeasurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ) :
    (fun _ => 1 - Real.exp (-ℓ)) ≤ᵐ[P]
      P[(upperGood P F X α T ℓ).indicator (fun _ => (1 : ℝ)) | F (α - 1)] :=
  condExp_indicator_ge_of_localized_compl (upperGood_measurable hX ℓ)
    (fun _ hA => upper_failure_localized hX hb hα hαT ℓ hA)

omit [IsProbabilityMeasure P] in
theorem lowerGood_eq_interval_event (ℓ : ℝ) :
    lowerGood P F X α T ℓ =
      {ω | ∀ n ∈ Set.Icc α T, (∑ t ∈ Icc α n, conditionalMean P F X t ω) / 2 - ℓ ≤
        ∑ t ∈ Icc α n, X t ω} := by
  ext ω
  constructor <;> intro h n hn
  · simpa only [intervalSum_eq_sum_Icc X hn.2,
      intervalSum_eq_sum_Icc (conditionalMean P F X) hn.2] using h n hn
  · rw [intervalSum_eq_sum_Icc X hn.2,
      intervalSum_eq_sum_Icc (conditionalMean P F X) hn.2]
    exact h n hn

omit [IsProbabilityMeasure P] in
theorem upperGood_eq_interval_event (ℓ : ℝ) :
    upperGood P F X α T ℓ =
      {ω | ∀ n ∈ Set.Icc α T, (∑ t ∈ Icc α n, X t ω) ≤
        2 * (∑ t ∈ Icc α n, conditionalMean P F X t ω) + ℓ} := by
  ext ω
  constructor <;> intro h n hn
  · simpa only [intervalSum_eq_sum_Icc X hn.2,
      intervalSum_eq_sum_Icc (conditionalMean P F X) hn.2] using h n hn
  · rw [intervalSum_eq_sum_Icc X hn.2,
      intervalSum_eq_sum_Icc (conditionalMean P F X) hn.2]
    exact h n hn

/-- Source-motivated lower interval estimate, with measurable real observations
and literal finite sums. It is conditional on `F (α - 1)` and simultaneous in `n`.
Source: appendix B, lines 247–292. The bound also holds for nonpositive `ℓ`. -/
theorem interval_lower_bound
    (hX : ∀ t, α ≤ t → t ≤ T → Measurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ) :
    (fun _ => 1 - Real.exp (-ℓ)) ≤ᵐ[P]
      P[({ω | ∀ n ∈ Set.Icc α T,
        (∑ t ∈ Icc α n, conditionalMean P F X t ω) / 2 - ℓ ≤
          ∑ t ∈ Icc α n, X t ω}).indicator (fun _ => (1 : ℝ)) | F (α - 1)] := by
  rw [← lowerGood_eq_interval_event]
  exact lower_conditional_probability (fun t h1 h2 => (hX t h1 h2).stronglyMeasurable)
    hb hα hαT ℓ

/-- Source-motivated upper interval estimate; its failure probability is bounded
separately from that of the lower estimate. Source: appendix B, lines 247–292. -/
theorem interval_upper_bound
    (hX : ∀ t, α ≤ t → t ≤ T → Measurable[F t] (X t))
    (hb : ∀ t, α ≤ t → t ≤ T → ∀ᵐ ω ∂P, 0 ≤ X t ω ∧ X t ω ≤ 1)
    (hα : 1 ≤ α) (hαT : α ≤ T) (ℓ : ℝ) :
    (fun _ => 1 - Real.exp (-ℓ)) ≤ᵐ[P]
      P[({ω | ∀ n ∈ Set.Icc α T, (∑ t ∈ Icc α n, X t ω) ≤
        2 * (∑ t ∈ Icc α n, conditionalMean P F X t ω) + ℓ}).indicator
          (fun _ => (1 : ℝ)) | F (α - 1)] := by
  rw [← upperGood_eq_interval_event]
  exact upper_conditional_probability (fun t h1 h2 => (hX t h1 h2).stronglyMeasurable)
    hb hα hαT ℓ

end Bandits.Support.BootstrapIntervalBounds
