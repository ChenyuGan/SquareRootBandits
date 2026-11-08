/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.AffineBatchDecoder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A finite causal affine one-batch experiment

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-155`
and `sources/zip4/manuscript/05_binary_transport.tex:7-53`.

The experiment samples complete fresh affine pairs, independently of fresh finite controls.
A policy sees an initial exposed value and the preceding draws. Its current positive rule
sees the current pair only through the hash of its selected word; with no word it sees no
current hash. Stopping is absorbing. These are structural restrictions on a finite experiment,
not hypotheses asserting a conditional law or a tail estimate. The candidate is fixed outside
the future sampling. Physical channel admissibility, stale-word exclusion, and the source
failure events require separate producers. No manuscript theorem is closed here.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace Bandits.Support.AdaptiveAffineBatchTail

open AffineChannelLaw

/-- One fresh complete affine pair and one independent finite control. -/
abbrev Draw (B : ℕ) (C : Type) := Sample B × C

/-- Literal finite product carrier, in chronological order. -/
abbrev Paths (B : ℕ) (C : Type) (n : ℕ) : Type :=
  Nat.rec Unit (fun _ X => Draw B C × X) n

noncomputable instance pathsFintype (B : ℕ) (C : Type) [Fintype C] :
    (n : ℕ) → Fintype (Paths B C n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := pathsFintype B C n
    exact inferInstanceAs (Fintype (Draw B C × Paths B C n))

/-- The policy chooses its word and continuation before inspecting the fresh pair.
The rule may use the fresh independent control; its bit argument is the sent-word hash.
For `none`, this argument is always zero. `active = false` stops the batch permanently. -/
structure Decision (B : ℕ) (C : Type) where
  sent : Option (Word B)
  active : Bool
  positive : C → Bit → Bool

/-- Causality is enforced by the domain: only the initial exposure and past draws are read.
Past outcomes are deterministic functions of these data. -/
abbrev Policy (B : ℕ) (C H : Type) := H → List (Draw B C) → Decision B C

/-- The actual current Boolean test. In particular `none` ignores the current pair. -/
def positiveTest {B : ℕ} {C : Type} (d : Decision B C) (s : Sample B) (c : C) : Bool :=
  d.active && d.positive c (match d.sent with | none => 0 | some w => affineHash s w)

/-- The absent-word branch is constant in the current affine sample. -/
theorem positiveTest_none {B : ℕ} {C : Type} (d : Decision B C)
    (h : d.sent = none) (s t : Sample B) (c : C) :
    positiveTest d s c = positiveTest d t c := by
  simp only [positiveTest, h]

/-- A retained positive test, with its chronological time and actually selected word. -/
structure Test (B : ℕ) where
  time : ℕ
  sample : Sample B
  sent : Option (Word B)

/-- Actual chronological tests. All future draws remain in the product space after stopping,
but cannot contribute another test. -/
def tests {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) : {n : ℕ} → Paths B C n → List (Test B)
  | 0, _ => []
  | _ + 1, (x, xs) =>
    let d := π initial past
    if d.active = true then
      let later := tests π initial (past ++ [x]) xs
      if positiveTest d x.1 x.2 = true then
        ⟨past.length, x.1, d.sent⟩ :: later
      else later
    else []

theorem tests_stopped {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (ha : (π initial past).active ≠ true)
    {n : ℕ} (xs : Paths B C n) : tests π initial past xs = [] := by
  cases n with
  | zero => rfl
  | succ n =>
    obtain ⟨x, rest⟩ := xs
    simp only [tests, ha, Bool.false_eq_true, ite_false]

/-- The actual number of tests, including tests with `sent = none`. -/
def testCount {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) {n : ℕ} (xs : Paths B C n) : ℕ :=
  (tests π initial past xs).length

/-- Time of test number `q+1`, or `none` if it does not occur before stopping. -/
def occurrenceTime {B : ℕ} (ts : List (Test B)) (q : ℕ) : Option ℕ :=
  (ts[q]?).map Test.time

/-- The literal per-test condition; `none` counts as a word different from the candidate. -/
def good {B : ℕ} (M : Word B) (e : Test B) : Prop :=
  e.sent ≠ some M ∧ affineHash e.sample M = 1

/-- The first `q` tests exist before stopping and all satisfy `good`. -/
def survives {B : ℕ} (M : Word B) : ℕ → List (Test B) → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | q + 1, e :: es => good M e ∧ survives M q es

/-- The actual source-shaped event `D_q` on the finite experiment. -/
def D {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) (q : ℕ) {n : ℕ}
    (xs : Paths B C n) : Prop := survives M q (tests π initial past xs)

/-- The `(q+1)`st test exists, its word differs from `M`, and its predecessors are good.
Its own candidate hash is deliberately not constrained. -/
def attempt {B : ℕ} (M : Word B) : ℕ → List (Test B) → Prop
  | _, [] => False
  | 0, e :: _ => e.sent ≠ some M
  | q + 1, e :: es => good M e ∧ attempt M q es

/-- A literal zero-one indicator, used only in finite sums. -/
noncomputable def indicator (P : Prop) : ℝ≥0∞ := if P then 1 else 0

/-- The full product atom weight; no candidate-dependent law occurs here. -/
noncomputable def atomMass {B : ℕ} {C : Type} (μ : PMF C) :
    (n : ℕ) → Paths B C n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, (x, xs) => jointLaw B x.1 * μ x.2 * atomMass μ n xs

/-- Finite expectation against the actual product weights. -/
noncomputable def average {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (f : Paths B C n → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ xs, atomMass μ n xs * f xs

private theorem pmf_sum {A : Type} [Fintype A] (p : PMF A) : ∑ a, p a = 1 := by
  exact (tsum_fintype (L := .unconditional A) _).symm.trans p.tsum_coe

theorem sum_atomMass {B : ℕ} {C : Type} [Fintype C] (μ : PMF C) (n : ℕ) :
    ∑ xs, atomMass (B := B) μ n xs = 1 := by
  induction n with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ≥0∞)) = 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  | succ n ih =>
    change (∑ x : Draw B C × Paths B C n,
      jointLaw B x.1.1 * μ x.1.2 * atomMass μ n x.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, pmf_sum, mul_one]
    exact pmf_sum _

/-- A normalized, concrete PMF on the entire finite product carrier. -/
noncomputable def experimentLaw {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) : PMF (Paths B C n) :=
  PMF.ofFintype (atomMass μ n) (sum_atomMass μ n)

/-- Exact atom formula for the actual experiment, including zero-mass control atoms. -/
theorem experimentLaw_apply {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (xs : Paths B C n) : experimentLaw (B := B) μ n xs = atomMass μ n xs := rfl

/-- Exact finite event formula, with no division by prefix probabilities. -/
theorem experimentLaw_event {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (E : Paths B C n → Prop) :
    (experimentLaw (B := B) μ n).toOuterMeasure {xs | E xs} =
      average (B := B) μ n (fun xs => indicator (E xs)) := by
  rw [PMF.toOuterMeasure_apply_fintype]
  unfold average
  apply Finset.sum_congr rfl
  intro xs _
  by_cases h : E xs <;> simp only [Set.indicator, Set.mem_ofPred_eq, h,
    indicator, ite_true, ite_false, experimentLaw_apply, mul_one, mul_zero]

private theorem average_zero {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) : average (B := B) μ n (fun _ => 0) = 0 := by
  simp only [average, mul_zero, Finset.sum_const_zero]

private theorem average_one {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) : average (B := B) μ n (fun _ => 1) = 1 := by
  simp only [average, mul_one, sum_atomMass]

private theorem average_mul {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (a : ℝ≥0∞) (f : Paths B C n → ℝ≥0∞) :
    average (B := B) μ n (fun xs => a * f xs) = a * average (B := B) μ n f := by
  unfold average
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  dsimp only
  ac_rfl

/-- The finite product factorization is proved from the literal atom weights. -/
theorem average_succ {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (f : Paths B C (n + 1) → ℝ≥0∞) :
    average (B := B) μ (n + 1) f = ∑ s : Sample B, ∑ c : C,
      jointLaw B s * μ c * average (B := B) μ n (fun xs => f ((s, c), xs)) := by
  change (∑ x : Draw B C × Paths B C n,
    (jointLaw B x.1.1 * μ x.1.2 * atomMass μ n x.2) * f x) = _
  simp only [Fintype.sum_prod_type, average, Finset.mul_sum, mul_assoc]

private theorem indicator_true : indicator True = 1 := by
  simp only [indicator, ite_true]

private theorem indicator_false : indicator False = 0 := by
  simp only [indicator, ite_false]

private theorem indicator_and (P Q : Prop) :
    indicator (P ∧ Q) = indicator P * indicator Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [indicator, hp, hq]

private theorem joint_event {B : ℕ} (E : Sample B → Prop) :
    (∑ s, jointLaw B s * indicator (E s)) = eventProbability E := by
  rw [eventProbability, PMF.toOuterMeasure_apply_fintype]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : E s <;> simp [Set.indicator, indicator, h]

private theorem weighted_partition {A K : Type} [Fintype A] [Fintype K]
    (p : A → ℝ≥0∞) (g : A → K) (E : A → Prop) (f : K → ℝ≥0∞) :
    (∑ x, p x * f (g x) * indicator (E x)) =
      ∑ k, (∑ x, p x * indicator (g x = k ∧ E x)) * f k := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [indicator, h, mul_ite, ite_mul, eq_comm]

private theorem hash_rule_half {B : ℕ} {u M : Word B} (hne : u ≠ M)
    (f : Bit → ℝ≥0∞) :
    (∑ s : Sample B, jointLaw B s * f (affineHash s u) *
      indicator (affineHash s M = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ s : Sample B, jointLaw B s * f (affineHash s u) := by
  have hp := weighted_partition (jointLaw B) (fun s => affineHash s u)
    (fun s => affineHash s M = 1) f
  have hm := weighted_partition (jointLaw B) (fun s => affineHash s u)
    (fun _ => True) f
  simp only [indicator_true, mul_one, and_true] at hm
  simp_rw [joint_event] at hp hm
  have hm' : (∑ s : Sample B, jointLaw B s * f (affineHash s u)) =
      ∑ a : Bit, eventProbability (fun s => affineHash s u = a) * f a := hm
  simp_rw [affineHash_pair_probability hne] at hp
  simp_rw [affineHash_probability] at hm'
  rw [hp, hm', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc]
  congr 1
  norm_num only [one_div]
  rw [← pow_two, ← ENNReal.inv_pow]
  norm_num

/-- The exact one-step half identity from affine pairwise independence. It also includes
`none`, whose test is constant in the affine pair. The current control is fixed here. -/
theorem one_step_half {B : ℕ} {C : Type} (d : Decision B C) (M : Word B) (c : C) :
    (∑ s : Sample B, jointLaw B s * indicator
      (positiveTest d s c = true ∧ d.sent ≠ some M ∧ affineHash s M = 1)) =
    ((1 : ℝ≥0∞) / 2) * ∑ s : Sample B, jointLaw B s * indicator
      (positiveTest d s c = true ∧ d.sent ≠ some M) := by
  classical
  cases hs : d.sent with
  | none =>
    by_cases ht : (d.active && d.positive c 0) = true
    · simp only [positiveTest, hs, ht, true_and, ne_eq, reduceCtorEq, not_false_eq_true,
        indicator, ite_true, mul_one]
      have he := joint_event (fun s => affineHash s M = 1)
      rw [affineHash_probability] at he
      convert he using 1
      · apply Finset.sum_congr rfl
        intro s _
        by_cases hh : affineHash s M = 1 <;> simp [indicator, hh]
      · rw [pmf_sum, mul_one]
    · simp [positiveTest, hs, ht, indicator]
  | some u =>
    by_cases h : u = M
    · subst u
      simp [indicator]
    · have hd : some u ≠ some M := fun heq => h (Option.some.inj heq)
      have hp := hash_rule_half h
        (fun a => indicator ((d.active && d.positive c a) = true))
      simpa [positiveTest, hs, hd, indicator, mul_ite, ite_mul, ← ite_and, and_comm] using hp

private theorem average_const {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (a : ℝ≥0∞) : average (B := B) μ n (fun _ => a) = a := by
  unfold average
  rw [← Finset.sum_mul, sum_atomMass, one_mul]

private theorem average_mono {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) {f g : Paths B C n → ℝ≥0∞} (h : ∀ xs, f xs ≤ g xs) :
    average (B := B) μ n f ≤ average (B := B) μ n g := by
  exact Finset.sum_le_sum fun xs _ => mul_le_mul_right (h xs) _

private theorem indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  by_cases hp : P
  · simp only [indicator, hp, h hp, ite_true, le_refl]
  · simp only [indicator, hp, ite_false, zero_le]

/-- Expanded meaning of the first-`q` event: existence and every retained hash/word test. -/
theorem survives_iff {B : ℕ} (M : Word B) (q : ℕ) (ts : List (Test B)) :
    survives M q ts ↔ q ≤ ts.length ∧ ∀ e ∈ ts.take q, good M e := by
  induction q generalizing ts with
  | zero => simp [survives]
  | succ q ih =>
    cases ts with
    | nil => simp [survives]
    | cons e es => simp [survives, ih, List.take_succ_cons, and_left_comm]

/-- `D_0` is the sure event, even after stopping and with zero remaining rounds. -/
theorem D_zero {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) {n : ℕ} (xs : Paths B C n) :
    D π initial past M 0 xs := trivial

/-- The unchecked last hash in `attempt` does not remove any predecessor requirement. -/
theorem attempt_implies_survives {B : ℕ} (M : Word B) (q : ℕ) (ts : List (Test B)) :
    attempt M q ts → survives M q ts := by
  induction q generalizing ts with
  | zero => exact fun _ => trivial
  | succ q ih =>
    cases ts with
    | nil => exact False.elim
    | cons e es => exact fun h => ⟨h.1, ih es h.2⟩

private theorem draw_half {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (d : Decision B C) (M : Word B) :
    (∑ s : Sample B, ∑ c : C, jointLaw B s * μ c * indicator
      (positiveTest d s c = true ∧ d.sent ≠ some M ∧ affineHash s M = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ s : Sample B, ∑ c : C,
        jointLaw B s * μ c * indicator (positiveTest d s c = true ∧ d.sent ≠ some M) := by
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have h := one_step_half d M c
  calc
    (∑ s : Sample B, jointLaw B s * μ c * indicator
        (positiveTest d s c = true ∧ d.sent ≠ some M ∧ affineHash s M = 1)) =
        μ c * ∑ s : Sample B, jointLaw B s * indicator
          (positiveTest d s c = true ∧ d.sent ≠ some M ∧ affineHash s M = 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ac_rfl
    _ = ((1 : ℝ≥0∞) / 2) * ∑ s : Sample B,
        jointLaw B s * μ c * indicator (positiveTest d s c = true ∧ d.sent ≠ some M) := by
      rw [h]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ac_rfl

private theorem first_average {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n : ℕ) (s : Sample B) (c : C)
    (ha : (π initial past).active = true) :
    average (B := B) μ n (fun xs => indicator (D π initial past M 1 (n := n + 1) ((s, c), xs))) =
      indicator (positiveTest (π initial past) s c = true ∧
        (π initial past).sent ≠ some M ∧ affineHash s M = 1) +
      (if positiveTest (π initial past) s c = true then 0 else
        average (B := B) μ n (fun xs => indicator (D π initial (past ++ [(s, c)]) M 1 xs))) := by
  by_cases ht : positiveTest (π initial past) s c = true
  · simp only [D, tests, ha, ite_true, ht, survives, and_true, good,
      true_and, average_const, add_zero]
  · simp [D, tests, ha, ht, indicator_false]

private theorem first_attempt_average {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n : ℕ) (s : Sample B) (c : C)
    (ha : (π initial past).active = true) :
    average (B := B) μ n (fun xs => indicator (attempt M 0 (tests π initial past (n := n + 1) ((s, c), xs)))) =
      indicator (positiveTest (π initial past) s c = true ∧ (π initial past).sent ≠ some M) +
      (if positiveTest (π initial past) s c = true then 0 else
        average (B := B) μ n (fun xs => indicator
          (attempt M 0 (tests π initial (past ++ [(s, c)]) xs)))) := by
  by_cases ht : positiveTest (π initial past) s c = true
  · simp only [tests, ha, ite_true, ht, attempt, true_and, average_const, add_zero]
  · simp [tests, ha, ht, indicator_false]

/-- Summing over the actual `(q+1)`st test gives exactly a factor of one half.
This is derived from the product PMF and the causal policy, with no conditional-law input. -/
theorem adaptive_half {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    average (B := B) μ n (fun xs => indicator (D π initial past M (q + 1) xs)) =
      ((1 : ℝ≥0∞) / 2) * average (B := B) μ n
        (fun xs => indicator (attempt M q (tests π initial past xs))) := by
  induction n generalizing past q with
  | zero => simp only [D, tests, survives, attempt, indicator_false, average_zero, mul_zero]
  | succ n ih =>
    by_cases ha : (π initial past).active = true
    · cases q with
      | zero =>
        rw [average_succ, average_succ]
        simp_rw [first_average (B := B) μ π initial past M n _ _ ha,
          first_attempt_average (B := B) μ π initial past M n _ _ ha, mul_add,
          Finset.sum_add_distrib]
        rw [draw_half]
        rw [mul_add]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        by_cases ht : positiveTest (π initial past) s c = true
        · simp only [ht, ite_true, mul_zero]
        · simp only [ht, Bool.false_eq_true, ite_false]
          rw [ih (past ++ [(s, c)]) 0]
          ac_rfl
      | succ q =>
        rw [average_succ, average_succ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        have local_half :
            average (B := B) μ n (fun xs => indicator (D π initial past M (q + 1 + 1) (n := n + 1) ((s, c), xs))) =
            ((1 : ℝ≥0∞) / 2) * average (B := B) μ n (fun xs =>
              indicator (attempt M (q + 1) (tests π initial past (n := n + 1) ((s, c), xs)))) := by
          by_cases ht : positiveTest (π initial past) s c = true
          · simp only [D, tests, ha, ite_true, ht, survives, attempt,
              indicator_and, average_mul]
            have hnext := ih (past ++ [(s, c)]) q
            unfold D at hnext
            rw [hnext]
            ac_rfl
          · simpa only [D, tests, ha, ite_true, ht, Bool.false_eq_true, ite_false] using
              ih (past ++ [(s, c)]) (q + 1)
        rw [local_half]
        ac_rfl
    · simp only [D, tests_stopped π initial past ha, survives, attempt, indicator_false,
        average_zero, mul_zero]

/-- Every generated test is stamped with a round in the actual remaining horizon. -/
theorem tests_mem_bounds {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) {n : ℕ} (xs : Paths B C n)
    (e : Test B) (he : e ∈ tests π initial past xs) :
    past.length ≤ e.time ∧ e.time < past.length + n := by
  induction n generalizing past with
  | zero => simp only [tests, List.not_mem_nil] at he
  | succ n ih =>
    obtain ⟨x, rest⟩ := xs
    simp only [tests] at he
    split at he
    next ha =>
      split at he
      next ht =>
        rcases List.mem_cons.mp he with he | he
        · subst e
          simp only
          omega
        · have hb := ih (past ++ [x]) rest he
          simp only [List.length_append, List.length_singleton] at hb
          omega
      next ht =>
        have hb := ih (past ++ [x]) rest he
        simp only [List.length_append, List.length_singleton] at hb
        omega
    next ha => simp only [List.not_mem_nil] at he

/-- The actual occurrence list is strictly chronological, including repeated samples. -/
theorem tests_ordered {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) {n : ℕ} (xs : Paths B C n) :
    (tests π initial past xs).Pairwise (fun e f => e.time < f.time) := by
  induction n generalizing past with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    obtain ⟨x, rest⟩ := xs
    simp only [tests]
    split
    next ha =>
      split
      next ht =>
        apply List.pairwise_cons.mpr
        constructor
        · intro e he
          have hb := (tests_mem_bounds π initial (past ++ [x]) rest e he).1
          simp only [List.length_append, List.length_singleton] at hb
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hb
        · exact ih (past ++ [x]) rest
      next ht => exact ih (past ++ [x]) rest
    next ha => exact List.Pairwise.nil

/-- Existing ordered occurrences have strictly increasing actual round numbers. -/
theorem occurrenceTime_strict {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) {n : ℕ} (xs : Paths B C n)
    {q j r s : ℕ} (hqj : q < j)
    (hr : occurrenceTime (tests π initial past xs) q = some r)
    (hs : occurrenceTime (tests π initial past xs) j = some s) : r < s := by
  cases hqe : (tests π initial past xs)[q]? with
  | none => simp only [occurrenceTime, hqe, Option.map_none, reduceCtorEq] at hr
  | some e =>
    cases hjf : (tests π initial past xs)[j]? with
    | none => simp only [occurrenceTime, hjf, Option.map_none, reduceCtorEq] at hs
    | some f =>
      simp only [occurrenceTime, hqe, Option.map_some, Option.some.injEq] at hr
      simp only [occurrenceTime, hjf, Option.map_some, Option.some.injEq] at hs
      obtain ⟨hq, he⟩ := List.getElem?_eq_some_iff.mp hqe
      obtain ⟨hj, hf⟩ := List.getElem?_eq_some_iff.mp hjf
      have hord := (tests_ordered π initial past xs).rel_getElem_of_lt hq hj hqj
      simpa only [he, hf, hr, hs] using hord

/-- No round can contribute more than one test. -/
theorem testCount_le {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) {n : ℕ} (xs : Paths B C n) :
    testCount π initial past xs ≤ n := by
  induction n generalizing past with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    obtain ⟨x, rest⟩ := xs
    unfold testCount
    simp only [tests]
    split
    next ha =>
      split
      next ht => exact Nat.succ_le_succ (ih (past ++ [x]) rest)
      next ht => exact Nat.le_succ_of_le (ih (past ++ [x]) rest)
    next ha => exact Nat.zero_le _

/-- The actual test count strictly before a round, as in the source's `N_{r-1}`. -/
def countBefore {B : ℕ} (ts : List (Test B)) (r : ℕ) : ℕ :=
  ts.countP (fun e => decide (e.time < r))

/-- In a chronological list the test with zero-based index `q` has exactly `q`
predecessors. This does not assume anything about the sample values. -/
theorem countBefore_eq_index {B : ℕ} (ts : List (Test B))
    (ho : ts.Pairwise (fun e f => e.time < f.time)) (q : ℕ) (e : Test B)
    (he : ts[q]? = some e) : countBefore ts e.time = q := by
  induction ts generalizing q with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at he
  | cons a es ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp ho
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      simp only [countBefore, List.countP_cons, lt_self_iff_false, decide_false,
        Bool.false_eq_true, ite_false, add_zero]
      apply List.countP_eq_zero.mpr
      intro f hf
      simpa only [decide_eq_true_eq] using Nat.not_lt_of_ge (Nat.le_of_lt (hfirst f hf))
    | succ q =>
      have het : es[q]? = some e := he
      have hem : e ∈ es := List.mem_iff_getElem?.mpr ⟨q, het⟩
      have hlt := hfirst e hem
      have hi := ih htail q het
      simp only [countBefore, List.countP_cons, hlt, decide_true, ite_true]
      exact congrArg (fun k => k + 1) hi

/-- A successful attempt has a genuine `(q+1)`st retained test. -/
theorem attempt_has_test {B : ℕ} (M : Word B) (q : ℕ) (ts : List (Test B)) :
    attempt M q ts → ∃ e, ts[q]? = some e := by
  induction q generalizing ts with
  | zero =>
    cases ts with
    | nil => exact False.elim
    | cons e es => exact fun _ => ⟨e, rfl⟩
  | succ q ih =>
    cases ts with
    | nil => exact False.elim
    | cons e es =>
      intro h
      obtain ⟨f, hf⟩ := ih es h.2
      exact ⟨f, hf⟩

/-- The last-hash-unchecked `(q+1)`st contribution at its actual round. -/
def qthAt {B : ℕ} (M : Word B) (q : ℕ) (ts : List (Test B)) (r : ℕ) : Prop :=
  attempt M q ts ∧ occurrenceTime ts q = some r

/-- There is at most one possible occurrence time on every sample path. -/
theorem qthAt_unique {B : ℕ} (M : Word B) (q : ℕ) (ts : List (Test B))
    {r s : ℕ} (hr : qthAt M q ts r) (hs : qthAt M q ts s) : r = s :=
  Option.some.inj (hr.2.symm.trans hs.2)

/-- At the possible `(q+1)`st-test round the actual preceding test count is `q`. -/
theorem qthAt_countBefore {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) (q r : ℕ) {n : ℕ} (xs : Paths B C n)
    (h : qthAt M q (tests π initial past xs) r) :
    countBefore (tests π initial past xs) r = q := by
  obtain ⟨e, he⟩ := attempt_has_test M q _ h.1
  have ht : e.time = r := by
    have htime := h.2
    simp only [occurrenceTime, he, Option.map_some, Option.some.injEq] at htime
    exact htime
  rw [← ht]
  exact countBefore_eq_index _ (tests_ordered π initial past xs) q e he

/-- Exact at-most-once summation over all possible rounds of the `(q+1)`st test. -/
theorem qth_sum {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) (q : ℕ) {n : ℕ} (xs : Paths B C n) :
    (∑ r ∈ Finset.Ico past.length (past.length + n),
      indicator (qthAt M q (tests π initial past xs) r)) =
      indicator (attempt M q (tests π initial past xs)) := by
  by_cases ha : attempt M q (tests π initial past xs)
  · obtain ⟨e, he⟩ := attempt_has_test M q _ ha
    have hmem : e ∈ tests π initial past xs := List.mem_iff_getElem?.mpr ⟨q, he⟩
    have hb := tests_mem_bounds π initial past xs e hmem
    have ht : occurrenceTime (tests π initial past xs) q = some e.time := by
      simp only [occurrenceTime, he, Option.map_some]
    simp [qthAt, ha, ht, indicator, eq_comm, Finset.mem_Ico, hb.1, hb.2]
  · simp only [qthAt, ha, false_and, indicator_false, Finset.sum_const_zero]

/-- Pathwise domination of the at-most-once sum by the preceding success event. -/
theorem qth_sum_le_D {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) (q : ℕ) {n : ℕ} (xs : Paths B C n) :
    (∑ r ∈ Finset.Ico past.length (past.length + n),
      indicator (qthAt M q (tests π initial past xs) r)) ≤
      indicator (D π initial past M q xs) := by
  rw [qth_sum]
  exact indicator_mono (attempt_implies_survives M q _)

/-- The source's summation identity, proved for actual chronological tests. -/
theorem adaptive_half_sum {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    average (B := B) μ n (fun xs => indicator (D π initial past M (q + 1) xs)) =
      ((1 : ℝ≥0∞) / 2) * average (B := B) μ n (fun xs =>
        ∑ r ∈ Finset.Ico past.length (past.length + n),
          indicator (qthAt M q (tests π initial past xs) r)) := by
  simp only [qth_sum, adaptive_half]

/-- The source's geometric recurrence follows from the at-most-once test event. -/
theorem tail_recurrence {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    average (B := B) μ n (fun xs => indicator (D π initial past M (q + 1) xs)) ≤
      ((1 : ℝ≥0∞) / 2) * average (B := B) μ n (fun xs => indicator (D π initial past M q xs)) := by
  rw [adaptive_half_sum]
  apply mul_le_mul_right
  apply average_mono
  intro xs
  exact qth_sum_le_D π initial past M q xs

/-- The genuine finite adaptive experiment has mass `D_q ≤ (1/2)^q`, uniformly in
initial exposure and in the candidate fixed before the future product draws. -/
theorem adaptive_tail {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    (experimentLaw (B := B) μ n).toOuterMeasure {xs | D π initial past M q xs} ≤
      ((1 : ℝ≥0∞) / 2) ^ q := by
  rw [experimentLaw_event]
  induction q with
  | zero => simp only [D, survives, indicator_true, average_one, pow_zero, le_refl]
  | succ q ih =>
    calc
      _ ≤ ((1 : ℝ≥0∞) / 2) *
          average (B := B) μ n (fun xs => indicator (D π initial past M q xs)) :=
        tail_recurrence μ π initial past M n q
      _ ≤ ((1 : ℝ≥0∞) / 2) * ((1 : ℝ≥0∞) / 2) ^ q := mul_le_mul_right ih _
      _ = _ := (pow_succ' _ _).symm

/-- Probability-mass form of the geometric recurrence for the concrete PMF. -/
theorem tail_mass_recurrence {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    (experimentLaw (B := B) μ n).toOuterMeasure {xs | D π initial past M (q + 1) xs} ≤
      ((1 : ℝ≥0∞) / 2) *
        (experimentLaw (B := B) μ n).toOuterMeasure {xs | D π initial past M q xs} := by
  simp only [experimentLaw_event]
  exact tail_recurrence μ π initial past M n q

/-- The same bound written as `2^(-q)`, using the inverse of the natural power. -/
theorem adaptive_tail_inv_pow {B : ℕ} {C H : Type} [Fintype C] (μ : PMF C)
    (π : Policy B C H) (initial : H) (past : List (Draw B C))
    (M : Word B) (n q : ℕ) :
    (experimentLaw (B := B) μ n).toOuterMeasure {xs | D π initial past M q xs} ≤
      (2 ^ q : ℝ≥0∞)⁻¹ := by
  simpa only [one_div, ENNReal.inv_pow] using adaptive_tail μ π initial past M n q

/-- Literal decoder interface: `D_q` retains exactly `q` existing good tests, whose
sample list satisfies the accepted decoder equations. This asserts no unique solution. -/
theorem D_iff_decoder {B : ℕ} {C H : Type} (π : Policy B C H) (initial : H)
    (past : List (Draw B C)) (M : Word B) (q : ℕ) {n : ℕ} (xs : Paths B C n) :
    D π initial past M q xs ↔
      q ≤ testCount π initial past xs ∧
      (∀ e ∈ (tests π initial past xs).take q, e.sent ≠ some M) ∧
      AffineBatchDecoder.satisfies
        (((tests π initial past xs).take q).map Test.sample) M := by
  rw [D, survives_iff, AffineBatchDecoder.satisfies_iff_hashes]
  constructor
  · rintro ⟨hlen, hg⟩
    refine ⟨hlen, fun e he => (hg e he).1, ?_⟩
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact (hg e he).2
  · rintro ⟨hlen, hne, hh⟩
    refine ⟨hlen, fun e he => ⟨hne e he, ?_⟩⟩
    exact hh e.sample (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- The whole next-draw atom factors as a fresh full affine pair, an independent control,
and the remaining product atom. It includes controls of probability zero. -/
theorem experimentLaw_cons {B : ℕ} {C : Type} [Fintype C] (μ : PMF C)
    (n : ℕ) (s : Sample B) (c : C) (xs : Paths B C n) :
    experimentLaw (B := B) μ (n + 1) ((s, c), xs) =
      jointLaw B s * μ c * experimentLaw (B := B) μ n xs := rfl

/-- With no extra controls, every complete affine sample path has exactly the uniform
product atom mass. Width zero and horizon zero are included. -/
theorem affine_only_atom (B n : ℕ) (xs : Paths B Unit n) :
    experimentLaw (B := B) (PMF.pure ()) n xs =
      ((2 ^ (B + 1) : ℝ≥0∞)⁻¹) ^ n := by
  induction n with
  | zero => simp only [experimentLaw_apply, atomMass, pow_zero]
  | succ n ih =>
    obtain ⟨⟨s, c⟩, rest⟩ := xs
    cases c
    rw [experimentLaw_cons, jointLaw_apply_eq_inv_pow, PMF.pure_apply_self,
      mul_one, ih rest]
    exact (pow_succ' _ _).symm

end Bandits.Support.AdaptiveAffineBatchTail

end
