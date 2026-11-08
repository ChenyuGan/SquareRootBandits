/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedProductiveSuccessPrefixLaw
public import Bandits.Support.GeneratedHeldArmRevealFiltration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Process.Adapted

/-!
# Productive exit mean on the auxiliary raw held-arm reveal history

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-415,586-625`
and `sources/zip4/manuscript/07_public_setup.tex:63-115`.

The base history and its current latent activity/held-arm join are exactly the
accepted auxiliary constructions, on the full original continuous coordinate
carrier. An arbitrary measurable test in this join is decomposed on the finite
pair fibers into causal-prefix tests. The accepted arbitrary-prefix success law
then supplies the lower conditional mean, without conditioning on continuous
singletons or normalizing by fiber mass. The exit remains the actual productive
indicator times one minus the next prelaunch/uninformed indicator, so a launch
crossing can also cause an exit.

This is an internal auxiliary-history result. Equality with manuscript local
information, transfer to source conditioning, the outer good-public-output then
all-rewards then private-expectation quantifiers, concentration, and the main
regret statement are not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedHeldArmRevealFiltration
open Bandits.Support.GeneratedProductiveSuccessCells

namespace Bandits.Support.GeneratedProductiveSuccessMean

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapBlockFiltrationRepair.Coordinates p

/-- Every test in a join with an observed map agrees on each map fiber with
a test in the base sigma algebra. No measurability, mass, or finiteness of a
fiber is assumed. -/
theorem measurableSet_join_comap_fiber {α β : Type*} (m : MeasurableSpace α)
    [MeasurableSpace β] (f : α → β) (T : Set α)
    (hT : MeasurableSet[m ⊔ MeasurableSpace.comap f inferInstance] T) :
    ∃ A : β → Set α, (∀ b, MeasurableSet[m] (A b)) ∧
      ∀ b, T ∩ {e | f e = b} = A b ∩ {e | f e = b} := by
  classical
  let M : MeasurableSpace α := {
    MeasurableSet' := fun S => ∀ b, ∃ A : Set α,
      MeasurableSet[m] A ∧ ∀ e, f e = b → (e ∈ S ↔ e ∈ A)
    measurableSet_empty := fun _ => ⟨∅, MeasurableSet.empty, fun _ _ => Iff.rfl⟩
    measurableSet_compl := by
      intro S hS b
      obtain ⟨A, hA, heq⟩ := hS b
      exact ⟨Aᶜ, hA.compl, fun e he => not_congr (heq e he)⟩
    measurableSet_iUnion := by
      intro S hS b
      choose A hA heq using fun n => hS n b
      refine ⟨⋃ n, A n, MeasurableSet.iUnion hA, ?_⟩
      intro e he
      simp only [Set.mem_iUnion]
      exact exists_congr fun n => heq n e he }
  have hbase : m ≤ M := fun S hS b => ⟨S, hS, fun _ _ => Iff.rfl⟩
  have hmap : MeasurableSpace.comap f inferInstance ≤ M := by
    intro S hS b
    obtain ⟨U, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
    by_cases hb : b ∈ U
    · exact ⟨Set.univ, MeasurableSet.univ, fun e he => by simp [he, hb]⟩
    · exact ⟨∅, @MeasurableSet.empty α m, fun e he => by simp [he, hb]⟩
  have htest : MeasurableSet[M] T := (sup_le hbase hmap) T hT
  choose A hA heq using htest
  refine ⟨A, hA, fun b => ?_⟩
  ext e
  exact ⟨fun he => ⟨(heq b e he.2).1 he.1, he.2⟩,
    fun he => ⟨(heq b e he.2).2 he.1, he.2⟩⟩

/-- Finite observed fibers partition a set integral on the original carrier.
Null and empty fibers are retained. -/
theorem setIntegral_eq_sum_pair_fibers {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (g : α → ℝ) (hg : Integrable g μ) (T : Set α) :
    (∫ e in T, g e ∂μ) = ∑ b : β, ∫ e in T ∩ {e | f e = b}, g e ∂μ := by
  classical
  have hsum : g = fun e => ∑ b : β, ({e | f e = b} : Set α).indicator g e := by
    funext e
    simp [Set.indicator, eq_comm]
  calc
    (∫ e in T, g e ∂μ) =
        ∫ e in T, ∑ b : β, ({e | f e = b} : Set α).indicator g e ∂μ :=
      congrArg (fun h : α → ℝ => ∫ e in T, h e ∂μ) hsum
    _ = ∑ b : β, ∫ e in T, ({e | f e = b} : Set α).indicator g e ∂μ := by
      apply integral_finsetSum
      intro b _
      exact (hg.indicator ((measurableSet_singleton b).preimage hf)).integrableOn
    _ = _ := Finset.sum_congr rfl fun b _ =>
      setIntegral_indicator ((measurableSet_singleton b).preimage hf)

section FixedData

variable (p : Parameters) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate) (i : Follower p.m) (s : Fin (n_boot p))

/-- The accepted actual enabled/held event is the incoming prelaunch status
intersected with the original latent active/held pair. -/
theorem enabledHeldCell_eq_prelaunch_inter_pair (a : Fin p.K) :
    enabledHeldCell p ids rewards C_star C_h eta s i a =
      {e | GeneratedProductiveExitBudget.prelaunchUninformedIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s.val = 1} ∩
      {e | revealedPair p ids rewards C_star C_h eta i s e = (true, a)} := by
  ext e
  simp only [enabledHeldCell, Set.mem_ofPred_eq, Set.mem_inter_iff,
    blockAt_enabled_eq_revealedActivity, blockAt_held_eq_revealedHeld,
    GeneratedProductiveExitBudget.prelaunchUninformedIndicator]
  by_cases hv : (ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none ∧
    (ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val).activation i = none
  · simp [hv, Prod.ext_iff]
  · simp [hv]

/-- The productive indicator written using only the accepted incoming status,
latent pair, and deterministic support threshold. This is an equality with the
existing indicator, not a new definition of productivity. -/
theorem productiveIndicator_eq_reveal_formula (e : Coordinates p) :
    GeneratedBootstrapGainBudget.productiveIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s =
      if GeneratedProductiveExitBudget.prelaunchUninformedIndicator
          (referenceInput p ids rewards C_star C_h eta e) i s.val = 1 ∧
        (revealedPair p ids rewards C_star C_h eta i s e).1 = true ∧
        (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤
          GeneratedBlockChoiceAverages.blockSupportCount p s rewards
            (revealedPair p ids rewards C_star C_h eta i s e).2
      then 1 else 0 := by
  have hsupport (a : Fin p.K) :
      GeneratedBootstrapGainBudget.rewardSupportCountAt
        (referenceInput p ids rewards C_star C_h eta e) s a =
      GeneratedBlockChoiceAverages.blockSupportCount p s rewards a := by
    rw [GeneratedBlockActivationAverage.blockSupportCount_eq_rewardSupportCount]
    rfl
  rw [GeneratedBootstrapGainBudget.productiveIndicator,
    blockAt_enabled_eq_revealedActivity, blockAt_held_eq_revealedHeld, hsupport]
  change (if (if _ then _ else false) = true ∧
      (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤ _ then (1 : ℝ) else 0) = _
  unfold GeneratedProductiveExitBudget.prelaunchUninformedIndicator
  by_cases hv : (ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none ∧
    (ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val).activation i = none
  · simp only [hv, ite_true, and_true, true_and]
  · simp only [hv, ite_false, Bool.false_eq_true, false_and, zero_ne_one]

/-- The actual incoming status test is causal-boundary measurable. -/
theorem measurableSet_prelaunch :
    MeasurableSet[boundarySigma p s.val]
      {e | GeneratedProductiveExitBudget.prelaunchUninformedIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s.val = 1} :=
  (measurableSet_singleton (1 : ℝ)).preimage
    (GeneratedProductiveExitBudget.measurable_prelaunchUninformedIndicator
      p s.val s.isLt.le ids rewards C_star C_h eta i)

/-- Integrability of the productive opportunity under the unchanged original
law. The only bound used is its accepted zero-one property. -/
theorem integrable_productiveIndicator_originalLaw :
    Integrable (fun e : Coordinates p => GeneratedBootstrapGainBudget.productiveIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  have hm := GeneratedProductiveSuccessPrefixLaw.measurable_productiveIndicator
    p s ids rewards C_star C_h eta i
  refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun e => ?_)
  rcases GeneratedProductiveExitBudget.productiveIndicator_eq_zero_or_one
    (referenceInput p ids rewards C_star C_h eta e) i s with h | h <;>
    simp only [h, norm_zero, norm_one, zero_le_one, le_refl]

/-- Integral comparison on every test in the full accepted reveal sigma.
The only probabilistic producer is the accepted arbitrary causal-prefix law;
no arm support, run validity, localized estimate, or mean is an input. -/
theorem productive_setIntegral_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (T : Set (Coordinates p))
    (hT : MeasurableSet[revealSigma p ids rewards C_star C_h eta i s] T) :
    (∫ e in T, (1 / (16 * (p.K : ℝ))) *
      GeneratedBootstrapGainBudget.productiveIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s
      ∂GeneratedBootstrapRoundLaw.originalLaw p) ≤
    ∫ e in T, GeneratedProductiveExitBudget.productiveExitIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s
      ∂GeneratedBootstrapRoundLaw.originalLaw p := by
  classical
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let x := referenceInput p ids rewards C_star C_h eta
  let P : Coordinates p → ℝ := fun e => GeneratedBootstrapGainBudget.productiveIndicator (x e) i s
  let X : Coordinates p → ℝ := fun e => GeneratedProductiveExitBudget.productiveExitIndicator (x e) i s
  let f := revealedPair p ids rewards C_star C_h eta i s
  let V : Set (Coordinates p) :=
    {e | GeneratedProductiveExitBudget.prelaunchUninformedIndicator (x e) i s.val = 1}
  let c : ℝ := 1 / (16 * (p.K : ℝ))
  have hm : revealSigma p ids rewards C_star C_h eta i s ≤
      (inferInstance : MeasurableSpace (Coordinates p)) :=
    (revealSigma_le_nextBoundary p ids rewards C_star C_h eta i s).trans
      (boundaryFiltration_le_ambient p (s.val + 1))
  have hTambient := hm T hT
  have hf : Measurable f := measurable_revealedPair p ids rewards C_star C_h eta i s
  have hV : MeasurableSet[boundarySigma p s.val] V :=
    measurableSet_prelaunch p ids rewards C_star C_h eta i s
  have hVambient := boundaryFiltration_le_ambient p s.val V hV
  obtain ⟨A, hA, hslice⟩ := measurableSet_join_comap_fiber
    (boundarySigma p s.val) f T hT
  have hP : Integrable P μ :=
    integrable_productiveIndicator_originalLaw p ids rewards C_star C_h eta i s
  have hX : Integrable X μ :=
    integrable_productiveExitIndicator_originalLaw p ids rewards C_star C_h eta i s
  have hXnonneg (e : Coordinates p) : 0 ≤ X e :=
    (productiveExitIndicator_mem_Icc p ids rewards C_star C_h eta i s e).1
  have hfiber (b : Bool × Fin p.K) : MeasurableSet {e | f e = b} :=
    (measurableSet_singleton b).preimage hf
  have hlocal (b : Bool × Fin p.K) :
      (∫ e in T ∩ {e | f e = b}, c * P e ∂μ) ≤
      ∫ e in T ∩ {e | f e = b}, X e ∂μ := by
    let B := T ∩ {e | f e = b}
    have hB : MeasurableSet B := hTambient.inter (hfiber b)
    by_cases hb : b.1 = true ∧
        (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤
          GeneratedBlockChoiceAverages.blockSupportCount p s rewards b.2
    · let E := enabledHeldCell p ids rewards C_star C_h eta s i b.2
      have hbpair : (true, b.2) = b := Prod.ext hb.1.symm rfl
      have hE : E = V ∩ {e | f e = b} := by
        change enabledHeldCell p ids rewards C_star C_h eta s i b.2 = _
        rw [enabledHeldCell_eq_prelaunch_inter_pair p ids rewards C_star C_h eta i s,
          hbpair]
      have hBE : B ∩ V = A b ∩ E := by
        dsimp only [B]
        rw [hslice b, hE]
        ext e
        exact ⟨fun he => ⟨he.1.1, he.2, he.1.2⟩,
          fun he => ⟨⟨he.1, he.2.2⟩, he.2.1⟩⟩
      have hPformula : (∫ e in B, P e ∂μ) = μ.real (A b ∩ E) := by
        calc
          _ = ∫ e in B, V.indicator (fun _ => (1 : ℝ)) e ∂μ := by
            apply setIntegral_congr_fun hB
            intro e he
            change GeneratedBootstrapGainBudget.productiveIndicator (x e) i s = _
            rw [productiveIndicator_eq_reveal_formula p ids rewards C_star C_h eta i s e]
            have hfe : revealedPair p ids rewards C_star C_h eta i s e = b := he.2
            simp only [hfe, hb.1, hb.2, and_self, and_true]
            rfl
          _ = ∫ _ in B ∩ V, (1 : ℝ) ∂μ := setIntegral_indicator hVambient
          _ = _ := by rw [hBE, setIntegral_const]; simp only [smul_eq_mul, mul_one]
      let G := A b ∩ E ∩ {e | X e = 1}
      have hG : MeasurableSet G :=
        (GeneratedProductiveSuccessPrefixLaw.measurableSet_productiveExit_intersections
          p s ids rewards C_star C_h eta i b.2 (A b) (hA b)).2.2.2
      have hGB : G ⊆ B := by
        intro e he
        have heE : e ∈ V ∩ {e | f e = b} := by rw [← hE]; exact he.1.2
        change e ∈ T ∩ {e | f e = b}
        rw [hslice b]
        exact ⟨he.1.1, heE.2⟩
      have hGmass : μ.real G ≤ ∫ e in B, X e ∂μ := by
        calc
          μ.real G = ∫ e in B, G.indicator (fun _ => (1 : ℝ)) e ∂μ := by
            rw [setIntegral_indicator hG, Set.inter_eq_right.mpr hGB, setIntegral_const]
            simp only [smul_eq_mul, mul_one]
          _ ≤ _ := by
            apply setIntegral_mono_on ((integrable_const (1 : ℝ)).indicator hG).integrableOn
              hX.integrableOn hB
            intro e _
            by_cases he : e ∈ G
            · rw [Set.indicator_of_mem he, he.2]
            · rw [Set.indicator_of_notMem he]
              exact hXnonneg e
      calc
        (∫ e in B, c * P e ∂μ) = c * μ.real (A b ∩ E) := by
          rw [integral_const_mul, hPformula]
        _ ≤ μ.real G := GeneratedProductiveSuccessPrefixLaw.productive_success_on_causalPrefix
          p ids hgood rewards C_star C_h eta hC_h s i b.2 hb.2 (A b) (hA b)
        _ ≤ _ := hGmass
    · have hzero : (∫ e in B, c * P e ∂μ) = 0 := by
        calc
          _ = ∫ _ in B, (0 : ℝ) ∂μ := by
            apply setIntegral_congr_fun hB
            intro e he
            change c * GeneratedBootstrapGainBudget.productiveIndicator (x e) i s = 0
            rw [productiveIndicator_eq_reveal_formula p ids rewards C_star C_h eta i s e]
            have hfe : revealedPair p ids rewards C_star C_h eta i s e = b := he.2
            simp only [hfe, hb, and_false, ite_false, mul_zero]
          _ = 0 := integral_zero _ _
      rw [hzero]
      exact integral_nonneg hXnonneg
  rw [setIntegral_eq_sum_pair_fibers μ f hf (fun e => c * P e) (hP.const_mul c) T,
    setIntegral_eq_sum_pair_fibers μ f hf X hX T]
  exact Finset.sum_le_sum fun b _ => hlocal b

/-- The actual productive-exit conditional lower mean on the full accepted
raw held-arm reveal join. Good IDs and the numerical support-scale regime
are the only substantive hypotheses beyond the typed fixed data. -/
theorem productive_condExp_ge
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) :
    (fun e : Coordinates p => (1 / (16 * (p.K : ℝ))) *
      GeneratedBootstrapGainBudget.productiveIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s) ≤ᵐ[
          GeneratedBootstrapRoundLaw.originalLaw p]
    (GeneratedBootstrapRoundLaw.originalLaw p)[
      (fun e : Coordinates p => GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s) |
      revealSigma p ids rewards C_star C_h eta i s] := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let L : Coordinates p → ℝ := fun e => (1 / (16 * (p.K : ℝ))) *
    GeneratedBootstrapGainBudget.productiveIndicator
      (referenceInput p ids rewards C_star C_h eta e) i s
  let X : Coordinates p → ℝ := fun e => GeneratedProductiveExitBudget.productiveExitIndicator
    (referenceInput p ids rewards C_star C_h eta e) i s
  have hm : revealSigma p ids rewards C_star C_h eta i s ≤
      (inferInstance : MeasurableSpace (Coordinates p)) :=
    (revealSigma_le_nextBoundary p ids rewards C_star C_h eta i s).trans
      (boundaryFiltration_le_ambient p (s.val + 1))
  have hL : StronglyMeasurable[revealSigma p ids rewards C_star C_h eta i s] L :=
    ((GeneratedHeldArmRevealFiltration.measurable_productiveIndicator
      p ids rewards C_star C_h eta i s).const_mul _).stronglyMeasurable
  have hLint : Integrable L μ :=
    (integrable_productiveIndicator_originalLaw p ids rewards C_star C_h eta i s).const_mul _
  have hXint : Integrable X μ :=
    integrable_productiveExitIndicator_originalLaw p ids rewards C_star C_h eta i s
  have hCE : StronglyMeasurable[revealSigma p ids rewards C_star C_h eta i s]
      (μ[X | revealSigma p ids rewards C_star C_h eta i s]) := stronglyMeasurable_condExp
  have hCEint : Integrable (μ[X | revealSigma p ids rewards C_star C_h eta i s]) μ :=
    integrable_condExp
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le (Integrable.trim hm hLint hL)
    (Integrable.trim hm hCEint hCE)
  intro T hT _
  rw [← setIntegral_trim hm hL hT, ← setIntegral_trim hm hCE hT,
    setIntegral_condExp hm hXint hT]
  exact productive_setIntegral_le p ids rewards C_star C_h eta i s hgood hC_h T hT

end FixedData

section Process

variable (p : Parameters) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : LearningRate) (i : Follower p.m)

/-- Exact source-index shift of the accepted productive exit. At time `s+1`
this is the literal block-`s` exit, and it is zero at zero and beyond `n_boot`.
Only the index is extended; the run, exit, and history are unchanged. -/
def productiveExitProcess : ℕ → Coordinates p → ℝ
  | 0, _ => 0
  | r + 1, e => if hr : r < n_boot p then
      GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i ⟨r, hr⟩
    else 0

/-- Opportunity alignment with the literal accepted exit, including the final
clipped block and a first launch-crossing block. -/
theorem productiveExitProcess_at_opportunity (s : Fin (n_boot p)) (e : Coordinates p) :
    productiveExitProcess p ids rewards C_star C_h eta i (s.val + 1) e =
      GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s := by
  simp only [productiveExitProcess, dite_eq_left s.isLt]

theorem productiveExitProcess_zero (e : Coordinates p) :
    productiveExitProcess p ids rewards C_star C_h eta i 0 e = 0 := rfl

theorem productiveExitProcess_eq_zero_of_horizon_lt (t : ℕ) (ht : n_boot p < t)
    (e : Coordinates p) :
    productiveExitProcess p ids rewards C_star C_h eta i t e = 0 := by
  cases t with
  | zero => rfl
  | succ r =>
      have hr : ¬ r < n_boot p := by omega
      simp only [productiveExitProcess, dite_eq_right hr]

/-- Strong adaptedness uses the existing accepted held-arm reveal filtration,
with the accepted successor measurability at each genuine opportunity. -/
theorem stronglyAdapted_productiveExitProcess :
    StronglyAdapted (heldArmRevealFiltration p ids rewards C_star C_h eta i)
      (productiveExitProcess p ids rewards C_star C_h eta i) := by
  intro t
  cases t with
  | zero => exact stronglyMeasurable_const
  | succ r =>
      change StronglyMeasurable[heldArmRevealFiltration p ids rewards C_star C_h eta i (r + 1)]
        (fun e => if hr : r < n_boot p then
          GeneratedProductiveExitBudget.productiveExitIndicator
            (referenceInput p ids rewards C_star C_h eta e) i ⟨r, hr⟩ else 0)
      by_cases hr : r < n_boot p
      · simp only [dite_eq_left hr]
        exact (measurable_productiveExitIndicator_at_heldArmRevealFiltration_succ
          p ids rewards C_star C_h eta i ⟨r, hr⟩).stronglyMeasurable
      · simp only [dite_eq_right hr]
        exact stronglyMeasurable_const

/-- The shifted process takes values in the unit interval everywhere. -/
theorem productiveExitProcess_mem_Icc (t : ℕ) (e : Coordinates p) :
    productiveExitProcess p ids rewards C_star C_h eta i t e ∈ Set.Icc 0 1 := by
  cases t with
  | zero => exact ⟨le_rfl, zero_le_one⟩
  | succ r =>
      by_cases hr : r < n_boot p
      · simp only [productiveExitProcess, dite_eq_left hr]
        exact productiveExitIndicator_mem_Icc p ids rewards C_star C_h eta i ⟨r, hr⟩ e
      · simp only [productiveExitProcess, dite_eq_right hr]
        exact ⟨le_rfl, zero_le_one⟩

/-- Integrability is inherited from the accepted actual block exit at every
nonzero in-horizon time. -/
theorem integrable_productiveExitProcess (t : ℕ) :
    Integrable (productiveExitProcess p ids rewards C_star C_h eta i t)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  cases t with
  | zero => exact integrable_zero (Coordinates p) ℝ _
  | succ r =>
      change Integrable (fun e => if hr : r < n_boot p then
        GeneratedProductiveExitBudget.productiveExitIndicator
          (referenceInput p ids rewards C_star C_h eta e) i ⟨r, hr⟩ else 0)
        (GeneratedBootstrapRoundLaw.originalLaw p)
      by_cases hr : r < n_boot p
      · simp only [dite_eq_left hr]
        exact integrable_productiveExitIndicator_originalLaw p ids rewards C_star C_h eta i ⟨r, hr⟩
      · simp only [dite_eq_right hr]
        exact integrable_zero (Coordinates p) ℝ _

/-- The source-indexed prefix, including its zero initial value, is exactly
the finite sum of actual block exits. -/
theorem productiveExitProcess_prefix_sum (r : ℕ) (hr : r ≤ n_boot p)
    (e : Coordinates p) :
    (∑ t ∈ Finset.range (r + 1), productiveExitProcess p ids rewards C_star C_h eta i t e) =
      ∑ s : Fin r, GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i ⟨s.val, s.isLt.trans_le hr⟩ := by
  rw [Finset.sum_range_succ']
  simp only [productiveExitProcess_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro s _
  exact productiveExitProcess_at_opportunity p ids rewards C_star C_h eta i
    ⟨s.val, s.isLt.trans_le hr⟩ e

/-- The accepted one-exit budget is retained for the source-shifted prefix. -/
theorem productiveExitProcess_prefix_sum_le_one (r : ℕ) (hr : r ≤ n_boot p)
    (e : Coordinates p) :
    (∑ t ∈ Finset.range (r + 1), productiveExitProcess p ids rewards C_star C_h eta i t e) ≤ 1 := by
  rw [productiveExitProcess_prefix_sum p ids rewards C_star C_h eta i r hr e]
  exact productiveExitIndicator_sum_le_one_originalCoordinates
    p ids rewards C_star C_h eta i r hr e

/-- The shifted process has the required mean at the prior index `s.val` of
the SAME existing held-arm reveal filtration. -/
theorem productiveExitProcess_condExp_ge_at_opportunity
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (s : Fin (n_boot p)) :
    (fun e : Coordinates p => (1 / (16 * (p.K : ℝ))) *
      GeneratedBootstrapGainBudget.productiveIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s) ≤ᵐ[
          GeneratedBootstrapRoundLaw.originalLaw p]
    (GeneratedBootstrapRoundLaw.originalLaw p)[
      productiveExitProcess p ids rewards C_star C_h eta i (s.val + 1) |
      heldArmRevealFiltration p ids rewards C_star C_h eta i s.val] := by
  have hprocess : productiveExitProcess p ids rewards C_star C_h eta i (s.val + 1) =
      fun e => GeneratedProductiveExitBudget.productiveExitIndicator
        (referenceInput p ids rewards C_star C_h eta e) i s := by
    funext e
    exact productiveExitProcess_at_opportunity p ids rewards C_star C_h eta i s e
  rw [hprocess, heldArmRevealFiltration_at_block p ids rewards C_star C_h eta i s]
  exact productive_condExp_ge p ids rewards C_star C_h eta i s hgood hC_h

end Process

end Bandits.Support.GeneratedProductiveSuccessMean

end
