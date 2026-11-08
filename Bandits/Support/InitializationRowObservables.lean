/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationIndexMixture
public import Bandits.Support.SelectedIndexLaunchJointLaw
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Concrete initialization row observables

For a fixed denominator-`D` reward matrix and an `m`-arm comparator, this
module measures the literal comparator reward before the accepted reference
launch and the accepted reference initialization-failure flag. The observables
are built from `ReferenceInitializationIndexMixture.fixedRowInput` and its
existing whole-family `actualOutput`; neither histories nor stopping data are
inputs.

Sources: `sources/zip4/manuscript/08_main_theorem.tex:26-48,67-83` and
`sources/zip4/manuscript/07_public_setup.tex:63-113`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationIndexMixture
open Bandits.Support.SelectedIndexLaunchJointLaw
open scoped BigOperators ENNReal

namespace Bandits.Support.InitializationRowObservables

abbrev Parameters := ConstructorDimensions.Parameters
abbrev PrivateCoordinates (p : Parameters) :=
  BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p

private theorem measurable_of_finite_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Finite β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hkey : Measurable key)
    (branch : β → α → γ) (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

private theorem integrable_bounded_probability
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

private theorem norm_le_of_nonneg_mem_Icc {x C : ℝ} (hC : 0 ≤ C)
    (hx : x ∈ Set.Icc 0 C) : ‖x‖ ≤ C := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hx.1, hC], hx.2⟩
/-- Launch endpoint read from the terminal boundary, with the `T+1` sentinel. -/
def launchRoundAtBoundary (p : Parameters) (b : Boundary p) : ℕ :=
  if b.crossing.isSome then elapsed p b.completed + 1 else p.T + 1
/-- Literal denominator-`D` comparator charge before the launch endpoint. -/
def comparatorChargeAtBoundary (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (S : Finset (Fin p.K)) (b : Boundary p) : ℝ :=
  ∑ t : Fin p.T, ∑ a ∈ S,
    if t.val + 1 < launchRoundAtBoundary p b then
      ((rewards t a).val : ℝ) / (D p : ℝ)
    else 0
/-- Exact strict-prefix expansion. Sources: `sources/zip4/manuscript/appendix_b_communication.tex:737-765`
and `sources/zip4/manuscript/07_public_setup.tex:106-140`. -/
theorem comparatorChargeAtBoundary_eq_sum (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K))
    (b : Boundary p) :
    comparatorChargeAtBoundary p rewards S b =
      ∑ t : Fin p.T, ∑ a ∈ S,
        if t.val + 1 < launchRoundAtBoundary p b then
          ((rewards t a).val : ℝ) / (D p : ℝ) else 0 := by
  unfold comparatorChargeAtBoundary; rfl
/-- The parsed ordinary-DOWN cause paired with the forced-failure bit. -/
def initializationFailureCauseAtBoundary (p : Parameters)
    (row : CompleteRow p) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (i : ActiveRoundActions.Follower p.m) : Prop :=
  b.forcedFailure i = true ∨
    ∃ a, b.activation i = some a ∧
      ∃ d ∈ ReferencePrelaunchFollower.decisions
          (BootstrapPhysicalInput.sourceFollowerIndex p i) row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (elapsed_le_T p b.completed)
          (List.ofFn (fun u : Fin (elapsed p b.completed) => u))
          (ReferencePrelaunchFollower.initial p eta),
        OrdinaryMessageCodec.acceptDown
          (ReferencePrelaunchFollower.codecParams p eta) 0 (d.1.val + 1) d.2
/-- The initialization flag read from the terminal boundary's accepted causes. -/
def initializationFailureAtBoundary (p : Parameters)
    (row : CompleteRow p) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) : Prop :=
  ∃ i : ActiveRoundActions.Follower p.m,
    initializationFailureCauseAtBoundary p row eta b i
/-- Real indicator of the boundary initialization flag. -/
def initializationFailureAtBoundaryIndicator (p : Parameters)
    (row : CompleteRow p) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) : ℝ := by
  classical
  exact if initializationFailureAtBoundary p row eta b then 1 else 0
/-- Fixed-row comparator cost from the existing accepted input and output. -/
def initializationComparatorCharge (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (row : CompleteRow p) (e : PrivateCoordinates p) : ℝ :=
  comparatorChargeAtBoundary p rewards S
    (ReferenceInitializationRun.output
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e))
/-- Exact fixed-row equation. Sources: `appendix_b_communication.tex:737-765`,
`07_public_setup.tex:106-140`, and `08_main_theorem.tex:78-83`. -/
theorem initializationComparatorCharge_eq_comparatorChargeAtBoundary
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (row : CompleteRow p) (e : PrivateCoordinates p) :
    initializationComparatorCharge p ids rewards C_star C_h eta S row e =
      comparatorChargeAtBoundary p rewards S (ReferenceInitializationRun.output
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)) := by
  unfold initializationComparatorCharge
  rfl
/-- The literal fixed-row initialization-flag event, before any endpoint
identification with the manuscript's `E_init`. -/
def initializationFailureEvent (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) : Set (PrivateCoordinates p) :=
  {e | ∃ i : ActiveRoundActions.Follower p.m,
    ReferenceInitializationRun.initializationFailure
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)
      (ReferenceInitializationRun.output
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e))
      i = true}
/-- The real indicator of the concrete fixed-row initialization flag event. -/
def initializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) : ℝ := by
  classical
  exact if e ∈ initializationFailureEvent p ids rewards C_star C_h eta row then 1 else 0
/-- The actual fixed-family charge uses the original coordinator scalar and the
accepted `actualOutput`, which selects exactly `rows (coordinatorIndex …)`. -/
def actualInitializationComparatorCharge (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (rows : CompleteRows p) (e : PrivateCoordinates p) : ℝ :=
  comparatorChargeAtBoundary p rewards S
    (ReferenceInitializationIndexMixture.actualOutput p ids rewards C_star C_h eta rows e)
/-- Actual fixed-family initialization flag event, formed from the same
selected `fixedRowInput` and its actual output. -/
def actualInitializationFailureEvent (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) : Set (PrivateCoordinates p) :=
  {e | ∃ i : ActiveRoundActions.Follower p.m,
    let x := ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
      (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e
    ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i = true}
/-- The real indicator of the actual fixed-family initialization flag. -/
def actualInitializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) (e : PrivateCoordinates p) : ℝ := by
  classical
  exact if e ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta rows then 1 else 0
/-- Per-row private integral of the literal prelaunch comparator charge. -/
def c_S (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (row : CompleteRow p) : ℝ :=
  ∫ e, initializationComparatorCharge p ids rewards C_star C_h eta S row e
    ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
/-- Per-row private mass of the actual initialization-failure flag. -/
def e_initFlag (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) : ℝ :=
  ∫ e, initializationFailureIndicator p ids rewards C_star C_h eta row e
    ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
/-- Combined concrete initialization row observable. -/
def g_init (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (row : CompleteRow p) : ℝ :=
  c_S p ids rewards C_star C_h eta S row +
    2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row
/-- Exact component equation for `g_init`; see the row-cost decomposition in
`sources/zip4/manuscript/08_main_theorem.tex:26-64`. -/
theorem g_init_eq_components (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (row : CompleteRow p) :
    g_init p ids rewards C_star C_h eta S row = c_S p ids rewards C_star C_h eta S row +
      2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row := by
  unfold g_init
  rfl
/-- The actual selected-family combined observable. -/
def actualGInit (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (rows : CompleteRows p) (e : PrivateCoordinates p) : ℝ :=
  actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e +
    2 * ((p.m : ℝ) * (p.T : ℝ)) *
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
/-! ### Source provenance and elementary pointwise bounds -/
/-- Accepted `fixedRowInput` provenance includes the parsed accepted-start-zero DOWN decision. -/
theorem initializationFailure_iff_accepted_causes (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) (b : Boundary p)
    (i : ActiveRoundActions.Follower p.m) :
    ReferenceInitializationRun.initializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)
        b i = true ↔ initializationFailureCauseAtBoundary p row eta b i := by
  have h := ReferenceInitializationRun.initializationFailure_provenance
    (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e) b i
  constructor
  · intro hfail
    rcases h.mp hfail with hforced | ⟨a, ha, d, hd, hdown⟩
    · exact Or.inl hforced
    · exact Or.inr ⟨a, ha, d, hd, hdown⟩
  · intro hc
    rcases hc with hforced | ⟨a, ha, d, hd, hdown⟩
    · exact h.mpr (Or.inl hforced)
    · exact h.mpr (Or.inr ⟨a, ha, d, hd, hdown⟩)
/-- The fixed-row event matches accepted boundary causes, including forced and suppressed DOWN failures. -/
theorem initializationFailureEvent_iff_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) :
    e ∈ initializationFailureEvent p ids rewards C_star C_h eta row ↔
      initializationFailureAtBoundary p row eta
        (ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput
            p ids rewards C_star C_h eta row e)) := by
  simp only [initializationFailureEvent, Set.mem_ofPred_eq,
    initializationFailureAtBoundary]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (initializationFailure_iff_accepted_causes p ids rewards C_star C_h eta
      row e _ i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (initializationFailure_iff_accepted_causes p ids rewards C_star C_h eta
      row e _ i).mpr hi⟩
/-- The flag equals its boundary cause; invariance checks parsed replay and terminal boundary. -/
theorem initializationFailureIndicator_eq_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) :
    initializationFailureIndicator p ids rewards C_star C_h eta row e =
      initializationFailureAtBoundaryIndicator p row eta
        (ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput
            p ids rewards C_star C_h eta row e)) := by
  by_cases h : e ∈ initializationFailureEvent p ids rewards C_star C_h eta row
  · have hb := (initializationFailureEvent_iff_boundary
      p ids rewards C_star C_h eta row e).mp h
    simp [initializationFailureIndicator, initializationFailureAtBoundaryIndicator, h, hb]
  · have hb : ¬ initializationFailureAtBoundary p row eta
        (ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput
            p ids rewards C_star C_h eta row e)) := by
      intro h'
      exact h ((initializationFailureEvent_iff_boundary
        p ids rewards C_star C_h eta row e).mpr h')
    simp [initializationFailureIndicator, initializationFailureAtBoundaryIndicator, h, hb]
/-- The original reference launch endpoint really is the boundary endpoint;
in particular its accepted `T+1` sentinel is unchanged. -/
theorem launchRound_output_boundary (p : Parameters)
    (x : ReferenceInitializationRun.Input p) :
    ReferenceInitializationRun.launchRound x =
      launchRoundAtBoundary p (ReferenceInitializationRun.output x) := by
  unfold launchRoundAtBoundary ReferenceInitializationRun.launchRound
  rfl
/-- The literal cost is nonnegative and at most one unit per comparator arm and
source round. -/
theorem comparatorChargeAtBoundary_bounds (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (S : Finset (Fin p.K)) (hS : S.card = p.m) (b : Boundary p) :
    comparatorChargeAtBoundary p rewards S b ∈
      Set.Icc 0 ((p.m : ℝ) * (p.T : ℝ)) := by
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hreward : ∀ t a,
      0 ≤ ((rewards t a).val : ℝ) / (D p : ℝ) ∧
        ((rewards t a).val : ℝ) / (D p : ℝ) ≤ 1 := by
    intro t a
    have hval : (rewards t a).val ≤ D p := by omega
    have hval' : ((rewards t a).val : ℝ) ≤ (D p : ℝ) := by exact_mod_cast hval
    exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hD), (div_le_one hD).2 hval'⟩
  constructor
  · unfold comparatorChargeAtBoundary
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro a ha
    split_ifs with h
    · exact (hreward t a).1
    · exact le_of_eq rfl
  · unfold comparatorChargeAtBoundary
    calc
      (∑ t : Fin p.T, ∑ a ∈ S,
          if t.val + 1 < launchRoundAtBoundary p b then
            ((rewards t a).val : ℝ) / (D p : ℝ) else 0)
          ≤ ∑ t : Fin p.T, ∑ a ∈ S, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            apply Finset.sum_le_sum
            intro a ha
            by_cases h : t.val + 1 < launchRoundAtBoundary p b
            · simp only [h, ↓reduceIte]
              exact (hreward t a).2
            · simp only [h, ↓reduceIte]
              norm_num
      _ = (p.T : ℝ) * (S.card : ℝ) := by simp
      _ = (p.m : ℝ) * (p.T : ℝ) := by rw [hS]; ring
/-- Pointwise bounds for the fixed-row concrete cost, with no startup-success
or good-ID assumption. -/
theorem initializationComparatorCharge_bounds (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) (row : CompleteRow p)
    (e : PrivateCoordinates p) :
    initializationComparatorCharge p ids rewards C_star C_h eta S row e ∈
      Set.Icc 0 ((p.m : ℝ) * (p.T : ℝ)) :=
  comparatorChargeAtBoundary_bounds p rewards S hS
    (ReferenceInitializationRun.output
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e))
/-- The fixed-row failure indicator always lies in the unit interval. -/
theorem initializationFailureIndicator_bounds (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) :
    initializationFailureIndicator p ids rewards C_star C_h eta row e ∈ Set.Icc 0 1 := by
  unfold initializationFailureIndicator
  split_ifs <;> norm_num
/-- The actual selected-family cost has the same elementary bound. -/
theorem actualInitializationComparatorCharge_bounds (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) (rows : CompleteRows p)
    (e : PrivateCoordinates p) :
    actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e ∈
      Set.Icc 0 ((p.m : ℝ) * (p.T : ℝ)) :=
  comparatorChargeAtBoundary_bounds p rewards S hS
    (ReferenceInitializationIndexMixture.actualOutput p ids rewards C_star C_h eta rows e)
/-- The actual selected-family flag indicator lies in `[0,1]`. -/
theorem actualInitializationFailureIndicator_bounds (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) (e : PrivateCoordinates p) :
    actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e ∈ Set.Icc 0 1 := by
  unfold actualInitializationFailureIndicator
  split_ifs <;> norm_num
/-! ### Measurability and scalar invariance -/
/-- Every real test of an initialization boundary is measurable on its accepted
countable boundary carrier. -/
theorem measurable_comparatorChargeAtBoundary (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K)) :
    Measurable (comparatorChargeAtBoundary p rewards S) :=
  measurable_of_countable _

theorem measurable_initializationFailureAtBoundaryIndicator (p : Parameters)
    (row : CompleteRow p) (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (initializationFailureAtBoundaryIndicator p row eta) :=
  measurable_of_countable _
/-- Joint measurability of the fixed-row comparator observable on the original
`CompleteRow × ExtendedPrivateCoordinates` carrier. -/
theorem measurable_initializationComparatorCharge_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) :
    Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      initializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2) := by
  exact (measurable_comparatorChargeAtBoundary p rewards S).comp
    (ReferenceInitializationIndexMixture.measurable_fixedRowOutput_pair
      p ids rewards C_star C_h eta)
/-- Measurability of the fixed-row failure event follows from the accepted
actual-output measurability for every genuine follower and a finite existential
union. -/
theorem measurable_initializationFailureEvent_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet {z : CompleteRow p × PrivateCoordinates p |
      z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1} := by
  have hinput : Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      (ids, (z.1, z.2))) := measurable_const.prodMk measurable_id
  have hfail : ∀ i : ActiveRoundActions.Follower p.m,
      Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
        ReferenceInitializationRun.initializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput
            p ids rewards C_star C_h eta z.1 z.2)
          (ReferenceInitializationRun.output
            (ReferenceInitializationIndexMixture.fixedRowInput
              p ids rewards C_star C_h eta z.1 z.2)) i) := by
    intro i
    change Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      ReferenceInitializationRun.initializationFailure
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, (z.1, z.2)))
        (ReferenceInitializationRun.output
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, (z.1, z.2)))) i)
    exact (ReferenceInitializationMeasurability.measurable_output_initializationFailure
      p C_star C_h eta rewards i).comp hinput
  have hset : {z : CompleteRow p × PrivateCoordinates p |
      z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1} =
      ⋃ i : ActiveRoundActions.Follower p.m,
        {z : CompleteRow p × PrivateCoordinates p |
          ReferenceInitializationRun.initializationFailure
            (ReferenceInitializationIndexMixture.fixedRowInput
              p ids rewards C_star C_h eta z.1 z.2)
            (ReferenceInitializationRun.output
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta z.1 z.2)) i = true} := by
    ext z
    simp [initializationFailureEvent]
  rw [hset]
  exact MeasurableSet.iUnion fun i => hfail i (measurableSet_singleton true)
/-- Joint measurability of the fixed-row flag indicator. -/
theorem measurable_initializationFailureIndicator_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      initializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2) := by
  have hevent := measurable_initializationFailureEvent_pair p ids rewards C_star C_h eta
  change Measurable ({z : CompleteRow p × PrivateCoordinates p |
    z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1}.indicator
      (fun _ => (1 : ℝ)))
  exact measurable_const.indicator hevent
/-- A fixed private section of the fixed-row failure event is measurable. -/
theorem measurable_initializationFailureEvent (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) :
    MeasurableSet (initializationFailureEvent p ids rewards C_star C_h eta row) := by
  have h := measurable_initializationFailureEvent_pair p ids rewards C_star C_h eta
  have hrow : Measurable (fun e : PrivateCoordinates p => (row, e)) :=
    measurable_const.prodMk measurable_id
  simpa using h.preimage hrow
/-- The concrete fixed-row indicator is measurable on its original private
coordinates. -/
theorem measurable_initializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) :
    Measurable (initializationFailureIndicator p ids rewards C_star C_h eta row) := by
  change Measurable ((initializationFailureEvent p ids rewards C_star C_h eta row).indicator
    (fun _ : PrivateCoordinates p => (1 : ℝ)))
  exact measurable_const.indicator
    (measurable_initializationFailureEvent p ids rewards C_star C_h eta row)
/-- The fixed-row cost is pointwise invariant when only the original
coordinator scalar changes. The accepted causal run comparison keeps the row,
IDs, block triples, targets and player-round scalars fixed. -/
theorem initializationComparatorCharge_scalar_invariant (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (row : CompleteRow p)
    (e : PrivateCoordinates p) (s : ContinuousCategorical.Scalar) :
    initializationComparatorCharge p ids rewards C_star C_h eta S row
        (ReferenceInitializationIndexMixture.withCoordinatorScalar e s) =
      initializationComparatorCharge p ids rewards C_star C_h eta S row e := by
  unfold initializationComparatorCharge
  exact congrArg (comparatorChargeAtBoundary p rewards S)
    (ReferenceInitializationIndexMixture.fixedRow_output_eq_of_coordinatorScalar_change
      p ids rewards C_star C_h eta row e s)
/-- The concrete flag is pointwise invariant under changing only the original
coordinator scalar. This uses the accepted forced/ordinary-replay provenance,
not an assumed scalar-independent event. -/
theorem initializationFailureIndicator_scalar_invariant (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p)
    (s : ContinuousCategorical.Scalar) :
    initializationFailureIndicator p ids rewards C_star C_h eta row
        (ReferenceInitializationIndexMixture.withCoordinatorScalar e s) =
      initializationFailureIndicator p ids rewards C_star C_h eta row e := by
  rw [initializationFailureIndicator_eq_boundary p ids rewards C_star C_h eta row
        (ReferenceInitializationIndexMixture.withCoordinatorScalar e s),
      initializationFailureIndicator_eq_boundary p ids rewards C_star C_h eta row e]
  rw [ReferenceInitializationIndexMixture.fixedRow_output_eq_of_coordinatorScalar_change
    p ids rewards C_star C_h eta row e s]
/-- On the actual selected-index atom, the literal flag is precisely the
accepted provenance event computed from the selected output boundary. -/
theorem actualInitializationFailureEvent_iff_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) (e : PrivateCoordinates p) :
    e ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta rows ↔
      initializationFailureAtBoundary p
        (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) eta
        (ReferenceInitializationIndexMixture.actualOutput p ids rewards C_star C_h eta rows e) := by
  change (∃ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
          (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)
        (ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)) i = true) ↔
    ∃ i : ActiveRoundActions.Follower p.m,
      initializationFailureCauseAtBoundary p
        (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) eta
        (ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)) i
  exact exists_congr fun i => initializationFailure_iff_accepted_causes
    p ids rewards C_star C_h eta (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e
    (ReferenceInitializationRun.output
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
        (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)) i
/-- The actual fixed-family comparator observable is measurable on the
original extended private coordinates, retaining the scalar that selects `J`.
-/
theorem measurable_actualInitializationComparatorCharge (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (rows : CompleteRows p) :
    Measurable (actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows) :=
  (measurable_comparatorChargeAtBoundary p rewards S).comp
    (ReferenceInitializationIndexMixture.measurable_actualOutput
      p ids rewards C_star C_h eta rows)
/-- Joint measurability of the actual fixed-family flag event over a complete
row family and the original private point. -/
theorem measurable_actualInitializationFailureEvent_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    MeasurableSet {z : CompleteRows p × PrivateCoordinates p |
      z.2 ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta z.1} := by
  have hJ : Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p z.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrow : Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      z.1 (PrivateSourceStreams.coordinatorIndex p z.2.1.2)) :=
    measurable_of_finite_cases _ hJ (fun j z => z.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
  have hinput : Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      (ids, (z.1 (PrivateSourceStreams.coordinatorIndex p z.2.1.2), z.2))) :=
    measurable_const.prodMk (hrow.prodMk measurable_snd)
  have hfail : ∀ i : ActiveRoundActions.Follower p.m,
      Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
        let x := ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
          (z.1 (PrivateSourceStreams.coordinatorIndex p z.2.1.2)) z.2
        ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i) := by
    intro i
    change Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, (z.1 (PrivateSourceStreams.coordinatorIndex p z.2.1.2), z.2))
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i)
    exact (ReferenceInitializationMeasurability.measurable_output_initializationFailure
      p C_star C_h eta rewards i).comp hinput
  have hset : {z : CompleteRows p × PrivateCoordinates p |
      z.2 ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta z.1} =
      ⋃ i : ActiveRoundActions.Follower p.m,
        {z : CompleteRows p × PrivateCoordinates p |
          let x := ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (z.1 (PrivateSourceStreams.coordinatorIndex p z.2.1.2)) z.2
          ReferenceInitializationRun.initializationFailure x
            (ReferenceInitializationRun.output x) i = true} := by
    ext z
    simp [actualInitializationFailureEvent]
  rw [hset]
  exact MeasurableSet.iUnion fun i => hfail i (measurableSet_singleton true)
/-- The actual fixed-family flag event is measurable on its original private
coordinates for every fixed numerical complete-row family. -/
theorem measurable_actualInitializationFailureEvent (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) :
    MeasurableSet (actualInitializationFailureEvent p ids rewards C_star C_h eta rows) := by
  have h := measurable_actualInitializationFailureEvent_pair p ids rewards C_star C_h eta
  have hrows : Measurable (fun e : PrivateCoordinates p => (rows, e)) :=
    measurable_const.prodMk measurable_id
  simpa using h.preimage hrows
/-- Joint measurability of the actual selected-family flag indicator. -/
theorem measurable_actualInitializationFailureIndicator_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2) := by
  have hevent := measurable_actualInitializationFailureEvent_pair p ids rewards C_star C_h eta
  change Measurable ({z : CompleteRows p × PrivateCoordinates p |
    z.2 ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta z.1}.indicator
      (fun _ => (1 : ℝ)))
  exact measurable_const.indicator hevent
/-- The actual fixed-family flag indicator is measurable on its original
private coordinates. -/
theorem measurable_actualInitializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) :
    Measurable (actualInitializationFailureIndicator p ids rewards C_star C_h eta rows) := by
  change Measurable ((actualInitializationFailureEvent p ids rewards C_star C_h eta rows).indicator
    (fun _ : PrivateCoordinates p => (1 : ℝ)))
  exact measurable_const.indicator
    (measurable_actualInitializationFailureEvent p ids rewards C_star C_h eta rows)
/-- The actual selected-family failure indicator is a boundary cause test for
the selected row and actual output. -/
theorem actualInitializationFailureIndicator_eq_boundary (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) (e : PrivateCoordinates p) :
    actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e =
      initializationFailureAtBoundaryIndicator p
        (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) eta
        (ReferenceInitializationIndexMixture.actualOutput p ids rewards C_star C_h eta rows e) := by
  unfold actualInitializationFailureIndicator initializationFailureAtBoundaryIndicator
  rw [actualInitializationFailureEvent_iff_boundary p ids rewards C_star C_h eta rows e]
/-- The selected-family combined observable is pointwise in `[0,3mT]`. -/
theorem actualGInit_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) (rows : CompleteRows p) (e : PrivateCoordinates p) :
    actualGInit p ids rewards C_star C_h eta S rows e ∈
      Set.Icc 0 (3 * ((p.m : ℝ) * (p.T : ℝ))) := by
  have hc := actualInitializationComparatorCharge_bounds
    p ids rewards C_star C_h eta S hS rows e
  have he := actualInitializationFailureIndicator_bounds p ids rewards C_star C_h eta rows e
  have hmT : 0 ≤ (p.m : ℝ) * (p.T : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ 2 * ((p.m : ℝ) * (p.T : ℝ)) := mul_nonneg (by norm_num) hmT
  have hprod : 0 ≤ 2 * ((p.m : ℝ) * (p.T : ℝ)) *
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e :=
    mul_nonneg hcoef he.1
  have hprod' : 2 * ((p.m : ℝ) * (p.T : ℝ)) *
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e ≤
        2 * ((p.m : ℝ) * (p.T : ℝ)) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left he.2 hcoef
  change actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e +
      2 * ((p.m : ℝ) * (p.T : ℝ)) *
        actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e ∈
    Set.Icc 0 (3 * ((p.m : ℝ) * (p.T : ℝ)))
  constructor
  · exact add_nonneg hc.1 hprod
  · calc
      actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e +
          2 * ((p.m : ℝ) * (p.T : ℝ)) *
            actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e ≤
        (p.m : ℝ) * (p.T : ℝ) + 2 * ((p.m : ℝ) * (p.T : ℝ)) := add_le_add hc.2 hprod'
      _ = 3 * ((p.m : ℝ) * (p.T : ℝ)) := by ring
/-- Measurability of the selected-family combined observable on fixed private
coordinates. -/
theorem measurable_actualGInit (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (rows : CompleteRows p) : Measurable (actualGInit p ids rewards C_star C_h eta S rows) := by
  exact (measurable_actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows).add
    ((measurable_actualInitializationFailureIndicator p ids rewards C_star C_h eta rows).const_mul
      (2 * ((p.m : ℝ) * (p.T : ℝ))))
/-- Joint measurability of the actual selected-family observables on the full
complete-row-family/private product carrier. -/
theorem measurable_actualInitializationObservables_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) :
    Measurable (fun z : CompleteRows p × PrivateCoordinates p =>
      (actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2,
        actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)) := by
  exact ((measurable_comparatorChargeAtBoundary p rewards S).comp
      (ReferenceInitializationIndexMixture.measurable_actualOutput_family
        p ids rewards C_star C_h eta)).prodMk
    (measurable_actualInitializationFailureIndicator_pair p ids rewards C_star C_h eta)
/-- The actual fixed-family charge is integrable under the original private
law for every full numerical family. -/
theorem integrable_actualInitializationComparatorCharge (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) (rows : CompleteRows p) :
    Integrable (actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hm := measurable_actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows
  apply integrable_bounded_probability _ _ hm ((p.m : ℝ) * (p.T : ℝ))
  intro e
  have hb := actualInitializationComparatorCharge_bounds
    p ids rewards C_star C_h eta S hS rows e
  exact norm_le_of_nonneg_mem_Icc
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb
/-- The actual fixed-family flag indicator is integrable under the original
private law for every full numerical family. -/
theorem integrable_actualInitializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) :
    Integrable (actualInitializationFailureIndicator p ids rewards C_star C_h eta rows)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hm := measurable_actualInitializationFailureIndicator p ids rewards C_star C_h eta rows
  apply integrable_bounded_probability _ _ hm 1
  intro e
  have hb := actualInitializationFailureIndicator_bounds
    p ids rewards C_star C_h eta rows e
  exact norm_le_of_nonneg_mem_Icc (by norm_num) hb
/-- Actual fixed-family observables are jointly integrable over the independent
complete-row/private product law. -/
theorem integrable_actualInitializationObservables_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) :
    Integrable
      (fun z : CompleteRows p × PrivateCoordinates p =>
        (actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2,
          actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2))
      ((CompletePublicTable.completeRowsMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  have hm := measurable_actualInitializationObservables_pair p ids rewards C_star C_h eta S
  have hcost := integrable_bounded_probability
    ((CompletePublicTable.completeRowsMeasure p).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
    (fun z : CompleteRows p × PrivateCoordinates p =>
      actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2)
    (measurable_fst.comp hm) ((p.m : ℝ) * (p.T : ℝ)) (fun z => by
      have hb := actualInitializationComparatorCharge_bounds
        p ids rewards C_star C_h eta S hS z.1 z.2
      exact norm_le_of_nonneg_mem_Icc
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb)
  have hflag := integrable_bounded_probability
    ((CompletePublicTable.completeRowsMeasure p).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
    (fun z : CompleteRows p × PrivateCoordinates p =>
      actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)
    (measurable_snd.comp hm) 1 (fun z => by
      have hb := actualInitializationFailureIndicator_bounds
        p ids rewards C_star C_h eta z.1 z.2
      exact norm_le_of_nonneg_mem_Icc (by norm_num) hb)
  exact hcost.prodMk hflag
/-! ### Fixed-family original-scalar averaging -/

private theorem coordinatorAtom_measurable (p : Parameters) (j : Fin (M p)) :
    MeasurableSet {e : PrivateCoordinates p |
      PrivateSourceStreams.coordinatorIndex p e.1.2 = j} := by
  exact ((PrivateSourceStreams.measurable_coordinatorIndex p).comp
    (measurable_snd.comp measurable_fst)) (measurableSet_singleton j)
/-- Integrals of an integrable concrete private observable split across the
actual original coordinator-scalar atoms. -/
private theorem integral_eq_sum_coordinator_atoms (p : Parameters)
    (f : PrivateCoordinates p → ℝ)
    (hf : Integrable f (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) :
    ∫ e, f e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      ∑ j : Fin (M p), ∫ e in
        {e : PrivateCoordinates p | PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
          f e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
  classical
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let atom : Fin (M p) → Set (PrivateCoordinates p) := fun j =>
    {e | PrivateSourceStreams.coordinatorIndex p e.1.2 = j}
  let piece : Fin (M p) → PrivateCoordinates p → ℝ := fun j => (atom j).indicator f
  have hpoint : ∀ e, f e = ∑ j : Fin (M p), piece j e := by
    intro e
    calc
      f e = piece (PrivateSourceStreams.coordinatorIndex p e.1.2) e := by
        simp [piece, atom]
      _ = ∑ j : Fin (M p), piece j e := by
        symm
        apply Finset.sum_eq_single (PrivateSourceStreams.coordinatorIndex p e.1.2)
        · intro j hj hne
          simp [piece, atom, Ne.symm hne]
        · simp
  have hpieces : ∀ j, Integrable (piece j) μ := by
    intro j
    simpa [piece] using hf.indicator (coordinatorAtom_measurable p j)
  calc
    ∫ e, f e ∂μ = ∫ e, ∑ j ∈ Finset.univ, piece j e ∂μ := by
      congr 1
      funext e
      exact hpoint e
    _ = ∑ j ∈ Finset.univ, ∫ e, piece j e ∂μ := by
      exact integral_finsetSum Finset.univ (fun j hj => hpieces j)
    _ = ∑ j : Fin (M p), ∫ e in atom j, f e ∂μ := by
      apply Finset.sum_congr rfl
      intro j hj
      change ∫ e, (atom j).indicator f e ∂μ = ∫ e in atom j, f e ∂μ
      exact integral_indicator (coordinatorAtom_measurable p j)
/-- For every fixed complete-row family, the actual launch-bounded comparator
charge averages over the original scalar-selected index exactly. -/
theorem actual_initializationComparatorCharge_integral_eq_average
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) (rows : CompleteRows p) :
    ∫ e, actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p), c_S p ids rewards C_star C_h eta S (rows j) := by
  let φ : Boundary p → ℝ := comparatorChargeAtBoundary p rewards S
  have hφ : Measurable φ := measurable_comparatorChargeAtBoundary p rewards S
  have hφ_bound : ∀ b, φ b ∈ Set.Icc 0 ((p.m : ℝ) * (p.T : ℝ)) :=
    fun b => comparatorChargeAtBoundary_bounds p rewards S hS b
  have hactual := integrable_actualInitializationComparatorCharge
    p ids rewards C_star C_h eta S hS rows
  rw [integral_eq_sum_coordinator_atoms p
    (actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows) hactual]
  calc
    (∑ j : Fin (M p), ∫ e in
        {e : PrivateCoordinates p | PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
          actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e
            ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      ∑ j : Fin (M p), (1 / (M p : ℝ)) *
        c_S p ids rewards C_star C_h eta S (rows j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases ReferenceInitializationIndexMixture.actualOutput_bounded_test_disintegration
              p ids rewards C_star C_h eta rows j φ hφ 0
              ((p.m : ℝ) * (p.T : ℝ)) hφ_bound with ⟨_, _, hformula⟩
          calc
            ∫ e in {e : PrivateCoordinates p |
                PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
                actualInitializationComparatorCharge p ids rewards C_star C_h eta S rows e
                  ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
              ∫ e in {e : PrivateCoordinates p |
                PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
                φ (ReferenceInitializationIndexMixture.actualOutput
                  p ids rewards C_star C_h eta rows e)
                  ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := rfl
            _ = (1 / (M p : ℝ)) * ∫ e,
                φ (ReferenceInitializationIndexMixture.fixedRowOutput
                  p ids rewards C_star C_h eta (rows j) e)
                  ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := hformula
            _ = (1 / (M p : ℝ)) * c_S p ids rewards C_star C_h eta S (rows j) := by
              rfl
    _ = (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), c_S p ids rewards C_star C_h eta S (rows j) := by
      rw [← Finset.mul_sum]
/-- For every fixed complete-row family, the actual initialization flag
probability is the uniform average of the concrete per-row private masses. -/
theorem actual_initializationFailure_probability_eq_average
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
      (actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).toReal =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j) := by
  calc
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
        (actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).toReal =
      ∫ e, actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
          rw [show (fun e : PrivateCoordinates p =>
              actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e) =
              (actualInitializationFailureEvent p ids rewards C_star C_h eta rows).indicator
                (fun _ => (1 : ℝ)) from by funext e; rfl]
          exact (integral_indicator_one
            (measurable_actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).symm
    _ = (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        e_initFlag p ids rewards C_star C_h eta (rows j) := by
          let φj : Fin (M p) → Boundary p → ℝ := fun j =>
            initializationFailureAtBoundaryIndicator p (rows j) eta
          have hφj : ∀ j, Measurable (φj j) := by
            intro j
            exact measurable_initializationFailureAtBoundaryIndicator p (rows j) eta
          have hbound : ∀ j b, φj j b ∈ Set.Icc 0 1 := by
            intro j b
            dsimp [φj, initializationFailureAtBoundaryIndicator]
            split_ifs <;> norm_num
          have hactual := integrable_actualInitializationFailureIndicator
            p ids rewards C_star C_h eta rows
          rw [integral_eq_sum_coordinator_atoms p
            (actualInitializationFailureIndicator p ids rewards C_star C_h eta rows) hactual]
          calc
            (∑ j : Fin (M p), ∫ e in
                {e : PrivateCoordinates p | PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
                  actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
                    ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
              ∑ j : Fin (M p), (1 / (M p : ℝ)) *
                e_initFlag p ids rewards C_star C_h eta (rows j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rcases ReferenceInitializationIndexMixture.actualOutput_bounded_test_disintegration
                      p ids rewards C_star C_h eta rows j (φj j) (hφj j) 0 1 (hbound j)
                    with ⟨_, _, hformula⟩
                  have heq : ∀ e,
                      PrivateSourceStreams.coordinatorIndex p e.1.2 = j →
                      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e =
                        φj j (ReferenceInitializationIndexMixture.actualOutput
                          p ids rewards C_star C_h eta rows e) := by
                    intro e hJ
                    rw [actualInitializationFailureIndicator_eq_boundary
                      p ids rewards C_star C_h eta rows e]
                    simp [φj, hJ]
                  calc
                    ∫ e in {e : PrivateCoordinates p |
                        PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
                        actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
                          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
                      ∫ e in {e : PrivateCoordinates p |
                        PrivateSourceStreams.coordinatorIndex p e.1.2 = j},
                        φj j (ReferenceInitializationIndexMixture.actualOutput
                          p ids rewards C_star C_h eta rows e)
                          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
                            apply setIntegral_congr_fun (coordinatorAtom_measurable p j)
                            intro e he
                            exact heq e he
                    _ = (1 / (M p : ℝ)) * ∫ e,
                        φj j (ReferenceInitializationIndexMixture.fixedRowOutput
                          p ids rewards C_star C_h eta (rows j) e)
                          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := hformula
                    _ = (1 / (M p : ℝ)) *
                        e_initFlag p ids rewards C_star C_h eta (rows j) := by
                          congr 1
                          apply integral_congr_ae
                          filter_upwards with e
                          exact (initializationFailureIndicator_eq_boundary
                            p ids rewards C_star C_h eta (rows j) e).symm
            _ = (1 / (M p : ℝ)) *
                ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j) := by
                  rw [← Finset.mul_sum]
/-- Integral form of the literal flag probability average. -/
theorem actual_initializationFailureIndicator_integral_eq_average
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    ∫ e, actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j) := by
  rw [show (fun e : PrivateCoordinates p =>
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e) =
      (actualInitializationFailureEvent p ids rewards C_star C_h eta rows).indicator
        (fun _ => (1 : ℝ)) from by funext e; rfl]
  calc
    ∫ e, actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p
        (actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).toReal :=
      integral_indicator_one
        (measurable_actualInitializationFailureEvent p ids rewards C_star C_h eta rows)
    _ = (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j) :=
      actual_initializationFailure_probability_eq_average p ids rewards C_star C_h eta rows

/-- The combined private expectation averages the concrete row function
`g_init`, with the same `2mT` coefficient as its definition. -/
theorem actual_g_init_integral_eq_average (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) (rows : CompleteRows p) :
    ∫ e, actualGInit p ids rewards C_star C_h eta S rows e
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), g_init p ids rewards C_star C_h eta S (rows j) := by
  let k := 2 * ((p.m : ℝ) * (p.T : ℝ))
  have hc := integrable_actualInitializationComparatorCharge
    p ids rewards C_star C_h eta S hS rows
  have he := integrable_actualInitializationFailureIndicator
    p ids rewards C_star C_h eta rows
  have he' : Integrable (fun e => k *
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := he.const_mul k
  unfold actualGInit
  rw [integral_add hc he', integral_const_mul,
    actual_initializationComparatorCharge_integral_eq_average p ids rewards C_star C_h
      eta S hS rows,
    actual_initializationFailureIndicator_integral_eq_average p ids rewards C_star C_h
      eta rows]
  simp only [g_init]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp [k]
  ring_nf

/-- Selected-index disintegration for the concrete failure event on the
original private/family product. The accepted law applies because the actual
flag was proved invariant under replacement of only the selector scalar. -/
theorem actualFailureEvent_selectedIndex_disintegration (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (M p)) :
    SelectedIndexLaunchJointLaw.originalLaw p
      {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
        PrivateSourceStreams.coordinatorIndex p z.1.1.2 = j ∧
          z.1 ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta z.2} =
      ENNReal.ofReal (1 / (M p : ℝ)) * GeneratedBootstrapRoundLaw.originalLaw p
        {z : CompleteRow p × PrivateCoordinates p |
          z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1} := by
  let f : CompleteRow p → PrivateCoordinates p → ℝ :=
    initializationFailureIndicator p ids rewards C_star C_h eta
  have hFixed : Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      f z.1 z.2) := measurable_initializationFailureIndicator_pair
        p ids rewards C_star C_h eta
  have hinv : ∀ row q s t,
      f row (ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) =
        f row (ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) := by
    intro row q s t
    simpa [f, ReferenceInitializationIndexMixture.insertScalarResidual,
      ReferenceInitializationIndexMixture.withCoordinatorScalar] using
      (initializationFailureIndicator_scalar_invariant p ids rewards C_star C_h eta row
        (ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) t).symm
  have hLaw := SelectedIndexLaunchJointLaw.fixedIndex_scalarInvariant_event_disintegration
    (p := p) f hFixed hinv j {1} (measurableSet_singleton (1 : ℝ))
  have hleft :
      {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
        PrivateSourceStreams.coordinatorIndex p z.1.1.2 = j ∧
          z.1 ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta z.2} =
      {z : SelectedIndexLaunchJointLaw.OriginalCoordinates p |
        PrivateSourceStreams.coordinatorIndex p z.1.1.2 = j ∧ f (z.2 j) z.1 ∈ ({1} : Set ℝ)} := by
    ext z
    rcases z with ⟨e, rows⟩
    by_cases hj : PrivateSourceStreams.coordinatorIndex p e.1.2 = j
    · have hEvent : e ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta rows ↔
          e ∈ initializationFailureEvent p ids rewards C_star C_h eta (rows j) := by
        simp [actualInitializationFailureEvent, initializationFailureEvent, hj]
      change (PrivateSourceStreams.coordinatorIndex p e.1.2 = j ∧
          e ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta rows) ↔
        (PrivateSourceStreams.coordinatorIndex p e.1.2 = j ∧
          initializationFailureIndicator p ids rewards C_star C_h eta (rows j) e ∈
            ({1} : Set ℝ))
      simp [hj, hEvent, initializationFailureIndicator]
    · simp [hj]
  have hright :
      {z : CompleteRow p × PrivateCoordinates p | f z.1 z.2 ∈ ({1} : Set ℝ)} =
      {z | z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1} := by
    ext z
    rcases z with ⟨row, e⟩
    simp [f, initializationFailureIndicator]
  rw [hleft, ← hright]
  exact hLaw

/-- Joint measurability of both concrete observables on the original product
row/private carrier. -/
theorem measurable_initializationRowObservables_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) :
    Measurable (fun z : CompleteRow p × PrivateCoordinates p =>
      (initializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2,
        initializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)) := by
  exact (measurable_initializationComparatorCharge_pair p ids rewards C_star C_h eta S).prodMk
    ((measurable_initializationFailureIndicator_pair p ids rewards C_star C_h eta).comp
      measurable_id)

/-! ### Integrability, row integrals, and real event mass -/

/-- Every fixed-row private section of the cost is integrable under the actual
extended-private law. -/
theorem integrable_initializationComparatorCharge (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) (row : CompleteRow p) :
    Integrable (initializationComparatorCharge p ids rewards C_star C_h eta S row)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hsection : Measurable
      (initializationComparatorCharge p ids rewards C_star C_h eta S row) := by
    exact (measurable_comparatorChargeAtBoundary p rewards S).comp
      (ReferenceInitializationIndexMixture.measurable_fixedRowOutput
        p ids rewards C_star C_h eta row)
  apply integrable_bounded_probability _ _ hsection ((p.m : ℝ) * (p.T : ℝ))
  intro e
  have h := initializationComparatorCharge_bounds p ids rewards C_star C_h eta S hS row e
  exact norm_le_of_nonneg_mem_Icc
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h

/-- Every fixed-row private section of the flag indicator is integrable under
the actual extended-private law. -/
theorem integrable_initializationFailureIndicator (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) :
    Integrable (initializationFailureIndicator p ids rewards C_star C_h eta row)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have h : Measurable (initializationFailureIndicator p ids rewards C_star C_h eta row) := by
    change Measurable ((initializationFailureEvent p ids rewards C_star C_h eta row).indicator
      (fun _ : PrivateCoordinates p => (1 : ℝ)))
    exact measurable_const.indicator
      (measurable_initializationFailureEvent p ids rewards C_star C_h eta row)
  apply integrable_bounded_probability _ _ h 1
  intro e
  have hb := initializationFailureIndicator_bounds p ids rewards C_star C_h eta row e
  exact norm_le_of_nonneg_mem_Icc (by norm_num) hb

/-- The fixed-row charge is jointly integrable on the original row/private
product law. -/
theorem integrable_initializationComparatorCharge_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (S : Finset (Fin p.K)) (hS : S.card = p.m) :
    Integrable
      (fun z : CompleteRow p × PrivateCoordinates p =>
        initializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2)
      ((CompletePublicTable.completeRowMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  have hm := measurable_initializationComparatorCharge_pair p ids rewards C_star C_h eta S
  apply integrable_bounded_probability _ _ hm ((p.m : ℝ) * (p.T : ℝ))
  intro z
  have h := initializationComparatorCharge_bounds p ids rewards C_star C_h eta S hS z.1 z.2
  exact norm_le_of_nonneg_mem_Icc
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h

/-- The fixed-row failure indicator is jointly integrable on the original
row/private product law. -/
theorem integrable_initializationFailureIndicator_pair (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate) :
    Integrable
      (fun z : CompleteRow p × PrivateCoordinates p =>
        initializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)
      ((CompletePublicTable.completeRowMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  have hm := measurable_initializationFailureIndicator_pair p ids rewards C_star C_h eta
  apply integrable_bounded_probability _ _ hm 1
  intro z
  have hb := initializationFailureIndicator_bounds p ids rewards C_star C_h eta z.1 z.2
  exact norm_le_of_nonneg_mem_Icc (by norm_num) hb

/-- The row-integrated cost is measurable by the product-integral measurability
theorem, using the actual jointly measurable integrand. -/
theorem measurable_c_S (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K)) :
    Measurable (c_S p ids rewards C_star C_h eta S) := by
  exact (measurable_initializationComparatorCharge_pair p ids rewards C_star C_h eta S
    ).stronglyMeasurable.integral_prod_right'.measurable

/-- The row-integrated failure flag is measurable, with no supplied row
factorization assumption. -/
theorem measurable_e_initFlag (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (e_initFlag p ids rewards C_star C_h eta) := by
  exact (measurable_initializationFailureIndicator_pair p ids rewards C_star C_h eta
    ).stronglyMeasurable.integral_prod_right'.measurable

/-- The row-level cost remains in `[0,mT]` after integrating the actual private
law. -/
theorem c_S_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) (row : CompleteRow p) :
    c_S p ids rewards C_star C_h eta S row ∈ Set.Icc 0 ((p.m : ℝ) * (p.T : ℝ)) := by
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  have hi := integrable_initializationComparatorCharge p ids rewards C_star C_h eta S hS row
  have hzero : Integrable (fun _ : PrivateCoordinates p => (0 : ℝ)) μ := integrable_const 0
  have htop : Integrable (fun _ : PrivateCoordinates p =>
      (p.m : ℝ) * (p.T : ℝ)) μ := integrable_const _
  constructor
  · calc
      0 = ∫ e, (0 : ℝ) ∂μ := by simp
      _ ≤ ∫ e, initializationComparatorCharge p ids rewards C_star C_h eta S row e ∂μ :=
        integral_mono hzero hi (fun e => (initializationComparatorCharge_bounds
          p ids rewards C_star C_h eta S hS row e).1)
  · calc
      (∫ e, initializationComparatorCharge p ids rewards C_star C_h eta S row e ∂μ) ≤
          ∫ e, (p.m : ℝ) * (p.T : ℝ) ∂μ :=
        integral_mono hi htop (fun e => (initializationComparatorCharge_bounds
          p ids rewards C_star C_h eta S hS row e).2)
      _ = (p.m : ℝ) * (p.T : ℝ) := by simp [μ]

/-- The row-level flag mass lies in `[0,1]`. -/
theorem e_initFlag_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    e_initFlag p ids rewards C_star C_h eta row ∈ Set.Icc 0 1 := by
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  have hi := integrable_initializationFailureIndicator p ids rewards C_star C_h eta row
  have hzero : Integrable (fun _ : PrivateCoordinates p => (0 : ℝ)) μ := integrable_const 0
  have hone : Integrable (fun _ : PrivateCoordinates p => (1 : ℝ)) μ := integrable_const 1
  constructor
  · calc
      0 = ∫ e, (0 : ℝ) ∂μ := by simp
      _ ≤ ∫ e, initializationFailureIndicator p ids rewards C_star C_h eta row e ∂μ :=
        integral_mono hzero hi (fun e => (initializationFailureIndicator_bounds
          p ids rewards C_star C_h eta row e).1)
  · calc
      (∫ e, initializationFailureIndicator p ids rewards C_star C_h eta row e ∂μ) ≤
          ∫ e, (1 : ℝ) ∂μ :=
        integral_mono hi hone (fun e => (initializationFailureIndicator_bounds
          p ids rewards C_star C_h eta row e).2)
      _ = 1 := by simp [μ]

/-- The combined row observable has its literal `[0,3mT]` bound. -/
theorem g_init_bounds (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) (row : CompleteRow p) :
    g_init p ids rewards C_star C_h eta S row ∈
      Set.Icc 0 (3 * ((p.m : ℝ) * (p.T : ℝ))) := by
  have hc := c_S_bounds p ids rewards C_star C_h eta S hS row
  have he := e_initFlag_bounds p ids rewards C_star C_h eta row
  have hmT : 0 ≤ (p.m : ℝ) * (p.T : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ 2 * ((p.m : ℝ) * (p.T : ℝ)) := mul_nonneg (by norm_num) hmT
  have hprod : 0 ≤ 2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row :=
    mul_nonneg hcoef he.1
  have hprod' : 2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row ≤
      2 * ((p.m : ℝ) * (p.T : ℝ)) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left he.2 hcoef
  change c_S p ids rewards C_star C_h eta S row +
      2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row ∈
    Set.Icc 0 (3 * ((p.m : ℝ) * (p.T : ℝ)))
  constructor
  · exact add_nonneg hc.1 hprod
  · calc
      c_S p ids rewards C_star C_h eta S row +
          2 * ((p.m : ℝ) * (p.T : ℝ)) * e_initFlag p ids rewards C_star C_h eta row ≤
        (p.m : ℝ) * (p.T : ℝ) + 2 * ((p.m : ℝ) * (p.T : ℝ)) := add_le_add hc.2 hprod'
      _ = 3 * ((p.m : ℝ) * (p.T : ℝ)) := by ring

/-- The row functions themselves are integrable under the complete-row law;
their measurability and bounds are established from the concrete observables. -/
theorem integrable_c_S (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) :
    Integrable (c_S p ids rewards C_star C_h eta S)
      (CompletePublicTable.completeRowMeasure p) := by
  have hm := measurable_c_S p ids rewards C_star C_h eta S
  apply integrable_bounded_probability _ _ hm ((p.m : ℝ) * (p.T : ℝ))
  intro row
  have hb := c_S_bounds p ids rewards C_star C_h eta S hS row
  exact norm_le_of_nonneg_mem_Icc
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb

theorem integrable_e_initFlag (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Integrable (e_initFlag p ids rewards C_star C_h eta)
      (CompletePublicTable.completeRowMeasure p) := by
  have hm := measurable_e_initFlag p ids rewards C_star C_h eta
  apply integrable_bounded_probability _ _ hm 1
  intro row
  have hb := e_initFlag_bounds p ids rewards C_star C_h eta row
  exact norm_le_of_nonneg_mem_Icc (by norm_num) hb

theorem measurable_g_init (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K)) :
    Measurable (g_init p ids rewards C_star C_h eta S) := by
  exact (measurable_c_S p ids rewards C_star C_h eta S).add
    ((measurable_e_initFlag p ids rewards C_star C_h eta).const_mul
      (2 * ((p.m : ℝ) * (p.T : ℝ))))

theorem integrable_g_init (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) :
    Integrable (g_init p ids rewards C_star C_h eta S)
      (CompletePublicTable.completeRowMeasure p) := by
  have hm := measurable_g_init p ids rewards C_star C_h eta S
  apply integrable_bounded_probability _ _ hm (3 * ((p.m : ℝ) * (p.T : ℝ)))
  intro row
  have hb := g_init_bounds p ids rewards C_star C_h eta S hS row
  exact norm_le_of_nonneg_mem_Icc
    (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hb

/-- The private integral of the failure indicator is exactly the real mass of
the actual measurable flag event. -/
theorem e_initFlag_eq_real_event_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
      (initializationFailureEvent p ids rewards C_star C_h eta row)).toReal =
      e_initFlag p ids rewards C_star C_h eta row := by
  unfold e_initFlag
  rw [show (fun e : PrivateCoordinates p =>
      initializationFailureIndicator p ids rewards C_star C_h eta row e) =
      (initializationFailureEvent p ids rewards C_star C_h eta row).indicator
        (fun _ => (1 : ℝ)) from by funext e; rfl]
  exact (integral_indicator_one
    (measurable_initializationFailureEvent p ids rewards C_star C_h eta row)).symm

/-- The actual fixed-family failure mass is the real mass of its own literal
measurable event. -/
theorem actual_failure_indicator_eq_real_event_mass (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
      (actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).toReal =
      ∫ e, actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
  rw [show (fun e : PrivateCoordinates p =>
      actualInitializationFailureIndicator p ids rewards C_star C_h eta rows e) =
      (actualInitializationFailureEvent p ids rewards C_star C_h eta rows).indicator
        (fun _ => (1 : ℝ)) from by funext e; rfl]
  exact (integral_indicator_one
    (measurable_actualInitializationFailureEvent p ids rewards C_star C_h eta rows)).symm

/-- The terminal sentinel is returned for no crossing or a final-round crossing. -/
theorem launchRoundAtBoundary_sentinel (p : Parameters) (b : Boundary p) :
    launchRoundAtBoundary p b = p.T + 1 ↔
      b.crossing.isSome = false ∨
        (b.crossing.isSome = true ∧ elapsed p b.completed = p.T) := by
  unfold launchRoundAtBoundary
  by_cases hc : b.crossing.isSome = true
  · simp [hc]
  · simp [hc]
/-- At endpoint `tau=1` the literal strict prelaunch prefix is empty. -/
theorem comparatorChargeAtBoundary_eq_zero_of_launch_one (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K))
    (b : Boundary p) (htau : launchRoundAtBoundary p b = 1) :
    comparatorChargeAtBoundary p rewards S b = 0 := by
  unfold comparatorChargeAtBoundary
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro a ha
  simp [htau]
/-- At `T+1`, the strict prelaunch prefix contains every source round. -/
theorem comparatorChargeAtBoundary_eq_full_of_launch_sentinel (p : Parameters)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K))
    (b : Boundary p) (htau : launchRoundAtBoundary p b = p.T + 1) :
    comparatorChargeAtBoundary p rewards S b =
      ∑ t : Fin p.T, ∑ a ∈ S, ((rewards t a).val : ℝ) / (D p : ℝ) := by
  unfold comparatorChargeAtBoundary
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  simp [htau]

/-- Product-stream Fubini identity for the concrete fixed-row comparator
charge, with IDs and denominator-`D` rewards fixed. -/
theorem integral_rowPrivate_comparatorCharge (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) :
    ∫ z : CompleteRow p × PrivateCoordinates p,
      initializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2
        ∂(CompletePublicTable.completeRowMeasure p).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      ∫ row, c_S p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p := by
  rw [integral_prod _ (integrable_initializationComparatorCharge_pair
    p ids rewards C_star C_h eta S hS)]
  rfl

/-- Product-stream Fubini identity for the literal initialization flag. -/
theorem integral_rowPrivate_failureIndicator (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    ∫ z : CompleteRow p × PrivateCoordinates p,
      initializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2
        ∂(CompletePublicTable.completeRowMeasure p).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      ∫ row, e_initFlag p ids rewards C_star C_h eta row
        ∂CompletePublicTable.completeRowMeasure p := by
  rw [integral_prod _ (integrable_initializationFailureIndicator_pair
    p ids rewards C_star C_h eta)]
  rfl

/-- The corresponding product-stream identity for the real event mass is
obtained from its literal indicator and the same Fubini factorization. -/
theorem generatedFailureEvent_real_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    (GeneratedBootstrapRoundLaw.originalLaw p
      {z : CompleteRow p × PrivateCoordinates p |
        z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1}).toReal =
      ∫ row, e_initFlag p ids rewards C_star C_h eta row
        ∂CompletePublicTable.completeRowMeasure p := by
  have hs : MeasurableSet {z : CompleteRow p × PrivateCoordinates p |
      z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1} :=
    measurable_initializationFailureEvent_pair p ids rewards C_star C_h eta
  change (((CompletePublicTable.completeRowMeasure p).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
      {z : CompleteRow p × PrivateCoordinates p |
        z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1}).toReal = _
  calc
    _ = ∫ z : CompleteRow p × PrivateCoordinates p,
        Set.indicator {z : CompleteRow p × PrivateCoordinates p |
          z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1}
          (fun _ => (1 : ℝ)) z
        ∂(CompletePublicTable.completeRowMeasure p).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p) :=
      (integral_indicator_one hs).symm
    _ = ∫ row, e_initFlag p ids rewards C_star C_h eta row
        ∂CompletePublicTable.completeRowMeasure p := by
      rw [show (fun z : CompleteRow p × PrivateCoordinates p =>
          Set.indicator {z : CompleteRow p × PrivateCoordinates p |
            z.2 ∈ initializationFailureEvent p ids rewards C_star C_h eta z.1}
            (fun _ => (1 : ℝ)) z) =
          (fun z => initializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)
          from by funext z; rfl]
      rw [integral_prod _ (integrable_initializationFailureIndicator_pair
        p ids rewards C_star C_h eta)]
      rfl

/-- Fubini identities for the concrete selected-family cost and failure flag
over the original independent complete-family/private product law. -/
theorem actual_observables_product_fubini (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (S : Finset (Fin p.K))
    (hS : S.card = p.m) :
    (∫ z : CompleteRows p × PrivateCoordinates p,
        actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p),
      ∫ z : CompleteRows p × PrivateCoordinates p,
        actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) =
    (∫ rows, (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), c_S p ids rewards C_star C_h eta S (rows j)
          ∂CompletePublicTable.completeRowsMeasure p,
      ∫ rows, (1 / (M p : ℝ)) *
        ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j)
          ∂CompletePublicTable.completeRowsMeasure p) := by
  have hobs := measurable_actualInitializationObservables_pair
    p ids rewards C_star C_h eta S
  have hcost : Integrable
      (fun z : CompleteRows p × PrivateCoordinates p =>
        actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2)
      ((CompletePublicTable.completeRowsMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
    apply integrable_bounded_probability _ _ (measurable_fst.comp hobs)
      ((p.m : ℝ) * (p.T : ℝ))
    intro z
    exact norm_le_of_nonneg_mem_Icc
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (actualInitializationComparatorCharge_bounds
        p ids rewards C_star C_h eta S hS z.1 z.2)
  have hflag : Integrable
      (fun z : CompleteRows p × PrivateCoordinates p =>
        actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2)
      ((CompletePublicTable.completeRowsMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
    apply integrable_bounded_probability _ _ (measurable_snd.comp hobs) 1
    intro z
    exact norm_le_of_nonneg_mem_Icc (by norm_num)
      (actualInitializationFailureIndicator_bounds
        p ids rewards C_star C_h eta z.1 z.2)
  apply Prod.ext
  · calc
      ∫ z : CompleteRows p × PrivateCoordinates p,
          actualInitializationComparatorCharge p ids rewards C_star C_h eta S z.1 z.2
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
        ∫ rows, ∫ e, actualInitializationComparatorCharge p ids rewards C_star C_h eta S
          rows e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
          ∂CompletePublicTable.completeRowsMeasure p := integral_prod _ hcost
      _ = ∫ rows, (1 / (M p : ℝ)) *
          ∑ j : Fin (M p), c_S p ids rewards C_star C_h eta S (rows j)
            ∂CompletePublicTable.completeRowsMeasure p := by
        apply integral_congr_ae
        filter_upwards with rows
        exact actual_initializationComparatorCharge_integral_eq_average
          p ids rewards C_star C_h eta S hS rows
  · calc
      ∫ z : CompleteRows p × PrivateCoordinates p,
          actualInitializationFailureIndicator p ids rewards C_star C_h eta z.1 z.2
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
        ∫ rows, ∫ e, actualInitializationFailureIndicator p ids rewards C_star C_h eta
          rows e ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
          ∂CompletePublicTable.completeRowsMeasure p := integral_prod _ hflag
      _ = ∫ rows, (1 / (M p : ℝ)) *
          ∑ j : Fin (M p), e_initFlag p ids rewards C_star C_h eta (rows j)
            ∂CompletePublicTable.completeRowsMeasure p := by
        apply integral_congr_ae
        filter_upwards with rows
        exact actual_initializationFailureIndicator_integral_eq_average
          p ids rewards C_star C_h eta rows

/-- The fixed-row named event is the terminal reference-run failure flag.
Sources: `sources/zip4/manuscript/07_public_setup.tex:129-140` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/
theorem initializationFailureEvent_iff_terminalFlag (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompleteRow p) (e : PrivateCoordinates p) :
    e ∈ initializationFailureEvent p ids rewards C_star C_h eta row ↔
      ∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput
            p ids rewards C_star C_h eta row e)
          (ReferenceInitializationRun.output
            (ReferenceInitializationIndexMixture.fixedRowInput
              p ids rewards C_star C_h eta row e))
          i = true := by
  simp only [initializationFailureEvent, Set.mem_ofPred_eq]

/-- The selected-row named event is the terminal reference-run failure flag,
using the original coordinator scalar to select from the complete row family.
Sources: `sources/zip4/manuscript/07_public_setup.tex:129-140` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/
theorem actualInitializationFailureEvent_iff_terminalFlag (p : Parameters)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompleteRows p) (e : PrivateCoordinates p) :
    e ∈ actualInitializationFailureEvent p ids rewards C_star C_h eta rows ↔
      ∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)
          (ReferenceInitializationRun.output
            (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
              (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e))
          i = true := by
  simp only [actualInitializationFailureEvent, Set.mem_ofPred_eq]

end Bandits.Support.InitializationRowObservables

end
