/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteFibreLift
public import Bandits.Support.CheckedAssignmentJointMeasurability

/-!
# Varying-parameter full-vector assignment-fibre kernel

For every Borel raw-mass and anchor parameter, this module keeps the original
`K + 1` assignment vector and disintegrates its complete checked-sampler law
over the successful slow-set outcome, with `none` retaining the full failure
fibre. It is a Borel kernel construction, not a chronological physical
coupling.

The assignment-fibre construction is the one described at
`sources/zip4/manuscript/06_interruptions.tex:410-423`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Bandits.Support.AssignmentParameterFibreKernel

open Bandits.Support
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.CheckedAssignmentJointMeasurability
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalOrientedSetLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RawMass (p : Parameters) := CheckedAssignmentJointMeasurability.RawMass p
abbrev Anchor (p : Parameters) := CheckedAssignmentJointMeasurability.Anchor p
abbrev Theta (p : Parameters) := RawMass p × Anchor p
abbrev AssignmentVector (p : Parameters) :=
  CheckedAssignmentJointMeasurability.AssignmentVector p
abbrev SlowSet (p : Parameters) := CanonicalOrientedSetLaw.SlowSet p.K p.m
abbrev Outcome (p : Parameters) := Option (SlowSet p)

local instance slowSetMeasurableSpace (p : Parameters) : MeasurableSpace (SlowSet p) := ⊤

local instance slowSetDiscreteMeasurableSpace (p : Parameters) :
    DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

local instance outcomeMeasurableSpace (p : Parameters) : MeasurableSpace (Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace (p : Parameters) :
    DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

/-- The literal successful slow-set projection of the existing checked
assignment sample. Every input coordinate, including the orientation
coordinate, remains in the original vector carrier.

Source: `sources/zip4/manuscript/06_interruptions.tex:410-423`.
-/
def successfulSlowSet (p : Parameters) (theta : Theta p)
    (v : AssignmentVector p) : Outcome p :=
  CheckedAssignmentSample.successfulSlowSet p
    (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2 v)

/-- The full joint sampler is Borel in the parameter and every assignment
coordinate, including all checked failure cases.
-/
theorem measurable_successfulSlowSet_joint (p : Parameters) :
    Measurable (fun z : Theta p × AssignmentVector p =>
      successfulSlowSet p z.1 z.2) := by
  exact CheckedAssignmentJointMeasurability.measurable_successfulSlowSet_joint p

/-- The finite-fibre mass derived from the original full-vector assignment law.
No corrected-mass or physical-history input is supplied.
-/
def fibreMass (p : Parameters) (theta : Theta p) (a : Outcome p) : ℝ≥0∞ :=
  FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
    (successfulSlowSet p theta) a

/-- The literal finite-fibre conditional measure on the entire assignment
vector. The null-fibre convention is inherited from `FiniteFibreLift`.
-/
def fibreMeasure (p : Parameters) (theta : Theta p) (a : Outcome p) :
    Measure (AssignmentVector p) :=
  FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
    (successfulSlowSet p theta) a

private theorem measurable_uncurry_finite
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Countable β] [MeasurableSpace γ]
    (f : α → β → γ) (hf : ∀ b, Measurable (fun a => f a b)) :
    Measurable (fun z : α × β => f z.1 z.2) := by
  classical
  intro s hs
  have hpre :
      (fun z : α × β => f z.1 z.2) ⁻¹' s =
        ⋃ b : β, {z : α × β | z.2 = b} ∩ {z | f z.1 b ∈ s} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨z.2, rfl, hz⟩
    · rintro ⟨b, hb, hz⟩
      simpa [hb] using hz
  rw [hpre]
  exact MeasurableSet.iUnion fun b =>
    (measurable_snd (measurableSet_singleton b)).inter
      ((hf b).comp measurable_fst hs)

private theorem measurable_fibreMass_fixed (p : Parameters) (a : Outcome p) :
    Measurable (fun theta : Theta p => fibreMass p theta a) := by
  change Measurable (fun theta =>
    ContinuousControlSlice.assignmentLaw p.K
      (Prod.mk theta ⁻¹' {z : Theta p × AssignmentVector p |
        successfulSlowSet p z.1 z.2 = a}))
  exact measurable_measure_prodMk_left
    (measurable_successfulSlowSet_joint p (measurableSet_singleton a))

theorem measurable_fibreMass_joint (p : Parameters) :
    Measurable (fun z : Theta p × Outcome p => fibreMass p z.1 z.2) := by
  exact measurable_uncurry_finite (fun theta a => fibreMass p theta a)
    (measurable_fibreMass_fixed p)

private theorem measurable_fibreMeasure_apply_fixed (p : Parameters)
    (a : Outcome p) (C : Set (AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable (fun theta : Theta p => fibreMeasure p theta a C) := by
  classical
  let sectionSet : Set (Theta p × AssignmentVector p) :=
    {z | z.2 ∈ C ∧ successfulSlowSet p z.1 z.2 = a}
  have hsection : MeasurableSet sectionSet := by
    exact (measurable_snd hC).inter
      (measurable_successfulSlowSet_joint p (measurableSet_singleton a))
  let q : Theta p → ℝ≥0∞ := fun theta => fibreMass p theta a
  let r : Theta p → ℝ≥0∞ := fun theta =>
    ContinuousControlSlice.assignmentLaw p.K (Prod.mk theta ⁻¹' sectionSet)
  have hq : Measurable q := measurable_fibreMass_fixed p a
  have hr : Measurable r := by
    change Measurable (fun theta =>
      ContinuousControlSlice.assignmentLaw p.K (Prod.mk theta ⁻¹' sectionSet))
    exact measurable_measure_prodMk_left hsection
  have hzero : MeasurableSet {theta : Theta p | q theta = 0} :=
    hq (measurableSet_singleton 0)
  have hformula (theta : Theta p) :
      fibreMeasure p theta a C =
        if q theta = 0 then ContinuousControlSlice.assignmentLaw p.K C
        else (q theta)⁻¹ * r theta := by
    change FiniteFibreLift.fibreMeasure
      (ContinuousControlSlice.assignmentLaw p.K)
      (successfulSlowSet p theta) a C = _
    by_cases hmass : q theta = 0
    · rw [FiniteFibreLift.fibreMeasure_of_eq_zero
        (μ := ContinuousControlSlice.assignmentLaw p.K)
        (F := successfulSlowSet p theta) (a := a) hmass]
      simp [q, hmass]
    · rw [FiniteFibreLift.fibreMeasure_apply
        (μ := ContinuousControlSlice.assignmentLaw p.K)
        (F := successfulSlowSet p theta) (a := a) hmass hC,
        ENNReal.div_eq_inv_mul]
      have hr_eq : r theta =
          ContinuousControlSlice.assignmentLaw p.K
            (C ∩ FiniteFibreLift.fibre (successfulSlowSet p theta) a) := by
        change ContinuousControlSlice.assignmentLaw p.K
            (Prod.mk theta ⁻¹' sectionSet) = _
        congr 1
      rw [ite_eq_right hmass, ← hr_eq]
      simp only [q, fibreMass]
  have hInv : Measurable (fun theta : Theta p => (q theta)⁻¹) := hq.inv
  have hval : Measurable (fun theta : Theta p =>
      if q theta = 0 then ContinuousControlSlice.assignmentLaw p.K C
      else (q theta)⁻¹ * r theta) := by
    exact Measurable.ite hzero measurable_const (hInv.mul hr)
  have hEq : (fun theta : Theta p => fibreMeasure p theta a C) =
      (fun theta => if q theta = 0 then ContinuousControlSlice.assignmentLaw p.K C
        else (q theta)⁻¹ * r theta) := funext hformula
  rw [hEq]
  exact hval

/-- For a fixed parameter and outcome, the conditional assignment-vector
measure is evaluated measurably on every Borel event.
-/
theorem measurable_fibreMeasure_apply_joint (p : Parameters)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable (fun z : Theta p × Outcome p => fibreMeasure p z.1 z.2 C) := by
  exact measurable_uncurry_finite (fun theta a => fibreMeasure p theta a C)
    (fun a => measurable_fibreMeasure_apply_fixed p a C hC)

/-- The full-vector conditional assignment-fibre kernel, jointly Borel in the
carried parameter and the `Option` outcome.
-/
def assignmentParameterFibreKernel (p : Parameters) :
    ProbabilityTheory.Kernel (Theta p × Outcome p) (AssignmentVector p) where
  toFun z := fibreMeasure p z.1 z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    exact measurable_fibreMeasure_apply_joint p C hC

@[simp] theorem assignmentParameterFibreKernel_apply (p : Parameters)
    (theta : Theta p) (a : Outcome p) :
    assignmentParameterFibreKernel p (theta, a) = fibreMeasure p theta a := rfl

instance instIsMarkovKernelAssignmentParameterFibreKernel (p : Parameters) :
    ProbabilityTheory.IsMarkovKernel (assignmentParameterFibreKernel p) where
  isProbabilityMeasure z :=
    FiniteFibreLift.instIsProbabilityMeasureFibreMeasure
      (μ := ContinuousControlSlice.assignmentLaw p.K)
      (F := successfulSlowSet p z.1) (a := z.2)

/-- The mass is a probability distribution over the complete `Option` output,
including the null-mass `none` outcome.
-/
theorem sum_fibreMass_eq_one (p : Parameters) (theta : Theta p) :
    (∑ a : Outcome p, fibreMass p theta a) = 1 := by
  let F : AssignmentVector p → Outcome p := successfulSlowSet p theta
  have hF : Measurable F := by
    exact (measurable_successfulSlowSet_joint p).comp measurable_prodMk_left
  exact FiniteFibreLift.sum_fibreMass
    (μ := ContinuousControlSlice.assignmentLaw p.K) (F := F) hF

/-- The derived mass times its conditional fibre measure recovers the original
assignment law, even on zero-mass fibres.
-/
theorem fibreMass_smul_fibreMeasure (p : Parameters) (theta : Theta p)
    (a : Outcome p) :
    fibreMass p theta a • fibreMeasure p theta a =
      (ContinuousControlSlice.assignmentLaw p.K).restrict
        (FiniteFibreLift.fibre (successfulSlowSet p theta) a) := by
  exact FiniteFibreLift.fibreMass_smul_fibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (F := successfulSlowSet p theta) (a := a)

/-- Summing all derived conditional rows recovers the entire continuous
`K + 1`-coordinate assignment law.
-/
theorem sum_fibreMass_smul_fibreMeasure (p : Parameters) (theta : Theta p) :
    (∑ a : Outcome p, fibreMass p theta a • fibreMeasure p theta a) =
      ContinuousControlSlice.assignmentLaw p.K := by
  let F : AssignmentVector p → Outcome p := successfulSlowSet p theta
  have hF : Measurable F := by
    exact (measurable_successfulSlowSet_joint p).comp measurable_prodMk_left
  exact FiniteFibreLift.sum_fibreMass_smul_fibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw p.K) (F := F) hF

/-- On every positive-mass outcome, the original full assignment vector lies
in precisely that sampler fibre almost surely. No support assertion is made
for null fibres, whose measure follows the inherited full-law convention.
-/
theorem ae_successfulSlowSet_eq_of_fibreMass_pos (p : Parameters)
    (theta : Theta p) (a : Outcome p) (hpos : 0 < fibreMass p theta a) :
    ∀ᵐ v ∂fibreMeasure p theta a, successfulSlowSet p theta v = a := by
  apply FiniteFibreLift.ae_fibreMeasure_eq
  · exact (measurable_successfulSlowSet_joint p).comp measurable_prodMk_left
  · exact hpos.ne'

/-- The row measure of `q(theta,a) K((theta,a),dv)` on parameter, outcome,
and full assignment-vector triples.
-/
def conditionalJointMeasure (p : Parameters) (theta : Theta p) :
    Measure ((Theta p × Outcome p) × AssignmentVector p) :=
  ∑ a : Outcome p, fibreMass p theta a •
    Measure.map (fun v : AssignmentVector p => ((theta, a), v))
      (fibreMeasure p theta a)

private theorem conditionalJointMeasure_eq_graphMap (p : Parameters)
    (theta : Theta p) :
    conditionalJointMeasure p theta =
      Measure.map (fun v : AssignmentVector p =>
        ((theta, successfulSlowSet p theta v), v))
        (ContinuousControlSlice.assignmentLaw p.K) := by
  classical
  let F : AssignmentVector p → Outcome p := successfulSlowSet p theta
  let graph : AssignmentVector p → (Theta p × Outcome p) × AssignmentVector p :=
    fun v => ((theta, F v), v)
  have hF : Measurable F := by
    exact (measurable_successfulSlowSet_joint p).comp measurable_prodMk_left
  have hgraph : Measurable graph := by
    exact (measurable_const.prodMk hF).prodMk measurable_id
  have hpartition := FiniteFibreLift.sum_restrict_fibre
    (μ := ContinuousControlSlice.assignmentLaw p.K) (F := F) hF
  unfold conditionalJointMeasure
  calc
    _ = ∑ a : Outcome p,
        Measure.map (fun v : AssignmentVector p => ((theta, a), v))
          (fibreMass p theta a • fibreMeasure p theta a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Measure.map_smul _
        (show AEMeasurable (fun v : AssignmentVector p => ((theta, a), v))
          (fibreMeasure p theta a) from
          (measurable_const.prodMk measurable_id).aemeasurable)]
    _ = ∑ a : Outcome p,
        Measure.map (fun v : AssignmentVector p => ((theta, a), v))
          ((ContinuousControlSlice.assignmentLaw p.K).restrict
            (FiniteFibreLift.fibre F a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [fibreMass_smul_fibreMeasure]
    _ = ∑ a : Outcome p,
        Measure.map graph
          ((ContinuousControlSlice.assignmentLaw p.K).restrict
            (FiniteFibreLift.fibre F a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem
        (FiniteFibreLift.measurableSet_fibre (F := F) (a := a) hF)] with v hv
      have hvalue : F v = a := by
        change v ∈ F ⁻¹' {a} at hv
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hv
      simp [graph, hvalue]
    _ = Measure.map graph
        (∑ a : Outcome p,
          (ContinuousControlSlice.assignmentLaw p.K).restrict
            (FiniteFibreLift.fibre F a)) := by
      symm
      exact Measure.map_finset_sum'
        (f := graph) (m := fun a : Outcome p =>
          (ContinuousControlSlice.assignmentLaw p.K).restrict
            (FiniteFibreLift.fibre F a)) hgraph.aemeasurable
    _ = Measure.map graph (ContinuousControlSlice.assignmentLaw p.K) := by
      rw [hpartition]

/-- The measure obtained by first drawing the parameter from a finite base
measure and then drawing `a` with its derived mass and `v` from the matching
full-vector conditional fibre.
-/
def jointMeasure (p : Parameters) (μ : Measure (Theta p)) :
    Measure ((Theta p × Outcome p) × AssignmentVector p) :=
  μ.bind (conditionalJointMeasure p)

/-- For every finite base measure on the Borel parameter space, the joint
`mu(dtheta) q(theta,a) K((theta,a),dv)` law is exactly the pushforward of the
base product with the original full assignment-vector law.
-/
theorem jointMeasure_eq_map (p : Parameters) (μ : Measure (Theta p))
    [IsFiniteMeasure μ] :
    jointMeasure p μ =
      (μ.prod (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun z : Theta p × AssignmentVector p =>
          ((z.1, successfulSlowSet p z.1 z.2), z.2)) := by
  classical
  let graph : Theta p × AssignmentVector p →
      (Theta p × Outcome p) × AssignmentVector p :=
    fun z => ((z.1, successfulSlowSet p z.1 z.2), z.2)
  have hgraph : Measurable graph := by
    exact (measurable_fst.prodMk (measurable_successfulSlowSet_joint p)).prodMk
      measurable_snd
  have hbase : SFinite (ContinuousControlSlice.assignmentLaw p.K) := by
    infer_instance
  have hparam : Measurable (fun theta : Theta p =>
      Measure.map (Prod.mk theta : AssignmentVector p → Theta p × AssignmentVector p)
        (ContinuousControlSlice.assignmentLaw p.K)) := by
    exact Measurable.map_prodMk_left
  calc
    jointMeasure p μ = μ.bind (fun theta => conditionalJointMeasure p theta) := rfl
    _ = μ.bind (fun theta =>
        Measure.map (fun v : AssignmentVector p =>
          ((theta, successfulSlowSet p theta v), v))
          (ContinuousControlSlice.assignmentLaw p.K)) := by
      apply Measure.bind_congr_right
      filter_upwards [] with theta
      exact conditionalJointMeasure_eq_graphMap p theta
    _ = Measure.map graph
        (μ.bind (fun theta =>
          Measure.map (Prod.mk theta : AssignmentVector p →
            Theta p × AssignmentVector p)
            (ContinuousControlSlice.assignmentLaw p.K))) := by
      rw [Measure.map_bind hparam.aemeasurable hgraph.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards [] with theta
      rw [Measure.map_map hgraph (measurable_prodMk_left)]
      rfl
    _ = (μ.prod (ContinuousControlSlice.assignmentLaw p.K)).map graph := by
      rw [Measure.prod_eq_of_sfinite μ (ContinuousControlSlice.assignmentLaw p.K)]

end Bandits.Support.AssignmentParameterFibreKernel

end
