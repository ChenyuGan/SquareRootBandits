/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterPhysicalFibreAssembly

/-!
# Paired resampling on the actual later physical assignment fibre

This module couples two complete original assignment-coordinate vectors by
first drawing the same actual successful-slow-set outcome and then drawing
independently from its two copies of the existing conditional fibre measure.
The resulting measure preserves each whole continuous assignment law and is
a jointly Borel Markov kernel in the original raw-mass and anchor parameters.

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,376-423` and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

The physical-evidence consequences consume the existing deterministic
later-fibre assembly. They do not assert a physical conditional law, a
feasible corrected law, a recorded-run bridge, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Bandits.Support.ReferenceLaterPhysicalFibreResampling

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentParameterFibreKernel
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceLaterPhysicalFibreAssembly
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon

local instance slowSetMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (AssignmentParameterFibreKernel.SlowSet p) := ⊤

local instance slowSetDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.SlowSet p) :=
  ⟨fun _ => trivial⟩

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev PairKernel (p : ConstructorDimensions.Parameters) :=
  ProbabilityTheory.Kernel.prod
    (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p)
    (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p)

/-- The literal same-outcome paired law on two whole original assignment
vectors. A zero-mass outcome contributes zero; its conditional measure retains
the existing full-law null-fibre convention.

Source: `sources/zip4/manuscript/06_interruptions.tex:410-423`.
-/
def pairedMeasure (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    Measure (CheckedAssignmentSample.AssignmentVector p ×
      CheckedAssignmentSample.AssignmentVector p) :=
  ∑ a : AssignmentParameterFibreKernel.Outcome p,
    AssignmentParameterFibreKernel.fibreMass p theta a •
      (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
        (AssignmentParameterFibreKernel.fibreMeasure p theta a)

private theorem fibreMass_event_sum (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) :
    (∑ a : AssignmentParameterFibreKernel.Outcome p,
      AssignmentParameterFibreKernel.fibreMass p theta a *
        AssignmentParameterFibreKernel.fibreMeasure p theta a C) =
      ContinuousControlSlice.assignmentLaw p.K C := by
  have h := congrArg (fun μ : Measure (CheckedAssignmentSample.AssignmentVector p) => μ C)
    (AssignmentParameterFibreKernel.sum_fibreMass_smul_fibreMeasure p theta)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

private theorem fibreMeasure_isProbability (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (a : AssignmentParameterFibreKernel.Outcome p) :
    IsProbabilityMeasure (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
  change IsProbabilityMeasure (FiniteFibreLift.fibreMeasure
    (ContinuousControlSlice.assignmentLaw p.K)
    (AssignmentParameterFibreKernel.successfulSlowSet p theta) a)
  exact FiniteFibreLift.instIsProbabilityMeasureFibreMeasure
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (F := AssignmentParameterFibreKernel.successfulSlowSet p theta) (a := a)

local instance instFibreMeasureProbability (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (a : AssignmentParameterFibreKernel.Outcome p) :
    IsProbabilityMeasure (AssignmentParameterFibreKernel.fibreMeasure p theta a) :=
  fibreMeasure_isProbability p theta a

/-- Each paired fibre law is a probability measure because the outcome masses
sum to one and each product uses two probability-valued conditional rows.
-/
theorem pairedMeasure_isProbabilityMeasure (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    IsProbabilityMeasure (pairedMeasure p theta) := by
  refine ⟨?_⟩
  have hprod (a : AssignmentParameterFibreKernel.Outcome p) :
      (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
        (AssignmentParameterFibreKernel.fibreMeasure p theta a) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp
  rw [pairedMeasure, Measure.finsetSum_apply]
  calc
    (∑ a : AssignmentParameterFibreKernel.Outcome p,
        (AssignmentParameterFibreKernel.fibreMass p theta a •
          ((AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
            (AssignmentParameterFibreKernel.fibreMeasure p theta a))) Set.univ) =
        ∑ a : AssignmentParameterFibreKernel.Outcome p,
          AssignmentParameterFibreKernel.fibreMass p theta a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Measure.smul_apply, smul_eq_mul, hprod, mul_one]
    _ = 1 := AssignmentParameterFibreKernel.sum_fibreMass_eq_one p theta

/-- The first vector marginal of the paired law is the entire original
continuous assignment-coordinate law.
-/
theorem pairedMeasure_fst (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    (pairedMeasure p theta).fst = ContinuousControlSlice.assignmentLaw p.K := by
  ext C hC
  rw [Measure.fst_apply hC]
  have hpre : Prod.fst ⁻¹' C = C ×ˢ (Set.univ : Set (CheckedAssignmentSample.AssignmentVector p)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [hpre, pairedMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    (∑ a : AssignmentParameterFibreKernel.Outcome p,
        AssignmentParameterFibreKernel.fibreMass p theta a *
          (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
            (AssignmentParameterFibreKernel.fibreMeasure p theta a)
              (C ×ˢ Set.univ)) =
        ∑ a : AssignmentParameterFibreKernel.Outcome p,
          AssignmentParameterFibreKernel.fibreMass p theta a *
            AssignmentParameterFibreKernel.fibreMeasure p theta a C := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Measure.prod_prod]
      simp
    _ = ContinuousControlSlice.assignmentLaw p.K C := fibreMass_event_sum p theta C

/-- The second vector marginal is also the entire original continuous
assignment-coordinate law.
-/
theorem pairedMeasure_snd (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    (pairedMeasure p theta).snd = ContinuousControlSlice.assignmentLaw p.K := by
  ext C hC
  rw [Measure.snd_apply hC]
  have hpre : Prod.snd ⁻¹' C = (Set.univ : Set (CheckedAssignmentSample.AssignmentVector p)) ×ˢ C := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
  rw [hpre, pairedMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    (∑ a : AssignmentParameterFibreKernel.Outcome p,
        AssignmentParameterFibreKernel.fibreMass p theta a *
          (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
            (AssignmentParameterFibreKernel.fibreMeasure p theta a)
              (Set.univ ×ˢ C)) =
        ∑ a : AssignmentParameterFibreKernel.Outcome p,
          AssignmentParameterFibreKernel.fibreMass p theta a *
            AssignmentParameterFibreKernel.fibreMeasure p theta a C := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Measure.prod_prod]
      simp
    _ = ContinuousControlSlice.assignmentLaw p.K C := fibreMass_event_sum p theta C

private theorem measurable_successfulSlowSet_fixed (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    Measurable (AssignmentParameterFibreKernel.successfulSlowSet p theta) := by
  exact (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
    measurable_prodMk_left

/-- Under the paired law, both vectors have the same actual optional sampler
outcome almost surely. Null-mass fibres vanish as summands and are not claimed
to be supported on their fibre.
-/
theorem ae_successfulSlowSet_eq (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    ∀ᵐ z ∂pairedMeasure p theta,
      AssignmentParameterFibreKernel.successfulSlowSet p theta z.1 =
        AssignmentParameterFibreKernel.successfulSlowSet p theta z.2 := by
  classical
  rw [pairedMeasure, ae_finsetSum_measure_iff]
  intro a ha
  by_cases hzero : AssignmentParameterFibreKernel.fibreMass p theta a = 0
  · simp [hzero]
  · have hpos : 0 < AssignmentParameterFibreKernel.fibreMass p theta a := by
      by_contra hn
      exact hzero (le_antisymm (not_lt.mp hn) bot_le)
    have hleft := AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos
      p theta a hpos
    have hright := hleft
    have hset : MeasurableSet {z :
        CheckedAssignmentSample.AssignmentVector p ×
          CheckedAssignmentSample.AssignmentVector p |
        AssignmentParameterFibreKernel.successfulSlowSet p theta z.1 = a ∧
          AssignmentParameterFibreKernel.successfulSlowSet p theta z.2 = a} :=
      (((measurable_successfulSlowSet_fixed p theta).comp measurable_fst)
          (measurableSet_singleton a)).inter
        (((measurable_successfulSlowSet_fixed p theta).comp measurable_snd)
          (measurableSet_singleton a))
    have hgood : ∀ᵐ z ∂
        (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
          (AssignmentParameterFibreKernel.fibreMeasure p theta a),
        AssignmentParameterFibreKernel.successfulSlowSet p theta z.1 = a ∧
          AssignmentParameterFibreKernel.successfulSlowSet p theta z.2 = a := by
      rw [Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [hleft] with v hv
      filter_upwards [hright] with w hw
      exact ⟨hv, hw⟩
    exact Measure.ae_smul_measure
      (hgood.mono fun z hz => hz.1.trans hz.2.symm)
      (AssignmentParameterFibreKernel.fibreMass p theta a)

/-- The jointly Borel paired-vector Markov kernel, formed from the product of
the existing parameter-and-outcome fibre kernel with itself at the same
`(theta, outcome)` and mixed by its derived outcome mass.
-/
def pairedKernel (p : ConstructorDimensions.Parameters) :
    ProbabilityTheory.Kernel (AssignmentParameterFibreKernel.Theta p)
      (CheckedAssignmentSample.AssignmentVector p ×
        CheckedAssignmentSample.AssignmentVector p) where
  toFun := pairedMeasure p
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    change Measurable (fun theta =>
      (∑ a : AssignmentParameterFibreKernel.Outcome p,
        AssignmentParameterFibreKernel.fibreMass p theta a •
          (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
            (AssignmentParameterFibreKernel.fibreMeasure p theta a)) C)
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro a ha
    let κ := PairKernel p
    have hmass : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
        AssignmentParameterFibreKernel.fibreMass p theta a) := by
      exact (AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
        (measurable_id.prodMk measurable_const)
    have hkernel : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
        κ (theta, a) C) := by
      exact (ProbabilityTheory.Kernel.measurable_coe κ hC).comp
        (measurable_id.prodMk measurable_const)
    have hrow (theta : AssignmentParameterFibreKernel.Theta p) :
        κ (theta, a) =
          (AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
            (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
      change ProbabilityTheory.Kernel.prod
        (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p)
        (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p) (theta, a) = _
      rw [ProbabilityTheory.Kernel.prod_apply]
      rfl
    have hEq :
        (fun theta : AssignmentParameterFibreKernel.Theta p =>
          AssignmentParameterFibreKernel.fibreMass p theta a *
            ((AssignmentParameterFibreKernel.fibreMeasure p theta a).prod
              (AssignmentParameterFibreKernel.fibreMeasure p theta a)) C) =
        (fun theta => AssignmentParameterFibreKernel.fibreMass p theta a *
          κ (theta, a) C) := by
      funext theta
      rw [← hrow theta]
    rw [hEq]
    exact hmass.mul hkernel

@[simp] theorem pairedKernel_apply (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    pairedKernel p theta = pairedMeasure p theta := rfl

/-- Every parameter row of the paired kernel is a probability measure.
-/
instance instIsMarkovKernelPairedKernel (p : ConstructorDimensions.Parameters) :
    ProbabilityTheory.IsMarkovKernel (pairedKernel p) where
  isProbabilityMeasure theta := by
    change IsProbabilityMeasure (pairedMeasure p theta)
    exact pairedMeasure_isProbabilityMeasure p theta

/-- The actual fixed-parameter paired law preserves successful slow-set
membership on the two sides almost surely.
-/
theorem ae_same_successfulSlowSet (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (A : Set (AssignmentParameterFibreKernel.Outcome p)) :
    ∀ᵐ z ∂pairedMeasure p theta,
      (AssignmentParameterFibreKernel.successfulSlowSet p theta z.1 ∈ A ↔
        AssignmentParameterFibreKernel.successfulSlowSet p theta z.2 ∈ A) := by
  filter_upwards [ae_successfulSlowSet_eq p theta] with z hz
  exact iff_of_eq (congrArg (fun a => a ∈ A) hz)

/-- The original whole-vector law splits exactly across the paired same-fibre
mixture, including the inherited convention on every null fibre.
-/
theorem pairedMeasure_fst_event_mass (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (C : Set (CheckedAssignmentSample.AssignmentVector p)) :
    ContinuousControlSlice.assignmentLaw p.K C =
      ∑ a : AssignmentParameterFibreKernel.Outcome p,
        AssignmentParameterFibreKernel.fibreMass p theta a *
          AssignmentParameterFibreKernel.fibreMeasure p theta a C := by
  exact (fibreMass_event_sum p theta C).symm

/-- The fixed-`x` evidence preimage for an arbitrary set of actual physical
round evidence. No measurable structure is placed on `RoundEvidence` or on
the supplied set.
-/
def evidencePreimage
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    Set (CheckedAssignmentSample.AssignmentVector p) :=
  {v | ReferenceActivePhysicalHorizon.computedEvidence
    (ReferenceLaterAssignmentFibreStep.withAssignment x v) ∈ A}

private abbrev EvidenceOutcome (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :=
  {a : AssignmentParameterFibreKernel.Outcome p //
    ∃ v, AssignmentParameterFibreKernel.successfulSlowSet p theta v = a ∧
      v ∈ evidencePreimage x A}

private theorem evidencePreimage_eq_fibres
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    evidencePreimage x A =
      ⋃ a : EvidenceOutcome x theta A,
        {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = a.val} := by
  classical
  ext v
  constructor
  · intro hv
    apply Set.mem_iUnion.mpr
    refine ⟨⟨AssignmentParameterFibreKernel.successfulSlowSet p theta v, ?_⟩, ?_⟩
    · exact ⟨v, rfl, hv⟩
    · rfl
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨⟨a, ha⟩, hv⟩
    obtain ⟨w, hw, hwa⟩ := ha
    have hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta' => AssignmentParameterFibreKernel.successfulSlowSet p theta' v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta' w := by
      rw [hparameters]
      exact hv.trans hw.symm
    have he := ReferenceLaterPhysicalFibreAssembly.computedEvidence_later_fibre
      x payload ledger proposal hphase v w hf
    change ReferenceActivePhysicalHorizon.computedEvidence
      (ReferenceLaterAssignmentFibreStep.withAssignment x v) ∈ A
    rw [he]
    exact hwa

/-- For any supplied set of actual round-evidence values, its full-vector
preimage is a finite union of genuine successful-slow-set fibres at the actual
later parameters, hence is measurable without a measurable structure on the
evidence type.
-/
theorem measurableSet_evidencePreimage
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    MeasurableSet (evidencePreimage x A) := by
  classical
  rw [evidencePreimage_eq_fibres x payload ledger proposal hphase theta hparameters A]
  exact MeasurableSet.iUnion fun a =>
    (measurable_successfulSlowSet_fixed p theta) (measurableSet_singleton a.val)

/-- The exact event-mass decomposition through the existing full-vector
conditional measures. This identity also applies to the inherited null-fibre
convention because zero weights annihilate those rows.
-/
theorem evidencePreimage_mass_decomposition
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    ContinuousControlSlice.assignmentLaw p.K (evidencePreimage x A) =
      ∑ a : AssignmentParameterFibreKernel.Outcome p,
        AssignmentParameterFibreKernel.fibreMass p theta a *
          AssignmentParameterFibreKernel.fibreMeasure p theta a (evidencePreimage x A) := by
  exact (fibreMass_event_sum p theta (evidencePreimage x A)).symm

/-- At every actual later-sampler parameter, the complete physical round
evidence is equal almost surely under the paired full-vector law.
-/
theorem ae_computedEvidence_later_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta) :
    ∀ᵐ z ∂pairedMeasure p theta,
      ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceLaterAssignmentFibreStep.withAssignment x z.1) =
        ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceLaterAssignmentFibreStep.withAssignment x z.2) := by
  filter_upwards [ae_successfulSlowSet_eq p theta] with z hz
  have hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta' => AssignmentParameterFibreKernel.successfulSlowSet p theta' z.1 =
          AssignmentParameterFibreKernel.successfulSlowSet p theta' z.2 := by
    rw [hparameters]
    exact hz
  exact ReferenceLaterPhysicalFibreAssembly.computedEvidence_later_fibre
    x payload ledger proposal hphase z.1 z.2 hf

/-- The same paired almost-sure conclusion for every actual physical successor
and output projection retained by the admitted assembly: actions, feedback,
own entries, coordinator and follower projections.
-/
theorem ae_step_projections_later_fibre
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta) :
    ∀ᵐ z ∂pairedMeasure p theta,
      let left := ReferenceActivePhysicalStep.step
        (ReferenceLaterAssignmentFibreStep.withAssignment x z.1)
      let right := ReferenceActivePhysicalStep.step
        (ReferenceLaterAssignmentFibreStep.withAssignment x z.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  filter_upwards [ae_successfulSlowSet_eq p theta] with z hz
  have hf : match ReferenceLaterAssignmentFibreStep.parameters? x with
      | none => True
      | some theta' => AssignmentParameterFibreKernel.successfulSlowSet p theta' z.1 =
          AssignmentParameterFibreKernel.successfulSlowSet p theta' z.2 := by
    rw [hparameters]
    exact hz
  exact ReferenceLaterPhysicalFibreAssembly.step_projections_later_fibre
    x payload ledger proposal hphase z.1 z.2 hf

/-- If the real optional parameter selector returns `none`, the admitted
assembly gives pointwise physical-evidence constancy for every pair of full
assignment vectors. No parameter or artificial fibre is introduced.
-/
theorem computedEvidence_eq_of_parameters_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hnone : ReferenceLaterAssignmentFibreStep.parameters? x = none)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceLaterAssignmentFibreStep.withAssignment x v) =
      ReferenceActivePhysicalHorizon.computedEvidence
        (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  exact ReferenceLaterPhysicalFibreAssembly.computedEvidence_later_fibre
    x payload ledger proposal hphase v w (by simp [hnone])

/-- In the same degenerate `none` case, all actual step projections are
pointwise equal for arbitrary complete assignment vectors.
-/
theorem step_projections_eq_of_parameters_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hnone : ReferenceLaterAssignmentFibreStep.parameters? x = none)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    let left := ReferenceActivePhysicalStep.step
      (ReferenceLaterAssignmentFibreStep.withAssignment x v)
    let right := ReferenceActivePhysicalStep.step
      (ReferenceLaterAssignmentFibreStep.withAssignment x w)
    left.next = right.next ∧
      left.preparation.arms.actions = right.preparation.arms.actions ∧
      left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
      left.ownEntries = right.ownEntries ∧
      left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  exact ReferenceLaterPhysicalFibreAssembly.step_projections_later_fibre
    x payload ledger proposal hphase v w (by simp [hnone])

/-- An arbitrary evidence event is preserved between the two paired vectors
almost surely, even though `RoundEvidence` and the event carry no measurable
structure.
-/
theorem ae_evidenceEvent_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameters : ReferenceLaterAssignmentFibreStep.parameters? x = some theta)
    (A : Set (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate))) :
    ∀ᵐ z ∂pairedMeasure p theta,
      (z.1 ∈ evidencePreimage x A ↔ z.2 ∈ evidencePreimage x A) := by
  filter_upwards [ae_computedEvidence_later_fibre
    x payload ledger proposal hphase theta hparameters] with z hz
  exact iff_of_eq (congrArg (fun e => e ∈ A) hz)

end Bandits.Support.ReferenceLaterPhysicalFibreResampling

end
