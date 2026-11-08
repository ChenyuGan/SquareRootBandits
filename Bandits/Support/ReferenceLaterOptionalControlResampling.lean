/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterSamplerParameterMeasurability

/-!
# Optional later-sampler coupling of the original current control

For the exact optional parameter selected by the existing physical
collection dispatcher, this module couples the two full assignment vectors,
then samples one shared remainder containing every original non-assignment
scalar and every DOWN/UP affine sample. The resulting paired controls each
have the original complete `TimeControl` law. The physical effect statement
uses the existing one-round input and actual step, and retains the untouched
forward arrays and every unselected row and time.

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,376-423`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

This is a current-control coupling only. It is not the chronological source
law and supplies no launch, past-exposure, conditional-law, feasibility,
iteration, full-row, private-array, or first-overflow conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceLaterPhysicalFibreAssembly
open Bandits.Support.ReferenceLaterPhysicalFibreResampling
open Bandits.Support.ReferenceLaterSamplerParameterMeasurability
open Bandits.Support.AssignmentParameterFibreKernel
open Bandits.Support.LaunchAssignmentCoordinateSplit

namespace Bandits.Support.ReferenceLaterOptionalControlResampling

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev AssignmentVector := CheckedAssignmentSample.AssignmentVector
abbrev AssignmentPair (p : ConstructorDimensions.Parameters) :=
  AssignmentVector p × AssignmentVector p
abbrev ControlRemainder (p : ConstructorDimensions.Parameters) :=
  LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
    ContinuousLearningRows.AffineSamples p
abbrev ControlPair (p : ConstructorDimensions.Parameters) :=
  ContinuousLearningRows.TimeControl p × ContinuousLearningRows.TimeControl p

local instance nonAssignmentScalarsMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p) where
  measurableSet_diagonal := by
    classical
    let α := LaunchAssignmentCoordinateSplit.NonAssignmentScalars p
    have hcoord (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
        MeasurableSet {z : α × α | z.1 label = z.2 label} :=
      measurableSet_eq_fun
        ((measurable_pi_apply label).comp measurable_fst)
        ((measurable_pi_apply label).comp measurable_snd)
    have hdiag : Set.diagonal α =
        ⋂ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
          {z : α × α | z.1 label = z.2 label} := by
      ext z
      simp only [Set.mem_diagonal_iff, Set.mem_iInter]
      constructor
      · intro h label
        exact congrFun h label
      · intro h
        exact funext h
    rw [hdiag]
    exact MeasurableSet.iInter hcoord

local instance affineSamplesMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (ContinuousLearningRows.AffineSamples p) where
  measurableSet_diagonal := by
    classical
    let α := ContinuousLearningRows.AffineSamples p
    have hcoord (channel : ContinuousLearningRows.Channel p) :
        MeasurableSet {z : α × α | z.1 channel = z.2 channel} :=
      measurableSet_eq_fun
        ((measurable_pi_apply channel).comp measurable_fst)
        ((measurable_pi_apply channel).comp measurable_snd)
    have hdiag : Set.diagonal α =
        ⋂ channel : ContinuousLearningRows.Channel p,
          {z : α × α | z.1 channel = z.2 channel} := by
      ext z
      simp only [Set.mem_diagonal_iff, Set.mem_iInter]
      constructor
      · intro h channel
        exact congrFun h channel
      · intro h
        exact funext h
    rw [hdiag]
    exact MeasurableSet.iInter hcoord

local instance controlRemainderMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (ControlRemainder p) where
  measurableSet_diagonal := by
    have hleft : MeasurableSet
        {z : ControlRemainder p × ControlRemainder p | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)
    have hright : MeasurableSet
        {z : ControlRemainder p × ControlRemainder p | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd)
    have hdiag : Set.diagonal (ControlRemainder p) =
        {z : ControlRemainder p × ControlRemainder p | z.1.1 = z.2.1} ∩
          {z : ControlRemainder p × ControlRemainder p | z.1.2 = z.2.2} := by
      ext z
      simp [Set.mem_diagonal_iff, Prod.ext_iff]
    rw [hdiag]
    exact hleft.inter hright

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩

local instance outcomeMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (AssignmentParameterFibreKernel.Outcome p) where
  measurableSet_diagonal := MeasurableSet.of_discrete

/-- The diagonal map retains one complete original `K+1` vector in both
coordinates. -/
def diagonalAssignmentMap (p : ConstructorDimensions.Parameters) :
    AssignmentVector p → AssignmentPair p := fun v => (v, v)

def diagonalControlMap (p : ConstructorDimensions.Parameters) :
    ContinuousLearningRows.TimeControl p → ControlPair p := fun c => (c, c)

theorem measurable_diagonalAssignmentMap (p : ConstructorDimensions.Parameters) :
    Measurable (diagonalAssignmentMap p) := by
  fun_prop [diagonalAssignmentMap]

theorem measurable_diagonalControlMap (p : ConstructorDimensions.Parameters) :
    Measurable (diagonalControlMap p) := by
  fun_prop [diagonalControlMap]

/-- The exact identity coupling used when the actual optional later selector
returns `none`: push forward the original complete assignment law along the
diagonal. -/
def diagonalAssignmentMeasure (p : ConstructorDimensions.Parameters) :
    Measure (AssignmentPair p) :=
  (ContinuousControlSlice.assignmentLaw p.K).map (diagonalAssignmentMap p)

/-- The total paired-vector measure over the genuine optional selector. The
absent branch is the original-law diagonal; no parameter is chosen there. -/
def optionalPairedMeasure (p : ConstructorDimensions.Parameters)
    (selected : Option (AssignmentParameterFibreKernel.Theta p)) :
    Measure (AssignmentPair p) :=
  match selected with
  | none => diagonalAssignmentMeasure p
  | some theta => ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta

private theorem measurable_optionElim {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  classical
  intro s hs
  change MeasurableSet[
    (inferInstance : MeasurableSpace (α ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit α)] ((fun o : Option α => o.elim b f) ⁻¹' s)
  rw [MeasurableSpace.measurableSet_comap]
  let someImage : Set (α ⊕ PUnit) := Sum.inl '' (f ⁻¹' s)
  let noneImage : Set (α ⊕ PUnit) :=
    if b ∈ s then Sum.inr '' ({PUnit.unit} : Set PUnit) else ∅
  have hsome : MeasurableSet someImage :=
    measurableSet_inl_image.mpr (hf hs)
  have hnone : MeasurableSet noneImage := by
    by_cases hb : b ∈ s
    · simp only [noneImage, ite_eq_left hb]
      exact measurableSet_inr_image.mpr (measurableSet_singleton PUnit.unit)
    · simp [noneImage, hb]
  refine ⟨someImage ∪ noneImage, hsome.union hnone, ?_⟩
  ext value
  cases value <;> simp [someImage, noneImage]

/-- The optional-parameter kernel before pulling it back to physical inputs.
Its measurable space is the actual inherited Borel `Option` space. -/
def optionalPairedKernel (p : ConstructorDimensions.Parameters) :
    Kernel (Option (AssignmentParameterFibreKernel.Theta p)) (AssignmentPair p) where
  toFun := optionalPairedMeasure p
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    change Measurable (fun selected => (optionalPairedMeasure p selected) s)
    have hfun :
        (fun selected => (optionalPairedMeasure p selected) s) =
          (fun selected => selected.elim (diagonalAssignmentMeasure p s)
            (fun theta => ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta s)) := by
      funext selected
      cases selected <;> rfl
    rw [hfun]
    exact measurable_optionElim
      (fun theta => ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta s)
      (by
        change Measurable (fun theta =>
          ReferenceLaterPhysicalFibreResampling.pairedKernel p theta s)
        exact (ReferenceLaterPhysicalFibreResampling.pairedKernel p).measurable_coe hs)
      (diagonalAssignmentMeasure p s)

instance optionalPairedKernel_isMarkovKernel (p : ConstructorDimensions.Parameters) :
    IsMarkovKernel (optionalPairedKernel p) where
  isProbabilityMeasure selected := by
    change IsProbabilityMeasure (optionalPairedMeasure p selected)
    cases selected with
    | none =>
        change IsProbabilityMeasure (diagonalAssignmentMeasure p)
        unfold diagonalAssignmentMeasure
        infer_instance
    | some theta =>
        exact ReferenceLaterPhysicalFibreResampling.pairedMeasure_isProbabilityMeasure
          p theta

@[simp] theorem optionalPairedKernel_apply (p : ConstructorDimensions.Parameters)
    (selected : Option (AssignmentParameterFibreKernel.Theta p)) :
    optionalPairedKernel p selected = optionalPairedMeasure p selected := by
  change (optionalPairedKernel p).toFun selected = _
  rfl

@[simp] theorem optionalPairedMeasure_none (p : ConstructorDimensions.Parameters) :
    optionalPairedMeasure p none = diagonalAssignmentMeasure p := rfl

@[simp] theorem optionalPairedMeasure_some (p : ConstructorDimensions.Parameters)
    (theta : AssignmentParameterFibreKernel.Theta p) :
    optionalPairedMeasure p (some theta) =
      ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta := rfl

/-- Pull the total optional coupling back along the accepted, unrestricted
Borel selector on the original physical `RoundInput`. -/
def pairedAssignmentKernel (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Kernel (ReferenceActivePhysicalStep.RoundInput p rate) (AssignmentPair p) :=
  (optionalPairedKernel p).comap
    ReferenceLaterSamplerParameterMeasurability.parameters?
    ReferenceLaterSamplerParameterMeasurability.measurable_parameters?

instance pairedAssignmentKernel_isMarkovKernel (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    IsMarkovKernel (pairedAssignmentKernel p rate) := by
  unfold pairedAssignmentKernel
  infer_instance

@[simp] theorem pairedAssignmentKernel_apply
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    pairedAssignmentKernel p rate x =
      optionalPairedMeasure p
        (ReferenceLaterSamplerParameterMeasurability.parameters? x) := by
  change (optionalPairedKernel p)
    (ReferenceLaterSamplerParameterMeasurability.parameters? x) = _
  rw [optionalPairedKernel_apply]

theorem pairedAssignmentKernel_apply_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hnone : ReferenceLaterSamplerParameterMeasurability.parameters? x = none) :
    pairedAssignmentKernel p rate x = diagonalAssignmentMeasure p := by
  rw [pairedAssignmentKernel_apply, hnone]
  rfl

theorem pairedAssignmentKernel_apply_some
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hsome : ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta) :
    pairedAssignmentKernel p rate x =
      ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta := by
  rw [pairedAssignmentKernel_apply, hsome]
  rfl

/-- On the actual some-call subtype, the total construction agrees exactly
with the already admitted actual paired kernel. -/
theorem pairedAssignmentKernel_eq_actualPairedKernel
    (call : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
      (p := p) (rate := rate)) :
    pairedAssignmentKernel p rate call.1 =
      ReferenceLaterSamplerParameterMeasurability.actualPairedKernel call := by
  have hselected : ReferenceLaterSamplerParameterMeasurability.parameters? call.1 =
      some (ReferenceLaterSamplerParameterMeasurability.actualParameter call) := by
    simp [ReferenceLaterSamplerParameterMeasurability.actualParameter]
  rw [pairedAssignmentKernel_apply_some call.1 _ hselected,
    ReferenceLaterSamplerParameterMeasurability.actualPairedKernel_apply]
  rfl

theorem pairedAssignmentKernel_fst
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (pairedAssignmentKernel p rate x).fst =
      ContinuousControlSlice.assignmentLaw p.K := by
  cases hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x with
  | none =>
      rw [pairedAssignmentKernel_apply_none x hselected]
      change (diagonalAssignmentMeasure p).map Prod.fst = _
      unfold diagonalAssignmentMeasure
      rw [Measure.map_map measurable_fst (measurable_diagonalAssignmentMap p)]
      change Measure.map (fun v : AssignmentVector p => v)
        (ContinuousControlSlice.assignmentLaw p.K) =
        ContinuousControlSlice.assignmentLaw p.K
      exact Measure.map_id
  | some theta =>
      let call : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
          (p := p) (rate := rate) := ⟨x, by simp [hselected]⟩
      rw [pairedAssignmentKernel_eq_actualPairedKernel call]
      exact ReferenceLaterSamplerParameterMeasurability.actualPairedKernel_fst call

theorem pairedAssignmentKernel_snd
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (pairedAssignmentKernel p rate x).snd =
      ContinuousControlSlice.assignmentLaw p.K := by
  cases hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x with
  | none =>
      rw [pairedAssignmentKernel_apply_none x hselected]
      change (diagonalAssignmentMeasure p).map Prod.snd = _
      unfold diagonalAssignmentMeasure
      rw [Measure.map_map measurable_snd (measurable_diagonalAssignmentMap p)]
      change Measure.map (fun v : AssignmentVector p => v)
        (ContinuousControlSlice.assignmentLaw p.K) =
        ContinuousControlSlice.assignmentLaw p.K
      exact Measure.map_id
  | some theta =>
      let call : ReferenceLaterSamplerParameterMeasurability.ActualSamplerCall
          (p := p) (rate := rate) := ⟨x, by simp [hselected]⟩
      rw [pairedAssignmentKernel_eq_actualPairedKernel call]
      exact ReferenceLaterSamplerParameterMeasurability.actualPairedKernel_snd call

theorem pairedAssignmentKernel_eq_of_state_eq_time_eq
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time) :
    pairedAssignmentKernel p rate x = pairedAssignmentKernel p rate y := by
  rw [pairedAssignmentKernel_apply, pairedAssignmentKernel_apply,
    ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
      x y hstate htime]

/-- Literal product law for the shared current-control remainder. Every
non-assignment label remains in its inherited `[0,1)` scalar carrier, and the
whole affine sample array retains all DOWN and UP channels. -/
def controlRemainderLaw (p : ConstructorDimensions.Parameters) :
    Measure (ControlRemainder p) :=
  (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)

instance controlRemainderLaw_isProbabilityMeasure (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (controlRemainderLaw p) := by
  unfold controlRemainderLaw
  infer_instance

/-- The source map takes one vector pair and one shared remainder, and uses
the exact inverse of the accepted original-control split for both controls. -/
def pairedControlConstruction (p : ConstructorDimensions.Parameters) :
    (AssignmentPair p × ControlRemainder p) → ControlPair p := fun z =>
  ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
      (z.1.1, z.2),
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
      (z.1.2, z.2))

theorem measurable_pairedControlConstruction (p : ConstructorDimensions.Parameters) :
    Measurable (pairedControlConstruction p) := by
  fun_prop [pairedControlConstruction]

/-- The full current-control Markov kernel: `Q` is independent of one shared
remainder with its literal product law, followed by the original inverse
coordinate split. -/
def pairedControlKernel (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Kernel (ReferenceActivePhysicalStep.RoundInput p rate) (ControlPair p) :=
  Kernel.map
    (Kernel.prod (pairedAssignmentKernel p rate)
      (Kernel.const (ReferenceActivePhysicalStep.RoundInput p rate)
        (controlRemainderLaw p)))
    (pairedControlConstruction p)

instance pairedControlKernel_isMarkovKernel (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    IsMarkovKernel (pairedControlKernel p rate) := by
  unfold pairedControlKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map
    (Kernel.prod (pairedAssignmentKernel p rate)
      (Kernel.const (ReferenceActivePhysicalStep.RoundInput p rate)
        (controlRemainderLaw p)))
    (measurable_pairedControlConstruction p)

theorem pairedControlKernel_apply
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    pairedControlKernel p rate x =
      ((pairedAssignmentKernel p rate x).prod (controlRemainderLaw p)).map
        (pairedControlConstruction p) := by
  change Kernel.map
      (Kernel.prod (pairedAssignmentKernel p rate)
        (Kernel.const (ReferenceActivePhysicalStep.RoundInput p rate)
          (controlRemainderLaw p)))
      (pairedControlConstruction p) x = _
  rw [Kernel.map_apply
    (Kernel.prod (pairedAssignmentKernel p rate)
      (Kernel.const (ReferenceActivePhysicalStep.RoundInput p rate)
        (controlRemainderLaw p)))
    (measurable_pairedControlConstruction p) x,
    Kernel.prod_apply, Kernel.const_apply]

theorem pairedControlKernel_apply_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hnone : ReferenceLaterSamplerParameterMeasurability.parameters? x = none) :
    pairedControlKernel p rate x =
      ((diagonalAssignmentMeasure p).prod (controlRemainderLaw p)).map
        (pairedControlConstruction p) := by
  rw [pairedControlKernel_apply, pairedAssignmentKernel_apply_none x hnone]

theorem pairedControlKernel_apply_none_eq_diagonalControlLaw
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hnone : ReferenceLaterSamplerParameterMeasurability.parameters? x = none) :
    pairedControlKernel p rate x =
      (ContinuousLearningRows.timeControlLaw p).map (diagonalControlMap p) := by
  rw [pairedControlKernel_apply_none x hnone]
  let source := (ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  have hsource : source.map e.symm = ContinuousLearningRows.timeControlLaw p :=
    (MeasurePreserving.symm e
      (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p)).map_eq
  calc
    ((diagonalAssignmentMeasure p).prod (controlRemainderLaw p)).map
        (pairedControlConstruction p) =
      (source.map (Prod.map (diagonalAssignmentMap p) id)).map
        (pairedControlConstruction p) := by
          change (((ContinuousControlSlice.assignmentLaw p.K).map
            (diagonalAssignmentMap p)).prod (controlRemainderLaw p)).map
              (pairedControlConstruction p) = _
          rw [← Measure.map_prod_map
            (ContinuousControlSlice.assignmentLaw p.K) (controlRemainderLaw p)
            (measurable_diagonalAssignmentMap p) measurable_id]
          simp
    _ = source.map (diagonalControlMap p ∘ e.symm) := by
          rw [Measure.map_map (measurable_pairedControlConstruction p)
            (by fun_prop [diagonalAssignmentMap])]
          have hmap :
              pairedControlConstruction p ∘ Prod.map (diagonalAssignmentMap p) id =
                diagonalControlMap p ∘ e.symm := by
            funext z
            rcases z with ⟨v, remainder⟩
            rfl
          rw [hmap]
    _ = (source.map e.symm).map (diagonalControlMap p) := by
          rw [← Measure.map_map (measurable_diagonalControlMap p) e.symm.measurable]
    _ = (ContinuousLearningRows.timeControlLaw p).map (diagonalControlMap p) := by
          rw [hsource]

theorem pairedControlKernel_apply_some
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hsome : ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta) :
    pairedControlKernel p rate x =
      ((ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta).prod
        (controlRemainderLaw p)).map (pairedControlConstruction p) := by
  rw [pairedControlKernel_apply, pairedAssignmentKernel_apply_some x theta hsome]

private theorem map_firstControlFromProduct
    (μ : Measure (AssignmentPair p)) :
    (μ.prod (controlRemainderLaw p)).map
        (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          (z.1.1, z.2)) =
      ((μ.map Prod.fst).prod (controlRemainderLaw p)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
  calc
    (μ.prod (controlRemainderLaw p)).map
        (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          (z.1.1, z.2)) =
      ((μ.prod (controlRemainderLaw p)).map (Prod.map Prod.fst id)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
          change (μ.prod (controlRemainderLaw p)).map
              ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm ∘
                Prod.map Prod.fst id) = _
          rw [← Measure.map_map
            (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm.measurable
            (by fun_prop)]
    _ = ((μ.map Prod.fst).prod (controlRemainderLaw p)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
          rw [← Measure.map_prod_map μ (controlRemainderLaw p)
            measurable_fst measurable_id]
          simp

private theorem map_secondControlFromProduct
    (μ : Measure (AssignmentPair p)) :
    (μ.prod (controlRemainderLaw p)).map
        (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          (z.1.2, z.2)) =
      ((μ.map Prod.snd).prod (controlRemainderLaw p)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
  calc
    (μ.prod (controlRemainderLaw p)).map
        (fun z => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          (z.1.2, z.2)) =
      ((μ.prod (controlRemainderLaw p)).map (Prod.map Prod.snd id)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
          change (μ.prod (controlRemainderLaw p)).map
              ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm ∘
                Prod.map Prod.snd id) = _
          rw [← Measure.map_map
            (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm.measurable
            (by fun_prop)]
    _ = ((μ.map Prod.snd).prod (controlRemainderLaw p)).map
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm := by
          rw [← Measure.map_prod_map μ (controlRemainderLaw p)
            measurable_snd measurable_id]
          simp

theorem pairedControlKernel_fst
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (pairedControlKernel p rate x).map Prod.fst =
      ContinuousLearningRows.timeControlLaw p := by
  rw [pairedControlKernel_apply]
  rw [Measure.map_map measurable_fst (measurable_pairedControlConstruction p)]
  change Measure.map
    (fun z : AssignmentPair p × ControlRemainder p =>
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (z.1.1, z.2))
    ((pairedAssignmentKernel p rate x).prod (controlRemainderLaw p)) = _
  rw [map_firstControlFromProduct]
  have hfst : Measure.map Prod.fst (pairedAssignmentKernel p rate x) =
      ContinuousControlSlice.assignmentLaw p.K := pairedAssignmentKernel_fst x
  rw [hfst]
  have hsplit := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  exact (MeasurePreserving.symm
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) hsplit).map_eq

theorem pairedControlKernel_snd
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (pairedControlKernel p rate x).map Prod.snd =
      ContinuousLearningRows.timeControlLaw p := by
  rw [pairedControlKernel_apply]
  rw [Measure.map_map measurable_snd (measurable_pairedControlConstruction p)]
  change Measure.map
    (fun z : AssignmentPair p × ControlRemainder p =>
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (z.1.2, z.2))
    ((pairedAssignmentKernel p rate x).prod (controlRemainderLaw p)) = _
  rw [map_secondControlFromProduct]
  have hsnd : Measure.map Prod.snd (pairedAssignmentKernel p rate x) =
      ContinuousControlSlice.assignmentLaw p.K := pairedAssignmentKernel_snd x
  rw [hsnd]
  have hsplit := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  exact (MeasurePreserving.symm
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) hsplit).map_eq

/-- Replace only the current selected row's `TimeControl`. The state, selected
index, calendar time, active proof, reward table, every other row, the selected
row's forward array, and every other time control are the original coordinates.
-/
def withControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  { x with rows := (Function.update x.rows x.selected
      (x.row.1, Function.update x.row.2 x.time c)) }

@[simp] theorem withControl_state
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) : (withControl x c).state = x.state := rfl

@[simp] theorem withControl_selected
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    (withControl x c).selected = x.selected := rfl

@[simp] theorem withControl_time
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) : (withControl x c).time = x.time := rfl

@[simp] theorem withControl_rewards
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    (withControl x c).rewards = x.rewards := rfl

@[simp] theorem withControl_active
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) : (withControl x c).active = x.active := rfl

@[simp] theorem withControl_row
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    (withControl x c).row = (x.row.1, Function.update x.row.2 x.time c) := by
  exact Function.update_self _ _ _

theorem withControl_otherRow
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) (q : Fin (ConstructorDimensions.M p))
    (hq : q ≠ x.selected) : (withControl x c).rows q = x.rows q := by
  simpa [withControl] using (Function.update_of_ne hq _ _)

theorem withControl_forwardArray
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    ((withControl x c).row).1 = x.row.1 := by
  rw [withControl_row]

theorem withControl_otherTime
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (ht : t ≠ x.time) :
    ((withControl x c).row).2 t = x.row.2 t := by
  rw [withControl_row]
  exact Function.update_of_ne ht _ _

@[simp] theorem withControl_currentControl
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    ((withControl x c).row).2 x.time = c := by
  rw [withControl_row]
  exact Function.update_self _ _ _

theorem parameters?_withControl
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceLaterSamplerParameterMeasurability.parameters? (withControl x c) =
      ReferenceLaterSamplerParameterMeasurability.parameters? x :=
  (ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
    x (withControl x c) rfl rfl).symm

/-- A present later-sampler parameter can only come from the literal
collection branch of the existing physical selector. -/
theorem parameters?_eq_some_implies_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (_hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x = some theta) :
    ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal := by
  cases hcoord : x.state.coordinator with
  | first =>
      simp [ReferenceLaterSamplerParameterMeasurability.parameters?,
        ReferenceLaterAssignmentFibreStep.parameters?, hcoord] at _hselected
  | live registers owned baseScores =>
      simp [ReferenceLaterSamplerParameterMeasurability.parameters?,
        ReferenceLaterAssignmentFibreStep.parameters?, hcoord] at _hselected
  | dagger =>
      simp [ReferenceLaterSamplerParameterMeasurability.parameters?,
        ReferenceLaterAssignmentFibreStep.parameters?, hcoord] at _hselected
  | collection payload ledger proposal =>
      exact ⟨payload, ledger, proposal, rfl⟩

private theorem controlWithAssignment_withControl
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceLaterAssignmentFibreStep.controlWithAssignment (withControl x c) v =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (v, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2) := by
  unfold ReferenceLaterAssignmentFibreStep.controlWithAssignment
  rw [withControl_time, withControl_currentControl]

/-- Exact assignment replacement after a literal control update. The original
shared remainder of `c` is retained by the accepted split. -/
theorem withAssignment_withControl
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ContinuousLearningRows.TimeControl p)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceLaterAssignmentFibreStep.withAssignment (withControl x c) v =
      withControl x
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          (v, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2)) := by
  cases x with
  | mk state rows selected time active rewards =>
      let x₀ := ReferenceActivePhysicalStep.RoundInput.mk state rows selected time active rewards
      have hcontrol : ReferenceLaterAssignmentFibreStep.controlWithAssignment
          (withControl x₀ c) v =
            (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
              (v, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2) :=
        controlWithAssignment_withControl x₀ c v
      apply congrArg (fun rs =>
        (ReferenceActivePhysicalStep.RoundInput.mk state rs selected time active rewards))
      funext q
      by_cases hq : q = selected
      · subst q
        simp only [ReferenceLaterAssignmentFibreStep.rowWithAssignment,
          withControl_selected, withControl_row, withControl_time,
          Function.update_self]
        rw [hcontrol]
        apply Prod.ext
        · rfl
        · exact @Function.update_idem (Fin p.T) _
            (fun _ => ContinuousLearningRows.TimeControl p) time c
            ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
              (v, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2))
            (rows selected).2
      · simp [withControl,
          ReferenceLaterAssignmentFibreStep.rowWithAssignment, hq]

/-- The measurable event certifying a common shared remainder and the exact
same checked outcome for the actual optional selector. In the absent branch
the certificate is literal equality of full assignment vectors. -/
def pairedControlFibreEvent
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Set (ControlPair p) :=
  {z | (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).2 =
         (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).2 ∧
         match ReferenceLaterSamplerParameterMeasurability.parameters? x with
         | none =>
             (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).1 =
               (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).1
         | some theta =>
             AssignmentParameterFibreKernel.successfulSlowSet p theta
                 (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).1 =
               AssignmentParameterFibreKernel.successfulSlowSet p theta
                 (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).1}

theorem measurableSet_pairedControlFibreEvent
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    MeasurableSet (pairedControlFibreEvent x) := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  have hleft : Measurable (fun z : ControlPair p => e z.1) :=
    e.measurable.comp measurable_fst
  have hright : Measurable (fun z : ControlPair p => e z.2) :=
    e.measurable.comp measurable_snd
  have hrem : MeasurableSet {z : ControlPair p | (e z.1).2 = (e z.2).2} :=
    measurableSet_eq_fun (measurable_snd.comp hleft) (measurable_snd.comp hright)
  cases hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x with
  | none =>
      have hv : MeasurableSet {z : ControlPair p | (e z.1).1 = (e z.2).1} :=
        measurableSet_eq_fun (measurable_fst.comp hleft) (measurable_fst.comp hright)
      rw [pairedControlFibreEvent, hselected]
      exact hrem.inter hv
  | some theta =>
      have hslowLeft : Measurable (fun z : ControlPair p =>
          AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.1).1) :=
        (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
          (measurable_const.prodMk (measurable_fst.comp hleft))
      have hslowRight : Measurable (fun z : ControlPair p =>
          AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.2).1) :=
        (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
          (measurable_const.prodMk (measurable_fst.comp hright))
      have hslow : MeasurableSet {z : ControlPair p |
          AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.1).1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.2).1} :=
        measurableSet_eq_fun hslowLeft hslowRight
      rw [pairedControlFibreEvent, hselected]
      exact hrem.inter hslow

private theorem ae_prod_firstCoordinate
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {q : α → Prop}
    (hq : MeasurableSet {x | q x})
    (h : ∀ᵐ x ∂μ, q x) :
    ∀ᵐ z ∂μ.prod ν, q z.1 := by
  have hset : MeasurableSet {z : α × β | q z.1 ∧ True} :=
    (hq.preimage measurable_fst).inter MeasurableSet.univ
  have hconj : ∀ᵐ z ∂μ.prod ν, q z.1 ∧ True := by
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [h] with x hx
    filter_upwards [Filter.Eventually.of_forall (fun _ : β => trivial)] with y hy
    exact ⟨hx, hy⟩
  exact hconj.mono fun _ hz => hz.1

theorem ae_pairedControlFibreEvent
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ∀ᵐ z ∂pairedControlKernel p rate x, z ∈ pairedControlFibreEvent x := by
  rw [pairedControlKernel_apply]
  apply (ae_map_iff (measurable_pairedControlConstruction p).aemeasurable
    (measurableSet_pairedControlFibreEvent x)).2
  cases hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x with
  | none =>
      rw [pairedAssignmentKernel_apply_none x hselected]
      have hvMeas : MeasurableSet {q : AssignmentPair p | q.1 = q.2} :=
        measurableSet_eq_fun measurable_fst measurable_snd
      have hv : ∀ᵐ q ∂diagonalAssignmentMeasure p, q.1 = q.2 := by
        change ∀ᵐ q ∂
          (ContinuousControlSlice.assignmentLaw p.K).map (diagonalAssignmentMap p), _
        rw [ae_map_iff (measurable_diagonalAssignmentMap p).aemeasurable hvMeas]
        filter_upwards using fun v => rfl
      have hproduct := ae_prod_firstCoordinate
        (diagonalAssignmentMeasure p) (controlRemainderLaw p) hvMeas hv
      filter_upwards [hproduct] with z hz
      rcases z with ⟨⟨v, w⟩, remainder⟩
      have hvw : v = w := by simpa using hz
      simp [pairedControlConstruction, hvw]
  | some theta =>
      have hslowMeas : MeasurableSet {q : AssignmentPair p |
          AssignmentParameterFibreKernel.successfulSlowSet p theta q.1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta q.2} := by
        have hleftMap : Measurable (fun q : AssignmentPair p => (theta, q.1)) :=
          measurable_const.prodMk measurable_fst
        have hrightMap : Measurable (fun q : AssignmentPair p => (theta, q.2)) :=
          measurable_const.prodMk measurable_snd
        have hl := (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
          hleftMap
        have hr := (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
          hrightMap
        exact measurableSet_eq_fun hl hr
      have hslow : ∀ᵐ q ∂pairedAssignmentKernel p rate x,
          AssignmentParameterFibreKernel.successfulSlowSet p theta q.1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta q.2 := by
        rw [pairedAssignmentKernel_apply_some x theta hselected]
        change ∀ᵐ q ∂ReferenceLaterPhysicalFibreResampling.pairedMeasure p theta, _
        exact ReferenceLaterPhysicalFibreResampling.ae_successfulSlowSet_eq p theta
      have hproduct := ae_prod_firstCoordinate
        (pairedAssignmentKernel p rate x) (controlRemainderLaw p) hslowMeas hslow
      filter_upwards [hproduct] with z hz
      rcases z with ⟨⟨v, w⟩, remainder⟩
      simp [pairedControlConstruction, hz]

/-- Any control pair in the measurable fibre event has equal actual physical
effects. The some branch derives the incoming collection phase from the
literal optional selector and applies the admitted later-fibre assembly to
the base input formed from the left vector and the shared remainder. -/
theorem pairedControlFibreEvent_effects
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (z : ControlPair p) (hz : z ∈ pairedControlFibreEvent x) :
    ReferenceActivePhysicalHorizon.computedEvidence (withControl x z.1) =
        ReferenceActivePhysicalHorizon.computedEvidence (withControl x z.2) ∧
      let left := ReferenceActivePhysicalStep.step (withControl x z.1)
      let right := ReferenceActivePhysicalStep.step (withControl x z.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let leftSplit := e z.1
  let rightSplit := e z.2
  have hgood : leftSplit.2 = rightSplit.2 ∧
      match ReferenceLaterSamplerParameterMeasurability.parameters? x with
      | none => leftSplit.1 = rightSplit.1
      | some theta =>
          AssignmentParameterFibreKernel.successfulSlowSet p theta leftSplit.1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta rightSplit.1 := by
    simpa [pairedControlFibreEvent, leftSplit, rightSplit, e] using hz
  cases hselected : ReferenceLaterSamplerParameterMeasurability.parameters? x with
  | none =>
      have hvec : leftSplit.1 = rightSplit.1 := by simpa [hselected] using hgood.2
      have hsplit : e z.1 = e z.2 := by
        exact Prod.ext hvec hgood.1
      have hcontrols : z.1 = z.2 := e.injective hsplit
      rcases z with ⟨leftControl, rightControl⟩
      have hcontrols' : leftControl = rightControl := by simpa using hcontrols
      subst rightControl
      exact ⟨rfl, by simp⟩
  | some theta =>
      obtain ⟨payload, ledger, proposal, hphase⟩ :=
        parameters?_eq_some_implies_collection x theta hselected
      let base := withControl x z.1
      have hbaseParameter :
          ReferenceLaterSamplerParameterMeasurability.parameters? base = some theta := by
        rw [parameters?_withControl, hselected]
      have hbasePhase : base.state.coordinator = .collection payload ledger proposal := by
        simpa [base, withControl_state] using hphase
      have hleftInput : ReferenceLaterAssignmentFibreStep.withAssignment base leftSplit.1 =
          withControl x z.1 := by
        dsimp [base, leftSplit]
        rw [withAssignment_withControl]
        congr 1
        simpa only [Prod.eta] using
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply z.1
      have hrightInput : ReferenceLaterAssignmentFibreStep.withAssignment base rightSplit.1 =
          withControl x z.2 := by
        dsimp [base, leftSplit, rightSplit]
        rw [withAssignment_withControl]
        rw [hgood.1]
        congr 1
        exact (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply z.2
      have hsuccess :
          AssignmentParameterFibreKernel.successfulSlowSet p theta leftSplit.1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta rightSplit.1 := by
        simpa [hselected] using hgood.2
      have he := ReferenceLaterPhysicalFibreAssembly.computedEvidence_later_fibre
        base payload ledger proposal hbasePhase leftSplit.1 rightSplit.1 (by
          change ReferenceLaterAssignmentFibreStep.parameters? base = some theta at hbaseParameter
          rw [hbaseParameter]
          exact hsuccess)
      have hs := ReferenceLaterPhysicalFibreAssembly.step_projections_later_fibre
        base payload ledger proposal hbasePhase leftSplit.1 rightSplit.1 (by
          change ReferenceLaterAssignmentFibreStep.parameters? base = some theta at hbaseParameter
          rw [hbaseParameter]
          exact hsuccess)
      rw [hleftInput, hrightInput] at he hs
      exact ⟨he, hs⟩

theorem ae_pairedControl_effects
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ∀ᵐ z ∂pairedControlKernel p rate x,
      ReferenceActivePhysicalHorizon.computedEvidence (withControl x z.1) =
          ReferenceActivePhysicalHorizon.computedEvidence (withControl x z.2) ∧
        let left := ReferenceActivePhysicalStep.step (withControl x z.1)
        let right := ReferenceActivePhysicalStep.step (withControl x z.2)
        left.next = right.next ∧
          left.preparation.arms.actions = right.preparation.arms.actions ∧
          left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
          left.ownEntries = right.ownEntries ∧
          left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  filter_upwards [ae_pairedControlFibreEvent x] with z hz
  exact pairedControlFibreEvent_effects x z hz

theorem ae_pairedControl_nonAssignmentScalars_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ∀ᵐ z ∂pairedControlKernel p rate x,
      ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).2.1 label) =
          ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).2.1 label) := by
  filter_upwards [ae_pairedControlFibreEvent x] with z hz
  have hrem :
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).2 := hz.1
  intro label
  exact congrArg (fun r : ControlRemainder p => r.1 label) hrem

theorem ae_pairedControl_affineSamples_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ∀ᵐ z ∂pairedControlKernel p rate x,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).2.2 := by
  filter_upwards [ae_pairedControlFibreEvent x] with z hz
  exact congrArg Prod.snd hz.1

theorem ae_pairedControl_affineChannel_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ∀ᵐ z ∂pairedControlKernel p rate x,
      ∀ direction : Fin 2, ∀ follower : Fin (p.m - 1),
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.1).2.2
            (direction, follower) =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2).2.2
            (direction, follower) := by
  filter_upwards [ae_pairedControl_affineSamples_eq x] with z hz
  intro direction follower
  exact congrFun hz (direction, follower)

end Bandits.Support.ReferenceLaterOptionalControlResampling

end
