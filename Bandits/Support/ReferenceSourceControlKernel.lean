/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFixedTimeSourceControlCoupling

/-!
# Measurable kernel for the fixed-boundary original-source coupling

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-423`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42`.

The fixed-boundary source-pair law is assembled into a Markov kernel by a
finite partition over the actual calendar time and original private row
index. Its source certificate is proved jointly Borel in the boundary and
both complete original sources. This does not establish a chronological
incoming-boundary law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceLaterOptionalControlResampling
open scoped Classical

namespace Bandits.Support.ReferenceSourceControlKernel

abbrev Parameters := ReferenceFixedTimeSourceControlCoupling.Parameters
abbrev SourceInput := ReferenceFixedTimeSourceControlCoupling.SourceInput
abbrev RoundInput := ReferenceFixedTimeSourceControlCoupling.RoundInput

private instance measurableEqContinuousScalar :
    MeasurableEq ContinuousLearningRows.Scalar where
  measurableSet_diagonal := by
    have hreal : MeasurableSet {z : ContinuousLearningRows.Scalar ×
        ContinuousLearningRows.Scalar | (z.1 : ℝ) = (z.2 : ℝ)} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hset : {z : ContinuousLearningRows.Scalar ×
        ContinuousLearningRows.Scalar | z.1 = z.2} =
        {z | (z.1 : ℝ) = (z.2 : ℝ)} := by
      ext z
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [Set.diagonal, hset]
    exact hreal

private instance measurableEqProd {α β : Type*} [MeasurableSpace α] [MeasurableEq α]
    [MeasurableSpace β] [MeasurableEq β] : MeasurableEq (α × β) where
  measurableSet_diagonal := by
    have hleft : MeasurableSet {z : (α × β) × (α × β) | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hright : MeasurableSet {z : (α × β) × (α × β) | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hdiag : Set.diagonal (α × β) =
        {z : (α × β) × (α × β) | z.1.1 = z.2.1} ∩
          {z : (α × β) × (α × β) | z.1.2 = z.2.2} := by
      ext z
      simp [Set.mem_diagonal_iff, Prod.ext_iff]
    rw [hdiag]
    exact hleft.inter hright

private instance measurableEqPi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableEq (α i)] :
    MeasurableEq (∀ i, α i) where
  measurableSet_diagonal := by
    classical
    have hdiag : Set.diagonal (∀ i, α i) =
        ⋂ i, {z : (∀ i, α i) × (∀ i, α i) | z.1 i = z.2 i} := by
      ext z
      simp [Set.mem_diagonal_iff, funext_iff]
    rw [hdiag]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (by fun_prop) (by fun_prop)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace (p : Parameters) :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace (p : Parameters) :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩

local instance optionOutcomeMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (AssignmentParameterFibreKernel.Outcome p)) :=
  @LaterAssignmentStartMeasurability.optionMeasurableSpace
    (AssignmentParameterFibreKernel.Outcome p) (outcomeMeasurableSpace p)

private instance measurableSingletonOptionOutcome (p : Parameters) :
    MeasurableSingletonClass (Option (AssignmentParameterFibreKernel.Outcome p)) where
  measurableSet_singleton value := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace
        (AssignmentParameterFibreKernel.Outcome p ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit (AssignmentParameterFibreKernel.Outcome p))]
      ({value} : Set (Option (AssignmentParameterFibreKernel.Outcome p)))
    rw [MeasurableSpace.measurableSet_comap]
    cases value with
    | none =>
        refine ⟨{Sum.inr PUnit.unit}, ?_, ?_⟩
        · convert measurableSet_inr_image.mpr
            (measurableSet_singleton PUnit.unit) using 1
          ext y
          simp
        · ext y
          cases y <;> simp
    | some a =>
        refine ⟨{Sum.inl a}, ?_, ?_⟩
        · convert measurableSet_inl_image.mpr (measurableSet_singleton a) using 1
          ext y
          simp
        · ext y
          cases y <;> simp

private instance measurableEqOptionOutcome (p : Parameters) :
    MeasurableEq (Option (AssignmentParameterFibreKernel.Outcome p)) := by
  infer_instance

private def timeCell (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T) : Set (RoundInput p rate) := {b | b.time = t}

theorem measurableSet_timeCell (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    MeasurableSet {b : RoundInput p rate | b.time = t} :=
  ReferenceActivePhysicalStepMeasurability.measurable_time
    (measurableSet_singleton t)

/-- One fixed-time, fixed-original-`J` summand. -/
def sourcePairKernelSummand (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (q : Fin (M p)) (t : Fin p.T) :
    Kernel (RoundInput p rate) (SourceInput p × SourceInput p) :=
  Kernel.map
    ((ReferenceLaterOptionalControlResampling.pairedControlKernel p rate).prod
      (Kernel.const (RoundInput p rate)
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
          (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t))))
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSourcePairMap p q t)

/-- The full original-source pair kernel, selected by the canonical calendar
time and summed over the original private coordinator row. Each remainder is
restricted to its genuine `J=q` stratum without normalization. -/
def pairedSourceKernel (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Kernel (RoundInput p rate) (SourceInput p × SourceInput p) :=
  Kernel.sum fun t : Fin p.T =>
    Kernel.sum fun q : Fin (M p) =>
      Kernel.piecewise (measurableSet_timeCell p rate t)
        (sourcePairKernelSummand p rate q t) 0

private theorem sourcePairKernelSummand_apply (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (q : Fin (M p)) (t : Fin p.T) (b : RoundInput p rate)
    (ht : b.time = t) :
    sourcePairKernelSummand p rate q t b =
      ReferenceFixedTimeSourceControlCoupling.fixedControlSourcePairSummand
        p rate b q := by
  rw [sourcePairKernelSummand,
    Kernel.map_apply _
      (ReferenceFixedTimeSourceControlCoupling.measurable_fixedControlSourcePairMap
        p q t) b,
    Kernel.prod_apply, Kernel.const_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSourcePairSummand]
  rw [ht]

/-- Pointwise, the kernel is exactly the admitted measure-valued
fixed-boundary original-source coupling. -/
theorem pairedSourceKernel_apply (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : RoundInput p rate) :
    pairedSourceKernel p rate b =
      ReferenceFixedTimeSourceControlCoupling.pairedSourceLaw p rate b := by
  classical
  rw [pairedSourceKernel, Kernel.sum_apply, Measure.sum_fintype]
  simp_rw [Kernel.sum_apply, Measure.sum_fintype]
  rw [ReferenceFixedTimeSourceControlCoupling.pairedSourceLaw, Measure.sum_fintype]
  ext s hs
  rw [Finset.sum_eq_single b.time]
  · simp only [Kernel.piecewise_apply, Set.mem_ofPred_eq, ite_true]
    rw [Measure.finsetSum_apply, Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro q hq
    exact congrArg (fun μ : Measure (SourceInput p × SourceInput p) => μ s)
      (sourcePairKernelSummand_apply p rate q b.time b rfl)
  · intro t ht hne
    apply Finset.sum_eq_zero
    intro q hq
    rw [Kernel.piecewise_apply]
    simp only [Set.mem_ofPred_eq]
    split_ifs with heq
    · exact False.elim (hne heq.symm)
    · rfl
  · simp

/-- The kernel property exports Borel evaluation in the boundary for every
measurable source-pair event. -/
theorem measurable_pairedSourceKernel_eval (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {s : Set (SourceInput p × SourceInput p)} (hs : MeasurableSet s) :
    Measurable (fun b => pairedSourceKernel p rate b s) :=
  (pairedSourceKernel p rate).measurable_coe hs

instance pairedSourceKernel_isMarkovKernel (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    IsMarkovKernel (pairedSourceKernel p rate) where
  isProbabilityMeasure b := by
    rw [pairedSourceKernel_apply]
    exact ⟨by
      rw [ReferenceFixedTimeSourceControlCoupling.pairedSourceLaw_mass]
    ⟩

/-- The first source marginal is the original complete source law at every
boundary. -/
theorem pairedSourceKernel_fst (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Kernel.map (pairedSourceKernel p rate) Prod.fst =
      Kernel.const (RoundInput p rate)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  ext b s hs
  rw [Kernel.map_apply' _ measurable_fst b hs, Kernel.const_apply,
    ← ReferenceFixedTimeSourceControlCoupling.pairedSourceLaw_fst p rate b,
    Measure.map_apply measurable_fst hs, pairedSourceKernel_apply]

/-- The second source marginal is the original complete source law at every
boundary. -/
theorem pairedSourceKernel_snd (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Kernel.map (pairedSourceKernel p rate) Prod.snd =
      Kernel.const (RoundInput p rate)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  ext b s hs
  rw [Kernel.map_apply' _ measurable_snd b hs, Kernel.const_apply,
    ← ReferenceFixedTimeSourceControlCoupling.pairedSourceLaw_snd p rate b,
    Measure.map_apply measurable_snd hs, pairedSourceKernel_apply]

private theorem measurable_optionMapDependent {X A C : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace C]
    (f : A × X → C) (hf : Measurable f) (g : X → Option A) (hg : Measurable g) :
    Measurable (fun x => (g x).map fun a => f (a, x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x => Equiv.optionEquivSumPUnit C
    ((g x).map fun a => f (a, x)))
  have hsource : Measurable (fun x => Equiv.optionEquivSumPUnit A (g x)) :=
    measurable_comap_iff.mp hg
  let distrib := MeasurableEquiv.sumProdDistrib A PUnit X
  let left : A × X → C ⊕ PUnit := fun z => Sum.inl (f z)
  let right : PUnit × X → C ⊕ PUnit := fun _ => Sum.inr PUnit.unit
  have hleft : Measurable left := measurable_inl.comp hf
  have hright : Measurable right := measurable_const
  let lift : (A ⊕ PUnit) × X → C ⊕ PUnit :=
    fun z => Sum.elim left right (distrib z)
  have hlift : Measurable lift := (hleft.sumElim hright).comp distrib.measurable_toFun
  have hpair : Measurable (fun x => (Equiv.optionEquivSumPUnit A (g x), x)) :=
    hsource.prodMk measurable_id
  have heq : (fun x => Equiv.optionEquivSumPUnit C
      ((g x).map fun a => f (a, x))) = lift ∘ fun x =>
        (Equiv.optionEquivSumPUnit A (g x), x) := by
    funext x
    cases h : g x <;> simp [h, lift, left, right, distrib,
      Equiv.optionEquivSumPUnit, MeasurableEquiv.sumProdDistrib,
      Equiv.sumProdDistrib, Sum.map]
  rw [heq]
  exact hlift.comp hpair

private abbrev JointControlDomain (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  RoundInput p rate × ReferenceLaterOptionalControlResampling.ControlPair p

private theorem measurableSet_jointControlFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    MeasurableSet {z : JointControlDomain p rate |
      z.2 ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent z.1} := by
  classical
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let leftControl : JointControlDomain p rate → ContinuousLearningRows.TimeControl p :=
    fun z => z.2.1
  let rightControl : JointControlDomain p rate → ContinuousLearningRows.TimeControl p :=
    fun z => z.2.2
  let leftSplit : JointControlDomain p rate →
      AssignmentParameterFibreKernel.AssignmentVector p ×
        ReferenceLaterOptionalControlResampling.ControlRemainder p :=
    fun z => e (leftControl z)
  let rightSplit : JointControlDomain p rate →
      AssignmentParameterFibreKernel.AssignmentVector p ×
        ReferenceLaterOptionalControlResampling.ControlRemainder p :=
    fun z => e (rightControl z)
  have hleftControl : Measurable leftControl := by
    exact measurable_fst.comp measurable_snd
  have hrightControl : Measurable rightControl := by
    exact measurable_snd.comp measurable_snd
  have hleftSplit : Measurable leftSplit := e.measurable.comp hleftControl
  have hrightSplit : Measurable rightSplit := e.measurable.comp hrightControl
  let leftVector : JointControlDomain p rate →
      AssignmentParameterFibreKernel.AssignmentVector p := fun z => (leftSplit z).1
  let rightVector : JointControlDomain p rate →
      AssignmentParameterFibreKernel.AssignmentVector p := fun z => (rightSplit z).1
  have hleftVector : Measurable leftVector := measurable_fst.comp hleftSplit
  have hrightVector : Measurable rightVector := measurable_fst.comp hrightSplit
  have hremainders : MeasurableSet {z : JointControlDomain p rate |
      (leftSplit z).2 = (rightSplit z).2} :=
    measurableSet_eq_fun (measurable_snd.comp hleftSplit)
      (measurable_snd.comp hrightSplit)
  have hvectors : MeasurableSet {z : JointControlDomain p rate |
      leftVector z = rightVector z} :=
    measurableSet_eq_fun hleftVector hrightVector
  let selected : JointControlDomain p rate →
      Option (AssignmentParameterFibreKernel.Theta p) :=
    fun z => ReferenceLaterSamplerParameterMeasurability.parameters? z.1
  have hselected : Measurable selected :=
    ReferenceLaterSamplerParameterMeasurability.measurable_parameters?.comp measurable_fst
  have hselectedNone : MeasurableSet {z : JointControlDomain p rate |
      selected z = none} := by
    exact (ReferenceLaterSamplerParameterMeasurability.measurableSet_parameters?_eq_none
      (p := p) (rate := rate)).preimage measurable_fst
  have hselectedSome : MeasurableSet {z : JointControlDomain p rate |
      (selected z).isSome} := by
    exact (ReferenceLaterSamplerParameterMeasurability.measurableSet_parameters?_isSome
      (p := p) (rate := rate)).preimage measurable_fst
  let leftOutcome : JointControlDomain p rate →
      Option (AssignmentParameterFibreKernel.Outcome p) := fun z =>
    (selected z).map fun theta =>
      AssignmentParameterFibreKernel.successfulSlowSet p theta (leftVector z)
  let rightOutcome : JointControlDomain p rate →
      Option (AssignmentParameterFibreKernel.Outcome p) := fun z =>
    (selected z).map fun theta =>
      AssignmentParameterFibreKernel.successfulSlowSet p theta (rightVector z)
  have hleftOutcomeInput : Measurable (fun w :
      AssignmentParameterFibreKernel.Theta p × JointControlDomain p rate =>
        (w.1, leftVector w.2)) :=
    measurable_fst.prodMk (hleftVector.comp measurable_snd)
  have hrightOutcomeInput : Measurable (fun w :
      AssignmentParameterFibreKernel.Theta p × JointControlDomain p rate =>
        (w.1, rightVector w.2)) :=
    measurable_fst.prodMk (hrightVector.comp measurable_snd)
  have hleftOutcome : Measurable leftOutcome := by
    exact measurable_optionMapDependent
      (fun w : AssignmentParameterFibreKernel.Theta p × JointControlDomain p rate =>
        AssignmentParameterFibreKernel.successfulSlowSet p w.1 (leftVector w.2))
      ((AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
        hleftOutcomeInput)
      selected hselected
  have hrightOutcome : Measurable rightOutcome := by
    exact measurable_optionMapDependent
      (fun w : AssignmentParameterFibreKernel.Theta p × JointControlDomain p rate =>
        AssignmentParameterFibreKernel.successfulSlowSet p w.1 (rightVector w.2))
      ((AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
        hrightOutcomeInput)
      selected hselected
  have houtcomeEq : MeasurableSet {z : JointControlDomain p rate |
      leftOutcome z = rightOutcome z} :=
    measurableSet_eq_fun hleftOutcome hrightOutcome
  have hselectedClause : MeasurableSet {z : JointControlDomain p rate |
      match selected z with
      | none => leftVector z = rightVector z
      | some theta =>
          AssignmentParameterFibreKernel.successfulSlowSet p theta (leftVector z) =
            AssignmentParameterFibreKernel.successfulSlowSet p theta (rightVector z)} := by
    have hsplit : {z : JointControlDomain p rate |
        match selected z with
        | none => leftVector z = rightVector z
        | some theta =>
            AssignmentParameterFibreKernel.successfulSlowSet p theta (leftVector z) =
              AssignmentParameterFibreKernel.successfulSlowSet p theta (rightVector z)} =
        ({z | selected z = none} ∩ {z | leftVector z = rightVector z}) ∪
        ({z | (selected z).isSome} ∩ {z | leftOutcome z = rightOutcome z}) := by
      ext z
      cases h : selected z <;> simp [h, leftOutcome, rightOutcome]
    rw [hsplit]
    exact hselectedNone.inter hvectors |>.union (hselectedSome.inter houtcomeEq)
  change MeasurableSet {z : JointControlDomain p rate |
    (e z.2.1).2 = (e z.2.2).2 ∧
      match ReferenceLaterSamplerParameterMeasurability.parameters? z.1 with
      | none => (e z.2.1).1 = (e z.2.2).1
      | some theta =>
          AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.2.1).1 =
            AssignmentParameterFibreKernel.successfulSlowSet p theta (e z.2.2).1}
  exact hremainders.inter hselectedClause

private def sourceFibreEventAtTime (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (q : Fin (M p)) (t : Fin p.T) :
    Set (RoundInput p rate × (SourceInput p × SourceInput p)) :=
  {z | ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.2.1 = q ∧
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.2.2 = q ∧
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2.1).2 =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2.2).2 ∧
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2.1).1,
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2.2).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent z.1}

private theorem measurableSet_sourceFibreEventAtTime (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurableSet (sourceFibreEventAtTime p rate q t) := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let leftSource : RoundInput p rate × (SourceInput p × SourceInput p) → SourceInput p :=
    fun z => z.2.1
  let rightSource : RoundInput p rate × (SourceInput p × SourceInput p) → SourceInput p :=
    fun z => z.2.2
  have hleftSource : Measurable leftSource := measurable_fst.comp measurable_snd
  have hrightSource : Measurable rightSource := measurable_snd.comp measurable_snd
  have hindex : Measurable (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p) := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hleftIndex : MeasurableSet {z : RoundInput p rate × (SourceInput p × SourceInput p) |
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.2.1 = q} :=
    (hindex.comp hleftSource) (measurableSet_singleton q)
  have hrightIndex : MeasurableSet {z : RoundInput p rate × (SourceInput p × SourceInput p) |
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.2.2 = q} :=
    (hindex.comp hrightSource) (measurableSet_singleton q)
  have : MeasurableEq (IDArray p) := by infer_instance
  have : MeasurableEq (ForwardRow p) := by infer_instance
  have : MeasurableEq (CompleteRow p) := by infer_instance
  have : MeasurableEq
      (ReferenceSelectedAffinePairLaw.Other t → TimeControl p) := by infer_instance
  have : MeasurableEq
      (ReferenceSelectedAffinePairLaw.Other q → CompleteRow p) := by infer_instance
  have : MeasurableEq (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) := by
    infer_instance
  have hleftSplit : Measurable (fun z => e (leftSource z)) :=
    e.measurable.comp hleftSource
  have hrightSplit : Measurable (fun z => e (rightSource z)) :=
    e.measurable.comp hrightSource
  have hremainders : MeasurableSet {z : RoundInput p rate ×
      (SourceInput p × SourceInput p) |
      (e (leftSource z)).2 = (e (rightSource z)).2} :=
    measurableSet_eq_fun (measurable_snd.comp hleftSplit)
      (measurable_snd.comp hrightSplit)
  let controls : RoundInput p rate × (SourceInput p × SourceInput p) →
      ReferenceLaterOptionalControlResampling.ControlPair p := fun z =>
        ((e (leftSource z)).1, (e (rightSource z)).1)
  have hcontrols : Measurable controls := by
    change Measurable (fun z : RoundInput p rate ×
      (SourceInput p × SourceInput p) =>
        ((e (leftSource z)).1, (e (rightSource z)).1))
    exact
      (measurable_fst.comp hleftSplit).prodMk (measurable_fst.comp hrightSplit)
  have hboundaryControls : Measurable (fun z : RoundInput p rate ×
      (SourceInput p × SourceInput p) => (z.1, controls z)) :=
    measurable_fst.prodMk hcontrols
  have hcontrolEvent : MeasurableSet {z : RoundInput p rate ×
      (ReferenceLaterOptionalControlResampling.ControlPair p) |
      z.2 ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent z.1} :=
    measurableSet_jointControlFibreEvent p rate
  rw [sourceFibreEventAtTime]
  exact hleftIndex.inter (hrightIndex.inter
    (hremainders.inter (hcontrolEvent.preimage hboundaryControls)))

/-- The complete source-pair certificate is jointly Borel in the canonical
round input and both original source draws. The proof partitions by both
calendar time and original private `J`, and retains the whole source remainder
and the actual checked-control fibre. -/
theorem measurableSet_pairedSourceFibreEvent_joint (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    MeasurableSet {z : RoundInput p rate × (SourceInput p × SourceInput p) |
      z.2 ∈ ReferenceFixedTimeSourceControlCoupling.pairedSourceFibreEvent
        p rate z.1} := by
  have hdecomp :
      {z : RoundInput p rate × (SourceInput p × SourceInput p) |
        z.2 ∈ ReferenceFixedTimeSourceControlCoupling.pairedSourceFibreEvent
          p rate z.1} =
        ⋃ t : Fin p.T, ⋃ q : Fin (M p),
          timeCell p rate t ×ˢ Set.univ ∩ sourceFibreEventAtTime p rate q t := by
    ext z
    change z.2 ∈
        (⋃ q : Fin (M p),
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceFibreEvent
            p rate z.1 q) ↔
      z ∈ ⋃ t : Fin p.T, ⋃ q : Fin (M p),
        timeCell p rate t ×ˢ Set.univ ∩ sourceFibreEventAtTime p rate q t
    constructor
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨q, hq⟩
      refine Set.mem_iUnion.mpr ⟨z.1.time, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
      constructor
      · constructor
        · change z.1.time = z.1.time
          rfl
        · trivial
      · simpa [sourceFibreEventAtTime,
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceFibreEvent] using hq
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨t, ht⟩
      rcases Set.mem_iUnion.mp ht with ⟨q, hq⟩
      rcases hq with ⟨hproduct, hcertificate⟩
      rcases Set.mem_prod.mp hproduct with ⟨htime, _⟩
      change z.1.time = t at htime
      subst t
      apply Set.mem_iUnion.mpr
      refine ⟨q, ?_⟩
      simpa [sourceFibreEventAtTime,
        ReferenceFixedTimeSourceControlCoupling.fixedControlSourceFibreEvent] using
        hcertificate
  rw [hdecomp]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun q =>
    (measurableSet_timeCell p rate t).prod MeasurableSet.univ |>.inter
      (measurableSet_sourceFibreEventAtTime p rate q t)

/-- The source certificate holds almost everywhere under the kernel at every
fixed boundary. -/
theorem ae_pairedSourceKernel_fibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : RoundInput p rate) :
    ∀ᵐ sources ∂pairedSourceKernel p rate b,
      sources ∈ ReferenceFixedTimeSourceControlCoupling.pairedSourceFibreEvent
        p rate b := by
  rw [pairedSourceKernel_apply]
  exact ReferenceFixedTimeSourceControlCoupling.ae_pairedSourceFibreEvent p rate b

/-- The kernel inherits the original-source frame equalities. -/
theorem ae_pairedSourceKernel_frames (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : RoundInput p rate) :
    ∀ᵐ sources ∂pairedSourceKernel p rate b,
      ∃ q : Fin (M p),
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sources.1 = q ∧
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sources.2 = q ∧
        sources.1.2 = sources.2.2 ∧
        sources.1.1.1 = sources.2.1.1 ∧
        (∀ j : Fin (M p), (sources.1.1.2 j).1 = (sources.2.1.2 j).1) ∧
        (∀ j : Fin (M p), j ≠ q → sources.1.1.2 j = sources.2.1.2 j) ∧
        (∀ s : ReferenceSelectedAffinePairLaw.Other b.time,
          (sources.1.1.2 q).2 s = (sources.2.1.2 q).2 s) ∧
        (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
          ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q b.time
              sources.1).1).2.1 label) =
          ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q b.time
              sources.2).1).2.1 label)) ∧
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q b.time
            sources.1).1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q b.time
            sources.2).1).2.2 := by
  rw [pairedSourceKernel_apply]
  exact ReferenceFixedTimeSourceControlCoupling.ae_pairedSource_frames p rate b

/-- The kernel inherits the admitted pointwise physical effects. -/
theorem ae_pairedSourceKernel_effects (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : RoundInput p rate) :
    ∀ᵐ sources ∂pairedSourceKernel p rate b,
      ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate b sources.1) =
        ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate b sources.2) ∧
      let left := ReferenceActivePhysicalStep.step
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate b sources.1)
      let right := ReferenceActivePhysicalStep.step
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate b sources.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  rw [pairedSourceKernel_apply]
  exact ReferenceFixedTimeSourceControlCoupling.ae_pairedSource_effects p rate b

end Bandits.Support.ReferenceSourceControlKernel

end
