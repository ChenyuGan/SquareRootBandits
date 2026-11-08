/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterOptionalControlResampling
public import Bandits.Support.ReferenceSelectedAffinePairLaw

/-!
# Fixed-time coupling on the complete original source

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-423`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42`.

At one fixed incoming physical record, this module splits one complete
original source at its actual private coordinator row and current time. It
then couples complete sources by the admitted current-control coupling while
retaining the full source remainder, including all private arrays. This is a
fixed-boundary coupling; it proves no chronological incoming-boundary law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFixedTimeSourceControlCoupling

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput

private instance measurableEqContinuousScalar :
    MeasurableEq ContinuousLearningRows.Scalar where
  measurableSet_diagonal := by
    have hreal : MeasurableSet {z : ContinuousLearningRows.Scalar ×
        ContinuousLearningRows.Scalar | (z.1 : ℝ) = (z.2 : ℝ)} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hset : {z : ContinuousLearningRows.Scalar × ContinuousLearningRows.Scalar |
        z.1 = z.2} = {z | (z.1 : ℝ) = (z.2 : ℝ)} := by
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
    have hleft : MeasurableSet {z : (α × β) × (α × β) | z.1.1 = z.2.1} := by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hright : MeasurableSet {z : (α × β) × (α × β) | z.1.2 = z.2.2} := by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
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
    have hdiag : Set.diagonal (∀ i, α i) = ⋂ i, {z : (∀ i, α i) × (∀ i, α i) |
        z.1 i = z.2 i} := by
      ext z
      simp [Set.mem_diagonal_iff, funext_iff]
    rw [hdiag]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) (by fun_prop)

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The published-output coordinates except one complete current
`TimeControl`, in the original ID/row grouping. -/
abbrev FixedControlPublishedRemainder (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) :=
  IDArray p ×
    ((ForwardRow p × (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) ×
      (ReferenceSelectedAffinePairLaw.Other q → CompleteRow p))

/-- All original source coordinates except one complete current `TimeControl`.
The product grouping follows the original published output and private input. -/
abbrev FixedControlRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  FixedControlPublishedRemainder p q t ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p

def selectedRowControlSplit (p : Parameters) (t : Fin p.T) :
    CompleteRow p ≃ᵐ TimeControl p ×
      (ForwardRow p × (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) :=
  ReferenceSelectedAffinePairLaw.extractRight
    (ReferenceSelectedAffinePairLaw.piExtract t)

def completeRowsControlSplit (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    CompletePublicTable.CompleteRows p ≃ᵐ TimeControl p ×
      ((ForwardRow p × (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) ×
        (ReferenceSelectedAffinePairLaw.Other q → CompleteRow p)) :=
  (ReferenceSelectedAffinePairLaw.piExtract q).trans
    (ReferenceSelectedAffinePairLaw.extractLeft (selectedRowControlSplit p t))

/-- Literal measurable equivalence removing the selected row's complete
current-time control while retaining every other original coordinate. -/
def fixedControlSplit (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    SourceInput p ≃ᵐ TimeControl p × FixedControlRemainder p q t :=
  ReferenceSelectedAffinePairLaw.extractLeft
    (ReferenceSelectedAffinePairLaw.extractRight (completeRowsControlSplit p q t))

def selectedRowRemainderLaw (p : Parameters) (t : Fin p.T) :
    Measure (ForwardRow p ×
      (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) :=
  (forwardRowMeasure p).prod
    (Measure.pi fun _ : ReferenceSelectedAffinePairLaw.Other t => timeControlLaw p)

def selectedRowsRemainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    Measure ((ForwardRow p ×
      (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) ×
      (ReferenceSelectedAffinePairLaw.Other q → CompleteRow p)) :=
  (selectedRowRemainderLaw p t).prod
    (Measure.pi fun _ : ReferenceSelectedAffinePairLaw.Other q => completeRowMeasure p)

instance selectedRowRemainderLaw_probability (p : Parameters) (t : Fin p.T) :
    IsProbabilityMeasure (selectedRowRemainderLaw p t) := by
  unfold selectedRowRemainderLaw
  infer_instance

instance selectedRowsRemainderLaw_probability (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    IsProbabilityMeasure (selectedRowsRemainderLaw p q t) := by
  unfold selectedRowsRemainderLaw
  infer_instance

def fixedControlRemainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    Measure (FixedControlRemainder p q t) :=
  ((idArrayMeasure p).prod (selectedRowsRemainderLaw p q t)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)

instance fixedControlRemainderLaw_probability (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    IsProbabilityMeasure (fixedControlRemainderLaw p q t) := by
  unfold fixedControlRemainderLaw
  infer_instance

theorem measurePreserving_selectedRowControlSplit (p : Parameters) (t : Fin p.T) :
    MeasurePreserving (selectedRowControlSplit p t) (completeRowMeasure p)
      ((timeControlLaw p).prod (selectedRowRemainderLaw p t)) := by
  unfold selectedRowControlSplit CompletePublicTable.completeRowMeasure
    ContinuousLearningRows.learningRowLaw
  exact ReferenceSelectedAffinePairLaw.measurePreserving_extractRight
    (ReferenceSelectedAffinePairLaw.piExtract t)
    (Measure.pi fun _ : Fin p.T => timeControlLaw p)
    (timeControlLaw p)
    (Measure.pi fun _ : ReferenceSelectedAffinePairLaw.Other t => timeControlLaw p)
    (forwardRowMeasure p)
    (ReferenceSelectedAffinePairLaw.measurePreserving_piExtract t (timeControlLaw p))

theorem measurePreserving_completeRowsControlSplit (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurePreserving (completeRowsControlSplit p q t)
      (CompletePublicTable.completeRowsMeasure p)
      ((timeControlLaw p).prod (selectedRowsRemainderLaw p q t)) := by
  unfold completeRowsControlSplit CompletePublicTable.completeRowsMeasure
  exact (ReferenceSelectedAffinePairLaw.measurePreserving_extractLeft
      (selectedRowControlSplit p t) (completeRowMeasure p) (timeControlLaw p)
      (selectedRowRemainderLaw p t)
      (Measure.pi fun _ : ReferenceSelectedAffinePairLaw.Other q => completeRowMeasure p)
      (measurePreserving_selectedRowControlSplit p t)).comp
    (ReferenceSelectedAffinePairLaw.measurePreserving_piExtract q (completeRowMeasure p))

theorem fixedControlSplit_measurePreserving (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurePreserving (fixedControlSplit p q t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p)
      ((timeControlLaw p).prod (fixedControlRemainderLaw p q t)) := by
  let ePub : CompletePublicTable.PublishedOutput p ≃ᵐ TimeControl p ×
      FixedControlPublishedRemainder p q t :=
    ReferenceSelectedAffinePairLaw.extractRight (completeRowsControlSplit p q t)
  have hPub : MeasurePreserving ePub (CompletePublicTable.publishedOutputMeasure p)
      ((timeControlLaw p).prod
        ((idArrayMeasure p).prod (selectedRowsRemainderLaw p q t))) := by
    unfold ePub CompletePublicTable.publishedOutputMeasure
    exact ReferenceSelectedAffinePairLaw.measurePreserving_extractRight
      (completeRowsControlSplit p q t)
      (CompletePublicTable.completeRowsMeasure p)
      (timeControlLaw p)
      (selectedRowsRemainderLaw p q t)
      (idArrayMeasure p)
      (measurePreserving_completeRowsControlSplit p q t)
  change MeasurePreserving (ReferenceSelectedAffinePairLaw.extractLeft ePub)
    ((CompletePublicTable.publishedOutputMeasure p).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
    ((timeControlLaw p).prod
      (((idArrayMeasure p).prod (selectedRowsRemainderLaw p q t)).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)))
  exact ReferenceSelectedAffinePairLaw.measurePreserving_extractLeft ePub
    (CompletePublicTable.publishedOutputMeasure p) (timeControlLaw p)
    ((idArrayMeasure p).prod (selectedRowsRemainderLaw p q t))
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p) hPub

theorem fixedControlSplit_measurePreserving_symm (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurePreserving (fixedControlSplit p q t).symm
      ((timeControlLaw p).prod (fixedControlRemainderLaw p q t))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
  (fixedControlSplit_measurePreserving p q t).symm

theorem sourceInputLaw_map_fixedControlSplit (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map (fixedControlSplit p q t) =
      ((timeControlLaw p).prod (fixedControlRemainderLaw p q t)) :=
  (fixedControlSplit_measurePreserving p q t).map_eq

theorem fixedControlSplit_control (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) :
    (fixedControlSplit p q t source).1 = (source.1.2 q).2 t := rfl

theorem fixedControlSplit_remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) :
    (fixedControlSplit p q t source).2 =
      ((source.1.1,
        (((source.1.2 q).1, fun s : ReferenceSelectedAffinePairLaw.Other t =>
            (source.1.2 q).2 s),
          fun j : ReferenceSelectedAffinePairLaw.Other q => source.1.2 j)), source.2) := rfl

theorem fixedControlSplit_reconstruct (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (fixedControlSplit p q t).symm (fixedControlSplit p q t source) = source :=
  (fixedControlSplit p q t).symm_apply_apply source

theorem fixedControlSplit_split_reconstruct (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (value : TimeControl p × FixedControlRemainder p q t) :
    fixedControlSplit p q t ((fixedControlSplit p q t).symm value) = value :=
  (fixedControlSplit p q t).apply_symm_apply value

theorem fixedControlSplit_id (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) :
    (fixedControlSplit p q t source).2.1.1 = source.1.1 := rfl

theorem fixedControlSplit_private (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) : (fixedControlSplit p q t source).2.2 = source.2 := rfl

theorem fixedControlSplit_symm_private (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t) :
    ((fixedControlSplit p q t).symm (control, remainder)).2 = remainder.2 := by
  have h := congrArg (fun z : TimeControl p × FixedControlRemainder p q t => z.2.2)
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_private] using h

theorem fixedControlSplit_symm_control (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t) :
    (((fixedControlSplit p q t).symm (control, remainder)).1.2 q).2 t = control := by
  have h := congrArg Prod.fst
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_control] using h

theorem fixedControlSplit_symm_id (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t) :
    ((fixedControlSplit p q t).symm (control, remainder)).1.1 = remainder.1.1 := by
  have h := congrArg
    (fun z : TimeControl p × FixedControlRemainder p q t => z.2.1.1)
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_remainder] using h

theorem fixedControlSplit_symm_forward (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t) :
    (((fixedControlSplit p q t).symm (control, remainder)).1.2 q).1 =
      remainder.1.2.1.1 := by
  have h := congrArg
    (fun z : TimeControl p × FixedControlRemainder p q t => z.2.1.2.1.1)
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_remainder] using h

theorem fixedControlSplit_symm_otherTime (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t)
    (s : ReferenceSelectedAffinePairLaw.Other t) :
    (((fixedControlSplit p q t).symm (control, remainder)).1.2 q).2 s =
      remainder.1.2.1.2 s := by
  have h := congrArg
    (fun z : TimeControl p × FixedControlRemainder p q t => z.2.1.2.1.2 s)
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_remainder] using h

theorem fixedControlSplit_symm_otherRow (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (remainder : FixedControlRemainder p q t)
    (j : ReferenceSelectedAffinePairLaw.Other q) :
    ((fixedControlSplit p q t).symm (control, remainder)).1.2 j = remainder.1.2.2 j := by
  have h := congrArg
    (fun z : TimeControl p × FixedControlRemainder p q t => z.2.1.2.2 j)
    ((fixedControlSplit p q t).apply_symm_apply (control, remainder))
  simpa only [fixedControlSplit_remainder] using h

theorem fixedControlSplit_forward (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) :
    (fixedControlSplit p q t source).2.1.2.1.1 = (source.1.2 q).1 := rfl

theorem fixedControlSplit_otherTime (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) (s : ReferenceSelectedAffinePairLaw.Other t) :
    (fixedControlSplit p q t source).2.1.2.1.2 s = (source.1.2 q).2 s := rfl

theorem fixedControlSplit_otherRow (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p) (j : ReferenceSelectedAffinePairLaw.Other q) :
    (fixedControlSplit p q t source).2.1.2.2 j = source.1.2 j := rfl

def sourceCoordinatorIndex (p : Parameters) (source : SourceInput p) : Fin (M p) :=
  PrivateSourceStreams.coordinatorIndex p source.2.1.2

def fixedControlSourceStratum (p : Parameters) (q : Fin (M p)) : Set (SourceInput p) :=
  {source | sourceCoordinatorIndex p source = q}

def fixedControlRemainderStratum (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) : Set (FixedControlRemainder p q t) :=
  {remainder | PrivateSourceStreams.coordinatorIndex p remainder.2.1.2 = q}

theorem measurableSet_fixedControlRemainderStratum (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurableSet (fixedControlRemainderStratum p q t) := by
  have hscalar : Measurable (fun r : FixedControlRemainder p q t => r.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hindex := (PrivateSourceStreams.measurable_coordinatorIndex p).comp hscalar
  change MeasurableSet ((fun r : FixedControlRemainder p q t =>
    PrivateSourceStreams.coordinatorIndex p r.2.1.2) ⁻¹' {q})
  exact hindex (measurableSet_singleton q)

theorem fixedControlSourceStratum_eq_preimage (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    fixedControlSourceStratum p q =
      fixedControlSplit p q t ⁻¹' (Set.univ ×ˢ fixedControlRemainderStratum p q t) := by
  ext source
  simp only [fixedControlSourceStratum, Set.mem_ofPred_eq, Set.mem_preimage,
    Set.mem_prod, Set.mem_univ, fixedControlRemainderStratum, sourceCoordinatorIndex,
    true_and]
  rw [fixedControlSplit_private]

theorem measurableSet_fixedControlSourceStratum (p : Parameters)
    (q : Fin (M p)) : MeasurableSet (fixedControlSourceStratum p q) := by
  have hscalar : Measurable (fun source : SourceInput p => source.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hindex := (PrivateSourceStreams.measurable_coordinatorIndex p).comp hscalar
  change MeasurableSet ((fun source : SourceInput p =>
    PrivateSourceStreams.coordinatorIndex p source.2.1.2) ⁻¹' {q})
  exact hindex (measurableSet_singleton q)

theorem fixedControlSplit_privateStratum_map (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    Measure.map (fixedControlSplit p q t)
        ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedControlSourceStratum p q)) =
      (timeControlLaw p).prod
        ((fixedControlRemainderLaw p q t).restrict (fixedControlRemainderStratum p q t)) := by
  let e := fixedControlSplit p q t
  let E : Set (TimeControl p × FixedControlRemainder p q t) :=
    Set.univ ×ˢ fixedControlRemainderStratum p q t
  have hE : MeasurableSet E :=
    MeasurableSet.univ.prod (measurableSet_fixedControlRemainderStratum p q t)
  have hF : fixedControlSourceStratum p q = e ⁻¹' E := by
    simpa [E] using fixedControlSourceStratum_eq_preimage p q t
  calc
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).map e).restrict E := by
      rw [hF]
      exact (Measure.restrict_map e.measurable hE).symm
    _ = ((timeControlLaw p).prod (fixedControlRemainderLaw p q t)).restrict E := by
      rw [(fixedControlSplit_measurePreserving p q t).map_eq]
    _ = (timeControlLaw p).prod
        ((fixedControlRemainderLaw p q t).restrict
          (fixedControlRemainderStratum p q t)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem fixedControlSplit_privateStratum_map_symm (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    ((timeControlLaw p).prod
      ((fixedControlRemainderLaw p q t).restrict (fixedControlRemainderStratum p q t))).map
        (fixedControlSplit p q t).symm =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) := by
  calc
    _ = Measure.map (fixedControlSplit p q t).symm
        (Measure.map (fixedControlSplit p q t)
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (fixedControlSourceStratum p q))) := by
      rw [← fixedControlSplit_privateStratum_map]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) := by
      rw [Measure.map_map (fixedControlSplit p q t).symm.measurable
        (fixedControlSplit p q t).measurable]
      simp

/-- Literal replacement of the current control in the original row selected
by the original private coordinator scalar. Every other source coordinate is
retained verbatim. -/
def replaceSourceControl (p : Parameters) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) : SourceInput p :=
  ((source.1.1,
    Function.update source.1.2 (sourceCoordinatorIndex p source)
      ((source.1.2 (sourceCoordinatorIndex p source)).1,
        Function.update (source.1.2 (sourceCoordinatorIndex p source)).2 t control)),
    source.2)

/-- Insert a full original source into the frozen incoming boundary. -/
def roundInputAtSource (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p)
    (boundary : RoundInput p rate) (source : SourceInput p) : RoundInput p rate :=
  { boundary with rows := source.1.2, selected := sourceCoordinatorIndex p source }

theorem sourceCoordinatorIndex_eq_selectedRowIndex (p : Parameters) (source : SourceInput p) :
    sourceCoordinatorIndex p source = ActualInitializationPhysicalStep.selectedRowIndex p source :=
  rfl

theorem roundInputAtSource_replaceSourceControl (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (source : SourceInput p) (control : TimeControl p) :
    roundInputAtSource p rate boundary (replaceSourceControl p boundary.time source control) =
      ReferenceLaterOptionalControlResampling.withControl
        (roundInputAtSource p rate boundary source) control := by
  rfl

theorem replaceSourceControl_private (p : Parameters) (t : Fin p.T)
    (source : SourceInput p) (control : TimeControl p) :
    (replaceSourceControl p t source control).2 = source.2 := rfl

theorem replaceSourceControl_id (p : Parameters) (t : Fin p.T)
    (source : SourceInput p) (control : TimeControl p) :
    (replaceSourceControl p t source control).1.1 = source.1.1 := rfl

theorem replaceSourceControl_forward (p : Parameters) (t : Fin p.T)
    (source : SourceInput p) (control : TimeControl p) :
    ((replaceSourceControl p t source control).1.2
      (sourceCoordinatorIndex p source)).1 =
        (source.1.2 (sourceCoordinatorIndex p source)).1 := by
  simp [replaceSourceControl]

theorem replaceSourceControl_original (p : Parameters) (t : Fin p.T)
    (source : SourceInput p) :
    replaceSourceControl p t source ((source.1.2 (sourceCoordinatorIndex p source)).2 t) =
      source := by
  simp [replaceSourceControl]

theorem fixedControlSplit_replaceSourceControl (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) (hq : sourceCoordinatorIndex p source = q) :
    (fixedControlSplit p q t).symm (control, (fixedControlSplit p q t source).2) =
      replaceSourceControl p t source control := by
  apply (fixedControlSplit p q t).injective
  rw [(fixedControlSplit p q t).apply_symm_apply]
  apply Prod.ext
  · simp [fixedControlSplit_control, replaceSourceControl, hq]
  · simp [fixedControlSplit_remainder, replaceSourceControl, hq]
    constructor
    · funext s
      exact (Function.update_of_ne s.property _ _).symm
    · funext j
      exact (Function.update_of_ne j.property _ _).symm

def fixedControlSourcePairMap (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    (ReferenceLaterOptionalControlResampling.ControlPair p × FixedControlRemainder p q t) →
      SourceInput p × SourceInput p := fun z =>
  ((fixedControlSplit p q t).symm (z.1.1, z.2),
    (fixedControlSplit p q t).symm (z.1.2, z.2))

theorem measurable_fixedControlSourcePairMap (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) : Measurable (fixedControlSourcePairMap p q t) := by
  fun_prop [fixedControlSourcePairMap]

/-- The unnormalized source-pair measure on one actual private-J stratum. -/
def fixedControlSourcePairSummand (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) : Measure (SourceInput p × SourceInput p) :=
  ((ReferenceLaterOptionalControlResampling.pairedControlKernel p rate boundary).prod
      ((fixedControlRemainderLaw p q boundary.time).restrict
        (fixedControlRemainderStratum p q boundary.time))).map
    (fixedControlSourcePairMap p q boundary.time)

/-- The two full original inputs are coupled by the actual paired control,
with one shared draw from the unnormalized retained remainder on each J
stratum. -/
def pairedSourceLaw (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p)
    (boundary : RoundInput p rate) : Measure (SourceInput p × SourceInput p) :=
  Measure.sum (fun q : Fin (M p) => fixedControlSourcePairSummand p rate boundary q)

private theorem map_firstControlFromSourceProduct (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) :
    (fixedControlSourcePairSummand p rate boundary q).map Prod.fst =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) := by
  let e := fixedControlSplit p q boundary.time
  let ρ := (fixedControlRemainderLaw p q boundary.time).restrict
    (fixedControlRemainderStratum p q boundary.time)
  let Q := ReferenceLaterOptionalControlResampling.pairedControlKernel p rate boundary
  calc
    _ = (Q.prod ρ).map (fun z => e.symm (z.1.1, z.2)) := by
      rw [fixedControlSourcePairSummand, Measure.map_map measurable_fst
        (measurable_fixedControlSourcePairMap p q boundary.time)]
      rfl
    _ = ((Q.prod ρ).map (Prod.map Prod.fst id)).map e.symm := by
      rw [Measure.map_map e.symm.measurable (by fun_prop)]
      rfl
    _ = ((Q.map Prod.fst).prod ρ).map e.symm := by
      rw [← Measure.map_prod_map Q ρ measurable_fst measurable_id]
      simp
    _ = ((timeControlLaw p).prod ρ).map e.symm := by
      rw [ReferenceLaterOptionalControlResampling.pairedControlKernel_fst]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) :=
      fixedControlSplit_privateStratum_map_symm p q boundary.time

private theorem map_secondControlFromSourceProduct (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) :
    (fixedControlSourcePairSummand p rate boundary q).map Prod.snd =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) := by
  let e := fixedControlSplit p q boundary.time
  let ρ := (fixedControlRemainderLaw p q boundary.time).restrict
    (fixedControlRemainderStratum p q boundary.time)
  let Q := ReferenceLaterOptionalControlResampling.pairedControlKernel p rate boundary
  calc
    _ = (Q.prod ρ).map (fun z => e.symm (z.1.2, z.2)) := by
      rw [fixedControlSourcePairSummand, Measure.map_map measurable_snd
        (measurable_fixedControlSourcePairMap p q boundary.time)]
      rfl
    _ = ((Q.prod ρ).map (Prod.map Prod.snd id)).map e.symm := by
      rw [Measure.map_map e.symm.measurable (by fun_prop)]
      rfl
    _ = ((Q.map Prod.snd).prod ρ).map e.symm := by
      rw [← Measure.map_prod_map Q ρ measurable_snd measurable_id]
      simp
    _ = ((timeControlLaw p).prod ρ).map e.symm := by
      rw [ReferenceLaterOptionalControlResampling.pairedControlKernel_snd]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q) :=
      fixedControlSplit_privateStratum_map_symm p q boundary.time

private theorem sourceStrata_sum (p : Parameters) :
    Measure.sum (fun q : Fin (M p) =>
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (fixedControlSourceStratum p q)) = BootstrapPrivateRoundStreams.sourceInputLaw p := by
  have hdis : Pairwise (fun q r =>
      Disjoint (fixedControlSourceStratum p q) (fixedControlSourceStratum p r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro source hq hr
    simp only [fixedControlSourceStratum, Set.mem_ofPred_eq,
      sourceCoordinatorIndex] at hq hr
    exact hqr (hq.symm.trans hr)
  have hmeas : ∀ q : Fin (M p), MeasurableSet (fixedControlSourceStratum p q) :=
    fun q => measurableSet_fixedControlSourceStratum p q
  have hcover : (⋃ q : Fin (M p), fixedControlSourceStratum p q) = Set.univ := by
    ext source
    constructor
    · intro _
      trivial
    · intro _
      simp only [Set.mem_iUnion]
      exact ⟨sourceCoordinatorIndex p source, rfl⟩
  calc
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (⋃ q : Fin (M p), fixedControlSourceStratum p q) :=
      (Measure.restrict_iUnion hdis hmeas).symm
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p := by rw [hcover, Measure.restrict_univ]

theorem pairedSourceLaw_fst (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    (pairedSourceLaw p rate boundary).map Prod.fst =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
  rw [pairedSourceLaw, Measure.map_sum measurable_fst.aemeasurable,
    Measure.sum_fintype]
  calc
    _ = ∑ q : Fin (M p),
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedControlSourceStratum p q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact map_firstControlFromSourceProduct p rate boundary q
    _ = Measure.sum (fun q : Fin (M p) =>
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedControlSourceStratum p q)) := by
      rw [Measure.sum_fintype]
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p := sourceStrata_sum p

theorem pairedSourceLaw_snd (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    (pairedSourceLaw p rate boundary).map Prod.snd =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
  rw [pairedSourceLaw, Measure.map_sum measurable_snd.aemeasurable,
    Measure.sum_fintype]
  calc
    _ = ∑ q : Fin (M p),
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedControlSourceStratum p q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact map_secondControlFromSourceProduct p rate boundary q
    _ = Measure.sum (fun q : Fin (M p) =>
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (fixedControlSourceStratum p q)) := by
      rw [Measure.sum_fintype]
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p := sourceStrata_sum p

theorem pairedSourceLaw_mass (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    pairedSourceLaw p rate boundary Set.univ = 1 := by
  calc
    pairedSourceLaw p rate boundary Set.univ =
        (pairedSourceLaw p rate boundary).map Prod.fst Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p Set.univ := by
      rw [pairedSourceLaw_fst]
    _ = 1 := measure_univ

instance pairedSourceLaw_probability (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    IsProbabilityMeasure (pairedSourceLaw p rate boundary) where
  measure_univ := pairedSourceLaw_mass p rate boundary

def fixedControlSourceFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) : Set (SourceInput p × SourceInput p) :=
  {z | sourceCoordinatorIndex p z.1 = q ∧
    sourceCoordinatorIndex p z.2 = q ∧
    (fixedControlSplit p q boundary.time z.1).2 =
      (fixedControlSplit p q boundary.time z.2).2 ∧
    ((fixedControlSplit p q boundary.time z.1).1,
      (fixedControlSplit p q boundary.time z.2).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary}

/-- The source-level certificate is a finite union over the original private
coordinator index. Each clause retains equal complete remainders and invokes
the admitted fixed-boundary control certificate on the extracted pair. -/
def pairedSourceFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    Set (SourceInput p × SourceInput p) :=
  ⋃ q : Fin (M p), fixedControlSourceFibreEvent p rate boundary q

theorem measurableSet_fixedControlSourceFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) : MeasurableSet (fixedControlSourceFibreEvent p rate boundary q) := by
  have hindex : Measurable (sourceCoordinatorIndex p) := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hleftIndex : MeasurableSet {z : SourceInput p × SourceInput p |
      sourceCoordinatorIndex p z.1 = q} := by
    exact (hindex.comp measurable_fst) (measurableSet_singleton q)
  have hrightIndex : MeasurableSet {z : SourceInput p × SourceInput p |
      sourceCoordinatorIndex p z.2 = q} := by
    exact (hindex.comp measurable_snd) (measurableSet_singleton q)
  have : MeasurableEq (IDArray p) := by infer_instance
  have : MeasurableEq (ForwardRow p) := by infer_instance
  have : MeasurableEq (CompleteRow p) := by infer_instance
  have : MeasurableEq (ReferenceSelectedAffinePairLaw.Other boundary.time → TimeControl p) :=
    by infer_instance
  have : MeasurableEq (ReferenceSelectedAffinePairLaw.Other q → CompleteRow p) := by infer_instance
  have : MeasurableEq (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) := by
    infer_instance
  let e := fixedControlSplit p q boundary.time
  have hleftSplit : Measurable (fun z : SourceInput p × SourceInput p => e z.1) :=
    e.measurable.comp measurable_fst
  have hrightSplit : Measurable (fun z : SourceInput p × SourceInput p => e z.2) :=
    e.measurable.comp measurable_snd
  have hremainders : MeasurableSet {z : SourceInput p × SourceInput p |
      (e z.1).2 = (e z.2).2} :=
    measurableSet_eq_fun (measurable_snd.comp hleftSplit) (measurable_snd.comp hrightSplit)
  have hcontrols : Measurable (fun z : SourceInput p × SourceInput p =>
      ((e z.1).1, (e z.2).1)) :=
    (measurable_fst.comp hleftSplit).prodMk (measurable_fst.comp hrightSplit)
  have hcontrolEvent : MeasurableSet
      (ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary) :=
    ReferenceLaterOptionalControlResampling.measurableSet_pairedControlFibreEvent boundary
  rw [fixedControlSourceFibreEvent]
  exact hleftIndex.inter (hrightIndex.inter
    (hremainders.inter (hcontrolEvent.preimage hcontrols)))

theorem measurableSet_pairedSourceFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    MeasurableSet (pairedSourceFibreEvent p rate boundary) := by
  rw [pairedSourceFibreEvent]
  exact MeasurableSet.iUnion fun q => measurableSet_fixedControlSourceFibreEvent p rate boundary q

theorem fixedControlSplit_symm_coordinatorIndex (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (control : TimeControl p)
    (remainder : FixedControlRemainder p q t)
    (hremainder : remainder ∈ fixedControlRemainderStratum p q t) :
    sourceCoordinatorIndex p
        ((fixedControlSplit p q t).symm (control, remainder)) = q := by
  have hprivate := fixedControlSplit_symm_private p q t control remainder
  change PrivateSourceStreams.coordinatorIndex p remainder.2.1.2 = q at hremainder
  unfold sourceCoordinatorIndex
  rw [hprivate]
  exact hremainder

private theorem fixedControlSourcePairMap_mem_iff (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (q : Fin (M p)) (controls : ReferenceLaterOptionalControlResampling.ControlPair p)
    (remainder : FixedControlRemainder p q boundary.time)
    (hremainder : remainder ∈ fixedControlRemainderStratum p q boundary.time) :
    fixedControlSourcePairMap p q boundary.time (controls, remainder) ∈
        pairedSourceFibreEvent p rate boundary ↔
      controls ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent
        boundary := by
  constructor
  · intro hsource
    rcases Set.mem_iUnion.mp hsource with ⟨q', hq'⟩
    change sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.1, remainder)) = q' ∧
      sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.2, remainder)) = q' ∧
      (fixedControlSplit p q' boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.1, remainder))).2 =
        (fixedControlSplit p q' boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.2, remainder))).2 ∧
      ((fixedControlSplit p q' boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.1, remainder))).1,
        (fixedControlSplit p q' boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.2, remainder))).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary at hq'
    have hindex : q' = q := by
      calc
        q' = sourceCoordinatorIndex p
            ((fixedControlSplit p q boundary.time).symm (controls.1, remainder)) := hq'.1.symm
        _ = q := fixedControlSplit_symm_coordinatorIndex p q boundary.time
          controls.1 remainder hremainder
    subst q'
    simpa [fixedControlSourcePairMap] using hq'.2.2.2
  · intro hcontrols
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    have hleft : sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.1, remainder)) = q :=
      fixedControlSplit_symm_coordinatorIndex p q boundary.time controls.1 remainder hremainder
    have hright : sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.2, remainder)) = q :=
      fixedControlSplit_symm_coordinatorIndex p q boundary.time controls.2 remainder hremainder
    change sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.1, remainder)) = q ∧
      sourceCoordinatorIndex p
        ((fixedControlSplit p q boundary.time).symm (controls.2, remainder)) = q ∧
      (fixedControlSplit p q boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.1, remainder))).2 =
        (fixedControlSplit p q boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.2, remainder))).2 ∧
      ((fixedControlSplit p q boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.1, remainder))).1,
        (fixedControlSplit p q boundary.time
          ((fixedControlSplit p q boundary.time).symm (controls.2, remainder))).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary
    refine ⟨hleft, hright, ?_, ?_⟩
    · simp
    · simpa [fixedControlSourcePairMap] using hcontrols

theorem ae_pairedSourceFibreEvent (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    ∀ᵐ z ∂pairedSourceLaw p rate boundary, z ∈ pairedSourceFibreEvent p rate boundary := by
  rw [pairedSourceLaw, Measure.ae_sum_iff]
  intro q
  let ρ := (fixedControlRemainderLaw p q boundary.time).restrict
    (fixedControlRemainderStratum p q boundary.time)
  have hremSet : MeasurableSet (fixedControlRemainderStratum p q boundary.time) :=
    measurableSet_fixedControlRemainderStratum p q boundary.time
  have hcontrolSet : MeasurableSet {z :
      ReferenceLaterOptionalControlResampling.ControlPair p ×
        FixedControlRemainder p q boundary.time |
      z.1 ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent
          boundary ∧ z.2 ∈ fixedControlRemainderStratum p q boundary.time} := by
    exact (ReferenceLaterOptionalControlResampling.measurableSet_pairedControlFibreEvent
      boundary).preimage measurable_fst |>.inter
        (hremSet.preimage measurable_snd)
  have hproduct : ∀ᵐ z ∂
      (ReferenceLaterOptionalControlResampling.pairedControlKernel p rate boundary).prod ρ,
      z.1 ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent
          boundary ∧ z.2 ∈ fixedControlRemainderStratum p q boundary.time := by
    rw [Measure.ae_prod_iff_ae_ae hcontrolSet]
    filter_upwards [ReferenceLaterOptionalControlResampling.ae_pairedControlFibreEvent
      (p := p) (rate := rate) boundary] with controls hcontrols
    filter_upwards [ae_restrict_mem hremSet] with remainder hremainder
    exact ⟨hcontrols, hremainder⟩
  have hmap : ∀ᵐ z ∂fixedControlSourcePairSummand p rate boundary q,
      z ∈ pairedSourceFibreEvent p rate boundary := by
    change ∀ᵐ z ∂((ReferenceLaterOptionalControlResampling.pairedControlKernel
      p rate boundary).prod ρ).map (fixedControlSourcePairMap p q boundary.time),
        z ∈ pairedSourceFibreEvent p rate boundary
    apply (ae_map_iff (measurable_fixedControlSourcePairMap p q boundary.time).aemeasurable
      (measurableSet_pairedSourceFibreEvent p rate boundary)).2
    filter_upwards [hproduct] with z hz
    exact (fixedControlSourcePairMap_mem_iff p rate boundary q z.1 z.2 hz.2).2 hz.1
  exact hmap

theorem pairedSourceFibreEvent_frames (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (sources : SourceInput p × SourceInput p)
    (hsources : sources ∈ pairedSourceFibreEvent p rate boundary) :
    ∃ q : Fin (M p),
      sourceCoordinatorIndex p sources.1 = q ∧
      sourceCoordinatorIndex p sources.2 = q ∧
      sources.1.2 = sources.2.2 ∧
      sources.1.1.1 = sources.2.1.1 ∧
      (∀ j : Fin (M p), (sources.1.1.2 j).1 = (sources.2.1.2 j).1) ∧
      (∀ j : Fin (M p), j ≠ q → sources.1.1.2 j = sources.2.1.2 j) ∧
      (∀ s : ReferenceSelectedAffinePairLaw.Other boundary.time,
        (sources.1.1.2 q).2 s = (sources.2.1.2 q).2 s) ∧
      (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (fixedControlSplit p q boundary.time sources.1).1).2.1 label) =
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (fixedControlSplit p q boundary.time sources.2).1).2.1 label)) ∧
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (fixedControlSplit p q boundary.time sources.1).1).2.2 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (fixedControlSplit p q boundary.time sources.2).1).2.2 := by
  rcases Set.mem_iUnion.mp hsources with ⟨q, hq⟩
  change sourceCoordinatorIndex p sources.1 = q ∧
    sourceCoordinatorIndex p sources.2 = q ∧
    (fixedControlSplit p q boundary.time sources.1).2 =
      (fixedControlSplit p q boundary.time sources.2).2 ∧
    ((fixedControlSplit p q boundary.time sources.1).1,
      (fixedControlSplit p q boundary.time sources.2).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary at hq
  rcases hq with ⟨hleftIndex, hrightIndex, hremainders, hcontrols⟩
  let leftControl := (fixedControlSplit p q boundary.time sources.1).1
  let rightControl := (fixedControlSplit p q boundary.time sources.2).1
  have hcontrolRemainder :
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p leftControl).2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p rightControl).2 := by
    change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p leftControl).2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p rightControl).2 ∧ _ at hcontrols
    exact hcontrols.1
  refine ⟨q, hleftIndex, hrightIndex, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fixedControlSplit_private] using congrArg Prod.snd hremainders
  · simpa only [fixedControlSplit_remainder] using
      congrArg (fun r : FixedControlRemainder p q boundary.time => r.1.1) hremainders
  · intro j
    by_cases hj : j = q
    · subst j
      simpa only [fixedControlSplit_remainder] using
        congrArg (fun r : FixedControlRemainder p q boundary.time => r.1.2.1.1)
          hremainders
    · have hrow : sources.1.1.2 j = sources.2.1.2 j := by
        simpa only [fixedControlSplit_remainder] using congrArg
          (fun r : FixedControlRemainder p q boundary.time => r.1.2.2 ⟨j, hj⟩)
          hremainders
      exact congrArg Prod.fst hrow
  · intro j hj
    simpa only [fixedControlSplit_remainder] using congrArg
      (fun r : FixedControlRemainder p q boundary.time => r.1.2.2 ⟨j, hj⟩)
      hremainders
  · intro s
    simpa only [fixedControlSplit_remainder] using congrArg
      (fun r : FixedControlRemainder p q boundary.time => r.1.2.1.2 ⟨s, s.property⟩)
      hremainders
  · intro label
    exact congrArg (fun r : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      r.1 label)
      hcontrolRemainder
  · exact congrArg Prod.snd hcontrolRemainder

theorem ae_pairedSource_frames (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    ∀ᵐ sources ∂pairedSourceLaw p rate boundary,
      ∃ q : Fin (M p),
        sourceCoordinatorIndex p sources.1 = q ∧
        sourceCoordinatorIndex p sources.2 = q ∧
        sources.1.2 = sources.2.2 ∧
        sources.1.1.1 = sources.2.1.1 ∧
        (∀ j : Fin (M p), (sources.1.1.2 j).1 = (sources.2.1.2 j).1) ∧
        (∀ j : Fin (M p), j ≠ q → sources.1.1.2 j = sources.2.1.2 j) ∧
        (∀ s : ReferenceSelectedAffinePairLaw.Other boundary.time,
          (sources.1.1.2 q).2 s = (sources.2.1.2 q).2 s) ∧
        (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
          ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (fixedControlSplit p q boundary.time sources.1).1).2.1 label) =
          ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (fixedControlSplit p q boundary.time sources.2).1).2.1 label)) ∧
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (fixedControlSplit p q boundary.time sources.1).1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (fixedControlSplit p q boundary.time sources.2).1).2.2 := by
  filter_upwards [ae_pairedSourceFibreEvent p rate boundary] with sources hsources
  exact pairedSourceFibreEvent_frames p rate boundary sources hsources

theorem pairedSourceFibreEvent_effects (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate)
    (sources : SourceInput p × SourceInput p)
    (hsources : sources ∈ pairedSourceFibreEvent p rate boundary) :
    ReferenceActivePhysicalHorizon.computedEvidence
        (roundInputAtSource p rate boundary sources.1) =
      ReferenceActivePhysicalHorizon.computedEvidence
        (roundInputAtSource p rate boundary sources.2) ∧
      let left := ReferenceActivePhysicalStep.step
        (roundInputAtSource p rate boundary sources.1)
      let right := ReferenceActivePhysicalStep.step
        (roundInputAtSource p rate boundary sources.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  rcases Set.mem_iUnion.mp hsources with ⟨q, hq⟩
  change sourceCoordinatorIndex p sources.1 = q ∧
    sourceCoordinatorIndex p sources.2 = q ∧
    (fixedControlSplit p q boundary.time sources.1).2 =
      (fixedControlSplit p q boundary.time sources.2).2 ∧
    ((fixedControlSplit p q boundary.time sources.1).1,
      (fixedControlSplit p q boundary.time sources.2).1) ∈
        ReferenceLaterOptionalControlResampling.pairedControlFibreEvent boundary at hq
  rcases hq with ⟨hleftIndex, hrightIndex, hremainders, hcontrols⟩
  let e := fixedControlSplit p q boundary.time
  let leftControl := (e sources.1).1
  let rightControl := (e sources.2).1
  let controls : ReferenceLaterOptionalControlResampling.ControlPair p :=
    (leftControl, rightControl)
  let leftInput := roundInputAtSource p rate boundary sources.1
  let rightInput := roundInputAtSource p rate boundary sources.2
  have hparameter :
      ReferenceLaterSamplerParameterMeasurability.parameters? leftInput =
        ReferenceLaterSamplerParameterMeasurability.parameters? boundary := by
    exact (ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
      boundary leftInput rfl rfl).symm
  have hcontrolsAtLeft :
      controls ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent leftInput := by
    rw [ReferenceLaterOptionalControlResampling.pairedControlFibreEvent] at hcontrols ⊢
    simp only [Set.mem_ofPred_eq] at hcontrols ⊢
    rw [hparameter]
    exact hcontrols
  have hreplaceLeft : replaceSourceControl p boundary.time sources.1 leftControl = sources.1 := by
    have hreplace := fixedControlSplit_replaceSourceControl p q boundary.time
      sources.1 leftControl hleftIndex
    calc
      replaceSourceControl p boundary.time sources.1 leftControl =
          e.symm (leftControl, (e sources.1).2) := hreplace.symm
      _ = e.symm (e sources.1) := by simp [leftControl]
      _ = sources.1 := e.symm_apply_apply sources.1
  have hsplitRight : e sources.2 = (rightControl, (e sources.1).2) := by
    apply Prod.ext
    · rfl
    · exact hremainders.symm
  have hreplaceRight : replaceSourceControl p boundary.time sources.1 rightControl = sources.2 := by
    have hreplace := fixedControlSplit_replaceSourceControl p q boundary.time
      sources.1 rightControl hleftIndex
    calc
      replaceSourceControl p boundary.time sources.1 rightControl =
          e.symm (rightControl, (e sources.1).2) := hreplace.symm
      _ = e.symm (e sources.2) := by rw [hsplitRight]
      _ = sources.2 := e.symm_apply_apply sources.2
  have hleftFrame : leftInput =
      ReferenceLaterOptionalControlResampling.withControl leftInput leftControl := by
    have h := roundInputAtSource_replaceSourceControl p rate boundary sources.1 leftControl
    rw [hreplaceLeft] at h
    simpa [leftInput] using h
  have hrightFrame : rightInput =
      ReferenceLaterOptionalControlResampling.withControl leftInput rightControl := by
    have h := roundInputAtSource_replaceSourceControl p rate boundary sources.1 rightControl
    rw [hreplaceRight] at h
    simpa [leftInput, rightInput] using h
  have hphysical := ReferenceLaterOptionalControlResampling.pairedControlFibreEvent_effects
    leftInput controls hcontrolsAtLeft
  change ReferenceActivePhysicalHorizon.computedEvidence leftInput =
      ReferenceActivePhysicalHorizon.computedEvidence rightInput ∧
    let left := ReferenceActivePhysicalStep.step leftInput
    let right := ReferenceActivePhysicalStep.step rightInput
    left.next = right.next ∧
      left.preparation.arms.actions = right.preparation.arms.actions ∧
      left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
      left.ownEntries = right.ownEntries ∧
      left.coordinator = right.coordinator ∧ left.followers = right.followers
  rw [hleftFrame, hrightFrame]
  exact hphysical

theorem ae_pairedSource_effects (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) (boundary : RoundInput p rate) :
    ∀ᵐ sources ∂pairedSourceLaw p rate boundary,
      ReferenceActivePhysicalHorizon.computedEvidence
          (roundInputAtSource p rate boundary sources.1) =
        ReferenceActivePhysicalHorizon.computedEvidence
          (roundInputAtSource p rate boundary sources.2) ∧
        let left := ReferenceActivePhysicalStep.step
          (roundInputAtSource p rate boundary sources.1)
        let right := ReferenceActivePhysicalStep.step
          (roundInputAtSource p rate boundary sources.2)
        left.next = right.next ∧
          left.preparation.arms.actions = right.preparation.arms.actions ∧
          left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
          left.ownEntries = right.ownEntries ∧
          left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  filter_upwards [ae_pairedSourceFibreEvent p rate boundary] with sources hsources
  exact pairedSourceFibreEvent_effects p rate boundary sources hsources

end Bandits.Support.ReferenceFixedTimeSourceControlCoupling

end
