/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport

/-!
# First-collection FAST evaluation with the original prefix observer

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

The incoming set is read from the existing observer list. The observer keeps
the whole label-zero array and the strict source prefix. Only the current
FAST coordinate is integrated, after retaining the incoming overflow gate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical
open Bandits.Support ConstructorDimensions ContinuousControlSlice
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstCollectionOneRoundLogicalCell

namespace Bandits.Support.ReferenceGeneratedCalendarPrefixCollectionFast

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "O" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate

/-- The literal COLLECTION branch of the existing prefix candidate. -/
def collectionBranch (q : Fin p.T)
    (v : O × (ContinuousLearningRows.TimeControl p × Scalar)) :
    Option (LogicalCell p rate) :=
  let d := extensionInput rate q v
  match currentCellTag rate rewards C_star C_h q d.1 with
  | .inr _ => none
  | .inl _ => match d.2.1 with
    | none => none
    | some U => collectionCellAt rate rewards C_star C_h q U d.1

/-- The actual first-LAUNCH unit anchor and the complete incoming PRE weights. -/
def unitFastPMF (S : RecordedQueueRun.RunState p.K) (U : SlowSet p) :
    PMF (CanonicalFastSampling.FastArm U) :=
  ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (fun _ => 1)
    (RecordedQueueRun.scoreWeight Q S) (fun _ => zero_lt_one)
    (RecordedSlowRefresh.scoreWeight_pos Q S) U

omit rewards C_star C_h in
/-- Incoming overflow is the only analytical stop gate in the test. -/
def retainedFastTest (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (o : O) (c : Option (LogicalCell p rate)) : ℝ≥0∞ :=
  c.elim 0 (fun e => if e.before.overflow = false then Phi (o, (e.slowSet, e.fastArm)) else 0)

omit rewards C_star C_h in
/-- Finite FAST expectation, using the same cell's incoming state and slow set. -/
def averagedFastTest (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (o : O) (c : Option (LogicalCell p rate)) : ℝ≥0∞ :=
  c.elim 0 (fun e => if e.before.overflow = false then
    ∑ j : CanonicalFastSampling.FastArm e.slowSet,
      Phi (o, (e.slowSet, j.val)) * unitFastPMF rate e.before e.slowSet j else 0)

/-- LIVE priority does not discard any actual first-COLLECTION cell. -/
theorem collectionBranch_eq (q : Fin p.T)
    (v : O × (ContinuousLearningRows.TimeControl p × Scalar)) :
    collectionBranch rate rewards C_star C_h q v =
      (incomingFromList rate v.1.2.2).bind (fun U =>
        collectionCellAt rate rewards C_star C_h q U (extensionInput rate q v).1) := by
  let d := extensionInput rate q v
  by_cases hz : d.1.1 ∈ actualDomain (rate := rate) rewards C_star C_h q
  · have ht := currentCellTag_absent_of_actualDomain rate rewards C_star C_h q d.1.1 d.1.2 hz
    change (match currentCellTag rate rewards C_star C_h q d.1 with
      | .inr _ => none
      | .inl _ => match d.2.1 with
        | none => none
        | some U => collectionCellAt rate rewards C_star C_h q U d.1) = _
    rw [ht]
    change (match incomingFromList rate v.1.2.2 with
      | none => none
      | some U => collectionCellAt rate rewards C_star C_h q U d.1) =
      (incomingFromList rate v.1.2.2).bind (fun U => collectionCellAt rate rewards C_star C_h q U d.1)
    cases incomingFromList rate v.1.2.2 <;> rfl
  · have hc (U : SlowSet p) : collectionCellAt rate rewards C_star C_h q U d.1 = none := by
      simp only [collectionCellAt, sourceCell?, dite_eq_right hz]
    change (match currentCellTag rate rewards C_star C_h q d.1 with
      | .inr _ => none
      | .inl _ => match incomingFromList rate v.1.2.2 with
        | none => none
        | some U => collectionCellAt rate rewards C_star C_h q U d.1) =
      (incomingFromList rate v.1.2.2).bind (fun U => collectionCellAt rate rewards C_star C_h q U d.1)
    cases currentCellTag rate rewards C_star C_h q d.1 <;>
      cases incomingFromList rate v.1.2.2 <;> simp only [Option.bind_none, Option.bind_some, hc]

section Native

variable (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T)
  (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
  (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r)
  (hm : r ∈ firstCollection (rate := rate) rewards C_star C_h z)

local notation "S" => RecordedQueueRun.run Q (actualPast rewards C_star C_h z q r hr hm)

/-- The genuine sampler marginal equals the literal native unit-anchor PMF. -/
theorem actualFast_map_unit (U : SlowSet p) :
    scalarLaw.map (actualFast rewards C_star C_h z q r hr hm U) =
      (unitFastPMF rate S U).toMeasure := by
  rw [actualFast_map]
  rfl

/-- Forgetting the actual residual result leaves the same before-state and FAST
test, including bottom recorder outcomes and the first detecting UPDATE. -/
theorem cellWithScalar_fast_lintegral (U : SlowSet p) (a0 : Fin p.T → Scalar)
    (x : Scalar) (o : O) (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    (∫⁻ f, retainedFastTest rate Phi o
      (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) ∂scalarLaw) =
    ∫⁻ f, averagedFastTest rate Phi o
      (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) ∂scalarLaw := by
  by_cases hc : (actualInput rewards C_star C_h z q r hr hm).enabled = true
  · by_cases hs : (S).overflow = false
    · have hl (f : Scalar) : retainedFastTest rate Phi o
          (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) =
          Phi (o, (U, (actualFast rewards C_star C_h z q r hr hm U f).val)) := by
        simp only [cellWithScalar?, hc, ite_true, retainedFastTest, Option.elim_some,
          cellWithScalar, cellWithNext, hs, Bool.false_eq_true, ite_false]
      have hright (f : Scalar) : averagedFastTest rate Phi o
          (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) =
          ∑ j : CanonicalFastSampling.FastArm U, Phi (o, (U, j.val)) * unitFastPMF rate S U j := by
        simp only [cellWithScalar?, hc, ite_true, averagedFastTest, Option.elim_some,
          cellWithScalar, cellWithNext, hs, Bool.false_eq_true, ite_false]
      simp_rw [hl, hright]
      rw [lintegral_const, measure_univ, mul_one]
      have htest : Measurable (fun j : CanonicalFastSampling.FastArm U => Phi (o, (U, j.val))) :=
        measurable_of_countable _
      rw [← lintegral_map htest (measurable_actualFast rewards C_star C_h z q r hr hm U),
        actualFast_map_unit, lintegral_fintype]
      apply Finset.sum_congr rfl
      intro j _
      rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]
    · have hzero (f : Scalar) : retainedFastTest rate Phi o
          (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) = 0 ∧
          averagedFastTest rate Phi o
          (cellWithScalar? rewards C_star C_h z q r hr hm U a0 f x) = 0 := by
        simp only [cellWithScalar?, hc, ite_true, retainedFastTest, averagedFastTest,
          Option.elim_some, cellWithScalar, cellWithNext, hs, Bool.true_eq_false, ite_false, and_self]
      simp_rw [(hzero _).1, (hzero _).2]
  · simp only [cellWithScalar?, hc, Bool.false_eq_true, ite_false, retainedFastTest,
      averagedFastTest, Option.elim_none]

end Native

section Insertion

open Bandits.Support.ReferenceFirstCollectionFastErasure (insertCurrentFastScalar replaceFastScalar)
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

/-- Presence of an actual first-COLLECTION record is unchanged by current FAST. -/
theorem actualDomain_insert_iff (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) (f : Scalar) :
    insertCurrentFastScalar q z f ∈ actualDomain (rate := rate) rewards C_star C_h q ↔
      z ∈ actualDomain (rate := rate) rewards C_star C_h q := by
  rw [actualDomain_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl,
    ReferenceFirstCollectionFastErasure.sourcePrefix_strictPast_insert_eq,
    ← actualDomain_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl]

/-- The inserted-source operation has the original PRE and numerical input.
This includes genuine absence outside the first physical collection. -/
theorem sourceCell_insert (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (U : SlowSet p) (a0 : Fin p.T → Scalar)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (f g x : Scalar) :
    sourceCell? (rate := rate) rewards C_star C_h q U a0
        (insertCurrentFastScalar q z f) g x =
      sourceCell? (rate := rate) rewards C_star C_h q U a0 z g x := by
  by_cases hz : z ∈ actualDomain (rate := rate) rewards C_star C_h q
  · have hz' := (actualDomain_insert_iff rate rewards C_star C_h control0 q z f).mpr hz
    let d : ActualSource (rate := rate) rewards C_star C_h q := ⟨z, hz⟩
    let r := domainRecord rewards C_star C_h q d
    have hr := domainRecord_spec rewards C_star C_h q d
    have hm := domainRecord_mem rewards C_star C_h q d
    have he : domainRecord rewards C_star C_h q ⟨insertCurrentFastScalar q z f, hz'⟩ =
        insertedRecord rewards C_star C_h z q r hr hm f :=
      Option.some.inj ((domainRecord_spec rewards C_star C_h q
        ⟨insertCurrentFastScalar q z f, hz'⟩).symm.trans
        (insertedRecord_spec rewards C_star C_h z q r hr hm f))
    simp only [sourceCell?, dite_eq_left hz, dite_eq_left hz', he]
    unfold cellWithScalar?
    rw [actualInput_insert, cellWithScalar_insert]
  · have hz' := (actualDomain_insert_iff rate rewards C_star C_h control0 q z f).not.mpr hz
    simp only [sourceCell?, dite_eq_right hz, dite_eq_right hz']

omit rate rewards C_star C_h in
/-- Replacing the full current control twice retains exactly the second one. -/
theorem replaceSourceControl_twice (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c d : ContinuousLearningRows.TimeControl p) :
    replaceSourceControl p q (replaceSourceControl p q z c) d = replaceSourceControl p q z d := by
  simp only [replaceSourceControl, ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    Function.update_self, Function.update_idem]

omit rate rewards C_star C_h in
/-- Source reconstruction commutes with inserting FAST in the current control. -/
theorem replaceSourceControl_fast (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) (f : Scalar) :
    replaceSourceControl p q z (replaceFastScalar c f) =
      insertCurrentFastScalar q (replaceSourceControl p q z c) f := by
  simp only [insertCurrentFastScalar,
    replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self,
    Function.update_idem]

end Insertion

section Innovation

open Bandits.Support.ReferenceFirstCollectionFastErasure (insertCurrentFastScalar replaceFastScalar)
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)

omit rate rewards C_star C_h in
/-- The accepted control split reconstructs precisely a FAST insertion. -/
theorem fastScalarControlSplit_symm_replace (c : ContinuousLearningRows.TimeControl p) (f : Scalar) :
    (ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p).symm
      (f, (ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p c).2) =
      replaceFastScalar c f := by
  apply (ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p).injective
  rw [MeasurableEquiv.apply_symm_apply,
    ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_apply,
    ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_apply]
  simp only [replaceFastScalar, Function.update_self]
  congr 2
  funext l
  exact (Function.update_of_ne l.property _ _).symm

/-- Fixed-source local evaluation, with absence and disabled dates included. -/
theorem sourceCell_fast_lintegral (q : Fin p.T) (U : SlowSet p)
    (a0 : Fin p.T → Scalar) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (x : Scalar) (o : O) (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    (∫⁻ f, retainedFastTest rate Phi o
      (sourceCell? (rate := rate) rewards C_star C_h q U a0 z f x) ∂scalarLaw) =
    ∫⁻ f, averagedFastTest rate Phi o
      (sourceCell? (rate := rate) rewards C_star C_h q U a0 z f x) ∂scalarLaw := by
  by_cases hz : z ∈ actualDomain (rate := rate) rewards C_star C_h q
  · simp only [sourceCell?, dite_eq_left hz]
    exact cellWithScalar_fast_lintegral rate rewards C_star C_h z q
      (domainRecord rewards C_star C_h q ⟨z, hz⟩)
      (domainRecord_spec rewards C_star C_h q ⟨z, hz⟩)
      (domainRecord_mem rewards C_star C_h q ⟨z, hz⟩) U a0 x o Phi
  · simp only [sourceCell?, dite_eq_right hz, retainedFastTest, averagedFastTest, Option.elim_none]

/-- The same observer and incoming set are retained while current FAST varies.
The residual scalar is the actual current label-one coordinate. -/
theorem collectionCellAt_insert_fast_lintegral (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (U : SlowSet p) (a0 : Fin p.T → Scalar)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (x : Scalar)
    (o : O) (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    (∫⁻ f, retainedFastTest rate Phi o
      (collectionCellAt rate rewards C_star C_h q U
        (insertCurrentFastScalar q z f, roundAuxiliary q (a0, x))) ∂scalarLaw) =
    ∫⁻ f, averagedFastTest rate Phi o
      (collectionCellAt rate rewards C_star C_h q U
        (insertCurrentFastScalar q z f, roundAuxiliary q (a0, x))) ∂scalarLaw := by
  have h0 : labelZero (roundAuxiliary q (a0, x)) = a0 := by
    funext t
    simp only [labelZero, roundAuxiliary, ite_true]
  have h1 : roundAuxiliary q (a0, x) (q, 1) = x := by
    simp only [roundAuxiliary, (show (1 : Fin 2) ≠ 0 by decide), ite_false, ite_true]
  simp only [collectionCellAt, h0, h1, sourceFastScalar_insert,
    sourceCell_insert rate rewards C_star C_h control0]
  exact sourceCell_fast_lintegral rate rewards C_star C_h q U a0 z x o Phi

end Innovation

section Measurability

private theorem measurable_optionalTest
    (F : O × LogicalCell p rate → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun v : O × Option (LogicalCell p rate) => v.2.elim 0 (fun e => F (v.1, e))) := by
  have hs : Measurable (Sum.elim F (fun _ : O × PUnit => (0 : ℝ≥0∞))) :=
    hF.sumElim measurable_const
  have he := (MeasurableEquiv.prodSumDistrib O (LogicalCell p rate) PUnit).measurable.comp
    (measurable_fst.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))).comp
      measurable_snd))
  convert hs.comp he using 1
  funext v
  rcases v with ⟨o, e⟩
  cases e <;> rfl

omit rewards C_star C_h in
theorem measurable_retainedFastTest (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (fun v : O × Option (LogicalCell p rate) => retainedFastTest rate Phi v.1 v.2) := by
  unfold retainedFastTest
  refine measurable_optionalTest rate (fun w => if w.2.before.overflow = false then
    Phi (w.1, (w.2.slowSet, w.2.fastArm)) else 0) ?_
  have ho : Measurable (fun v : O × LogicalCell p rate => v.2.before.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp
      (measurable_logicalCell_before.comp measurable_snd)
  exact (hPhi.comp (measurable_fst.prodMk
    (((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd).prodMk
      (measurable_logicalCell_fastArm.comp measurable_snd)))).ite
        ((measurableSet_singleton false).preimage ho) measurable_const

omit rewards C_star C_h in
theorem measurable_averagedFastTest (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (fun v : O × Option (LogicalCell p rate) => averagedFastTest rate Phi v.1 v.2) := by
  unfold averagedFastTest
  refine measurable_optionalTest rate (fun w => if w.2.before.overflow = false then
    ∑ j : CanonicalFastSampling.FastArm w.2.slowSet,
      Phi (w.1, (w.2.slowSet, j.val)) * unitFastPMF rate w.2.before w.2.slowSet j else 0) ?_
  let F := fun v : O × (RecordedQueueRun.RunState p.K × SlowSet p) =>
    if v.2.1.overflow = false then
      ∑ j : CanonicalFastSampling.FastArm v.2.2,
        Phi (v.1, (v.2.2, j.val)) * unitFastPMF rate v.2.1 v.2.2 j else 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro su
    dsimp only [F]
    by_cases h : su.1.overflow = false
    · simp only [h, ite_true]
      have hj (j : CanonicalFastSampling.FastArm su.2) :
          Measurable (fun o : O => Phi (o, (su.2, j.val)) * unitFastPMF rate su.1 su.2 j) :=
        (hPhi.comp (measurable_id.prodMk (measurable_const (a := (su.2, j.val))))).mul_const
          (unitFastPMF rate su.1 su.2 j)
      exact Finset.measurable_fun_sum Finset.univ (fun j _ => hj j)
    · simp only [h]
      exact measurable_const
  exact hF.comp (measurable_fst.prodMk
    ((measurable_logicalCell_before.comp measurable_snd).prodMk
      ((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd)))

end Measurability

section Composition

open Bandits.Support.ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open Bandits.Support.ReferenceFirstCollectionFastErasure (insertCurrentFastScalar replaceFastScalar)

private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun v => match o v with | none => f v | some a => g (v, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext v
  cases h : o v <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

private theorem measurable_optionalCollection (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) :
    Measurable (fun v : Option (SlowSet p) ×
      (BootstrapPrivateRoundStreams.SourceInput p × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) =>
      v.1.bind (fun U => collectionCellAt rate rewards C_star C_h q U v.2)) := by
  let X := Option (SlowSet p) ×
    (BootstrapPrivateRoundStreams.SourceInput p × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
  let F : SlowSet p ×
      (BootstrapPrivateRoundStreams.SourceInput p × ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) →
      Option (LogicalCell p rate) := fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2
  have hF : Measurable F :=
    ReferenceFirstCollectionLogicalPrefixExtension.measurable_collectionCellAt
      rate rewards C_star C_h control0 q
  have hp : Measurable (fun v : X × SlowSet p => (v.2, v.1.2)) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hg : Measurable (fun v : X × SlowSet p => F (v.2, v.1.2)) := hF.comp hp
  have hm := measurable_option_cases (Prod.fst : X → Option (SlowSet p)) measurable_fst
    (fun _ => (none : Option (LogicalCell p rate))) measurable_const _ hg
  convert hm using 1
  funext v
  cases v.1 <;> rfl

/-- Borelness uses the existing source, list and collection operation. -/
theorem measurable_collectionBranch (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T) :
    Measurable (collectionBranch rate rewards C_star C_h q) := by
  have hi : Measurable (fun v : O × (ContinuousLearningRows.TimeControl p × Scalar) =>
      incomingFromList rate v.1.2.2) :=
    (measurable_incomingFromList rate).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hin : Measurable (fun v : O × (ContinuousLearningRows.TimeControl p × Scalar) =>
      (extensionInput rate q v).1) := measurable_fst.comp (measurable_extensionInput rate q)
  have hm := (measurable_optionalCollection rate rewards C_star C_h control0 q).comp (hi.prodMk hin)
  have heq : collectionBranch rate rewards C_star C_h q = fun v =>
      (incomingFromList rate v.1.2.2).bind (fun U =>
        collectionCellAt rate rewards C_star C_h q U (extensionInput rate q v).1) :=
    funext (collectionBranch_eq rate rewards C_star C_h q)
  rw [heq]
  exact hm

omit rate rewards C_star C_h in
private theorem innovation_fast_split_lintegral
    (F : ContinuousLearningRows.TimeControl p × Scalar → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ux, F ux ∂calendarInnovationLaw p) =
      ∫⁻ x, ∫⁻ a, ∫⁻ f,
        F ((ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p).symm (f, a), x)
        ∂scalarLaw
        ∂(Measure.pi (fun _ : ReferenceSourceFastScalarDisintegration.OtherFast p => scalarLaw)).prod
          (ContinuousLearningRows.affineSamplesLaw p)
        ∂scalarLaw := by
  rw [calendarInnovationLaw, lintegral_prod_symm _ hF.aemeasurable]
  apply lintegral_congr
  intro x
  let e := ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p
  have hp := ReferenceSourceFastScalarDisintegration.fastScalarControlSplit_measurePreserving p
  rw [MeasurePreserving.lintegral_map_equiv (fun c => F (c, x)) e.symm hp.symm]
  exact lintegral_prod_symm _
    (hF.comp (e.symm.measurable.prodMk measurable_const)).aemeasurable

/-- Current innovation evaluation retains the entire original observer. No
distributional assumption on its incoming list or slow set is required. -/
theorem collection_innovation_fast_lintegral (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (o : O) (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ ux, retainedFastTest rate Phi o
      (collectionBranch rate rewards C_star C_h q (o, ux)) ∂calendarInnovationLaw p) =
    ∫⁻ ux, averagedFastTest rate Phi o
      (collectionBranch rate rewards C_star C_h q (o, ux)) ∂calendarInnovationLaw p := by
  have hb : Measurable (fun ux => collectionBranch rate rewards C_star C_h q (o, ux)) :=
    (measurable_collectionBranch rate rewards C_star C_h control0 q).comp
      (measurable_const.prodMk measurable_id)
  have hleft : Measurable (fun ux => retainedFastTest rate Phi o
      (collectionBranch rate rewards C_star C_h q (o, ux))) :=
    (measurable_retainedFastTest rate Phi hPhi).comp (measurable_const.prodMk hb)
  have hright : Measurable (fun ux => averagedFastTest rate Phi o
      (collectionBranch rate rewards C_star C_h q (o, ux))) :=
    (measurable_averagedFastTest rate Phi hPhi).comp (measurable_const.prodMk hb)
  rw [innovation_fast_split_lintegral _ hleft, innovation_fast_split_lintegral _ hright]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro a
  let e := ReferenceSourceFastScalarDisintegration.fastScalarControlSplit p
  let c0 := e.symm (ReferenceFirstLiveActualRefreshTestLaw.scalarZero, a)
  have hc (f : Scalar) : e.symm (f, a) = replaceFastScalar c0 f := by
    have h := fastScalarControlSplit_symm_replace (p := p) c0 f
    have he : e c0 = (ReferenceFirstLiveActualRefreshTestLaw.scalarZero, a) :=
      e.apply_symm_apply _
    change e.symm (f, (e c0).2) = _ at h
    rw [he] at h
    exact h
  have hz (f : Scalar) : replaceSourceControl p q o.1 (e.symm (f, a)) =
      insertCurrentFastScalar q (replaceSourceControl p q o.1 c0) f := by
    rw [hc, replaceSourceControl_fast]
  simp_rw [collectionBranch_eq]
  cases hu : incomingFromList rate o.2.2 with
  | none => simp only [Option.bind_none, retainedFastTest, averagedFastTest, Option.elim_none]
  | some U =>
      simp only [Option.bind_some]
      change (∫⁻ f, retainedFastTest rate Phi o
        (collectionCellAt rate rewards C_star C_h q U
          (replaceSourceControl p q o.1 (e.symm (f, a)), roundAuxiliary q (o.2.1, x))) ∂scalarLaw) =
        ∫⁻ f, averagedFastTest rate Phi o
        (collectionCellAt rate rewards C_star C_h q U
          (replaceSourceControl p q o.1 (e.symm (f, a)), roundAuxiliary q (o.2.1, x))) ∂scalarLaw
      simp_rw [hz]
      exact collectionCellAt_insert_fast_lintegral rate rewards C_star C_h control0 q U o.2.1
        (replaceSourceControl p q o.1 c0) x o Phi

end Composition

/-- Actual first-COLLECTION FAST evaluation under the original killed,
unnormalized observer law, raw or at the same original ID atom. The current
no-call gate excludes ROOT at `q`; only incoming PRE overflow is tested. -/
theorem betaPre_collection_fast_joint_lintegral
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ v, if noCallAt rate rewards C_star C_h q v.1.1 then
        (collectionBranch rate rewards C_star C_h q v).elim 0 (fun e =>
          if e.before.overflow = false then Phi (v.1, (e.slowSet, e.fastArm)) else 0) else 0
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDBetaPre
          rate rewards C_star C_h control0 id q.castSucc)).prod (calendarInnovationLaw p)) =
    ∫⁻ v, if noCallAt rate rewards C_star C_h q v.1.1 then
        (collectionBranch rate rewards C_star C_h q v).elim 0 (fun e =>
          if e.before.overflow = false then
            ∑ j : CanonicalFastSampling.FastArm e.slowSet,
              Phi (v.1, (e.slowSet, j.val)) * unitFastPMF rate e.before e.slowSet j else 0) else 0
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDBetaPre
          rate rewards C_star C_h control0 id q.castSucc)).prod (calendarInnovationLaw p) := by
  let B := collectionBranch rate rewards C_star C_h q
  have hB := measurable_collectionBranch rate rewards C_star C_h control0 q
  have hgate : MeasurableSet {v : O × (ContinuousLearningRows.TimeControl p × Scalar) |
      noCallAt rate rewards C_star C_h q v.1.1} :=
    (measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage
      (measurable_fst.comp measurable_fst)
  have hl : Measurable (fun v : O × (ContinuousLearningRows.TimeControl p × Scalar) =>
      if noCallAt rate rewards C_star C_h q v.1.1 then retainedFastTest rate Phi v.1 (B v) else 0) :=
    ((measurable_retainedFastTest rate Phi hPhi).comp (measurable_fst.prodMk hB)).ite
      hgate measurable_const
  have hr : Measurable (fun v : O × (ContinuousLearningRows.TimeControl p × Scalar) =>
      if noCallAt rate rewards C_star C_h q v.1.1 then averagedFastTest rate Phi v.1 (B v) else 0) :=
    ((measurable_averagedFastTest rate Phi hPhi).comp (measurable_fst.prodMk hB)).ite
      hgate measurable_const
  change (∫⁻ v, if noCallAt rate rewards C_star C_h q v.1.1 then
      retainedFastTest rate Phi v.1 (B v) else 0
    ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDBetaPre
        rate rewards C_star C_h control0 id q.castSucc)).prod (calendarInnovationLaw p)) =
    ∫⁻ v, if noCallAt rate rewards C_star C_h q v.1.1 then
      averagedFastTest rate Phi v.1 (B v) else 0
    ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDBetaPre
        rate rewards C_star C_h control0 id q.castSucc)).prod (calendarInnovationLaw p)
  rw [lintegral_prod _ hl.aemeasurable, lintegral_prod _ hr.aemeasurable]
  apply lintegral_congr
  intro o
  by_cases hc : noCallAt rate rewards C_star C_h q o.1
  · simp only [hc, ite_true]
    exact collection_innovation_fast_lintegral rate rewards C_star C_h control0 q o Phi hPhi
  · simp only [hc, ite_false]

end Bandits.Support.ReferenceGeneratedCalendarPrefixCollectionFast

end
