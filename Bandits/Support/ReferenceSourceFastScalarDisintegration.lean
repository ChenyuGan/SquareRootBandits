/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFixedTimeSourceControlCoupling

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fixed-time disintegration of the original FAST scalar

For each literal selected row and fixed calendar time, this module refines the
accepted complete-control split by extracting only the `fast` scalar. Every
other scalar, the complete affine vector, the accepted fixed-control
remainder, and all private coordinates are retained. Restricting to the
original private coordinator-index stratum gives an unnormalized remainder
measure and an exact disintegration of tests of the complete source together
with a deterministic arm selected from the same extracted scalar.

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-426`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceSelectedAffinePairLaw

namespace Bandits.Support.ReferenceSourceFastScalarDisintegration

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev ScalarLabel (p : Parameters) := ContinuousLearningRows.Label p
abbrev FastLabel (p : Parameters) : ScalarLabel p :=
  (ContinuousControlSlice.Label.fast : ContinuousLearningRows.Label p)
abbrev OtherFast (p : Parameters) := ReferenceSelectedAffinePairLaw.Other (FastLabel p)
abbrev AffineSamples (p : Parameters) := ContinuousLearningRows.AffineSamples p
abbrev TimeControl (p : Parameters) := ContinuousLearningRows.TimeControl p
abbrev FixedRemainder (p : Parameters) :=
  ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p

abbrev FastScalarRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ((OtherFast p → Scalar) × AffineSamples p) × FixedRemainder p q t

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- Extract precisely the `fast` coordinate of one literal continuous slice.
The remaining scalar labels and the full affine vector stay in the remainder. -/
def fastScalarControlSplit (p : Parameters) :
    TimeControl p ≃ᵐ Scalar × ((OtherFast p → Scalar) × AffineSamples p) :=
  ReferenceSelectedAffinePairLaw.extractLeft
    (ReferenceSelectedAffinePairLaw.piExtract (FastLabel p))

private theorem extractLeft_apply {X S R Y : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace Y]
    (e : X ≃ᵐ S × R) (x : X) (y : Y) :
    ReferenceSelectedAffinePairLaw.extractLeft e (x, y) =
      Prod.mk (e x).1 (Prod.mk (e x).2 y) := by
  simp [ReferenceSelectedAffinePairLaw.extractLeft, MeasurableEquiv.prodCongr,
    Equiv.prodCongr_apply, MeasurableEquiv.prodAssoc, Equiv.prodAssoc_apply]

theorem fastScalarControlSplit_apply (p : Parameters) (control : TimeControl p) :
    fastScalarControlSplit p control =
      (control.1 (FastLabel p),
        (fun label : OtherFast p => control.1 label.val, control.2)) := by
  simp [fastScalarControlSplit, ReferenceSelectedAffinePairLaw.extractLeft,
    ReferenceSelectedAffinePairLaw.piExtract_apply,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    MeasurableEquiv.prodAssoc, Equiv.prodAssoc_apply]

/-- The complete original source, split first at its actual fixed-row/current-
time control and then at that control's single FAST scalar. -/
def sourceFastScalarSplit (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    SourceInput p ≃ᵐ Scalar × FastScalarRemainder p q t :=
  (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).trans
    (ReferenceSelectedAffinePairLaw.extractLeft (fastScalarControlSplit p))

theorem sourceFastScalarSplit_apply (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    sourceFastScalarSplit p q t source =
      Prod.mk
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1.1
          (FastLabel p))
        (Prod.mk
          (Prod.mk
            (fun label : OtherFast p =>
              (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1.1 label.val)
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1.2)
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) := by
  rw [sourceFastScalarSplit, MeasurableEquiv.coe_trans, Function.comp_apply,
    extractLeft_apply, fastScalarControlSplit_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]

/-- The scalar law, all remaining scalar labels, the complete affine vector,
and the same accepted fixed-control remainder restricted only by the original
private `J=q` stratum. This measure is intentionally unnormalized. -/
def fastScalarRemainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    Measure (FastScalarRemainder p q t) :=
  ((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
      (ContinuousLearningRows.affineSamplesLaw p)).prod
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
      (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t))

theorem fastScalarControlSplit_measurePreserving (p : Parameters) :
    MeasurePreserving (fastScalarControlSplit p)
      (ContinuousLearningRows.timeControlLaw p)
      (ContinuousControlSlice.scalarLaw.prod
        ((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
          (ContinuousLearningRows.affineSamplesLaw p))) := by
  change MeasurePreserving
    (ReferenceSelectedAffinePairLaw.extractLeft
      (ReferenceSelectedAffinePairLaw.piExtract (FastLabel p)))
    ((ContinuousControlSlice.sliceLaw p.m p.K).prod
      (ContinuousLearningRows.affineSamplesLaw p))
    (ContinuousControlSlice.scalarLaw.prod
      ((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
        (ContinuousLearningRows.affineSamplesLaw p)))
  exact ReferenceSelectedAffinePairLaw.measurePreserving_extractLeft
    (ReferenceSelectedAffinePairLaw.piExtract (FastLabel p))
    (ContinuousControlSlice.sliceLaw p.m p.K)
    ContinuousControlSlice.scalarLaw
    (Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw))
    (ContinuousLearningRows.affineSamplesLaw p)
    (ReferenceSelectedAffinePairLaw.measurePreserving_piExtract (FastLabel p)
      ContinuousControlSlice.scalarLaw)

theorem sourceFastScalarSplit_measurePreserving (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    MeasurePreserving (sourceFastScalarSplit p q t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p)
      (ContinuousControlSlice.scalarLaw.prod
        (((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
          (ContinuousLearningRows.affineSamplesLaw p)).prod
          (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t))) := by
  exact
    (ReferenceSelectedAffinePairLaw.measurePreserving_extractLeft
      (fastScalarControlSplit p)
      (ContinuousLearningRows.timeControlLaw p)
      ContinuousControlSlice.scalarLaw
      ((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
        (ContinuousLearningRows.affineSamplesLaw p))
      (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t)
      (fastScalarControlSplit_measurePreserving p)).comp
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_measurePreserving p q t)

/-- The scalar extraction remains a measurable equivalence in both directions. -/
theorem measurable_sourceFastScalarSplit (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) : Measurable (sourceFastScalarSplit p q t) :=
  (sourceFastScalarSplit p q t).measurable

theorem measurable_sourceFastScalarSplit_symm (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) : Measurable (sourceFastScalarSplit p q t).symm :=
  (sourceFastScalarSplit p q t).symm.measurable

/-- The first coordinate is the literal `fast` scalar in the selected row and
fixed time. -/
theorem sourceFastScalarSplit_fast (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).1 = ((source.1.2 q).2 t).1 (FastLabel p) := by
  simp only [sourceFastScalarSplit_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]

/-- Every non-FAST scalar of the complete selected slice is retained. -/
theorem sourceFastScalarSplit_otherScalar (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) (label : OtherFast p) :
    (sourceFastScalarSplit p q t source).2.1.1 label =
      ((source.1.2 q).2 t).1 label.val := by
  simp only [sourceFastScalarSplit_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]

/-- Every affine channel, including the entire assignment-independent vector,
is retained exactly. -/
theorem sourceFastScalarSplit_affineSamples (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).2.1.2 = ((source.1.2 q).2 t).2 := by
  simp only [sourceFastScalarSplit_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]

theorem sourceFastScalarSplit_affineChannel (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) (channel : ContinuousLearningRows.Channel p) :
    (sourceFastScalarSplit p q t source).2.1.2 channel =
      ((source.1.2 q).2 t).2 channel := by
  simp only [sourceFastScalarSplit_apply,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]

/-- The fixed-control remainder is precisely the one from the accepted
whole-control split. -/
theorem sourceFastScalarSplit_fixedRemainder (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).2.2 =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 := by
  simp only [sourceFastScalarSplit_apply]

theorem sourceFastScalarSplit_idArray (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).2.2.1.1 = source.1.1 := rfl

theorem sourceFastScalarSplit_selectedForwardRow (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).2.2.1.2.1.1 = (source.1.2 q).1 := rfl

/-- All other dates in the selected row remain in their original positions. -/
theorem sourceFastScalarSplit_otherTime (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p)
    (s : ReferenceSelectedAffinePairLaw.Other t) :
    (sourceFastScalarSplit p q t source).2.2.1.2.1.2 s = (source.1.2 q).2 s := rfl

/-- Every other complete row remains in its original position. -/
theorem sourceFastScalarSplit_otherRow (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p)
    (j : ReferenceSelectedAffinePairLaw.Other q) :
    (sourceFastScalarSplit p q t source).2.2.1.2.2 j = source.1.2 j := rfl

/-- All original private arrays and streams, including the coordinator scalar
that determines `J`, are retained verbatim. -/
theorem sourceFastScalarSplit_private (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t source).2.2.2 = source.2 := rfl

theorem sourceFastScalarSplit_coordinatorIndex (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    PrivateSourceStreams.coordinatorIndex p
      (sourceFastScalarSplit p q t source).2.2.2.1.2 =
        PrivateSourceStreams.coordinatorIndex p source.2.1.2 := rfl

/-- Exact inverse identities for sources and extracted scalar/remainder pairs. -/
theorem sourceFastScalarSplit_reconstruct (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (source : SourceInput p) :
    (sourceFastScalarSplit p q t).symm (sourceFastScalarSplit p q t source) = source :=
  (sourceFastScalarSplit p q t).symm_apply_apply source

theorem sourceFastScalarSplit_split_reconstruct (p : Parameters) (q : Fin (M p))
    (t : Fin p.T) (value : Scalar × FastScalarRemainder p q t) :
    sourceFastScalarSplit p q t ((sourceFastScalarSplit p q t).symm value) = value :=
  (sourceFastScalarSplit p q t).apply_symm_apply value

/-- On the actual original `J=q` stratum, replacing the extracted scalar
reconstructs the accepted literal source replacement exactly. -/
theorem sourceFastScalarSplit_replaceSourceControl (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (source : SourceInput p) (f : Scalar)
    (hJ : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q) :
    (sourceFastScalarSplit p q t).symm
        (f, (sourceFastScalarSplit p q t source).2) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source
        (Function.update (((source.1.2 q).2 t).1) (FastLabel p) f,
          ((source.1.2 q).2 t).2) := by
  let newSlice := Function.update ((source.1.2 q).2 t).1 (FastLabel p) f
  let newControl : TimeControl p := (newSlice, ((source.1.2 q).2 t).2)
  have hfixed :
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source newControl) =
        (newControl,
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) := by
    have hreplace :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
        p q t source newControl hJ
    have hmap := congrArg (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t) hreplace
    simpa only [(ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply]
      using hmap.symm
  apply (sourceFastScalarSplit p q t).injective
  rw [(sourceFastScalarSplit p q t).apply_symm_apply]
  symm
  change sourceFastScalarSplit p q t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source newControl) =
    (f, (sourceFastScalarSplit p q t source).2)
  rw [sourceFastScalarSplit_apply, hfixed, sourceFastScalarSplit_apply]
  apply Prod.ext
  · simp [newControl, newSlice, Function.update_self]
  · apply Prod.ext
    · apply Prod.ext
      · funext label
        simp only [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
        simp [newControl, newSlice, Function.update_of_ne label.property]
      · rfl
    · rfl

/-- Restricting the source to its actual fixed-`J` stratum and applying the
scalar split gives exactly scalar law times the unnormalized literal remainder
law. The proof starts from the accepted whole-control private-stratum map. -/
theorem sourceFastScalarSplit_privateStratum_map (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    Measure.map (sourceFastScalarSplit p q t)
        ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) =
      ContinuousControlSlice.scalarLaw.prod (fastScalarRemainderLaw p q t) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let extract : TimeControl p × FixedRemainder p q t ≃ᵐ
      Scalar × FastScalarRemainder p q t :=
    ReferenceSelectedAffinePairLaw.extractLeft (fastScalarControlSplit p)
  let stratumLaw :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
      (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
  have hstratumSFinite : SFinite stratumLaw := by
    dsimp [stratumLaw]
    infer_instance
  let _ : SFinite stratumLaw := hstratumSFinite
  have hextract : MeasurePreserving extract
      ((ContinuousLearningRows.timeControlLaw p).prod stratumLaw)
      (ContinuousControlSlice.scalarLaw.prod
        (((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
          (ContinuousLearningRows.affineSamplesLaw p)).prod stratumLaw)) := by
    exact ReferenceSelectedAffinePairLaw.measurePreserving_extractLeft
      (fastScalarControlSplit p)
      (ContinuousLearningRows.timeControlLaw p)
      ContinuousControlSlice.scalarLaw
      ((Measure.pi (fun _ : OtherFast p => ContinuousControlSlice.scalarLaw)).prod
        (ContinuousLearningRows.affineSamplesLaw p))
      stratumLaw (fastScalarControlSplit_measurePreserving p)
  change Measure.map (extract ∘ split)
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) =
    ContinuousControlSlice.scalarLaw.prod (fastScalarRemainderLaw p q t)
  rw [← Measure.map_map extract.measurable split.measurable,
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map]
  rw [hextract.map_eq]
  rfl

/-- Applying the inverse split to the product law returns exactly the
restriction of the original source law to `J=q`. -/
theorem sourceFastScalarSplit_privateStratum_map_symm (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) :
    (ContinuousControlSlice.scalarLaw.prod (fastScalarRemainderLaw p q t)).map
        (sourceFastScalarSplit p q t).symm =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) := by
  calc
    _ = Measure.map (sourceFastScalarSplit p q t).symm
        (Measure.map (sourceFastScalarSplit p q t)
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q))) := by
      rw [sourceFastScalarSplit_privateStratum_map]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) := by
      rw [Measure.map_map (sourceFastScalarSplit p q t).symm.measurable
        (sourceFastScalarSplit p q t).measurable]
      simp

/-- The `J` strata form the actual disjoint finite partition of the complete
original source law. -/
theorem sourceStrata_sum (p : Parameters) :
    Measure.sum (fun q : Fin (M p) =>
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) =
      BootstrapPrivateRoundStreams.sourceInputLaw p := by
  have hdis : Pairwise (fun q r =>
      Disjoint (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro source hq hr
    simp only [ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      Set.mem_ofPred_eq] at hq hr
    exact hqr (hq.symm.trans hr)
  have hmeas : ∀ q : Fin (M p),
      MeasurableSet (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) :=
    fun q => ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q
  have hcover :
      (⋃ q : Fin (M p), ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) =
        Set.univ := by
    ext source
    constructor
    · intro _
      trivial
    · intro _
      simp only [Set.mem_iUnion]
      exact ⟨ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source, rfl⟩
  calc
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (⋃ q : Fin (M p), ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) :=
      (Measure.restrict_iUnion hdis hmeas).symm
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p := by
      rw [hcover, Measure.restrict_univ]

private theorem measurable_eval_finite {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    Measurable (fun z : (ι → α) × ι => z.1 z.2) := by
  classical
  intro s hs
  have hpre : {z : (ι → α) × ι | z.1 z.2 ∈ s} =
      ⋃ i : ι, {f : ι → α | f i ∈ s} ×ˢ ({i} : Set ι) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨z.2, hz, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  change MeasurableSet {z : (ι → α) × ι | z.1 z.2 ∈ s}
  rw [hpre]
  exact MeasurableSet.iUnion fun i =>
    (measurable_pi_apply i hs).prod (measurableSet_singleton i)

/-- The FAST scalar selected by the actual original private coordinator index. -/
def sourceFastScalar (p : Parameters) (t : Fin p.T) (source : SourceInput p) : Scalar :=
  ((source.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).2 t).1
    (FastLabel p)

theorem measurable_sourceFastScalar (p : Parameters) (t : Fin p.T) :
    Measurable (sourceFastScalar p t) := by
  have hrows : Measurable (fun source : SourceInput p => source.1.2) :=
    measurable_pi_iff.mpr (fun q => by fun_prop)
  have hindex : Measurable
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p) := by
    have hprivate : Measurable (fun source : SourceInput p => source.2.1.2) := by
      fun_prop
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp hprivate
  have hselected : Measurable (fun source : SourceInput p =>
      source.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)) := by
    have heval := measurable_eval_finite
      (ι := Fin (M p)) (α := CompletePublicTable.CompleteRow p)
    exact heval.comp (hrows.prodMk hindex)
  have htime : Measurable (fun source : SourceInput p =>
      (source.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).2 t) := by
    exact (measurable_pi_apply t).comp (measurable_snd.comp hselected)
  exact (measurable_pi_apply (FastLabel p)).comp (measurable_fst.comp htime)

private theorem sourceFastScalar_eq_split_on_stratum (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (source : SourceInput p)
    (hsource : source ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) :
    sourceFastScalar p t source = (sourceFastScalarSplit p q t source).1 := by
  change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q at hsource
  simp [sourceFastScalar, sourceFastScalarSplit_fast, hsource]

/-- Full-source nonnegative test-integral identity. The source-side arm and
the source reconstruction on the right use the same extracted FAST scalar.
The remainder factor keeps its literal, possibly subprobability mass. -/
theorem sourceFastScalar_lintegral (p : Parameters) (t : Fin p.T)
    {β : Type*} [MeasurableSpace β] (test : SourceInput p × β → ENNReal)
    (htest : Measurable test) (fastArm : Scalar → β) (hfastArm : Measurable fastArm) :
    ∫⁻ source, test (source, fastArm (sourceFastScalar p t source)) ∂
        BootstrapPrivateRoundStreams.sourceInputLaw p =
      ∑ q : Fin (M p),
        ∫⁻ remainder, ∫⁻ f, test
          ((sourceFastScalarSplit p q t).symm (f, remainder), fastArm f)
          ∂ContinuousControlSlice.scalarLaw ∂fastScalarRemainderLaw p q t := by
  let integrand : SourceInput p → ENNReal := fun source =>
    test (source, fastArm (sourceFastScalar p t source))
  have hintegrand : Measurable integrand := by
    exact htest.comp (measurable_id.prodMk (hfastArm.comp (measurable_sourceFastScalar p t)))
  calc
    _ = ∫⁻ source, integrand source ∂
        Measure.sum (fun q : Fin (M p) =>
          (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) := by
      rw [sourceStrata_sum]
    _ = ∑ q : Fin (M p),
        ∫⁻ source, integrand source ∂
          (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) := by
      rw [lintegral_sum_measure, tsum_fintype]
    _ = ∑ q : Fin (M p),
        ∫⁻ remainder, ∫⁻ f, test
          ((sourceFastScalarSplit p q t).symm (f, remainder), fastArm f)
          ∂ContinuousControlSlice.scalarLaw ∂fastScalarRemainderLaw p q t := by
      apply Finset.sum_congr rfl
      intro q _
      let split := sourceFastScalarSplit p q t
      let targetTest : Scalar × FastScalarRemainder p q t → ENNReal := fun z =>
        test (split.symm z, fastArm z.1)
      have hremainderSFinite : SFinite (fastScalarRemainderLaw p q t) := by
        unfold fastScalarRemainderLaw
        infer_instance
      let _ : SFinite (fastScalarRemainderLaw p q t) := hremainderSFinite
      have htargetTest : Measurable targetTest := by
        exact htest.comp (split.symm.measurable.prodMk (hfastArm.comp measurable_fst))
      have hsame : integrand =ᵐ[(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)]
          (fun source => targetTest (split source)) := by
        filter_upwards [ae_restrict_mem
          (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q)]
          with source hsource
        simp only [integrand, targetTest, split, MeasurableEquiv.symm_apply_apply]
        rw [sourceFastScalar_eq_split_on_stratum p q t source hsource]
      calc
        _ = ∫⁻ source, targetTest (split source) ∂
            (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
              (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q) :=
          lintegral_congr_ae hsame
        _ = ∫⁻ z, targetTest z ∂
            ContinuousControlSlice.scalarLaw.prod (fastScalarRemainderLaw p q t) := by
          rw [← sourceFastScalarSplit_privateStratum_map p q t]
          exact (lintegral_map htargetTest split.measurable).symm
        _ = ∫⁻ remainder, ∫⁻ f, test
            ((sourceFastScalarSplit p q t).symm (f, remainder), fastArm f)
            ∂ContinuousControlSlice.scalarLaw ∂fastScalarRemainderLaw p q t := by
          rw [← lintegral_prod_swap (μ := ContinuousControlSlice.scalarLaw)
            (ν := fastScalarRemainderLaw p q t) targetTest]
          exact lintegral_prod (fun z => targetTest z.swap)
            (htargetTest.comp measurable_swap).aemeasurable

/-- Source-only specialization of the complete-source test identity. -/
theorem source_lintegral (p : Parameters) (t : Fin p.T)
    (test : SourceInput p → ENNReal) (htest : Measurable test) :
    ∫⁻ source, test source ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      ∑ q : Fin (M p),
        ∫⁻ remainder, ∫⁻ f, test ((sourceFastScalarSplit p q t).symm (f, remainder))
          ∂ContinuousControlSlice.scalarLaw ∂fastScalarRemainderLaw p q t := by
  simpa only [Prod.fst] using sourceFastScalar_lintegral p t
    (fun z : SourceInput p × Scalar => test z.1)
    (htest.comp measurable_fst) (fun f => f) measurable_id

end Bandits.Support.ReferenceSourceFastScalarDisintegration

end
