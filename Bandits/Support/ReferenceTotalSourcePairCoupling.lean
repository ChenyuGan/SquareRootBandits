/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedSourceCoupling

/-!
# Fixed-calendar total coupling of the original source

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-423`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-46`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

At an ordinary calendar time, the literal active initialization strata are
glued with their already constructed unnormalized pair laws. The complement
uses the original-source diagonal law, so both complete-source marginals are
preserved without a success, positive-mass, or operational-state premise.
This construction is fixed-time only and asserts no chronological conditional
law. At the natural terminal time, the separate no-current-control branch is
the original-source diagonal measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceRetainedSourceCoupling
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical

namespace Bandits.Support.ReferenceTotalSourcePairCoupling

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceRetainedSourceCoupling.RateInput
abbrev SourceInput := ReferenceRetainedSourceCoupling.SourceInput
abbrev SourcePair (p : Parameters) := SourceInput p × SourceInput p
abbrev TimeControl := ReferenceRetainedSourceCoupling.TimeControl
abbrev StratumIndex {p : Parameters} (t : Fin p.T) := Fin (M p) × Fin (t.val + 1)

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private instance sourcePairMeasurableEqScalar :
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

private instance sourcePairMeasurableEqProd {α β : Type*} [MeasurableSpace α]
    [MeasurableEq α] [MeasurableSpace β] [MeasurableEq β] :
    MeasurableEq (α × β) where
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

private instance sourcePairMeasurableEqPi {ι : Type*} [Fintype ι] {α : ι → Type*}
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

private theorem measurableSet_eq_of_maps {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableEq β] (f g : α → β)
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  measurableSet_eq_fun hf hg

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (control0 : TimeControl p)

/-- The original-source event for one literal selected-row and elapsed-time
stratum. The original private coordinator scalar is retained by `R`. -/
def sourceStratumEvent (i : StratumIndex t) : Set (SourceInput p) :=
  ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h
    i.1 i.2.val

/-- The already proved, unnormalized retained pair law on one source stratum. -/
def sourceStratumPairLaw (i : StratumIndex t) : Measure (SourcePair p) :=
  ReferenceRetainedSourceCoupling.retainedSourcePairLaw rate rewards C_star C_h
    i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0

/-- The active set is the finite union of actual selected-row/elapsed strata. -/
def activeSourceSet : Set (SourceInput p) :=
  ⋃ i : StratumIndex t, sourceStratumEvent rate rewards C_star C_h t i

/-- The literal event that the corrected reference has crossed and its elapsed
boundary is at or before this calendar time. -/
def actualCrossingElapsedBy : Set (SourceInput p) :=
  {z | (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed ≤ t.val}

/-- Each active cell is exactly a Borel set from the retained construction. -/
theorem measurableSet_sourceStratumEvent (c0 : TimeControl p) (i : StratumIndex t) :
    MeasurableSet (sourceStratumEvent rate rewards C_star C_h t i) :=
  ReferenceRetainedSourceCoupling.measurableSet_retainedSourceEvent
    rate rewards C_star C_h i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) c0

/-- The active union is Borel, including when it is empty as a set. -/
theorem measurableSet_activeSourceSet (c0 : TimeControl p) :
    MeasurableSet (activeSourceSet rate rewards C_star C_h t) :=
  MeasurableSet.iUnion fun i => measurableSet_sourceStratumEvent rate rewards C_star C_h t c0 i

/-- Distinct cells disagree on the unique original coordinator index or the
unique actual elapsed boundary. -/
theorem sourceStratumEvent_disjoint (i j : StratumIndex t) (hij : i ≠ j) :
    Disjoint (sourceStratumEvent rate rewards C_star C_h t i)
      (sourceStratumEvent rate rewards C_star C_h t j) := by
  rw [Set.disjoint_left]
  intro z hi hj
  change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = i.1 ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = i.2.val at hi
  change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = j.1 ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = j.2.val at hj
  have hq : i.1 = j.1 := hi.1.symm.trans hj.1
  have hs : i.2.val = j.2.val := hi.2.2.symm.trans hj.2.2
  apply hij
  exact Prod.ext hq (Fin.ext hs)

/-- The finite union consists pointwise of exactly the actual crossing
sources whose elapsed boundary has occurred by `t`. -/
theorem activeSourceSet_eq_actualCrossingElapsedBy :
    activeSourceSet rate rewards C_star C_h t =
      actualCrossingElapsedBy rate rewards C_star C_h t := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = i.1 ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = i.2.val at hi
    refine ⟨hi.2.1, ?_⟩
    rw [hi.2.2]
    exact Nat.lt_succ_iff.mp i.2.isLt
  · intro hz
    change (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed ≤ t.val at hz
    let elapsed := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
    let i : StratumIndex t :=
      (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z,
        ⟨elapsed, Nat.lt_succ_of_le hz.2⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z = i.1 ∧
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = i.2.val
    simp only [i, elapsed, hz.1, and_self]

/-- The literal actual crossing event is Borel by its pointwise identity with
the finite union of retained source strata. -/
theorem measurableSet_actualCrossingElapsedBy (c0 : TimeControl p) :
    MeasurableSet (actualCrossingElapsedBy rate rewards C_star C_h t) := by
  rw [← activeSourceSet_eq_actualCrossingElapsedBy rate rewards C_star C_h t]
  exact measurableSet_activeSourceSet rate rewards C_star C_h t c0

/-- The unnormalized active strata partition the restricted original source
measure on the active set. -/
theorem sourceStrata_restrict_sum :
    (c0 : TimeControl p) →
    (sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t) =
      ∑ i : StratumIndex t,
        (sourceInputLaw p).restrict
          (ReferenceRetainedSourceCoupling.retainedSourceEvent rate rewards C_star C_h i.1 i.2.val) := by
  intro c0
  rw [activeSourceSet, Measure.restrict_iUnion
    (fun i j hij => sourceStratumEvent_disjoint rate rewards C_star C_h t i j hij)
    (fun i => measurableSet_sourceStratumEvent rate rewards C_star C_h t c0 i)]
  rw [Measure.sum_fintype]
  simp only [sourceStratumEvent]

/-- A diagonal copy is a measurable map of the original source space. -/
def sourceDiagonalMap {p : Parameters} : SourceInput p → SourcePair p := fun z => (z, z)

theorem measurable_sourceDiagonalMap {p : Parameters} : Measurable (@sourceDiagonalMap p) := by
  exact measurable_id.prodMk measurable_id

/-- The complement branch is a literal diagonal restriction of the original
source law; it is not an off-source operational default. -/
def complementDiagonalSourcePairLaw : Measure (SourcePair p) :=
  ((sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t)ᶜ).map
    (sourceDiagonalMap (p := p))

theorem complementDiagonalSourcePairLaw_fst :
    (complementDiagonalSourcePairLaw rate rewards C_star C_h t).map Prod.fst =
      (sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t)ᶜ := by
  rw [complementDiagonalSourcePairLaw, Measure.map_map measurable_fst
    (measurable_sourceDiagonalMap (p := p))]
  change ((sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t)ᶜ).map id = _
  rw [Measure.map_id]

theorem complementDiagonalSourcePairLaw_snd :
    (complementDiagonalSourcePairLaw rate rewards C_star C_h t).map Prod.snd =
      (sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t)ᶜ := by
  rw [complementDiagonalSourcePairLaw, Measure.map_map measurable_snd
    (measurable_sourceDiagonalMap (p := p))]
  change ((sourceInputLaw p).restrict (activeSourceSet rate rewards C_star C_h t)ᶜ).map id = _
  rw [Measure.map_id]

/-- The literal total original-source pair measure: the finite sum of the
retained cell laws plus the diagonal complement. -/
def totalSourcePairLaw : Measure (SourcePair p) :=
  (∑ i : StratumIndex t, sourceStratumPairLaw rate rewards C_star C_h t control0 i) +
    complementDiagonalSourcePairLaw rate rewards C_star C_h t

theorem totalSourcePairLaw_fst :
    (totalSourcePairLaw rate rewards C_star C_h t control0).map Prod.fst = sourceInputLaw p := by
  rw [totalSourcePairLaw, Measure.map_add _ _ measurable_fst,
    Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp_rw [sourceStratumPairLaw,
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw_fst]
  rw [complementDiagonalSourcePairLaw_fst,
    ← sourceStrata_restrict_sum rate rewards C_star C_h t control0,
    Measure.restrict_add_restrict_compl
      (measurableSet_activeSourceSet rate rewards C_star C_h t control0)]

theorem totalSourcePairLaw_snd :
    (totalSourcePairLaw rate rewards C_star C_h t control0).map Prod.snd = sourceInputLaw p := by
  rw [totalSourcePairLaw, Measure.map_add _ _ measurable_snd,
    Measure.map_finset_sum' measurable_snd.aemeasurable]
  simp_rw [sourceStratumPairLaw,
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw_snd]
  rw [complementDiagonalSourcePairLaw_snd,
    ← sourceStrata_restrict_sum rate rewards C_star C_h t control0,
    Measure.restrict_add_restrict_compl
      (measurableSet_activeSourceSet rate rewards C_star C_h t control0)]

/-- The active total pair measure has mass one because either full marginal is
the probability law of the original complete source. -/
theorem totalSourcePairLaw_mass :
    totalSourcePairLaw rate rewards C_star C_h t control0 Set.univ = 1 := by
  have h := congrArg (fun μ : Measure (SourceInput p) => μ Set.univ)
    (totalSourcePairLaw_fst rate rewards C_star C_h t control0)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] using h.trans (by simp)

/-- Restrict a source pair according to membership of its first original
source. -/
def sourcePairFirstEvent (A : Set (SourceInput p)) : Set (SourcePair p) :=
  Prod.fst ⁻¹' A

theorem measurableSet_sourcePairFirstEvent (A : Set (SourceInput p))
    (hA : MeasurableSet A) : MeasurableSet (sourcePairFirstEvent A) :=
  measurable_fst hA

theorem sourceStratumPairLaw_fst (i : StratumIndex t) :
    (sourceStratumPairLaw rate rewards C_star C_h t control0 i).map Prod.fst =
      (sourceInputLaw p).restrict (sourceStratumEvent rate rewards C_star C_h t i) := by
  simpa only [sourceStratumPairLaw, sourceStratumEvent] using
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw_fst rate rewards C_star C_h
      i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0

theorem sourceStratumPairLaw_snd (i : StratumIndex t) :
    (sourceStratumPairLaw rate rewards C_star C_h t control0 i).map Prod.snd =
      (sourceInputLaw p).restrict (sourceStratumEvent rate rewards C_star C_h t i) := by
  simpa only [sourceStratumPairLaw, sourceStratumEvent] using
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw_snd rate rewards C_star C_h
      i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0

private theorem restrict_eq_zero_of_measure_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) (_hA : MeasurableSet A) (hzero : μ A = 0) :
    μ.restrict A = 0 := by
  ext B hB
  rw [Measure.restrict_apply hB]
  exact measure_mono_null Set.inter_subset_right hzero

private theorem restrict_eq_self_of_compl_measure_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) (hA : MeasurableSet A) (hzero : μ Aᶜ = 0) :
    μ.restrict A = μ := by
  have hnull : μ.restrict Aᶜ = 0 :=
    restrict_eq_zero_of_measure_eq_zero μ Aᶜ hA.compl hzero
  have hsplit := μ.restrict_add_restrict_compl hA
  rw [hnull, add_zero] at hsplit
  exact hsplit

private theorem sourceStratumPairLaw_first_compl_null (i : StratumIndex t) :
    sourceStratumPairLaw rate rewards C_star C_h t control0 i
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i))ᶜ = 0 := by
  have hE := measurableSet_sourceStratumEvent rate rewards C_star C_h t control0 i
  have hpre : (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i))ᶜ =
      Prod.fst ⁻¹' (sourceStratumEvent rate rewards C_star C_h t i)ᶜ := by
    ext z
    simp [sourcePairFirstEvent]
  rw [hpre, ← Measure.map_apply measurable_fst hE.compl,
    sourceStratumPairLaw_fst rate rewards C_star C_h t control0 i,
    Measure.restrict_apply hE.compl]
  simp

private theorem sourceStratumPairLaw_first_cross_null (i j : StratumIndex t)
    (hij : j ≠ i) :
    sourceStratumPairLaw rate rewards C_star C_h t control0 j
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)) = 0 := by
  have hE_i := measurableSet_sourceStratumEvent rate rewards C_star C_h t control0 i
  have hE_j := measurableSet_sourceStratumEvent rate rewards C_star C_h t control0 j
  have hdis := sourceStratumEvent_disjoint rate rewards C_star C_h t i j (Ne.symm hij)
  have hinter : sourceStratumEvent rate rewards C_star C_h t i ∩
      sourceStratumEvent rate rewards C_star C_h t j = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdis
  rw [sourcePairFirstEvent, ← Measure.map_apply measurable_fst hE_i,
    sourceStratumPairLaw_fst rate rewards C_star C_h t control0 j,
    Measure.restrict_apply hE_i]
  rw [hinter]
  simp

private theorem complementDiagonalSourcePairLaw_first_stratum_null (c0 : TimeControl p)
    (i : StratumIndex t) :
    complementDiagonalSourcePairLaw rate rewards C_star C_h t
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)) = 0 := by
  have hE := measurableSet_sourceStratumEvent rate rewards C_star C_h t c0 i
  have hsub : sourceStratumEvent rate rewards C_star C_h t i ⊆
      activeSourceSet rate rewards C_star C_h t := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have hinter : sourceStratumEvent rate rewards C_star C_h t i ∩
      (activeSourceSet rate rewards C_star C_h t)ᶜ = ∅ := by
    ext z
    constructor
    · rintro ⟨hz, hnot⟩
      exact (hnot (hsub hz)).elim
    · intro hz
      simp at hz
  have hpre : (sourceDiagonalMap (p := p)) ⁻¹'
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)) =
        sourceStratumEvent rate rewards C_star C_h t i := by
    ext z
    simp [sourcePairFirstEvent, sourceDiagonalMap]
  rw [complementDiagonalSourcePairLaw, Measure.map_apply
    (measurable_sourceDiagonalMap (p := p))
    (measurableSet_sourcePairFirstEvent _ hE), hpre,
    Measure.restrict_apply hE, hinter]
  simp

private theorem complementDiagonalSourcePairLaw_restrict_first_stratum
    (c0 : TimeControl p) (i : StratumIndex t) :
    (complementDiagonalSourcePairLaw rate rewards C_star C_h t).restrict
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)) = 0 := by
  apply restrict_eq_zero_of_measure_eq_zero
    (complementDiagonalSourcePairLaw rate rewards C_star C_h t)
    (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i))
    (measurableSet_sourcePairFirstEvent _
      (measurableSet_sourceStratumEvent rate rewards C_star C_h t c0 i))
  exact complementDiagonalSourcePairLaw_first_stratum_null rate rewards C_star C_h t c0 i

/-- Restricting to a real active source stratum removes every cross-cell term
and the diagonal complement, leaving exactly its pre-existing unnormalized
retained pair law. -/
theorem totalSourcePairLaw_restrict_stratum (i : StratumIndex t) :
    (totalSourcePairLaw rate rewards C_star C_h t control0).restrict
      (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)) =
        sourceStratumPairLaw rate rewards C_star C_h t control0 i := by
  let firstCell := sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)
  have hfirst : MeasurableSet firstCell :=
    measurableSet_sourcePairFirstEvent _
      (measurableSet_sourceStratumEvent rate rewards C_star C_h t control0 i)
  have hself : (sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict
      firstCell = sourceStratumPairLaw rate rewards C_star C_h t control0 i := by
    apply restrict_eq_self_of_compl_measure_eq_zero _ firstCell hfirst
    simpa only [firstCell] using
      sourceStratumPairLaw_first_compl_null rate rewards C_star C_h t control0 i
  have hcross (j : StratumIndex t) (hji : j ≠ i) :
      (sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell = 0 := by
    apply restrict_eq_zero_of_measure_eq_zero _ firstCell hfirst
    simpa only [firstCell] using
      sourceStratumPairLaw_first_cross_null rate rewards C_star C_h t control0 i j hji
  have hterms :
      ∑ j : StratumIndex t,
        (sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell =
          sourceStratumPairLaw rate rewards C_star C_h t control0 i := by
    classical
    calc
      _ = ∑ j : StratumIndex t,
          if j = i then sourceStratumPairLaw rate rewards C_star C_h t control0 i else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [hself]
        · simp [hji, hcross j hji]
      _ = sourceStratumPairLaw rate rewards C_star C_h t control0 i := by simp
  have hsum_restrict :
      (∑ j : StratumIndex t,
        sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell =
        ∑ j : StratumIndex t,
          (sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell := by
    calc
      _ = (Measure.sum fun j : StratumIndex t =>
          sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell := by
        rw [Measure.sum_fintype]
      _ = Measure.sum (fun j : StratumIndex t =>
          (sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell) :=
        Measure.restrict_sum _ hfirst
      _ = _ := Measure.sum_fintype _
  calc
    _ = (∑ j : StratumIndex t,
          sourceStratumPairLaw rate rewards C_star C_h t control0 j).restrict firstCell +
        (complementDiagonalSourcePairLaw rate rewards C_star C_h t).restrict firstCell := by
      rw [totalSourcePairLaw, Measure.restrict_add]
    _ = sourceStratumPairLaw rate rewards C_star C_h t control0 i := by
      rw [hsum_restrict, hterms,
        complementDiagonalSourcePairLaw_restrict_first_stratum rate rewards C_star C_h t control0 i,
        add_zero]

/-- Any almost-everywhere source-pair certificate already proved for an active
retained law transfers unchanged to that stratum of the total law. -/
theorem totalSourcePairLaw_restrict_stratum_ae (i : StratumIndex t)
    {P : SourcePair p → Prop}
    (hP : ∀ᵐ z ∂sourceStratumPairLaw rate rewards C_star C_h t control0 i, P z) :
    ∀ᵐ z ∂(totalSourcePairLaw rate rewards C_star C_h t control0).restrict
        (sourcePairFirstEvent (sourceStratumEvent rate rewards C_star C_h t i)), P z := by
  rw [totalSourcePairLaw_restrict_stratum rate rewards C_star C_h t control0 i]
  exact hP

private theorem sourceStratumPairLaw_activeComplement_null (i : StratumIndex t) :
    sourceStratumPairLaw rate rewards C_star C_h t control0 i
      (sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)ᶜ) = 0 := by
  have hA := measurableSet_activeSourceSet rate rewards C_star C_h t control0
  have hE := measurableSet_sourceStratumEvent rate rewards C_star C_h t control0 i
  have hsub : sourceStratumEvent rate rewards C_star C_h t i ⊆
      activeSourceSet rate rewards C_star C_h t := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have hinter : sourceStratumEvent rate rewards C_star C_h t i ∩
      (activeSourceSet rate rewards C_star C_h t)ᶜ = ∅ := by
    ext z
    constructor
    · rintro ⟨hz, hnot⟩
      exact (hnot (hsub hz)).elim
    · intro hz
      simp at hz
  have hpre : (sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)ᶜ) =
      Prod.fst ⁻¹' (activeSourceSet rate rewards C_star C_h t)ᶜ := rfl
  rw [hpre, ← Measure.map_apply measurable_fst hA.compl,
    sourceStratumPairLaw_fst rate rewards C_star C_h t control0 i,
    Measure.restrict_apply hA.compl]
  rw [Set.inter_comm, hinter]
  simp

private theorem complementDiagonalSourcePairLaw_on_active_null (c0 : TimeControl p) :
    complementDiagonalSourcePairLaw rate rewards C_star C_h t
      (sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)) = 0 := by
  have hA := measurableSet_activeSourceSet rate rewards C_star C_h t c0
  have hpre : (sourceDiagonalMap (p := p)) ⁻¹'
      (sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)) =
        activeSourceSet rate rewards C_star C_h t := by
    ext z
    simp [sourcePairFirstEvent, sourceDiagonalMap]
  rw [complementDiagonalSourcePairLaw, Measure.map_apply
    (measurable_sourceDiagonalMap (p := p))
    (measurableSet_sourcePairFirstEvent _ hA), hpre,
    Measure.restrict_apply hA]
  simp

/-- On the no-launch/later-boundary complement, first-source restriction of
the total pair law is exactly the diagonal complement measure. -/
theorem totalSourcePairLaw_restrict_activeComplement :
    (totalSourcePairLaw rate rewards C_star C_h t control0).restrict
      (sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)ᶜ) =
        complementDiagonalSourcePairLaw rate rewards C_star C_h t := by
  let firstComplement := sourcePairFirstEvent (activeSourceSet rate rewards C_star C_h t)ᶜ
  have hfirst : MeasurableSet firstComplement :=
    measurableSet_sourcePairFirstEvent _
      (measurableSet_activeSourceSet rate rewards C_star C_h t control0).compl
  have hsum_restrict :
      (∑ i : StratumIndex t,
        sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict firstComplement = 0 := by
    calc
      _ = ∑ i : StratumIndex t,
          (sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict firstComplement := by
        calc
          _ = (Measure.sum fun i : StratumIndex t =>
              sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict firstComplement := by
            rw [Measure.sum_fintype]
          _ = Measure.sum (fun i : StratumIndex t =>
              (sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict firstComplement) :=
            Measure.restrict_sum _ hfirst
          _ = _ := Measure.sum_fintype _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply restrict_eq_zero_of_measure_eq_zero _ firstComplement hfirst
        exact sourceStratumPairLaw_activeComplement_null rate rewards C_star C_h t control0 i
  have hdiagSelf :
      (complementDiagonalSourcePairLaw rate rewards C_star C_h t).restrict firstComplement =
        complementDiagonalSourcePairLaw rate rewards C_star C_h t := by
    apply restrict_eq_self_of_compl_measure_eq_zero _ firstComplement hfirst
    simpa [firstComplement, sourcePairFirstEvent] using
      complementDiagonalSourcePairLaw_on_active_null rate rewards C_star C_h t control0
  calc
    _ = (∑ i : StratumIndex t,
          sourceStratumPairLaw rate rewards C_star C_h t control0 i).restrict firstComplement +
        (complementDiagonalSourcePairLaw rate rewards C_star C_h t).restrict firstComplement := by
      rw [totalSourcePairLaw, Measure.restrict_add]
    _ = complementDiagonalSourcePairLaw rate rewards C_star C_h t := by
      rw [hsum_restrict, hdiagSelf, zero_add]

/-- The frame requirements on one source-pair cell. The fixed split uses the
actual selected row and current calendar coordinate; its remainder includes
all private data, the original `J`, IDs, every forward row, every other row,
and every other time in the selected row. Only the assignment coordinates in
the current control are left free. -/
def sourceFrameCell (t : Fin p.T) (q : Fin (M p)) : Set (SourcePair p) :=
  {z | BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1 = q ∧
    BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2 = q ∧
    z.1.2 = z.2.2 ∧
    z.1.1.1 = z.2.1.1 ∧
    (∀ j : Fin (M p), (z.1.1.2 j).1 = (z.2.1.2 j).1) ∧
    (∀ j : Fin (M p), j ≠ q → z.1.1.2 j = z.2.1.2 j) ∧
    (∀ v : ReferenceSelectedAffinePairLaw.Other t,
      (z.1.1.2 q).2 v = (z.2.1.2 q).2 v) ∧
    (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.1 label =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.1 label) ∧
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.2 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.2}

/-- The global source-frame predicate is the finite union indexed by the
actual original coordinator scalar. -/
def sourceFrameSet (t : Fin p.T) : Set (SourcePair p) :=
  ⋃ q : Fin (M p), sourceFrameCell t q

theorem measurableSet_sourceFrameCell (t : Fin p.T) (q : Fin (M p)) :
    MeasurableSet (sourceFrameCell t q) := by
  classical
  have hcoordLeft : Measurable
      (fun z : SourcePair p => BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp measurable_fst
  have hcoordRight : Measurable
      (fun z : SourcePair p => BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp measurable_snd
  have hcoordLeftSet : MeasurableSet
      {z : SourcePair p | BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1 = q} :=
    measurableSet_eq_of_maps _ _ hcoordLeft measurable_const
  have hcoordRightSet : MeasurableSet
      {z : SourcePair p | BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2 = q} :=
    measurableSet_eq_of_maps _ _ hcoordRight measurable_const
  have hprivateSet : MeasurableSet {z : SourcePair p | z.1.2 = z.2.2} := by
    exact measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  have hidsSet : MeasurableSet {z : SourcePair p | z.1.1.1 = z.2.1.1} := by
    exact measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  have hforwardSet : MeasurableSet
      {z : SourcePair p | ∀ j : Fin (M p), (z.1.1.2 j).1 = (z.2.1.2 j).1} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  have hrowsSet : MeasurableSet
      {z : SourcePair p | ∀ j : Fin (M p), j ≠ q → z.1.1.2 j = z.2.1.2 j} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => by
      by_cases hj : j = q
      · simp [hj]
      · simpa [hj] using
          (measurableSet_eq_of_maps (fun z : SourcePair p => z.1.1.2 j)
            (fun z => z.2.1.2 j) (by fun_prop) (by fun_prop))
  have htimesSet : MeasurableSet
      {z : SourcePair p | ∀ v : ReferenceSelectedAffinePairLaw.Other t,
        (z.1.1.2 q).2 v = (z.2.1.2 q).2 v} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun v =>
      measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  have hscalarSet : MeasurableSet
      {z : SourcePair p | ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.1 label =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.1 label} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun label =>
      measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  have haffineSet : MeasurableSet
      {z : SourcePair p |
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.2} := by
    exact measurableSet_eq_of_maps _ _ (by fun_prop) (by fun_prop)
  change MeasurableSet {z : SourcePair p |
    BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1 = q ∧
    BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2 = q ∧
    z.1.2 = z.2.2 ∧ z.1.1.1 = z.2.1.1 ∧
    (∀ j : Fin (M p), (z.1.1.2 j).1 = (z.2.1.2 j).1) ∧
    (∀ j : Fin (M p), j ≠ q → z.1.1.2 j = z.2.1.2 j) ∧
    (∀ v : ReferenceSelectedAffinePairLaw.Other t,
      (z.1.1.2 q).2 v = (z.2.1.2 q).2 v) ∧
    (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.1 label =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.1 label) ∧
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1).2.2 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.2).1).2.2}
  simp only [Set.ofPred_and]
  exact hcoordLeftSet.inter (hcoordRightSet.inter (hprivateSet.inter (hidsSet.inter
    (hforwardSet.inter (hrowsSet.inter (htimesSet.inter (hscalarSet.inter haffineSet)))))))

theorem measurableSet_sourceFrameSet (t : Fin p.T) : MeasurableSet (sourceFrameSet t) :=
  MeasurableSet.iUnion fun q => measurableSet_sourceFrameCell t q

/-- Identical sources satisfy every original-source frame. -/
theorem sourceDiagonal_mem_sourceFrameSet (t : Fin p.T) (z : SourceInput p) :
    (z, z) ∈ sourceFrameSet t := by
  apply Set.mem_iUnion.mpr
  refine ⟨BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z, ?_⟩
  simp [sourceFrameCell, ReferenceFixedTimeSourceControlCoupling.fixedControlSplit]

/-- Each unnormalized retained stratum inherits the complete source-frame
certificate through the actual inverse split that defines its pair law. -/
theorem ae_sourceStratum_sourceFrames (i : StratumIndex t) :
    ∀ᵐ z ∂sourceStratumPairLaw rate rewards C_star C_h t control0 i,
      z ∈ sourceFrameCell t i.1 := by
  rw [sourceStratumPairLaw, ReferenceRetainedSourceCoupling.retainedSourcePairLaw]
  apply (MeasureTheory.ae_map_iff
    (ReferenceRetainedSourceCoupling.measurable_retainedSourcePairMap rate rewards
      C_star C_h i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0).aemeasurable
    (measurableSet_sourceFrameCell t i.1)).2
  filter_upwards [ReferenceRetainedSourceCoupling.ae_retained_frames rate rewards C_star C_h
      i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0] with z hz
  rcases hz with ⟨hleft, hright, _hremLeft, _hremRight, hprivate, hids, hforward,
    hrows, htimes, hscalar, haffine⟩
  have hsplit := ReferenceRetainedSourceCoupling.retainedSourcePairMap_split
    rate rewards C_star C_h i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z
  have hcontrolLeft :
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i.1 t
        (ReferenceRetainedSourceCoupling.retainedSourcePairMap rate rewards C_star C_h
          i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z).1).1 = z.2.1 :=
    congrArg Prod.fst hsplit.1
  have hcontrolRight :
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p i.1 t
        (ReferenceRetainedSourceCoupling.retainedSourcePairMap rate rewards C_star C_h
          i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z).2).1 = z.2.2 :=
    congrArg Prod.fst hsplit.2
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hleft, hright, hprivate, hids, hforward, hrows, htimes, ?_, ?_⟩
  · simpa only [hcontrolLeft, hcontrolRight] using hscalar
  · simpa only [hcontrolLeft, hcontrolRight] using haffine

/-- The one-round generated effects on an active cell remain exactly the
retained construction's certificate. Together with
`totalSourcePairLaw_restrict_stratum`, this exposes the established effects
only on their genuine active stratum and gives the complement no input state. -/
theorem ae_sourceStratum_generatedEffects (i : StratumIndex t) :
    ∀ᵐ z ∂ReferenceRetainedSourceCoupling.retainedCoupling rate rewards C_star C_h
        i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0,
      ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput rate rewards C_star C_h
            i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.1) =
        ReferenceActivePhysicalHorizon.computedEvidence
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput rate rewards C_star C_h
            i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.2) ∧
      let left := ReferenceActivePhysicalStep.step
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput rate rewards C_star C_h
          i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.1)
      let right := ReferenceActivePhysicalStep.step
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput rate rewards C_star C_h
          i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers :=
  ReferenceRetainedSourceCoupling.ae_retained_generated_effects rate rewards C_star C_h
    i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0

/-- The global fixed-calendar coupling has the full original-source frames
almost surely. The diagonal complement satisfies them pointwise, and every
active term inherits its own retained certificate. -/
theorem ae_totalSourcePairLaw_sourceFrames :
    ∀ᵐ z ∂totalSourcePairLaw rate rewards C_star C_h t control0,
      z ∈ sourceFrameSet t := by
  rw [totalSourcePairLaw, MeasureTheory.ae_add_measure_iff]
  constructor
  · rw [MeasureTheory.ae_finsetSum_measure_iff]
    intro i hi
    filter_upwards [ae_sourceStratum_sourceFrames rate rewards C_star C_h t control0 i]
      with z hz
    exact Set.mem_iUnion.mpr ⟨i.1, hz⟩
  · rw [complementDiagonalSourcePairLaw]
    apply (MeasureTheory.ae_map_iff
      (measurable_sourceDiagonalMap (p := p)).aemeasurable
      (measurableSet_sourceFrameSet t)).2
    exact Filter.Eventually.of_forall fun z =>
      sourceDiagonal_mem_sourceFrameSet (p := p) t z

/-- The actual selected row index agrees across the two full original
sources under the total law. -/
theorem ae_totalSourcePairLaw_selectedIndices :
    ∀ᵐ z ∂totalSourcePairLaw rate rewards C_star C_h t control0,
      ActualInitializationPhysicalStep.selectedRowIndex p z.1 =
        ActualInitializationPhysicalStep.selectedRowIndex p z.2 := by
  filter_upwards [ae_totalSourcePairLaw_sourceFrames rate rewards C_star C_h t control0]
    with z hz
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
  change BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1 = q ∧
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2 = q ∧ _ at hq
  calc
    _ = BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1 :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p z.1).symm
    _ = BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.2 := hq.1.trans hq.2.1.symm
    _ = _ := ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p z.2

/-- The natural terminal `T` no-current-control branch is exactly the
original-source diagonal measure. It creates no `Fin p.T` control. -/
def terminalSourcePairLaw (p : Parameters) : Measure (SourcePair p) :=
  (sourceInputLaw p).map (sourceDiagonalMap (p := p))

theorem terminalSourcePairLaw_fst :
    (terminalSourcePairLaw p).map Prod.fst = sourceInputLaw p := by
  rw [terminalSourcePairLaw, Measure.map_map measurable_fst
    (measurable_sourceDiagonalMap (p := p))]
  change (sourceInputLaw p).map id = _
  rw [Measure.map_id]

theorem terminalSourcePairLaw_snd :
    (terminalSourcePairLaw p).map Prod.snd = sourceInputLaw p := by
  rw [terminalSourcePairLaw, Measure.map_map measurable_snd
    (measurable_sourceDiagonalMap (p := p))]
  change (sourceInputLaw p).map id = _
  rw [Measure.map_id]

theorem terminalSourcePairLaw_mass : (terminalSourcePairLaw p) Set.univ = 1 := by
  have h := congrArg (fun μ : Measure (SourceInput p) => μ Set.univ)
    (terminalSourcePairLaw_fst (p := p))
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] using h.trans (by simp)

end Bandits.Support.ReferenceTotalSourcePairCoupling

end
