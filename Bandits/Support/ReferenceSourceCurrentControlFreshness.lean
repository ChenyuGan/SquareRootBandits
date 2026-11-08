/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceReleaseWaitingReadouts
public import Bandits.Support.ReferenceRetainedSourceCoupling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Freshness of the whole current source control

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,459-490`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module proves the one-step product law for the complete current control
and the original source with that selected row's control suffix
replaced. The source carrier retains every original row and private coordinate.
The result is a freshness law only; it does not identify this prefix with a
protocol filtration or prove conditional physical service.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceSourceCurrentControlFreshness

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The original source with the entire selected-row control suffix replaced
by the fixed baseline. Its private coordinates and all rows remain present. -/
def c_t (p : Parameters) (control0 : TimeControl p) (t : Fin p.T)
    (source : SourceInput p) : SourceInput p :=
  ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
    source t (fun _ => control0)

/-- The complete current `TimeControl` read from the row selected by the
original private coordinator index. -/
def u_t (p : Parameters) (t : Fin p.T) (source : SourceInput p) : TimeControl p :=
  (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t

/-- The comap sigma algebra of the literal source prefix `c_t`. -/
abbrev m_t (p : Parameters) (control0 : TimeControl p) (t : Fin p.T) :
    MeasurableSpace (SourceInput p) :=
  (inferInstance : MeasurableSpace (SourceInput p)).comap (c_t p control0 t)

private def fixedRowSuffixReplacement (p : Parameters) (q : Fin (M p))
    (control0 : TimeControl p) (t : Fin p.T) (source : SourceInput p) :
    SourceInput p :=
  ((source.1.1,
      Function.update source.1.2 q
        ((source.1.2 q).1, fun v =>
          if v.val < t.val then (source.1.2 q).2 v else control0)),
    source.2)

private theorem measurable_fixedRowSuffixReplacement (p : Parameters)
    (q : Fin (M p)) (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (fixedRowSuffixReplacement p q control0 t) := by
  fun_prop [fixedRowSuffixReplacement]

private theorem measurable_by_finite_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

private theorem measurable_sourceCoordinatorIndex (p : Parameters) :
    Measurable (fun source : SourceInput p =>
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source) := by
  exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
    (measurable_snd.comp (measurable_fst.comp measurable_snd))

/-- The complete selected-row prefix replacement is Borel measurable on the
canonical original-source product Borel space. -/
theorem measurable_c_t {p : Parameters} (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (c_t p control0 t) := by
  have hcases := measurable_by_finite_cases
    (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p)
    (measurable_sourceCoordinatorIndex p)
    (fun q source => fixedRowSuffixReplacement p q control0 t source)
    (fun q => measurable_fixedRowSuffixReplacement p q control0 t)
  have heq :
      (fun source => fixedRowSuffixReplacement p
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)
        control0 t source) = c_t p control0 t := by
    funext source
    change fixedRowSuffixReplacement p
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)
        control0 t source =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t
        (fun _ => control0)
    unfold fixedRowSuffixReplacement
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p source]
  rw [← heq]
  exact hcases

/-- The complete selected current control is Borel measurable on the
canonical original-source product Borel space. -/
theorem measurable_u_t {p : Parameters} (t : Fin p.T) :
    Measurable (u_t p t) := by
  exact measurable_by_finite_cases
    (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p)
    (measurable_sourceCoordinatorIndex p)
    (fun q source => (source.1.2 q).2 t)
    (fun _ => by fun_prop)

private theorem m_t_le_sourceBorel (p : Parameters) (control0 : TimeControl p)
    (t : Fin p.T) :
    m_t p control0 t ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
  (measurable_c_t (p := p) control0 t).comap_le

private def sourceStratum (p : Parameters) (q : Fin (M p)) :
    Set (SourceInput p) :=
  ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q

private def remainderStratum (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    Set (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t

private def remainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t |>.restrict
    (remainderStratum p q t)

private theorem sourceStrata_sum (p : Parameters) :
    Measure.sum (fun q : Fin (M p) =>
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (sourceStratum p q)) =
        BootstrapPrivateRoundStreams.sourceInputLaw p := by
  have hdis : Pairwise (fun q r => Disjoint (sourceStratum p q) (sourceStratum p r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro source hq hr
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q at hq
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = r at hr
    exact hqr (hq.symm.trans hr)
  have hmeas : ∀ q : Fin (M p), MeasurableSet (sourceStratum p q) := by
    intro q
    exact ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum
      p q
  have hcover : (⋃ q : Fin (M p), sourceStratum p q) = Set.univ := by
    ext source
    constructor
    · intro _
      trivial
    · intro _
      refine Set.mem_iUnion.mpr ⟨
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source, ?_⟩
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source =
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source
      rfl
  calc
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (⋃ q : Fin (M p), sourceStratum p q) :=
      (Measure.restrict_iUnion hdis hmeas).symm
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p := by
      rw [hcover, Measure.restrict_univ]

/-- After splitting the selected current control, replacing the complete
selected-row suffix depends only on the actual `J=q` remainder. -/
private theorem c_t_fixedControlSplit_factors (p : Parameters)
    (control0 control : TimeControl p) (t : Fin p.T) (q : Fin (M p))
    (r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)
    (hr : r ∈ remainderStratum p q t) :
    c_t p control0 t
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (control, r)) =
      c_t p control0 t
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (control0, r)) := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let left := e.symm (control, r)
  let right := e.symm (control0, r)
  have hleftIndex :
      ActualInitializationPhysicalStep.selectedRowIndex p left = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p left]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control r hr
  have hrightIndex :
      ActualInitializationPhysicalStep.selectedRowIndex p right = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p right]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 r hr
  change ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      left t (fun _ => control0) =
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      right t (fun _ => control0)
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = q
      · subst j
        apply Prod.ext
        · simpa [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
            hleftIndex, hrightIndex] using
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_forward
              p q t control r).trans
              (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_forward
                p q t control0 r).symm
        · funext v
          by_cases hv : v.val < t.val
          · have hvne : v ≠ t := by
              intro h
              subst v
              omega
            have htime :=
              ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
                p q t control r ⟨v, hvne⟩
            have hvFin : v < t := Fin.lt_def.mpr hv
            simpa [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
              hleftIndex, hrightIndex, hvFin] using
              htime.trans
                (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
                  p q t control0 r ⟨v, hvne⟩).symm
          · have hvFin : ¬ v < t := by
              intro hvlt
              have hvlt' := Fin.lt_def.mp hvlt
              omega
            simp [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
              hleftIndex, hrightIndex, hvFin]
      · have hleftNe : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p left := by
          rw [hleftIndex]
          exact hj
        have hrightNe : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p right := by
          rw [hrightIndex]
          exact hj
        rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
            left t (fun _ => control0) j hleftNe,
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
            right t (fun _ => control0) j hrightNe]
        calc
          left.1.2 j = r.1.2.2 ⟨j, hj⟩ :=
            ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherRow
              p q t control r ⟨j, hj⟩
          _ = right.1.2 j :=
            (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherRow
              p q t control0 r ⟨j, hj⟩).symm
  · rfl

private def prefixFromRemainder (p : Parameters) (control0 : TimeControl p)
    (t : Fin p.T) (q : Fin (M p))
    (r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :
    SourceInput p :=
  c_t p control0 t
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control0, r))

private theorem measurable_prefixFromRemainder (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T) (q : Fin (M p)) :
    Measurable (prefixFromRemainder p control0 t q) := by
  unfold prefixFromRemainder
  exact (measurable_c_t (p := p) control0 t).comp
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_id))

private theorem map_product_prefix_snd {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (f : β → γ)
    (hf : Measurable f) [IsProbabilityMeasure μ] [SFinite ν] :
    (μ.prod ν).map (fun z => (f z.2, z.1)) = (ν.map f).prod μ := by
  calc
    _ = ((μ.prod ν).map Prod.swap).map (Prod.map f id) := by
      have hcomp : (fun z : α × β => (f z.2, z.1)) =
          Prod.map f id ∘ Prod.swap := by funext z; rfl
      rw [hcomp]
      exact (Measure.map_map (hf.prodMap measurable_id) measurable_swap).symm
    _ = (ν.prod μ).map (Prod.map f id) := by rw [Measure.prod_swap]
    _ = (ν.map f).prod (μ.map id) := by
      rw [Measure.map_prod_map ν μ hf measurable_id]
    _ = (ν.map f).prod μ := by simp

private theorem source_joint_map_stratum (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T) (q : Fin (M p)) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (sourceStratum p q)).map
        (fun source => (c_t p control0 t source, u_t p t source)) =
      ((remainderLaw p q t).map (prefixFromRemainder p control0 t q)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let controlLaw := ContinuousLearningRows.timeControlLaw p
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let ρ := remainderLaw p q t
  have : SFinite ρ := by
    change SFinite
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
        (remainderStratum p q t))
    infer_instance
  let pairMap := fun source : SourceInput p =>
    (c_t p control0 t source, u_t p t source)
  have hp : Measurable pairMap :=
    (measurable_c_t (p := p) control0 t).prodMk (measurable_u_t (p := p) t)
  have hsplit :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map_symm
      p q t
  have hrem : ∀ᵐ r ∂ρ, r ∈ remainderStratum p q t :=
    ae_restrict_mem
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
        p q t)
  have hpair : ∀ᵐ z ∂controlLaw.prod ρ, z.2 ∈ remainderStratum p q t := by
    have hproj : Measurable
        (fun z : TimeControl p ×
          ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t => z.2) :=
      measurable_snd
    have hset : MeasurableSet
        ((fun z : TimeControl p ×
          ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t => z.2) ⁻¹'
            remainderStratum p q t) :=
      measurableSet_preimage hproj
        (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
          p q t)
    simpa only [Set.mem_preimage] using
      (Measure.ae_prod_mem_iff_ae_ae_mem hset).mpr
        (Filter.Eventually.of_forall fun _ => hrem)
  calc
    _ = ((controlLaw.prod ρ).map e.symm).map pairMap := by
      change ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)).map pairMap =
        ((controlLaw.prod ρ).map e.symm).map pairMap
      rw [← hsplit]
      rfl
    _ = (controlLaw.prod ρ).map (pairMap ∘ e.symm) := by
      rw [Measure.map_map hp e.symm.measurable]
    _ = (controlLaw.prod ρ).map (fun z =>
        (prefixFromRemainder p control0 t q z.2, z.1)) := by
      apply Measure.map_congr
      filter_upwards [hpair] with z hz
      apply Prod.ext
      · exact c_t_fixedControlSplit_factors p control0 z.1 t q z.2 hz
      · change ((e.symm (z.1, z.2)).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p (e.symm (z.1, z.2)))).2 t = z.1
        rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p (e.symm (z.1, z.2))]
        rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
          p q t z.1 z.2 hz]
        exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control
          p q t z.1 z.2
    _ = (ρ.map (prefixFromRemainder p control0 t q)).prod controlLaw := by
      exact map_product_prefix_snd controlLaw ρ (prefixFromRemainder p control0 t q)
        (measurable_prefixFromRemainder p control0 t q)

private theorem source_prefix_map_stratum (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T) (q : Fin (M p)) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (sourceStratum p q)).map
        (c_t p control0 t) =
      (remainderLaw p q t).map (prefixFromRemainder p control0 t q) := by
  have h := source_joint_map_stratum p control0 t q
  calc
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (sourceStratum p q)).map
        (fun source => (c_t p control0 t source, u_t p t source))).fst := by
      rw [Measure.fst_map_prodMk (measurable_c_t (p := p) control0 t) (measurable_u_t (p := p) t)]
    _ = (((remainderLaw p q t).map (prefixFromRemainder p control0 t q)).prod
          (ContinuousLearningRows.timeControlLaw p)).fst := by rw [h]
    _ = (remainderLaw p q t).map (prefixFromRemainder p control0 t q) := by
      exact Measure.fst_prod

/-- Under the original product source law, the full current `TimeControl` is
independent of the source prefix obtained by replacing the selected row's
whole suffix. The proof joins every original private-index stratum with its
unnormalized restricted law. -/
theorem source_joint_prefix_control {p : Parameters} (control0 : TimeControl p)
    (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun source => (c_t p control0 t source, u_t p t source)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map (c_t p control0 t)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let controlLaw := ContinuousLearningRows.timeControlLaw p
  let sourcePrefixLaw := fun q : Fin (M p) =>
    (remainderLaw p q t).map (prefixFromRemainder p control0 t q)
  have hsourcePrefix : Measure.sum sourcePrefixLaw = μ.map (c_t p control0 t) := by
    calc
      _ = Measure.sum (fun q : Fin (M p) =>
          (μ.restrict (sourceStratum p q)).map (c_t p control0 t)) := by
        congr 1
        funext q
        exact (source_prefix_map_stratum p control0 t q).symm
      _ = (Measure.sum (fun q : Fin (M p) => μ.restrict (sourceStratum p q))).map
          (c_t p control0 t) := (Measure.map_sum
            (measurable_c_t (p := p) control0 t).aemeasurable).symm
      _ = μ.map (c_t p control0 t) := by rw [sourceStrata_sum p]
  calc
    _ = (Measure.sum (fun q : Fin (M p) => μ.restrict (sourceStratum p q))).map
        (fun source => (c_t p control0 t source, u_t p t source)) := by
      rw [sourceStrata_sum p]
    _ = Measure.sum (fun q : Fin (M p) =>
        (μ.restrict (sourceStratum p q)).map
          (fun source => (c_t p control0 t source, u_t p t source))) :=
      Measure.map_sum
        ((measurable_c_t (p := p) control0 t).prodMk (measurable_u_t (p := p) t)).aemeasurable
    _ = Measure.sum (fun q : Fin (M p) => (sourcePrefixLaw q).prod controlLaw) := by
      congr 1
      funext q
      exact source_joint_map_stratum p control0 t q
    _ = (Measure.sum sourcePrefixLaw).prod controlLaw :=
      (Measure.prod_sum_left sourcePrefixLaw controlLaw).symm
    _ = (μ.map (c_t p control0 t)).prod controlLaw := by rw [hsourcePrefix]

/-- Every event measurable from the replaced source prefix is independent of
an arbitrary Borel event of the complete current control. -/
theorem source_control_cylinder {p : Parameters} (control0 : TimeControl p)
    (t : Fin p.T) (A : Set (SourceInput p))
    (hA : MeasurableSet[m_t p control0 t] A) (U : Set (TimeControl p))
    (hU : MeasurableSet U) :
    BootstrapPrivateRoundStreams.sourceInputLaw p (A ∩ (u_t p t) ⁻¹' U) =
      BootstrapPrivateRoundStreams.sourceInputLaw p A *
        ContinuousLearningRows.timeControlLaw p U := by
  rcases (MeasurableSpace.measurableSet_comap (m :=
    (inferInstance : MeasurableSpace (SourceInput p))) (f := c_t p control0 t)).mp hA
    with ⟨V, hV, hVA⟩
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let controlLaw := ContinuousLearningRows.timeControlLaw p
  let pairMap := fun source : SourceInput p => (c_t p control0 t source, u_t p t source)
  have hbox : pairMap ⁻¹' (V ×ˢ U) = A ∩ (u_t p t) ⁻¹' U := by
    ext source
    constructor
    · rintro ⟨hc, hu⟩
      have hpre : source ∈ (c_t p control0 t) ⁻¹' V := by
        simpa only [Set.mem_preimage] using hc
      exact ⟨hVA ▸ hpre, hu⟩
    · rintro ⟨ha, hu⟩
      have hpre : source ∈ (c_t p control0 t) ⁻¹' V := hVA.symm ▸ ha
      exact ⟨by simpa only [Set.mem_preimage] using hpre, hu⟩
  calc
    μ (A ∩ (u_t p t) ⁻¹' U) = (μ.map pairMap) (V ×ˢ U) := by
      rw [Measure.map_apply
        ((measurable_c_t (p := p) control0 t).prodMk (measurable_u_t (p := p) t)) (hV.prod hU), hbox]
    _ = ((μ.map (c_t p control0 t)).prod controlLaw) (V ×ˢ U) := by
      rw [source_joint_prefix_control (p := p) control0 t]
    _ = (μ.map (c_t p control0 t) V) * controlLaw U := by rw [Measure.prod_prod]
    _ = μ A * controlLaw U := by
      rw [Measure.map_apply (measurable_c_t (p := p) control0 t) hV, hVA]

/-- The literal indicator test on the replaced original source and its whole
current selected-row control. -/
def sourceControlTest (p : Parameters) (control0 : TimeControl p)
    (t : Fin p.T) (B : Set (SourceInput p × TimeControl p))
    (source : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (c_t p control0 t source, u_t p t source)

private def sourceControlSectionIntegral (p : Parameters)
    (B : Set (SourceInput p × TimeControl p)) (sourcePrefix : SourceInput p) : ℝ :=
  ∫ control, B.indicator (fun _ => (1 : ℝ)) (sourcePrefix, control)
    ∂ContinuousLearningRows.timeControlLaw p

private theorem measurable_sourceControlSectionIntegral (p : Parameters)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B) :
    Measurable (sourceControlSectionIntegral p B) := by
  have hBfun : Measurable (B.indicator (fun _ : SourceInput p × TimeControl p => (1 : ℝ))) :=
    measurable_const.indicator hB
  unfold sourceControlSectionIntegral
  have hsm : StronglyMeasurable (fun source =>
      ∫ control, B.indicator (fun _ => (1 : ℝ)) (source, control)
        ∂ContinuousLearningRows.timeControlLaw p) :=
    hBfun.stronglyMeasurable.integral_prod_right'
      (ν := ContinuousLearningRows.timeControlLaw p)
  exact hsm.measurable

private theorem integrable_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

private theorem sourceControlSectionIntegral_integrable (p : Parameters)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B)
    (sourcePrefix : SourceInput p) :
    Integrable (fun control => B.indicator (fun _ => (1 : ℝ)) (sourcePrefix, control))
      (ContinuousLearningRows.timeControlLaw p) := by
  have hsection : MeasurableSet {control : TimeControl p | (sourcePrefix, control) ∈ B} :=
    measurable_prodMk_left hB
  have hfun : (fun control => B.indicator (fun _ => (1 : ℝ))
      (sourcePrefix, control)) =
      ({control : TimeControl p | (sourcePrefix, control) ∈ B}).indicator
        (fun _ => (1 : ℝ)) := by
    funext control
    by_cases h : (sourcePrefix, control) ∈ B <;> simp [Set.indicator, h]
  rw [hfun, integrable_indicator_iff hsection]
  exact (integrable_const (1 : ℝ)).integrableOn

private theorem sourceControlSectionIntegral_nonneg (p : Parameters)
    (B : Set (SourceInput p × TimeControl p))
    (sourcePrefix : SourceInput p) :
    0 ≤ sourceControlSectionIntegral p B sourcePrefix := by
  unfold sourceControlSectionIntegral
  exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun control => by
    by_cases h : (sourcePrefix, control) ∈ B <;> simp [Set.indicator, h]

private theorem sourceControlSectionIntegral_le_one (p : Parameters)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B)
    (sourcePrefix : SourceInput p) :
    sourceControlSectionIntegral p B sourcePrefix ≤ 1 := by
  unfold sourceControlSectionIntegral
  calc
    _ ≤ ∫ _ : TimeControl p, (1 : ℝ)
        ∂ContinuousLearningRows.timeControlLaw p :=
      integral_mono
        (sourceControlSectionIntegral_integrable p B hB sourcePrefix)
        (integrable_const (1 : ℝ))
        (fun control => by
          by_cases h : (sourcePrefix, control) ∈ B <;> simp [Set.indicator, h])
    _ = 1 := by simp

private theorem sourceControlCandidate_measurable (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B) :
    Measurable[m_t p control0 t]
      (fun source => sourceControlSectionIntegral p B (c_t p control0 t source)) := by
  exact (measurable_sourceControlSectionIntegral p B hB).comp
    (comap_measurable (c_t p control0 t))

private theorem sourceControlCandidate_integrable (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B) :
    Integrable
      (fun source => sourceControlSectionIntegral p B (c_t p control0 t source))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hm := sourceControlCandidate_measurable p control0 t B hB
  have hBorel : Measurable
      (fun source => sourceControlSectionIntegral p B (c_t p control0 t source)) := by
    intro V hV
    exact m_t_le_sourceBorel p control0 t _ (hm hV)
  have hbound : ∀ source, ‖sourceControlSectionIntegral p B
      (c_t p control0 t source)‖ ≤ 1 := by
    intro source
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sourceControlSectionIntegral_nonneg p B _)]
    exact sourceControlSectionIntegral_le_one p B hB _
  exact integrable_measurable_norm_le_one _ hBorel hbound

private theorem source_control_test_setIntegral (p : Parameters)
    (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (SourceInput p × TimeControl p)) (hB : MeasurableSet B)
    (V : Set (SourceInput p)) (hV : MeasurableSet V) :
    ∫ source in (c_t p control0 t) ⁻¹' V,
        sourceControlTest p control0 t B source ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      ∫ source in (c_t p control0 t) ⁻¹' V,
        sourceControlSectionIntegral p B (c_t p control0 t source)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let controlLaw := ContinuousLearningRows.timeControlLaw p
  let c := c_t p control0 t
  let u := u_t p t
  let f : SourceInput p × TimeControl p → ℝ :=
    B.indicator (fun _ => (1 : ℝ))
  let H : SourceInput p × TimeControl p → ℝ := fun z =>
    V.indicator (fun _ => (1 : ℝ)) z.1 * f z
  let G : SourceInput p → ℝ := fun sourcePrefix =>
    V.indicator (fun _ => (1 : ℝ)) sourcePrefix * sourceControlSectionIntegral p B sourcePrefix
  let pairMap := fun source : SourceInput p => (c source, u source)
  let μsourcePrefix := μ.map c
  have hf : Measurable f := measurable_const.indicator hB
  have hH : Measurable H := by
    exact (measurable_const.indicator hV).comp measurable_fst |>.mul hf
  have hHbound : ∀ z, ‖H z‖ ≤ 1 := by
    intro z
    by_cases hzV : z.1 ∈ V <;> by_cases hzB : z ∈ B <;>
      simp [H, f, Set.indicator, hzV, hzB]
  have hHint : Integrable H (μsourcePrefix.prod controlLaw) := by
    exact integrable_measurable_norm_le_one H hH hHbound
  have hjoint := source_joint_prefix_control (p := p) control0 t
  have hHmap : AEStronglyMeasurable H (μ.map pairMap) := by
    rw [hjoint]
    exact hHint.aestronglyMeasurable
  have hG : Measurable G := by
    exact (measurable_const.indicator hV).mul
      (measurable_sourceControlSectionIntegral p B hB)
  have hGbound : ∀ sourcePrefix, ‖G sourcePrefix‖ ≤ 1 := by
    intro sourcePrefix
    by_cases hsourcePrefix : sourcePrefix ∈ V
    · simpa [G, Set.indicator, hsourcePrefix, Real.norm_eq_abs,
        abs_of_nonneg (sourceControlSectionIntegral_nonneg p B sourcePrefix)]
        using sourceControlSectionIntegral_le_one p B hB sourcePrefix
    · simp [G, Set.indicator, hsourcePrefix]
  have hGint : Integrable G μsourcePrefix :=
    integrable_measurable_norm_le_one G hG hGbound
  have hsetTest :
      (c ⁻¹' V).indicator (sourceControlTest p control0 t B) =
        fun source => H (pairMap source) := by
    funext source
    by_cases h : c source ∈ V <;>
      simp [H, f, pairMap, sourceControlTest, Set.indicator, h, c, u]
  have hsetCandidate :
      (c ⁻¹' V).indicator (fun source =>
        sourceControlSectionIntegral p B (c source)) = fun source => G (c source) := by
    funext source
    by_cases h : c source ∈ V <;> simp [G, Set.indicator, h]
  calc
    _ = ∫ source, (c ⁻¹' V).indicator
        (sourceControlTest p control0 t B) source ∂μ := by
      rw [integral_indicator (measurable_c_t (p := p) control0 t hV)]
    _ = ∫ source, H (pairMap source) ∂μ := by rw [hsetTest]
    _ = ∫ z, H z ∂μ.map pairMap := by
      symm
      exact MeasureTheory.integral_map
        ((measurable_c_t (p := p) control0 t).prodMk (measurable_u_t (p := p) t)).aemeasurable hHmap
    _ = ∫ z, H z ∂(μsourcePrefix.prod controlLaw) := by rw [hjoint]
    _ = ∫ sourcePrefix, ∫ control, H (sourcePrefix, control) ∂controlLaw ∂μsourcePrefix :=
      MeasureTheory.integral_prod H hHint
    _ = ∫ sourcePrefix, G sourcePrefix ∂μsourcePrefix := by
      congr 1
      funext sourcePrefix
      simp only [H, G, f]
      rw [integral_const_mul, sourceControlSectionIntegral]
    _ = ∫ source, G (c source) ∂μ := by
      exact MeasureTheory.integral_map
        (measurable_c_t (p := p) control0 t).aemeasurable hGint.aestronglyMeasurable
    _ = ∫ source, (c ⁻¹' V).indicator
        (fun source => sourceControlSectionIntegral p B (c source)) source ∂μ := by
      rw [← hsetCandidate]
    _ = _ := by rw [integral_indicator (measurable_c_t (p := p) control0 t hV)]

/-- The conditional expectation of a Borel test of the replaced source prefix and
the whole current control is its integral over a fresh complete
`TimeControl`. All measurability, bound, and integrability facts for the
right-hand side are proved internally. -/
theorem source_control_test_condExp {p : Parameters} (control0 : TimeControl p)
    (t : Fin p.T) (B : Set (SourceInput p × TimeControl p))
    (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      sourceControlTest p control0 t B | m_t p control0 t] =ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun source => ∫ control,
        B.indicator (fun _ => (1 : ℝ)) (c_t p control0 t source, control)
          ∂ContinuousLearningRows.timeControlLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let candidate := fun source =>
    sourceControlSectionIntegral p B (c_t p control0 t source)
  have hle : m_t p control0 t ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    m_t_le_sourceBorel p control0 t
  have hfmeas : Measurable (sourceControlTest p control0 t B) := by
    exact (measurable_const.indicator hB).comp
      ((measurable_c_t (p := p) control0 t).prodMk (measurable_u_t (p := p) t))
  have hfint : Integrable (sourceControlTest p control0 t B) μ := by
    have hbound : ∀ source, ‖sourceControlTest p control0 t B source‖ ≤ 1 := by
      intro source
      by_cases h : (c_t p control0 t source, u_t p t source) ∈ B <;>
        simp [sourceControlTest, Set.indicator, h]
    exact integrable_measurable_norm_le_one _ hfmeas hbound
  have hcandidateMeas : Measurable[m_t p control0 t] candidate :=
    sourceControlCandidate_measurable p control0 t B hB
  have hcandidateInt : Integrable candidate μ :=
    sourceControlCandidate_integrable p control0 t B hB
  have hsetint : ∀ A : Set (SourceInput p), MeasurableSet[m_t p control0 t] A →
      μ A < ⊤ →
      ∫ source in A, candidate source ∂μ =
        ∫ source in A, sourceControlTest p control0 t B source ∂μ := by
    intro A hA _
    rcases (MeasurableSpace.measurableSet_comap
      (m := (inferInstance : MeasurableSpace (SourceInput p)))
      (f := c_t p control0 t)).mp hA with ⟨V, hV, hVA⟩
    rw [← hVA]
    exact (source_control_test_setIntegral p control0 t B hB V hV).symm
  have hce := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (m := m_t p control0 t)
    (m₀ := (inferInstance : MeasurableSpace (SourceInput p))) (μ := μ)
    (f := sourceControlTest p control0 t B) (g := candidate)
    hle hfint
    (fun _ _ _ => hcandidateInt.integrableOn)
    hsetint
    (hcandidateMeas.stronglyMeasurable.aestronglyMeasurable)
  exact hce.symm

end Bandits.Support.ReferenceSourceCurrentControlFreshness

end
