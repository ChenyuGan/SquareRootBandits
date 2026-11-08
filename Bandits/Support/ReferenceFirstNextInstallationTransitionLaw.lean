/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInstallationCellFactors

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# First next-installation transition

The source event measures in this file are finite unnormalized restrictions.
The physical source coordinates and the two auxiliary labels retain their
original continuous carriers. Recorder and FAST coordinates are used jointly.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition
open Bandits.Support.ReferenceFirstNextInvocationJointLift
open Bandits.Support.ReferenceFirstNextInstallationCellFactors
open Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw
  (ErasedAuxiliaryArray erasedAuxiliaryLaw scalarZero auxiliarySection
    insertActualRefreshCoordinate measurable_insertActualRefreshCoordinate)

namespace Bandits.Support.ReferenceFirstNextInstallationTransitionLaw

variable {p : ConstructorDimensions.Parameters}

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Scalar := ContinuousControlSlice.Scalar

section SourceCoordinates

open ReferenceFixedTimeSourceControlCoupling

variable (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))

/-- The original fixed-row remainder, including the original private arrays
and index, restricted to its own index stratum and the actual source event.
Only the current control has been removed; later controls remain present. -/
def eventRemainderSet (q : Fin (M p)) : Set (FixedControlRemainder p q t) :=
  {r | r ∈ fixedControlRemainderStratum p q t ∧
    (fixedControlSplit p q t).symm (control0, r) ∈ E}

abbrev EventRemainder (q : Fin (M p)) := ↥(eventRemainderSet control0 t E q)

theorem measurableSet_eventRemainderSet (hE : MeasurableSet E) (q : Fin (M p)) :
    MeasurableSet (eventRemainderSet control0 t E q) :=
  (measurableSet_fixedControlRemainderStratum p q t).inter
    (hE.preimage ((fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_id)))

/-- No normalization by event mass or private-index mass. -/
def eventRemainderLaw (q : Fin (M p)) : Measure (EventRemainder control0 t E q) :=
  (fixedControlRemainderLaw p q t).comap Subtype.val

theorem eventRemainderLaw_finite (hE : MeasurableSet E) (q : Fin (M p)) :
    IsFiniteMeasure (eventRemainderLaw control0 t E q) := by
  constructor
  rw [eventRemainderLaw, comap_subtype_coe_apply
    (measurableSet_eventRemainderSet control0 t E hE q)]
  exact measure_lt_top _ _

theorem restore_event_mem
    (hinv : ∀ z c, replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p)) (r : EventRemainder control0 t E q) (c : TimeControl p) :
    (fixedControlSplit p q t).symm (c, r.val) ∈ E := by
  let z := (fixedControlSplit p q t).symm (control0, r.val)
  have hq : sourceCoordinatorIndex p z = q :=
    fixedControlSplit_symm_coordinatorIndex p q t control0 r.val r.property.1
  have hr : (fixedControlSplit p q t z).2 = r.val :=
    congrArg Prod.snd ((fixedControlSplit p q t).apply_symm_apply (control0, r.val))
  have heq := fixedControlSplit_replaceSourceControl p q t z c hq
  rw [hr] at heq
  rw [heq]
  exact (hinv z c).mpr r.property.2

/-- Reinsert the SAME current control in the SAME full original source.
Every other calendar coordinate, other row and private coordinate is retained. -/
def restoreEventSource
    (hinv : ∀ z c, replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p)) (rc : EventRemainder control0 t E q × TimeControl p) : ↥E :=
  ⟨(fixedControlSplit p q t).symm (rc.2, rc.1.val),
    restore_event_mem control0 t E hinv q rc.1 rc.2⟩

theorem measurable_restoreEventSource
    (hinv : ∀ z c, replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p)) : Measurable (restoreEventSource control0 t E hinv q) :=
  ((fixedControlSplit p q t).symm.measurable.comp
    (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))).subtype_mk

/-- Exact current-control disintegration of an actual event. The subtype
contains all original source coordinates except this one whole control. -/
theorem eventSourceLaw_eq_sum_restore
    (hE : MeasurableSet E)
    (hinv : ∀ z c, replaceSourceControl p t z c ∈ E ↔ z ∈ E) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).comap (Subtype.val : ↥E → SourceInput p) =
      Measure.sum (fun q : Fin (M p) =>
        ((eventRemainderLaw control0 t E q).prod
          (ContinuousLearningRows.timeControlLaw p)).map
            (restoreEventSource control0 t E hinv q)) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hstr (q : Fin (M p)) : MeasurableSet (fixedControlSourceStratum p q) :=
    measurableSet_fixedControlSourceStratum p q
  have hpre (q : Fin (M p)) :
      (fixedControlSplit p q t) ⁻¹' (Set.univ ×ˢ eventRemainderSet control0 t E q) =
        fixedControlSourceStratum p q ∩ E := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      eventRemainderSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
    have hs : (fixedControlSplit p q t z).2 ∈ fixedControlRemainderStratum p q t ↔
        z ∈ fixedControlSourceStratum p q := by rfl
    rw [hs]
    by_cases hq : z ∈ fixedControlSourceStratum p q
    · rw [and_iff_right hq, and_iff_right hq,
        fixedControlSplit_replaceSourceControl p q t z control0 hq]
      exact hinv z control0
    · simp only [hq, false_and]
  have hterm (q : Fin (M p)) :
      (((eventRemainderLaw control0 t E q).prod
        (ContinuousLearningRows.timeControlLaw p)).map
          (restoreEventSource control0 t E hinv q)).map Subtype.val =
        mu.restrict (fixedControlSourceStratum p q ∩ E) := by
    let e := fixedControlSplit p q t
    have hr : (eventRemainderLaw control0 t E q).map Subtype.val =
        (fixedControlRemainderLaw p q t).restrict (eventRemainderSet control0 t E q) :=
      map_comap_subtype_coe (measurableSet_eventRemainderSet control0 t E hE q) _
    have he : (mu.restrict (fixedControlSourceStratum p q ∩ E)).map e =
        (ContinuousLearningRows.timeControlLaw p).prod
          ((fixedControlRemainderLaw p q t).restrict (eventRemainderSet control0 t E q)) := by
      rw [← hpre q, ← Measure.restrict_map e.measurable
        (MeasurableSet.univ.prod (measurableSet_eventRemainderSet control0 t E hE q)),
        (fixedControlSplit_measurePreserving p q t).map_eq,
        ← Measure.prod_restrict, Measure.restrict_univ]
    calc
      _ = ((eventRemainderLaw control0 t E q).prod
          (ContinuousLearningRows.timeControlLaw p)).map
          (fun rc => e.symm (rc.2, rc.1.val)) := by
        rw [Measure.map_map measurable_subtype_coe
          (measurable_restoreEventSource control0 t E hinv q)]
        rfl
      _ = (((eventRemainderLaw control0 t E q).prod
          (ContinuousLearningRows.timeControlLaw p)).map
          (Prod.map Subtype.val id)).map (e.symm ∘ Prod.swap) := by
        rw [Measure.map_map (e.symm.measurable.comp measurable_swap)
          (measurable_subtype_coe.prodMap measurable_id)]
        rfl
      _ = (((fixedControlRemainderLaw p q t).restrict
          (eventRemainderSet control0 t E q)).prod
          (ContinuousLearningRows.timeControlLaw p)).map (e.symm ∘ Prod.swap) := by
        rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
          hr, Measure.map_id]
      _ = ((ContinuousLearningRows.timeControlLaw p).prod
          ((fixedControlRemainderLaw p q t).restrict
            (eventRemainderSet control0 t E q))).map e.symm := by
        rw [← Measure.map_map e.symm.measurable measurable_swap, Measure.prod_swap]
      _ = _ := by
        rw [← he, Measure.map_map e.symm.measurable e.measurable]
        simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
  apply (MeasurableEmbedding.subtype_coe hE).map_injective
  rw [map_comap_subtype_coe hE,
    Measure.map_sum (by exact measurable_subtype_coe.aemeasurable)]
  simp_rw [hterm]
  have hsum := FiniteFibreLift.sum_restrict_fibre (mu.restrict E)
    (sourceCoordinatorIndex p) (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p)
  rw [Measure.sum_fintype]
  convert hsum.symm using 1
  congr 1
  funext q
  change mu.restrict (fixedControlSourceStratum p q ∩ E) =
    (mu.restrict E).restrict (fixedControlSourceStratum p q)
  rw [Measure.restrict_restrict (hstr q), Set.inter_comm]

end SourceCoordinates

section ProposalCoordinate

open ReferenceFirstLivePostUpdateProposalLaw

/-- Scalar-level reindexing of the existing proposal split. This retains the
scalar itself for full source readouts, rather than only its Bernoulli image. -/
theorem measurePreserving_proposalControlSplit :
    MeasurePreserving (proposalControlSplit p) (ContinuousLearningRows.timeControlLaw p)
      (scalarLaw.prod (proposalRestControlLaw p)) := by
  classical
  let pred : ContinuousControlSlice.Label p.m p.K → Prop := fun c => c = propLabel p
  let : Unique {c : ContinuousControlSlice.Label p.m p.K // pred c} :=
    ⟨⟨propLabel p, rfl⟩, fun c => Subtype.ext c.property⟩
  let : Fintype {c : ContinuousControlSlice.Label p.m p.K // pred c} := Subtype.fintype pred
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : ContinuousControlSlice.Label p.m p.K => scalarLaw) pred
  have hone := measurePreserving_piUnique
    (fun _ : {c : ContinuousControlSlice.Label p.m p.K // pred c} => scalarLaw)
  have hslice := (hone.prod (MeasurePreserving.id
    (Measure.pi (fun _ : PropRestLabel p => scalarLaw)))).comp hsplit
  exact (measurePreserving_prodAssoc scalarLaw
    (Measure.pi (fun _ : PropRestLabel p => scalarLaw))
    (ContinuousLearningRows.affineSamplesLaw p)).comp
    (hslice.prod (MeasurePreserving.id (ContinuousLearningRows.affineSamplesLaw p)))

/-- Restore the actual scalar and every nonproposal coordinate. -/
def restoreProposalEventSource
    (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))
    (hinv : ∀ z c, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p))
    (rc : EventRemainder control0 t E q × (Scalar × PropRestControl p)) : ↥E :=
  restoreEventSource control0 t E hinv q
    (rc.1, (proposalControlSplit p).symm rc.2)

theorem measurable_restoreProposalEventSource
    (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))
    (hinv : ∀ z c, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p)) : Measurable (restoreProposalEventSource control0 t E hinv q) :=
  (measurable_restoreEventSource control0 t E hinv q).comp
    (measurable_fst.prodMk ((proposalControlSplit p).symm.measurable.comp measurable_snd))

/-- Whole original source law, with the actual proposal scalar explicitly
independent of all other current controls, original private data and rows. -/
theorem eventSourceLaw_eq_sum_restoreProposal
    (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))
    (hE : MeasurableSet E)
    (hinv : ∀ z c, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E ↔ z ∈ E) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).comap (Subtype.val : ↥E → SourceInput p) =
      Measure.sum (fun q : Fin (M p) =>
        ((eventRemainderLaw control0 t E q).prod
          (scalarLaw.prod (proposalRestControlLaw p))).map
            (restoreProposalEventSource control0 t E hinv q)) := by
  rw [eventSourceLaw_eq_sum_restore control0 t E hE hinv]
  congr 1
  funext q
  have := eventRemainderLaw_finite control0 t E hE q
  have hp := (MeasurePreserving.id (eventRemainderLaw control0 t E q)).prod
    (measurePreserving_proposalControlSplit (p := p)).symm
  rw [← hp.map_eq, Measure.map_map
    (measurable_restoreEventSource control0 t E hinv q) hp.measurable]
  rfl

end ProposalCoordinate

/-- Exchange the unused scalar with the actual assignment kernel. This is
only Fubini; each branch below supplies its literal unused-coordinate law. -/
private theorem scalar_kernel_reorder {Z E V : Type*}
    [MeasurableSpace Z] [MeasurableSpace E] [MeasurableSpace V]
    (mu : Measure Z) [IsFiniteMeasure mu] (nu : Measure E) [IsFiniteMeasure nu]
    (k : ProbabilityTheory.Kernel (Z × E) V) [ProbabilityTheory.IsMarkovKernel k]
    (f : ((Z × E) × V) × Scalar → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ bx, ∫ v, f ((bx.1, v), bx.2) ∂k bx.1 ∂(mu.prod nu).prod scalarLaw) =
      ∫ z, ∫ e, ∫ v, ∫ x, f (((z, e), v), x) ∂scalarLaw ∂k (z, e) ∂nu ∂mu := by
  let K : ProbabilityTheory.Kernel ((Z × E) × Scalar) V :=
    k.comap Prod.fst measurable_fst
  let F : ((Z × E) × Scalar) × V → ℝ := fun q => f ((q.1.1, q.2), q.1.2)
  have hF : Measurable F := hf.comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hg : Measurable (fun bx : (Z × E) × Scalar => ∫ v, F (bx, v) ∂K bx) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable
  have hb (bx : (Z × E) × Scalar) : ‖∫ v, F (bx, v) ∂K bx‖ ≤ B := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := K bx)
        (Filter.Eventually.of_forall (fun v => hB ((bx.1, v), bx.2))))
  have hi : Integrable (fun bx : (Z × E) × Scalar => ∫ v, F (bx, v) ∂K bx)
      ((mu.prod nu).prod scalarLaw) :=
    (integrable_const B).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  calc
    _ = ∫ b : Z × E, ∫ x, ∫ v, f ((b, v), x) ∂k b ∂scalarLaw ∂mu.prod nu :=
      integral_prod _ hi
    _ = ∫ b : Z × E, ∫ v, ∫ x, f ((b, v), x) ∂scalarLaw ∂k b ∂mu.prod nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun b => by
        have hm : Measurable (fun xv : Scalar × V => f ((b, xv.2), xv.1)) :=
          hf.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
        exact integral_integral_swap ((integrable_const B).mono' hm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun xv => hB ((b, xv.2), xv.1)))
    _ = _ := by
      let fx : (Z × E) × V → ℝ := fun bv => ∫ x, f (bv, x) ∂scalarLaw
      have hfx : Measurable fx := hf.stronglyMeasurable.integral_prod_right'.measurable
      have hx (bv : (Z × E) × V) : ‖fx bv‖ ≤ B := by
        simpa only [probReal_univ, mul_one] using
          (norm_integral_le_of_norm_le_const (μ := scalarLaw)
            (Filter.Eventually.of_forall fun x => hB (bv, x)))
      have hg' : Measurable (fun b : Z × E => ∫ v, fx (b, v) ∂k b) :=
        (hfx.stronglyMeasurable.integral_kernel_prod_right' (κ := k)).measurable
      apply integral_prod
      exact (integrable_const B).mono' hg'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun b => by
          simpa only [probReal_univ, mul_one] using
            (norm_integral_le_of_norm_le_const (μ := k b)
              (Filter.Eventually.of_forall fun v => hx (b, v))))

/-- Source-event disintegration applied after unused-scalar Fubini. The
current-control invariance premise is discharged separately at BOTH actual
branch kernels below. -/
private theorem event_kernel_scalar_test {Eaux V : Type*}
    [MeasurableSpace Eaux] [MeasurableSpace V]
    (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))
    (hE : MeasurableSet E)
    (hinv : ∀ z c, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (nu : Measure Eaux) [IsFiniteMeasure nu]
    (k : ProbabilityTheory.Kernel (↥E × Eaux) V) [ProbabilityTheory.IsMarkovKernel k]
    (hk : ∀ q (r : EventRemainder control0 t E q) c e,
      k (restoreEventSource control0 t E hinv q (r, c), e) =
      k (restoreEventSource control0 t E hinv q (r, control0), e))
    (f : ((↥E × Eaux) × V) × Scalar → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ bx, ∫ v, f ((bx.1, v), bx.2) ∂k bx.1
      ∂(((BootstrapPrivateRoundStreams.sourceInputLaw p).comap
        (Subtype.val : ↥E → SourceInput p)).prod nu).prod scalarLaw) =
    ∑ q : Fin (M p), ∫ rc : EventRemainder control0 t E q ×
        (Scalar × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p),
      ∫ e, ∫ v, ∫ x,
        f (((restoreProposalEventSource control0 t E hinv q rc, e), v), x)
        ∂scalarLaw
        ∂k (restoreEventSource control0 t E hinv q (rc.1, control0), e)
        ∂nu ∂(eventRemainderLaw control0 t E q).prod
          (scalarLaw.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)) := by
  let mu := (BootstrapPrivateRoundStreams.sourceInputLaw p).comap
    (Subtype.val : ↥E → SourceInput p)
  have : IsFiniteMeasure mu := by
    constructor
    rw [show mu = (BootstrapPrivateRoundStreams.sourceInputLaw p).comap
      (Subtype.val : ↥E → SourceInput p) from rfl, comap_subtype_coe_apply hE]
    exact measure_lt_top _ _
  let fx : (↥E × Eaux) × V → ℝ := fun bv => ∫ x, f (bv, x) ∂scalarLaw
  have hfx : Measurable fx := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hfxB (bv) : ‖fx bv‖ ≤ B := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := scalarLaw)
        (Filter.Eventually.of_forall fun x => hB (bv, x)))
  let g : ↥E × Eaux → ℝ := fun b => ∫ v, fx (b, v) ∂k b
  have hg : Measurable g :=
    (hfx.stronglyMeasurable.integral_kernel_prod_right' (κ := k)).measurable
  have hgB (b) : ‖g b‖ ≤ B := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := k b)
        (Filter.Eventually.of_forall fun v => hfxB (b, v)))
  let G : ↥E → ℝ := fun z => ∫ e, g (z, e) ∂nu
  have hG : Measurable G := hg.stronglyMeasurable.integral_prod_right'.measurable
  have hGi : Integrable G mu := by
    have hi : Integrable g (mu.prod nu) :=
      (integrable_const B).mono' hg.aestronglyMeasurable
        (Filter.Eventually.of_forall hgB)
    exact hi.integral_prod_left
  rw [scalar_kernel_reorder mu nu k f hf B hB]
  change (∫ z, G z ∂mu) = _
  rw [show mu = _ from eventSourceLaw_eq_sum_restoreProposal control0 t E hE hinv]
  rw [integral_sum_measure (by
    rw [← eventSourceLaw_eq_sum_restoreProposal control0 t E hE hinv]
    exact hGi), tsum_fintype]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_map (measurable_restoreProposalEventSource control0 t E hinv q).aemeasurable
    hG.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun rc => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun e => by
      dsimp only [G, g]
      rw [show k (restoreProposalEventSource control0 t E hinv q rc, e) =
        k (restoreEventSource control0 t E hinv q (rc.1, control0), e) from hk q rc.1 _ e]

section ActualInputs

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T)

/-- Actual nonrenewal event invariance, with no support or survival premise. -/
theorem nonrenewedEvent_control_invariant (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
      ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t :=
  (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_replace_current_iff
    rate rewards C_star C_h u t z c).symm

include control0 in
/-- Actual renewal event invariance follows from strict source-prefix
locality, including its renewal/anchor boundary test. -/
theorem renewedEvent_control_invariant (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t := by
  have hp (s : SourceInput p) :
      s ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val s ∈
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t :=
    ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h s u t (fun _ => control0)
  rw [hp, ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current]
  exact (hp z).symm

/-- The SAME retained strict prefix is obtained for every restored control. -/
theorem restoreEventSource_prefix (E : Set (SourceInput p))
    (hinv : ∀ z c, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈ E ↔ z ∈ E)
    (q : Fin (M p)) (r : EventRemainder control0 t E q) (c : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (restoreEventSource control0 t E hinv q (r, c)).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (restoreEventSource control0 t E hinv q (r, control0)).val := by
  let z := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
    (control0, r.val)
  have hq := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t control0 r.val r.property.1
  have hr := congrArg Prod.snd
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply (control0, r.val))
  have he := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t z c hq
  rw [hr] at he
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm (c, r.val)) = _
  rw [he]
  exact ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z c

/-- The actual nonrenewed fibre kernel uses the complete generated past and
sampler parameter, both strict-prefix data. -/
theorem nonrenewedVectorKernel_prefix_ext
    (z z' : EventSource rate rewards C_star C_h u t)
    (hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z'.val)
    (a : AuxArray p) :
    nonrenewedVectorKernel rate rewards C_star C_h u t control0 (z, a) =
      nonrenewedVectorKernel rate rewards C_star C_h u t control0 (z', a) := by
  have hpref : prefixEvent rate rewards C_star C_h u t control0 z =
      prefixEvent rate rewards C_star C_h u t control0 z' := Subtype.ext hp
  have ho := (nextInvocationObservation_prefixEvent rate rewards C_star C_h u t control0 z a).symm.trans
    ((congrArg (fun s => nextInvocationObservation rate rewards C_star C_h u t control0 (s, a))
      hpref).trans (nextInvocationObservation_prefixEvent rate rewards C_star C_h u t control0 z' a))
  have htheta : nextParameter rate rewards C_star C_h u t control0 z =
      nextParameter rate rewards C_star C_h u t control0 z' := by
    apply Option.some.inj
    rw [← nextParameter_spec, ← nextParameter_spec, hp]
  have hpath := congrArg Prod.snd ho
  change ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z a =
    ReferenceFirstLiveCollectionPathJoin.collectionPath rate rewards C_star C_h u t z' a at hpath
  unfold nonrenewedVectorKernel
  rw [ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.comap_apply, htheta, hpath]

/-- The actual renewal fibre has the same strict-prefix locality, while its
initial draw remains the original label-one draw. -/
theorem renewedVectorKernel_prefix_ext
    (z z' : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z'.val)
    (a : AuxArray p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z, a) =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel
        rate rewards C_star C_h u t (z', a) := by
  let pref := ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
    rate rewards C_star C_h u t
  have hpref : pref z (fun _ => control0) = pref z' (fun _ => control0) := Subtype.ext hp
  have htheta := (ReferenceFirstCollectionRenewalPastLocality.renewalCallParameter_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t z (fun _ => control0)).trans
    ((congrArg (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t) hpref).trans
      (ReferenceFirstCollectionRenewalPastLocality.renewalCallParameter_eq_of_replaceSelectedControlSuffix
        rate rewards C_star C_h u t z' (fun _ => control0)).symm)
  have hs := (ReferenceFirstCollectionRenewalPastLocality.renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t z (fun _ => control0) a).trans
    ((congrArg (fun s => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t s a) hpref).trans
      (ReferenceFirstCollectionRenewalPastLocality.renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
        rate rewards C_star C_h u t z' (fun _ => control0) a).symm)
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply, htheta, hs]

end ActualInputs

section NativeResidual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (t : Fin p.T)

/-- The accepted native residual law at the source-derived PRE, anchor and
whole-arm input, including PRE overflow and no-proposal Dirac branches. -/
def firstResidualLaw (z : FirstInvocationSource rate rewards C_star C_h t) : Measure (SlowSet p) :=
  logicalCellResidualLaw rate (firstRecord rate rewards C_star C_h t z)
    (firstSourceCell rate rewards C_star C_h t z)
    (firstBefore rate rewards C_star C_h control0 t z)

/-- Every native field is retained; only the freshly sampled next set varies. -/
def firstResidualCell (z : FirstInvocationSource rate rewards C_star C_h t) (U : SlowSet p) :
    ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate :=
  logicalCellWithNext rate (firstRecord rate rewards C_star C_h t z)
    (firstSourceCell rate rewards C_star C_h t z)
    (firstBefore rate rewards C_star C_h control0 t z) U

/-- Arbitrary Borel cell tests integrate the true residual measure. -/
theorem firstResidual_test (z : FirstInvocationSource rate rewards C_star C_h t)
    (f : ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate → ℝ)
    (hf : Measurable f) :
    (∫ x, f (actualFirstCell rate rewards C_star C_h control0 t z x) ∂scalarLaw) =
      ∫ U, f (firstResidualCell rate rewards C_star C_h control0 t z U)
        ∂firstResidualLaw rate rewards C_star C_h control0 t z := by
  have hcell : Measurable (actualFirstCell rate rewards C_star C_h control0 t z) :=
    Measurable.of_uncurry_left (measurable_actualFirstCell rate rewards C_star C_h control0 t)
  have hnext : Measurable (firstResidualCell rate rewards C_star C_h control0 t z) :=
    measurable_of_countable _
  calc
    _ = ∫ cell, f cell ∂scalarLaw.map (actualFirstCell rate rewards C_star C_h control0 t z) :=
      (integral_map hcell.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [actualFirstCell_refresh_law rate rewards C_star C_h control0 t z]
      change (∫ cell, f cell ∂(firstResidualLaw rate rewards C_star C_h control0 t z).map
        (firstResidualCell rate rewards C_star C_h control0 t z)) = _
      exact integral_map hnext.aemeasurable hf.aestronglyMeasurable

end NativeResidual

/-- Complete retained coordinates for a native cell transition. The old list
is retained in full, and the inserted full source is reconstructed on the RHS.
For renewal the erased auxiliary array retains the initialization label 1. -/
abbrev TransitionData (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :=
  ((SourceInput p × ErasedAuxiliaryArray t) × Vector p) ×
    (List (ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) ×
      (SourceInput p × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate))

section NonrenewedTransition

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T)

local notation "NZ" => EventSource rate rewards C_star C_h u t
local notation "NE" => ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t
local notation "Nbase" => ((NZ × ErasedAuxiliaryArray t) × Vector p)

/-- The same generated old list, together with a supplied native current cell.
The supplied cell is an output argument, never a proof-law hypothesis. -/
def nonrenewedReadout (b : Nbase)
    (cell : ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) : TransitionData rate t :=
  (((b.1.1.val, b.1.2), b.2),
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (b.1.1.val, insertActualRefreshCoordinate t b.1.2 scalarZero),
      ((nonrenewedFirstSource rate rewards C_star C_h t u b.1.1 b.2).val, cell)))

include control0 in
theorem measurable_nonrenewedReadout : Measurable (fun bc : Nbase ×
    ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      nonrenewedReadout rate rewards C_star C_h u t bc.1 bc.2) := by
  have hz : Measurable (fun bc : Nbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      bc.1.1.1.val) := measurable_subtype_coe.comp measurable_fst.fst.fst
  have he : Measurable (fun bc : Nbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      insertActualRefreshCoordinate t bc.1.1.2 scalarZero) :=
    (measurable_insertActualRefreshCoordinate t).comp
      (measurable_fst.fst.snd.prodMk measurable_const)
  have hp := (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
    rate rewards C_star C_h control0 t.castSucc).comp (hz.prodMk he)
  have hs : Measurable (fun bc : Nbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      (nonrenewedFirstSource rate rewards C_star C_h t u bc.1.1.1 bc.1.2).val) :=
    (measurable_subtype_coe.comp
      (measurable_nonrenewedFirstSource rate rewards C_star C_h t u)).comp
      (measurable_fst.fst.fst.prodMk measurable_fst.snd)
  exact ((hz.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd).prodMk
    (hp.prodMk (hs.prodMk measurable_snd))

/-- The complete transition readout on the literal nonrenewed lift. -/
def nonrenewedTransition (wv : (NZ × AuxArray p) × Vector p) : TransitionData rate t :=
  (((wv.1.1.val,
      (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit t wv.1.2).1), wv.2),
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (wv.1.1.val, wv.1.2),
      ((nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val,
        nonrenewedFirstCell rate rewards C_star C_h control0 t u wv)))

theorem nonrenewedReadout_actual (wv : (NZ × AuxArray p) × Vector p) :
    nonrenewedReadout rate rewards C_star C_h u t
      ((wv.1.1, (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit t wv.1.2).1), wv.2)
      (actualFirstCell rate rewards C_star C_h control0 t
        (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2)
        (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit t wv.1.2).2) =
      nonrenewedTransition rate rewards C_star C_h control0 u t wv := by
  let s := ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit t wv.1.2
  have hr : wv.1.2 = insertActualRefreshCoordinate t s.1 s.2 :=
    ((ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit t).symm_apply_apply wv.1.2).symm.trans
      (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply t s)
  have hx : s.2 = wv.1.2 (t, 1) := by
    rw [hr]
    simp only [ReferenceFirstLiveActualRefreshTestLaw.insertActualRefreshCoordinate, dite_true]
  have hp := congrArg (fun o => o.1.2.2)
    (nextInvocationObservation_refreshScalar_ext rate rewards C_star C_h u t control0
      wv.1.1 s.1 s.2 scalarZero)
  change ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
    t.castSucc (wv.1.1.val, insertActualRefreshCoordinate t s.1 s.2) =
    ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (wv.1.1.val, insertActualRefreshCoordinate t s.1 scalarZero) at hp
  dsimp only [nonrenewedReadout, nonrenewedTransition, nonrenewedFirstCell]
  rw [← hp, ← hr, hx]

theorem nonrenewedReadout_residual_test (b : Nbase)
    (Phi : TransitionData rate t → ℝ) (hPhi : Measurable Phi) :
    (∫ x, Phi (nonrenewedReadout rate rewards C_star C_h u t b
      (actualFirstCell rate rewards C_star C_h control0 t
        (nonrenewedFirstSource rate rewards C_star C_h t u b.1.1 b.2) x)) ∂scalarLaw) =
    ∫ U, Phi (nonrenewedReadout rate rewards C_star C_h u t b
      (firstResidualCell rate rewards C_star C_h control0 t
        (nonrenewedFirstSource rate rewards C_star C_h t u b.1.1 b.2) U))
      ∂firstResidualLaw rate rewards C_star C_h control0 t
        (nonrenewedFirstSource rate rewards C_star C_h t u b.1.1 b.2) := by
  exact firstResidual_test rate rewards C_star C_h control0 t _ _
    (hPhi.comp ((measurable_nonrenewedReadout rate rewards C_star C_h control0 u t).comp
      (measurable_const.prodMk measurable_id)))

/-- The actual native post-cell law, retaining the full old generated list,
original source, inserted source, every other auxiliary coordinate and the
SAME installed vector. The physical proposal scalar is an explicit independent
product coordinate; the last integral is the true native residual law. -/
theorem nonrenewedFirstCell_transition_test
    (Phi : TransitionData rate t → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ x, ‖Phi x‖ ≤ B) :
    (∫ wv, Phi (nonrenewedTransition rate rewards C_star C_h control0 u t wv)
      ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∑ q : Fin (M p), ∫ rc : EventRemainder control0 t NE q ×
        (Scalar × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p),
      ∫ e : ErasedAuxiliaryArray t, ∫ v : Vector p,
        let z := restoreProposalEventSource control0 t NE
          (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q rc
        let installed := nonrenewedFirstSource rate rewards C_star C_h t u z v
        ∫ U, Phi (nonrenewedReadout rate rewards C_star C_h u t ((z, e), v)
          (firstResidualCell rate rewards C_star C_h control0 t installed U))
          ∂firstResidualLaw rate rewards C_star C_h control0 t installed
        ∂nonrenewedVectorKernel rate rewards C_star C_h u t control0
          (restoreEventSource control0 t NE
            (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (rc.1, control0),
            insertActualRefreshCoordinate t e scalarZero)
        ∂erasedAuxiliaryLaw t
        ∂(eventRemainderLaw control0 t NE q).prod
          (scalarLaw.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)) := by
  let k : ProbabilityTheory.Kernel (NZ × ErasedAuxiliaryArray t) (Vector p) :=
    (nonrenewedVectorKernel rate rewards C_star C_h u t control0).comap
      (fun b => (b.1, insertActualRefreshCoordinate t b.2 scalarZero))
      (measurable_fst.prodMk ((measurable_insertActualRefreshCoordinate t).comp
        (measurable_snd.prodMk measurable_const)))
  let src : Nbase → FirstInvocationSource rate rewards C_star C_h t :=
    fun b => nonrenewedFirstSource rate rewards C_star C_h t u b.1.1 b.2
  have hsrc : Measurable src := (measurable_nonrenewedFirstSource rate rewards C_star C_h t u).comp
    (measurable_fst.fst.prodMk measurable_snd)
  let f : Nbase × Scalar → ℝ := fun bx => Phi
    (nonrenewedReadout rate rewards C_star C_h u t bx.1
      (actualFirstCell rate rewards C_star C_h control0 t (src bx.1) bx.2))
  have hf : Measurable f := hPhi.comp
    ((measurable_nonrenewedReadout rate rewards C_star C_h control0 u t).comp
      (measurable_fst.prodMk ((measurable_actualFirstCell rate rewards C_star C_h control0 t).comp
        ((hsrc.comp measurable_fst).prodMk measurable_snd))))
  have hk : ∀ q (r : EventRemainder control0 t NE q) c e,
      k (restoreEventSource control0 t NE
        (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (r, c), e) =
      k (restoreEventSource control0 t NE
        (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (r, control0), e) := by
    intro q r c e
    exact nonrenewedVectorKernel_prefix_ext rate rewards C_star C_h control0 u t _ _
      (restoreEventSource_prefix control0 t NE
        (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q r c) _
  have hsplit := nonrenewedRefreshScalar_vector_joint_test rate rewards C_star C_h u t control0
    f hf B (fun _ => hB _)
  have hcompose := event_kernel_scalar_test control0 t NE
    (ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t)
    (nonrenewedEvent_control_invariant rate rewards C_star C_h u t)
    (erasedAuxiliaryLaw t) k hk f hf B (fun _ => hB _)
  calc
    _ = _ := by
      refine Eq.trans ?_ hsplit
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun wv =>
        (congrArg Phi (nonrenewedReadout_actual rate rewards C_star C_h control0 u t wv)).symm
    _ = _ := hcompose
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun rc => by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun e => by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun v => by
            exact nonrenewedReadout_residual_test rate rewards C_star C_h control0 u t _ Phi hPhi

end NonrenewedTransition

section RenewedTransition

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T)

local notation "RZ" => ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
local notation "RE" => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t
local notation "Rbase" => ((RZ × ErasedAuxiliaryArray t) × Vector p)

/-- Renewal retains the SAME complete generated old list and every auxiliary
coordinate except the original current label zero, which is the new refresh. -/
def renewedReadout (b : Rbase)
    (cell : ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) : TransitionData rate t :=
  (((b.1.1.val, b.1.2), b.2),
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (b.1.1.val, insertRenewalRefreshScalar t b.1.2 scalarZero),
      ((ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t b.1.1 b.2).val, cell)))

include control0 in
theorem measurable_renewedReadout : Measurable (fun bc : Rbase ×
    ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      renewedReadout rate rewards C_star C_h u t bc.1 bc.2) := by
  have hz : Measurable (fun bc : Rbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      bc.1.1.1.val) := measurable_subtype_coe.comp measurable_fst.fst.fst
  have he : Measurable (fun bc : Rbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      insertRenewalRefreshScalar t bc.1.1.2 scalarZero) :=
    (renewalRefreshScalarSplit t).symm.measurable.comp
      (measurable_fst.fst.snd.prodMk measurable_const)
  have hp := (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
    rate rewards C_star C_h control0 t.castSucc).comp (hz.prodMk he)
  have hs : Measurable (fun bc : Rbase × ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate =>
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t bc.1.1.1 bc.1.2).val) :=
    (measurable_subtype_coe.comp
      (ReferenceFirstCollectionRenewalVectorInsertion.measurable_put rate rewards C_star C_h u t)).comp
      (measurable_fst.fst.fst.prodMk measurable_fst.snd)
  exact ((hz.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd).prodMk
    (hp.prodMk (hs.prodMk measurable_snd))

/-- Native complete-cell readout on the literal renewal insertion lift. -/
def renewedTransition (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
    rate rewards C_star C_h u t) : TransitionData rate t :=
  (((wv.1.1.val, (renewalRefreshScalarSplit t wv.1.2).1), wv.2),
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
      t.castSucc (wv.1.1.val, wv.1.2),
      ((ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val,
        renewedFirstCell rate rewards C_star C_h control0 t u wv)))

theorem renewedReadout_actual (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
    rate rewards C_star C_h u t) :
    renewedReadout rate rewards C_star C_h u t
      ((wv.1.1, (renewalRefreshScalarSplit t wv.1.2).1), wv.2)
      (actualFirstCell rate rewards C_star C_h control0 t
        (renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2))
        (renewalRefreshScalarSplit t wv.1.2).2) =
      renewedTransition rate rewards C_star C_h control0 u t wv := by
  exact Prod.ext rfl
    (renewedErasedCellReadout_actual rate rewards C_star C_h control0 t u wv)

theorem renewedReadout_residual_test (b : Rbase)
    (Phi : TransitionData rate t → ℝ) (hPhi : Measurable Phi) :
    (∫ x, Phi (renewedReadout rate rewards C_star C_h u t b
      (actualFirstCell rate rewards C_star C_h control0 t
        (renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t b.1.1 b.2)) x))
      ∂scalarLaw) =
    ∫ U, Phi (renewedReadout rate rewards C_star C_h u t b
      (firstResidualCell rate rewards C_star C_h control0 t
        (renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t b.1.1 b.2)) U))
      ∂firstResidualLaw rate rewards C_star C_h control0 t
        (renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t b.1.1 b.2)) := by
  exact firstResidual_test rate rewards C_star C_h control0 t _ _
    (hPhi.comp ((measurable_renewedReadout rate rewards C_star C_h control0 u t).comp
      (measurable_const.prodMk measurable_id)))

/-- Renewal's complete native post-cell law. Initial sampling still uses
original label one. The true residual law consumes distinct fresh label zero;
its erased observer retains the complete old generated list and original
label one. The current physical proposal scalar is separately product-uniform. -/
theorem renewedFirstCell_transition_test
    (Phi : TransitionData rate t → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ x, ‖Phi x‖ ≤ B) :
    (∫ wv, Phi (renewedTransition rate rewards C_star C_h control0 u t wv)
      ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t) =
    ∑ q : Fin (M p), ∫ rc : EventRemainder control0 t RE q ×
        (Scalar × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p),
      ∫ e : ErasedAuxiliaryArray t, ∫ v : Vector p,
        let z := restoreProposalEventSource control0 t RE
          (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q rc
        let installed := renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v)
        ∫ U, Phi (renewedReadout rate rewards C_star C_h u t ((z, e), v)
          (firstResidualCell rate rewards C_star C_h control0 t installed U))
          ∂firstResidualLaw rate rewards C_star C_h control0 t installed
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t
          (restoreEventSource control0 t RE
            (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (rc.1, control0),
            insertRenewalRefreshScalar t e scalarZero)
        ∂erasedAuxiliaryLaw t
        ∂(eventRemainderLaw control0 t RE q).prod
          (scalarLaw.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)) := by
  let k : ProbabilityTheory.Kernel (RZ × ErasedAuxiliaryArray t) (Vector p) :=
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t).comap
      (fun b => (b.1, insertRenewalRefreshScalar t b.2 scalarZero))
      (measurable_fst.prodMk ((renewalRefreshScalarSplit t).symm.measurable.comp
        (measurable_snd.prodMk measurable_const)))
  let src : Rbase → FirstInvocationSource rate rewards C_star C_h t :=
    fun b => renewedFirstSource rate rewards C_star C_h t u
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t b.1.1 b.2)
  have hsrc : Measurable src := (measurable_renewedFirstSource rate rewards C_star C_h t u).comp
    ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_put rate rewards C_star C_h u t).comp
      (measurable_fst.fst.prodMk measurable_snd))
  let f : Rbase × Scalar → ℝ := fun bx => Phi
    (renewedReadout rate rewards C_star C_h u t bx.1
      (actualFirstCell rate rewards C_star C_h control0 t (src bx.1) bx.2))
  have hf : Measurable f := hPhi.comp
    ((measurable_renewedReadout rate rewards C_star C_h control0 u t).comp
      (measurable_fst.prodMk ((measurable_actualFirstCell rate rewards C_star C_h control0 t).comp
        ((hsrc.comp measurable_fst).prodMk measurable_snd))))
  have hk : ∀ q (r : EventRemainder control0 t RE q) c e,
      k (restoreEventSource control0 t RE
        (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (r, c), e) =
      k (restoreEventSource control0 t RE
        (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (r, control0), e) := by
    intro q r c e
    exact renewedVectorKernel_prefix_ext rate rewards C_star C_h control0 u t _ _
      (restoreEventSource_prefix control0 t RE
        (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q r c) _
  have hsplit := renewalRefreshScalar_vector_joint_test rate rewards C_star C_h t u
    f hf B (fun _ => hB _)
  have hcompose := event_kernel_scalar_test control0 t RE
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t)
    (renewedEvent_control_invariant rate rewards C_star C_h control0 u t)
    (erasedAuxiliaryLaw t) k hk f hf B (fun _ => hB _)
  calc
    _ = _ := by
      refine Eq.trans ?_ hsplit
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun wv =>
        (congrArg Phi (renewedReadout_actual rate rewards C_star C_h control0 u t wv)).symm
    _ = _ := hcompose
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun rc => by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun e => by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun v => by
            exact renewedReadout_residual_test rate rewards C_star C_h control0 u t _ Phi hPhi

end RenewedTransition

section CorrelatedProposal

open ReferenceFirstLivePostUpdateProposalLaw
open LaunchAssignmentCoordinateSplit

/-- Insert the complete fixed assignment vector and retain the original
nonassignment scalars and entire affine family. -/
def fixedVectorControl (v : Vector p) (c : TimeControl p) : TimeControl p :=
  (controlAssignmentSplitEquiv p).symm (v, (controlAssignmentSplitEquiv p c).2)

theorem fixedVectorControl_nonassignment (v : Vector p) (c : TimeControl p)
    (l : NonAssignmentLabel p) : (fixedVectorControl v c).1 l.val = c.1 l.val :=
  congrArg (fun d => d.2.1 l)
    ((controlAssignmentSplitEquiv p).apply_symm_apply (v, (controlAssignmentSplitEquiv p c).2))

theorem fixedVectorControl_assignment (v : Vector p) (c : TimeControl p)
    (i : Fin (p.K + 1)) : (fixedVectorControl v c).1 (ContinuousControlSlice.Label.assign i) = v i :=
  congrArg (fun d => d.1 i)
    ((controlAssignmentSplitEquiv p).apply_symm_apply (v, (controlAssignmentSplitEquiv p c).2))

/-- Assignment insertion commutes with literal proposal replacement. -/
theorem fixedVectorControl_replaceProposalScalar (v : Vector p) (c : TimeControl p) (a : Scalar) :
    fixedVectorControl v (replaceProposalScalar p c a) =
      replaceProposalScalar p (fixedVectorControl v c) a := by
  apply Prod.ext
  · funext l
    by_cases hl : ∃ i : Fin (p.K + 1), l = ContinuousControlSlice.Label.assign i
    · obtain ⟨i, rfl⟩ := hl
      rw [fixedVectorControl_assignment, replaceProposalScalar_other,
        fixedVectorControl_assignment]
      exact Sum.inr_ne_inl
    · rw [fixedVectorControl_nonassignment v (replaceProposalScalar p c a) ⟨l, hl⟩]
      by_cases hp : l = propLabel p
      · subst l
        rw [replaceProposalScalar_prop, replaceProposalScalar_prop]
      · rw [replaceProposalScalar_other p c a l hp,
          replaceProposalScalar_other p (fixedVectorControl v c) a l hp,
          fixedVectorControl_nonassignment v c ⟨l, hl⟩]
  · rfl

/-- Repeated whole-control restoration keeps the latter current control and
all the original other source coordinates. -/
theorem replaceSourceControl_twice (t : Fin p.T) (z : SourceInput p) (c d : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) d =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z d := by
  simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex]

theorem currentControl_replaceSourceControl (t : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    ReferenceSourceCurrentControlFreshness.u_t p t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) = c := by
  simp [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex]

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (t : Fin p.T)

/-- The actual correlated recorder/FAST draw and whole-arm numerical update,
from the original current control after fixing only the installed vector. -/
def firstPairUpdateDraw (z : FirstInvocationSource rate rewards C_star C_h t) (c : TimeControl p) :
    ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p :=
  ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate rate rewards C_star C_h control0 t
    (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val)
    (controlAssignmentSplitEquiv p c).2

theorem measurable_firstPairUpdateDraw (z : FirstInvocationSource rate rewards C_star C_h t) :
    Measurable (firstPairUpdateDraw rate rewards C_star C_h control0 t z) := by
  let H : ReferenceRankInstallationCommonUpdateJointLaw.History p :=
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val
  have hf : Measurable (fun d : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
        rate rewards C_star C_h control0 t H d) :=
    Measurable.of_uncurry_left
      (ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
        rate rewards C_star C_h control0 t)
  exact hf.comp (measurable_snd.comp (controlAssignmentSplitEquiv p).measurable)

/-- No current proposal coordinate is present in the actual reconstructed
view/recorder/FAST/whole-update observer. The PRE includes every arm's full
record stream and comes from the strict source prefix. -/
theorem firstPairUpdateDraw_replaceProposalScalar
    (z : FirstInvocationSource rate rewards C_star C_h t) (c : TimeControl p) (a : Scalar) :
    firstPairUpdateDraw rate rewards C_star C_h control0 t z (replaceProposalScalar p c a) =
      firstPairUpdateDraw rate rewards C_star C_h control0 t z c := by
  let H := ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val
  let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
    t H (controlAssignmentSplitEquiv p c).2
  obtain ⟨v, valid, hv, hall⟩ :=
    ReferenceRankInstallationCommonUpdateJointLaw.reconstructedObserver_eq_commonReadout
      rate rewards C_star C_h control0 0 t z.val z.property
  have hx := (hall (controlAssignmentSplitEquiv p c).2).1
  have heq : ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder t H
      (controlAssignmentSplitEquiv p (replaceProposalScalar p c a)).2 =
      ReferenceRankInstallationPostUpdateProposalLaw.replaceSelectedProp t x a := by
    change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t H.1
      (fixedVectorControl H.2.2 (replaceProposalScalar p c a)) = _
    rw [fixedVectorControl_replaceProposalScalar]
    unfold ReferenceRankInstallationPostUpdateProposalLaw.replaceSelectedProp
    rw [show ReferenceSourceCurrentControlFreshness.u_t p t x = fixedVectorControl H.2.2 c from
      currentControl_replaceSourceControl t H.1 (fixedVectorControl H.2.2 c)]
    exact (replaceSourceControl_twice t H.1 (fixedVectorControl H.2.2 c)
      (replaceProposalScalar p (fixedVectorControl H.2.2 c) a)).symm
  have ho := ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver_replaceSelectedProp
    rate rewards C_star C_h control0 0 t x hx a
  have hpair := congrArg Prod.snd ho
  change firstPairUpdateDraw rate rewards C_star C_h control0 t z (replaceProposalScalar p c a) = _
  unfold firstPairUpdateDraw ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
    ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
  rw [heq]
  exact hpair

/-- The current-control draw has exactly the accepted correlated common-update
kernel at its actual source-derived view and PRE state. -/
theorem firstPairUpdateDraw_law (z : FirstInvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map
      (firstPairUpdateDraw rate rewards C_star C_h control0 t z) =
    ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards t
      (firstSourceCell rate rewards C_star C_h t z).selected.view
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid rate rewards C_star C_h t z.val _
        (actualFirstCell_view rate rewards C_star C_h control0 t z))
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z.val) := by
  have hrem := (measurePreserving_snd
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).comp
      (measurePreserving_controlAssignmentSplitEquiv p)
  have hf : Measurable (fun d : ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val) d) :=
    Measurable.of_uncurry_left (ReferenceRankInstallationCommonUpdateJointLaw.measurable_reconstructedPairUpdate
      rate rewards C_star C_h control0 t)
  change (ContinuousLearningRows.timeControlLaw p).map
    ((fun d => ReferenceRankInstallationCommonUpdateJointLaw.reconstructedPairUpdate
      rate rewards C_star C_h control0 t
      (ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val) d) ∘
      (Prod.snd ∘ controlAssignmentSplitEquiv p)) = _
  rw [← Measure.map_map hf hrem.measurable, hrem.map_eq]
  exact actualFirstCell_commonUpdateKernel rate rewards C_star C_h control0 t z

/-- The SAME correlated draw and whole-arm update have an independent actual
physical Bernoulli proposal. This uses the existing proposal-factor API;
recorder and FAST are never replaced by independent draws. -/
theorem firstPairUpdateDraw_joint_proposal (z : FirstInvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      (firstPairUpdateDraw rate rewards C_star C_h control0 t z c, physicalProposalBit rate c)) =
    ((ContinuousLearningRows.timeControlLaw p).map
      (firstPairUpdateDraw rate rewards C_star C_h control0 t z)).prod (proposalBitLaw rate) := by
  let draw := firstPairUpdateDraw rate rewards C_star C_h control0 t z
  have hdraw := measurable_firstPairUpdateDraw rate rewards C_star C_h control0 t z
  let g : Unit × PropRestControl p → ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p :=
    fun r => draw ((proposalControlSplit p).symm (scalarZero, r.2))
  have hg : Measurable g := hdraw.comp ((proposalControlSplit p).symm.measurable.comp
    (measurable_const.prodMk measurable_snd))
  have hp := proposalSplit_joint_pushforward (Measure.dirac ()) g hg rate
  have hpoint (c : TimeControl p) : g ((), (proposalControlSplit p c).2) = draw c := by
    have he := proposalControlSplit_symm_replace p scalarZero
      (proposalControlSplit p c).1 (proposalControlSplit p c).2
    rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at he
    change draw ((proposalControlSplit p).symm (scalarZero, (proposalControlSplit p c).2)) = draw c
    rw [he]
    exact firstPairUpdateDraw_replaceProposalScalar rate rewards C_star C_h control0 t z c scalarZero
  have hj : (ContinuousLearningRows.timeControlLaw p).map (fun c => (draw c, physicalProposalBit rate c)) =
      (((Measure.dirac ()).prod (proposalRestControlLaw p)).map g).prod (proposalBitLaw rate) := by
    calc
      _ = ((Measure.dirac ()).prod (ContinuousLearningRows.timeControlLaw p)).map
          (fun uc => (draw uc.2, physicalProposalBit rate uc.2)) := by
        rw [Measure.dirac_prod]
        have htest : Measurable (fun uc : Unit × TimeControl p =>
            (draw uc.2, physicalProposalBit rate uc.2)) :=
          (hdraw.comp measurable_snd).prodMk
            ((measurable_physicalProposalBit rate).comp measurable_snd)
        exact (Measure.map_map htest measurable_prodMk_left).symm
      _ = _ := by
        convert hp using 1
        congr 1
        funext uc
        cases uc.1
        rw [hpoint]
  have hm := congrArg (Measure.map Prod.fst) hj
  rw [Measure.map_map measurable_fst (hdraw.prodMk (measurable_physicalProposalBit rate)),
    Measure.map_fst_prod, measure_univ, one_smul] at hm
  change (ContinuousLearningRows.timeControlLaw p).map draw =
    ((Measure.dirac ()).prod (proposalRestControlLaw p)).map g at hm
  rw [hj, hm]

end CorrelatedProposal

section ProjectionsAndNativeFields

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (t : Fin p.T)

/-- The actual input control gives the actual pair and complete update. -/
theorem firstPairUpdateDraw_actual (z : FirstInvocationSource rate rewards C_star C_h t) :
    firstPairUpdateDraw rate rewards C_star C_h control0 t z
      (ReferenceSourceCurrentControlFreshness.u_t p t z.val) =
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t z.val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z.val) :=
  (actualFirstCell_pairUpdate_reconstruction rate rewards C_star C_h control0 t z).symm

/-- Projecting one coordinate preserves its correlation with every other
coordinate retained by the test; only the independent proposal is separated. -/
theorem firstPairUpdateDraw_project_proposal {A : Type*} [MeasurableSpace A]
    (z : FirstInvocationSource rate rewards C_star C_h t)
    (proj : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p → A) (hproj : Measurable proj) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      (proj (firstPairUpdateDraw rate rewards C_star C_h control0 t z c),
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)) =
      (((ContinuousLearningRows.timeControlLaw p).map
        (firstPairUpdateDraw rate rewards C_star C_h control0 t z)).map proj).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
  have h := congrArg (fun mu => mu.map (Prod.map proj id))
    (firstPairUpdateDraw_joint_proposal rate rewards C_star C_h control0 t z)
  rw [Measure.map_map (hproj.prodMap measurable_id)
      ((measurable_firstPairUpdateDraw rate rewards C_star C_h control0 t z).prodMk
        (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate)),
    ← Measure.map_prod_map _ _ hproj measurable_id, Measure.map_id] at h
  exact h

/-- Recorder marginal projected from the SAME correlated pair/update law. -/
theorem firstPairUpdateDraw_recorder_proposal (z : FirstInvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      ((firstPairUpdateDraw rate rewards C_star C_h control0 t z c).1.1,
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)) =
      (((ContinuousLearningRows.timeControlLaw p).map
        (firstPairUpdateDraw rate rewards C_star C_h control0 t z)).map (fun q => q.1.1)).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) :=
  firstPairUpdateDraw_project_proposal rate rewards C_star C_h control0 t z _ measurable_fst.fst

/-- FAST marginal projected from the SAME correlated pair/update law. -/
theorem firstPairUpdateDraw_fast_proposal (z : FirstInvocationSource rate rewards C_star C_h t) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      ((firstPairUpdateDraw rate rewards C_star C_h control0 t z c).1.2,
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)) =
      (((ContinuousLearningRows.timeControlLaw p).map
        (firstPairUpdateDraw rate rewards C_star C_h control0 t z)).map (fun q => q.1.2)).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) :=
  firstPairUpdateDraw_project_proposal rate rewards C_star C_h control0 t z _ measurable_fst.snd

/-- Native proposal/refresh gating uses PRE overflow, including on the first
update whose POST queues detect overflow. -/
theorem firstResidualCell_proposal (z : FirstInvocationSource rate rewards C_star C_h t) (U : SlowSet p) :
    (firstResidualCell rate rewards C_star C_h control0 t z U).proposal =
      (!(firstBefore rate rewards C_star C_h control0 t z).overflow &&
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
          (ReferenceSourceCurrentControlFreshness.u_t p t z.val)) :=
  actualFirstCell_proposal rate rewards C_star C_h control0 t z scalarZero

theorem firstResidualCell_next (z : FirstInvocationSource rate rewards C_star C_h t) (U : SlowSet p) :
    (firstResidualCell rate rewards C_star C_h control0 t z U).nextSlowSet = U := rfl

/-- Every arm's actual register and record stream undergoes the same complete
numerical step. No endpoint equality with the old logical list is needed. -/
theorem firstResidualCell_step (z : FirstInvocationSource rate rewards C_star C_h t) (U : SlowSet p) :
    (firstResidualCell rate rewards C_star C_h control0 t z U).before =
        firstBefore rate rewards C_star C_h control0 t z ∧
    (firstResidualCell rate rewards C_star C_h control0 t z U).after =
      RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (firstBefore rate rewards C_star C_h control0 t z)
        (firstSourceCell rate rewards C_star C_h t z).input := ⟨rfl, rfl⟩

end ProjectionsAndNativeFields

section RestoredProposal

open ReferenceFirstLivePostUpdateProposalLaw
open ReferenceFixedTimeSourceControlCoupling

variable (control0 : TimeControl p) (t : Fin p.T) (E : Set (SourceInput p))
  (hinv : ∀ z c, replaceSourceControl p t z c ∈ E ↔ z ∈ E)

/-- Restore reads the exact current control from the row selected by original J. -/
theorem restoreEventSource_currentControl (q : Fin (M p))
    (rc : EventRemainder control0 t E q × TimeControl p) :
    ReferenceSourceCurrentControlFreshness.u_t p t
      (restoreEventSource control0 t E hinv q rc).val = rc.2 := by
  let z := (fixedControlSplit p q t).symm (rc.2, rc.1.val)
  have hq := fixedControlSplit_symm_coordinatorIndex p q t rc.2 rc.1.val rc.1.property.1
  change (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t = _
  rw [← sourceCoordinatorIndex_eq_selectedRowIndex, hq]
  exact fixedControlSplit_symm_control p q t rc.2 rc.1.val

/-- The explicit independent scalar in BOTH branch RHSs is the actual
physical Bernoulli threshold h = 4*m*eta. -/
theorem restoreProposalEventSource_bit (rate : ReferenceActivePhysicalStep.RateInput p)
    (q : Fin (M p))
    (rc : EventRemainder control0 t E q × (Scalar × PropRestControl p)) :
    physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p t
        (restoreProposalEventSource control0 t E hinv q rc).val) =
    FollowerCutoffScan.thresholdProposalBit rc.2.1 (4 * (p.m : ℝ) * rate.eta.val) := by
  rw [show (restoreProposalEventSource control0 t E hinv q rc).val =
      (restoreEventSource control0 t E hinv q (rc.1, (proposalControlSplit p).symm rc.2)).val from rfl,
    restoreEventSource_currentControl]
  unfold physicalProposalBit
  rw [proposalControlSplit_symm_prop]
  rfl

/-- Whole-vector insertion preserves the original physical proposal scalar. -/
theorem insertedSource_proposalBit (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : SourceInput p) (v : Vector p) :
    physicalProposalBit rate (ReferenceSourceCurrentControlFreshness.u_t p t
        (ReferenceFirstCollectionRenewalVectorInsertion.insert t z v)) =
      physicalProposalBit rate (ReferenceSourceCurrentControlFreshness.u_t p t z) := by
  have hp : ¬ ∃ i : Fin (p.K + 1), propLabel p = ContinuousControlSlice.Label.assign i := by
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr hi
  exact congrArg (fun a => FollowerCutoffScan.thresholdProposalBit a
    (FollowerCutoffScan.proposalHazard p rate.eta.val))
    (ReferenceFirstCollectionRenewalVectorInsertion.insert_nonAssignmentScalars t z v ⟨propLabel p, hp⟩)

end RestoredProposal

/-- The transition constructs this full append. It makes no assertion about
`extendedPast` at the successor boundary, whose first-call recursion kills
before this invocation. -/
def postHistory {rate : ReferenceActivePhysicalStep.RateInput p} {t : Fin p.T}
    (d : TransitionData rate t) : List (ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) :=
  d.2.1 ++ [d.2.2.2]

theorem measurable_postHistory (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (postHistory (rate := rate) (t := t)) :=
  (measurable_appendCurrentTag rate).comp
    (measurable_snd.fst.prodMk (measurable_inr.comp measurable_snd.snd.snd))

/-- Full retained transition and appended list are jointly Borel test data. -/
theorem measurable_transitionWithPostHistory (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (fun d : TransitionData rate t => (d, postHistory d)) :=
  measurable_id.prodMk (measurable_postHistory rate t)

theorem nonrenewedTransition_postHistory
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (u t : Fin p.T)
    (wv : (EventSource rate rewards C_star C_h u t × AuxArray p) × Vector p) :
    postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t wv) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2) ++
        [nonrenewedFirstCell rate rewards C_star C_h control0 t u wv] := rfl

theorem renewedTransition_postHistory
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (u t : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    postHistory (renewedTransition rate rewards C_star C_h control0 u t wv) =
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2) ++
        [renewedFirstCell rate rewards C_star C_h control0 t u wv] := rfl

section ActualBranchDraws

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T)

/-- This internal comparison is used only after its source identities,
strict-prefix equality and exact current control have all been supplied by
the two literal branch restorations below. -/
private theorem insertedSource_pairUpdate_from_prefix
    (z z0 : FirstInvocationSource rate rewards C_star C_h t)
    (base base0 : SourceInput p) (v : Vector p) (c : TimeControl p)
    (hz : z.val = insertedSource t base v) (hz0 : z0.val = insertedSource t base0 v)
    (hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val base =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val base0)
    (hc : ReferenceSourceCurrentControlFreshness.u_t p t base = c) :
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t z.val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z.val) =
      firstPairUpdateDraw rate rewards C_star C_h control0 t z0 c := by
  have hprefix (b : SourceInput p) :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val (insertedSource t b v) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val b :=
    congrArg Prod.fst (nextInvocationPrefix_insertVector rate rewards C_star C_h t control0 b auxiliarySection v)
  have hH : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z.val =
      ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0 0 t z0.val := by
    change (_, ([], _)) = (_, ([], _))
    rw [hz, hz0, hprefix, hprefix, hp]
    have hv (b : SourceInput p) : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
        (insertedSource t b v) = v := ReferenceFirstCollectionRenewalVectorInsertion.av_insert t b v
    rw [hv base, hv base0]
  have hrem : currentRemainder t z.val =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2 := by
    rw [hz]
    have h := congrArg Prod.snd (insertedVector_preserves_remainder_and_private t base v).1
    change currentRemainder t (insertedSource t base v) =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceSourceCurrentControlFreshness.u_t p t base)).2 at h
    exact h.trans (congrArg (fun x => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p x).2) hc)
  rw [actualFirstCell_pairUpdate_reconstruction rate rewards C_star C_h control0 t z, hH, hrem]
  rfl

/-- The exact actual first source at a nonrenewed restored physical draw. -/
def nonrenewedSourceAt (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) q)
    (c : TimeControl p) (v : Vector p) : FirstInvocationSource rate rewards C_star C_h t :=
  nonrenewedFirstSource rate rewards C_star C_h t u
    (restoreEventSource control0 t _ (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (r, c)) v

/-- The exact actual first source at a renewed restored physical draw. -/
def renewedSourceAt (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) q)
    (c : TimeControl p) (v : Vector p) : FirstInvocationSource rate rewards C_star C_h t :=
  renewedFirstSource rate rewards C_star C_h t u
    (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
      (restoreEventSource control0 t _
        (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (r, c)) v)

theorem nonrenewedSourceAt_pairUpdate (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) q)
    (c : TimeControl p) (v : Vector p) :
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t
        (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r c v).val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t
        (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r c v).val) =
      firstPairUpdateDraw rate rewards C_star C_h control0 t
        (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r control0 v) c := by
  exact insertedSource_pairUpdate_from_prefix rate rewards C_star C_h control0 t _ _ _ _ v c rfl rfl
    (restoreEventSource_prefix control0 t _
      (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q r c)
    (restoreEventSource_currentControl control0 t _
      (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (r, c))

theorem renewedSourceAt_pairUpdate (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) q)
    (c : TimeControl p) (v : Vector p) :
    (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t
        (renewedSourceAt rate rewards C_star C_h control0 u t q r c v).val,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t
        (renewedSourceAt rate rewards C_star C_h control0 u t q r c v).val) =
      firstPairUpdateDraw rate rewards C_star C_h control0 t
        (renewedSourceAt rate rewards C_star C_h control0 u t q r control0 v) c := by
  apply insertedSource_pairUpdate_from_prefix rate rewards C_star C_h control0 t _ _ _ _ v c
  · exact ReferenceFirstCollectionRenewalVectorInsertion.put_val rate rewards C_star C_h u t _ v
  · exact ReferenceFirstCollectionRenewalVectorInsertion.put_val rate rewards C_star C_h u t _ v
  · exact restoreEventSource_prefix control0 t _
      (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q r c
  · exact restoreEventSource_currentControl control0 t _
      (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (r, c)

/-- Correlated actual nonrenewed physical draw and numerical update, jointly
with the independent LIVE proposal at the SAME retained source and vector. -/
theorem nonrenewedSourceAt_joint_proposal (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) q)
    (v : Vector p) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t
          (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r c v).val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t
          (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r c v).val),
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)) =
      ((ContinuousLearningRows.timeControlLaw p).map
        (firstPairUpdateDraw rate rewards C_star C_h control0 t
          (nonrenewedSourceAt rate rewards C_star C_h control0 u t q r control0 v))).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
  simp_rw [nonrenewedSourceAt_pairUpdate]
  exact firstPairUpdateDraw_joint_proposal rate rewards C_star C_h control0 t _

/-- The corresponding actual renewal factor, using its source-derived PRE
and renewed anchor; no relation to the last old logical cell is assumed. -/
theorem renewedSourceAt_joint_proposal (q : Fin (M p))
    (r : EventRemainder control0 t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) q)
    (v : Vector p) :
    (ContinuousLearningRows.timeControlLaw p).map (fun c =>
      ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h t
          (renewedSourceAt rate rewards C_star C_h control0 u t q r c v).val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t
          (renewedSourceAt rate rewards C_star C_h control0 u t q r c v).val),
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate c)) =
      ((ContinuousLearningRows.timeControlLaw p).map
        (firstPairUpdateDraw rate rewards C_star C_h control0 t
          (renewedSourceAt rate rewards C_star C_h control0 u t q r control0 v))).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
  simp_rw [renewedSourceAt_pairUpdate]
  exact firstPairUpdateDraw_joint_proposal rate rewards C_star C_h control0 t _

end ActualBranchDraws

section PostHistoryTests

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (u t : Fin p.T)

/-- Joint native nonrenewed transition and constructed appended history. -/
theorem nonrenewedFirstCell_postHistory_transition_test
    (Phi : TransitionData rate t × List (ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ d, ‖Phi d‖ ≤ B) :
    (∫ wv, Phi (nonrenewedTransition rate rewards C_star C_h control0 u t wv,
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2) ++
        [nonrenewedFirstCell rate rewards C_star C_h control0 t u wv])
      ∂nonrenewedLiftLaw rate rewards C_star C_h u t control0) =
    ∑ q : Fin (M p), ∫ rc : EventRemainder control0 t
        (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) q ×
        (Scalar × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p),
      ∫ e : ErasedAuxiliaryArray t, ∫ v : Vector p,
        let z := restoreProposalEventSource control0 t _
          (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q rc
        let installed := nonrenewedFirstSource rate rewards C_star C_h t u z v
        ∫ U,
          let d := nonrenewedReadout rate rewards C_star C_h u t ((z, e), v)
            (firstResidualCell rate rewards C_star C_h control0 t installed U)
          Phi (d, postHistory d)
          ∂firstResidualLaw rate rewards C_star C_h control0 t installed
        ∂nonrenewedVectorKernel rate rewards C_star C_h u t control0
          (restoreEventSource control0 t _
            (nonrenewedEvent_control_invariant rate rewards C_star C_h u t) q (rc.1, control0),
            insertActualRefreshCoordinate t e scalarZero)
        ∂erasedAuxiliaryLaw t
        ∂(eventRemainderLaw control0 t
          (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t) q).prod
          (scalarLaw.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)) := by
  exact nonrenewedFirstCell_transition_test rate rewards C_star C_h control0 u t
    (fun d => Phi (d, postHistory d))
    (hPhi.comp (measurable_transitionWithPostHistory rate t)) B (fun d => hB (d, postHistory d))

/-- Joint native renewed transition and constructed appended history. The
old list is retained while original current label zero is freshly consumed. -/
theorem renewedFirstCell_postHistory_transition_test
    (Phi : TransitionData rate t × List (ReferenceFirstLiveChronologicalPrefixFoundation.LogicalCell p rate) → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ d, ‖Phi d‖ ≤ B) :
    (∫ wv, Phi (renewedTransition rate rewards C_star C_h control0 u t wv,
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
        t.castSucc (wv.1.1.val, wv.1.2) ++
        [renewedFirstCell rate rewards C_star C_h control0 t u wv])
      ∂ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t) =
    ∑ q : Fin (M p), ∫ rc : EventRemainder control0 t
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) q ×
        (Scalar × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p),
      ∫ e : ErasedAuxiliaryArray t, ∫ v : Vector p,
        let z := restoreProposalEventSource control0 t _
          (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q rc
        let installed := renewedFirstSource rate rewards C_star C_h t u
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v)
        ∫ U,
          let d := renewedReadout rate rewards C_star C_h u t ((z, e), v)
            (firstResidualCell rate rewards C_star C_h control0 t installed U)
          Phi (d, postHistory d)
          ∂firstResidualLaw rate rewards C_star C_h control0 t installed
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t
          (restoreEventSource control0 t _
            (renewedEvent_control_invariant rate rewards C_star C_h control0 u t) q (rc.1, control0),
            insertRenewalRefreshScalar t e scalarZero)
        ∂erasedAuxiliaryLaw t
        ∂(eventRemainderLaw control0 t
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) q).prod
          (scalarLaw.prod (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)) := by
  exact renewedFirstCell_transition_test rate rewards C_star C_h control0 u t
    (fun d => Phi (d, postHistory d))
    (hPhi.comp (measurable_transitionWithPostHistory rate t)) B (fun d => hB (d, postHistory d))

end PostHistoryTests

end Bandits.Support.ReferenceFirstNextInstallationTransitionLaw
