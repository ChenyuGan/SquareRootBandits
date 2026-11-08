/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedBoundaryMeasurability
public import Bandits.Support.ReferenceSourceControlKernel
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# One retained original-source coupling on an actual launch-start stratum

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-423`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-46`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

The original remainder, including the original private J and every private
array, is retained in a finite, unnormalized composition product. Its boundary
is the actual generated initialization and active prefix on this subtype.
Both joint remainder/control laws and both restricted original-source laws
are proved by construction. The jointly Borel source certificate gives the
one-current-round effects on the two actual generated incoming inputs.

This does not assemble a total-source partition, no-input or terminal diagonal
branches, chronological iteration, logical queue/score laws, batch pre-pair
laws, conditional service/waiting laws, exceptional-event probabilities, or
regret. Predictable pending/current flag composition needs the independently
accepted release-observable producer; chronological gluing is another consumer.
The real zero-prefix seed at s=t is retained. No input at natural time T is
constructed, and no operational state is supplied outside the retained set.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open scoped Classical

namespace Bandits.Support.ReferenceRetainedSourceCoupling

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev ControlPair := ReferenceLaterOptionalControlResampling.ControlPair

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlPairMeasurableSpace (p : Parameters) : MeasurableSpace (ControlPair p) :=
  inferInstanceAs (MeasurableSpace (TimeControl p × TimeControl p))

include hs control0

local notation "Cset" => retainedLaunchStartSet rate rewards C_star C_h q t s control0
local notation "X" => RetainedLaunchStart rate rewards C_star C_h q t s hs control0
local notation "ν" => fixedControlRemainderLaw p q t
local notation "ctrlLaw" => timeControlLaw p
local notation "e" => fixedControlSplit p q t
local notation "β" => retainedIncomingBoundary rate rewards C_star C_h q t s hs control0

/-- The genuine inherited subtype measure, without normalization. -/
def retainedRemainderMeasure : Measure X := Measure.comap Subtype.val ν

local notation "μC" => retainedRemainderMeasure rate rewards C_star C_h q t s hs control0

instance retainedRemainderMeasure_finite : IsFiniteMeasure μC := by
  unfold retainedRemainderMeasure
  infer_instance

theorem retainedRemainderMeasure_map :
    (μC).map Subtype.val = (ν).restrict Cset :=
  map_comap_subtype_coe
    (measurableSet_retainedLaunchStartSet rate rewards C_star C_h q t s hs control0) ν

theorem retainedRemainderMeasure_apply (A : Set X) :
    μC A = ν (Subtype.val '' A) :=
  comap_subtype_coe_apply
    (measurableSet_retainedLaunchStartSet rate rewards C_star C_h q t s hs control0) ν A

theorem retainedRemainderMeasure_mass : μC Set.univ = ν Cset := by
  rw [retainedRemainderMeasure_apply]
  congr 1
  exact Set.image_univ.trans Subtype.range_coe

/-- Pull the actual paired-control kernel back along the proved Borel beta. -/
def retainedControlKernel : Kernel X (ControlPair p) :=
  (ReferenceLaterOptionalControlResampling.pairedControlKernel p rate).comap β
    (measurable_retainedIncomingBoundary rate rewards C_star C_h q t s hs control0)

local notation "K" => retainedControlKernel rate rewards C_star C_h q t s hs control0

theorem retainedControlKernel_apply (x : X) :
    K x = ReferenceLaterOptionalControlResampling.pairedControlKernel p rate (β x) := rfl

instance retainedControlKernel_markov : IsMarkovKernel K := by
  unfold retainedControlKernel
  infer_instance

theorem retainedControlKernel_fst :
    (K).map Prod.fst = Kernel.const X ctrlLaw := by
  ext x A hA
  rw [Kernel.map_apply _ measurable_fst, Kernel.const_apply,
    retainedControlKernel_apply,
    ReferenceLaterOptionalControlResampling.pairedControlKernel_fst]

theorem retainedControlKernel_snd :
    (K).map Prod.snd = Kernel.const X ctrlLaw := by
  ext x A hA
  rw [Kernel.map_apply _ measurable_snd, Kernel.const_apply,
    retainedControlKernel_apply,
    ReferenceLaterOptionalControlResampling.pairedControlKernel_snd]

/-- Retain the original subtype point while drawing only the current pair. -/
def retainedCoupling : Measure (X × ControlPair p) := (μC).compProd K

local notation "Λ" => retainedCoupling rate rewards C_star C_h q t s hs control0

instance retainedCoupling_finite : IsFiniteMeasure Λ := by
  unfold retainedCoupling
  infer_instance

theorem retainedCoupling_fst_joint :
    (Λ).map (fun z => (z.1, z.2.1)) = (μC).prod ctrlLaw := by
  change ((μC).compProd K).map (Prod.map id Prod.fst) = _
  rw [← Measure.compProd_map measurable_fst, retainedControlKernel_fst,
    Measure.compProd_const]

theorem retainedCoupling_snd_joint :
    (Λ).map (fun z => (z.1, z.2.2)) = (μC).prod ctrlLaw := by
  change ((μC).compProd K).map (Prod.map id Prod.snd) = _
  rw [← Measure.compProd_map measurable_snd, retainedControlKernel_snd,
    Measure.compProd_const]

/-- All Borel cylinders, with the retained point present in the joint law. -/
theorem retainedCoupling_fst_cylinder (A : Set X) (U : Set (TimeControl p))
    (hA : MeasurableSet A) (hU : MeasurableSet U) :
    Λ {z | z.1 ∈ A ∧ z.2.1 ∈ U} = μC A * ctrlLaw U := by
  have h := congrArg (fun m : Measure (X × TimeControl p) => m (A ×ˢ U))
    (retainedCoupling_fst_joint rate rewards C_star C_h q t s hs control0)
  rw [Measure.map_apply (μ := Λ) (f := fun z : X × ControlPair p => (z.1, z.2.1))
    (measurable_fst.prodMk
    (measurable_fst.comp measurable_snd)) (hA.prod hU), Measure.prod_prod] at h
  exact h

theorem retainedCoupling_snd_cylinder (A : Set X) (U : Set (TimeControl p))
    (hA : MeasurableSet A) (hU : MeasurableSet U) :
    Λ {z | z.1 ∈ A ∧ z.2.2 ∈ U} = μC A * ctrlLaw U := by
  have h := congrArg (fun m : Measure (X × TimeControl p) => m (A ×ˢ U))
    (retainedCoupling_snd_joint rate rewards C_star C_h q t s hs control0)
  rw [Measure.map_apply (μ := Λ) (f := fun z : X × ControlPair p => (z.1, z.2.2))
    (measurable_fst.prodMk
    (measurable_snd.comp measurable_snd)) (hA.prod hU), Measure.prod_prod] at h
  exact h

theorem retainedCoupling_mass : Λ Set.univ = ν Cset := by
  change ((μC).compProd K) Set.univ = _
  rw [Measure.compProd_apply_univ, retainedRemainderMeasure_mass]

/-- The literal source event: actual original J, crossing, and elapsed start. -/
def retainedSourceEvent : Set (SourceInput p) :=
  {z | sourceCoordinatorIndex p z = q ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s}

local notation "Esource" => retainedSourceEvent rate rewards C_star C_h q s

/-- Both directions use the actual initialization event/source theorem.
In particular the removed current control is arbitrary. -/
theorem retainedSourceEvent_iff_remainder (z : SourceInput p) :
    z ∈ Esource ↔ (e z).2 ∈ Cset := by
  constructor
  · rintro ⟨hindex, hcross, helapsed⟩
    apply retainedLaunchStartInputOfSource_mem rate rewards C_star C_h q t s hs control0 z
    · exact (sourceCoordinatorIndex_eq_selectedRowIndex p z).symm.trans hindex
    · exact hcross
    · exact helapsed
  · rintro ⟨hrem, hstart⟩
    have hindex : sourceCoordinatorIndex p z = q := by
      change PrivateSourceStreams.coordinatorIndex p (e z).2.2.1.2 = q at hrem
      rw [fixedControlSplit_private] at hrem
      exact hrem
    refine ⟨hindex, ?_⟩
    exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h q t control0 z
      ((sourceCoordinatorIndex_eq_selectedRowIndex p z).symm.trans hindex) s hs).mp hstart

theorem retainedSourceEvent_eq_preimage :
    Esource = e ⁻¹' (Set.univ ×ˢ Cset) := by
  ext z
  simpa only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and] using
    retainedSourceEvent_iff_remainder rate rewards C_star C_h q t s hs control0 z

theorem measurableSet_retainedSourceEvent : MeasurableSet Esource := by
  rw [retainedSourceEvent_eq_preimage rate rewards C_star C_h q t s hs control0]
  exact (e).measurable (MeasurableSet.univ.prod
    (measurableSet_retainedLaunchStartSet rate rewards C_star C_h q t s hs control0))

theorem retainedSourceEvent_reconstruct_iff (r : FixedControlRemainder p q t)
    (control : TimeControl p) :
    (e).symm (control, r) ∈ Esource ↔ r ∈ Cset := by
  rw [retainedSourceEvent_iff_remainder rate rewards C_star C_h q t s hs control0,
    (e).apply_symm_apply]

/-- Reconstruct one original source from the same retained remainder. -/
def retainedSourceMap : X × TimeControl p → SourceInput p :=
  fun z => (e).symm (z.2, z.1.val)

theorem measurable_retainedSourceMap :
    Measurable (retainedSourceMap rate rewards C_star C_h q t s hs control0) :=
  (e).symm.measurable.comp
    (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))

private theorem retained_product_lift :
    ((μC).prod ctrlLaw).map (fun z => (z.2, z.1.val)) = (ctrlLaw).prod ((ν).restrict Cset) := by
  calc
    _ = (((μC).prod ctrlLaw).map Prod.swap).map (Prod.map id Subtype.val) := by
      rw [Measure.map_map (measurable_id.prodMap measurable_subtype_coe) measurable_swap]
      rfl
    _ = ((ctrlLaw).prod μC).map (Prod.map id Subtype.val) := by rw [Measure.prod_swap]
    _ = (ctrlLaw).prod ((ν).restrict Cset) := by
      rw [← Measure.map_prod_map ctrlLaw μC measurable_id measurable_subtype_coe,
        Measure.map_id, retainedRemainderMeasure_map]

/-- The inverse product law is restricted to precisely the actual source
event; no extra private-index factor or positive-mass premise occurs. -/
theorem retained_inverse_restrict :
    ((ctrlLaw).prod ((ν).restrict Cset)).map (e).symm =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
  have hC := measurableSet_retainedLaunchStartSet rate rewards C_star C_h q t s hs control0
  calc
    _ = ((((ctrlLaw).prod ν).restrict (Set.univ ×ˢ Cset))).map (e).symm := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ((((BootstrapPrivateRoundStreams.sourceInputLaw p).map e).restrict (Set.univ ×ˢ Cset))).map (e).symm := by
      rw [sourceInputLaw_map_fixedControlSplit]
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (e ⁻¹' (Set.univ ×ˢ Cset))).map
        ((e).symm ∘ e) := by
      rw [Measure.restrict_map (e).measurable (MeasurableSet.univ.prod hC),
        Measure.map_map (e).symm.measurable (e).measurable]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
      rw [← retainedSourceEvent_eq_preimage rate rewards C_star C_h q t s hs control0]
      have he : (e).symm ∘ e = id := funext (e).symm_apply_apply
      rw [he, Measure.map_id]

theorem retainedSourceMap_product :
    ((μC).prod ctrlLaw).map (retainedSourceMap rate rewards C_star C_h q t s hs control0) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
  calc
    _ = (((μC).prod ctrlLaw).map (fun z => (z.2, z.1.val))).map (e).symm := by
      exact (Measure.map_map (μ := (μC).prod ctrlLaw)
        (f := fun z : X × TimeControl p => (z.2, z.1.val)) (e).symm.measurable
        (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))).symm
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
      rw [retained_product_lift rate rewards C_star C_h q t s hs control0,
        retained_inverse_restrict rate rewards C_star C_h q t s hs control0]

/-- Both inverse splits use exactly the same original remainder. -/
def retainedSourcePairMap : X × ControlPair p → SourceInput p × SourceInput p :=
  fun z => ((e).symm (z.2.1, z.1.val), (e).symm (z.2.2, z.1.val))

local notation "pairMap" => retainedSourcePairMap rate rewards C_star C_h q t s hs control0

theorem measurable_retainedSourcePairMap : Measurable pairMap := by
  exact ((e).symm.measurable.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_subtype_coe.comp measurable_fst))).prodMk
    ((e).symm.measurable.comp ((measurable_snd.comp measurable_snd).prodMk
      (measurable_subtype_coe.comp measurable_fst)))

theorem retainedSourcePairMap_split (z : X × ControlPair p) :
    e (pairMap z).1 = (z.2.1, z.1.val) ∧
      e (pairMap z).2 = (z.2.2, z.1.val) :=
  ⟨(e).apply_symm_apply _, (e).apply_symm_apply _⟩

theorem retainedSourcePairMap_mem (z : X × ControlPair p) :
    (pairMap z).1 ∈ Esource ∧ (pairMap z).2 ∈ Esource := by
  exact ⟨(retainedSourceEvent_reconstruct_iff rate rewards C_star C_h q t s hs control0
      z.1.val z.2.1).mpr z.1.property,
    (retainedSourceEvent_reconstruct_iff rate rewards C_star C_h q t s hs control0
      z.1.val z.2.2).mpr z.1.property⟩

/-- The finite source-pair measure on this actual launch-start stratum. -/
def retainedSourcePairLaw : Measure (SourceInput p × SourceInput p) := (Λ).map pairMap

local notation "sourcePairLaw" => retainedSourcePairLaw rate rewards C_star C_h q t s hs control0

instance retainedSourcePairLaw_finite : IsFiniteMeasure sourcePairLaw := by
  unfold retainedSourcePairLaw
  infer_instance

theorem retainedSourcePairLaw_fst :
    (sourcePairLaw).map Prod.fst = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
  rw [retainedSourcePairLaw, Measure.map_map measurable_fst
    (measurable_retainedSourcePairMap rate rewards C_star C_h q t s hs control0)]
  change (Λ).map (retainedSourceMap rate rewards C_star C_h q t s hs control0 ∘
    fun z => (z.1, z.2.1)) = _
  rw [← Measure.map_map (μ := Λ) (f := fun z : X × ControlPair p => (z.1, z.2.1))
    (measurable_retainedSourceMap rate rewards C_star C_h q t s hs control0)
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)),
    retainedCoupling_fst_joint, retainedSourceMap_product]

theorem retainedSourcePairLaw_snd :
    (sourcePairLaw).map Prod.snd = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict Esource := by
  rw [retainedSourcePairLaw, Measure.map_map measurable_snd
    (measurable_retainedSourcePairMap rate rewards C_star C_h q t s hs control0)]
  change (Λ).map (retainedSourceMap rate rewards C_star C_h q t s hs control0 ∘
    fun z => (z.1, z.2.2)) = _
  rw [← Measure.map_map (μ := Λ) (f := fun z : X × ControlPair p => (z.1, z.2.2))
    (measurable_retainedSourceMap rate rewards C_star C_h q t s hs control0)
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)),
    retainedCoupling_snd_joint, retainedSourceMap_product]

theorem retainedSourcePairLaw_mass :
    sourcePairLaw Set.univ = BootstrapPrivateRoundStreams.sourceInputLaw p Esource := by
  have h := congrArg (fun m : Measure (SourceInput p) => m Set.univ)
    (retainedSourcePairLaw_fst rate rewards C_star C_h q t s hs control0)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h

theorem retained_stratum_mass : ν Cset = BootstrapPrivateRoundStreams.sourceInputLaw p Esource := by
  calc
    _ = Λ Set.univ := (retainedCoupling_mass rate rewards C_star C_h q t s hs control0).symm
    _ = sourcePairLaw Set.univ := by
      rw [retainedSourcePairLaw, Measure.map_apply
        (measurable_retainedSourcePairMap rate rewards C_star C_h q t s hs control0)
        MeasurableSet.univ, Set.preimage_univ]
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p Esource :=
      retainedSourcePairLaw_mass rate rewards C_star C_h q t s hs control0

/-- The actual varying boundary together with its two reconstructed sources. -/
def retainedBoundarySourcePairMap : X × ControlPair p →
    ReferenceActivePhysicalStep.RoundInput p rate × (SourceInput p × SourceInput p) :=
  fun z => (β z.1, pairMap z)

theorem measurable_retainedBoundarySourcePairMap :
    Measurable (retainedBoundarySourcePairMap rate rewards C_star C_h q t s hs control0) := by
  have hboundary : Measurable (fun z : X × ControlPair p => β z.1) :=
    (measurable_retainedIncomingBoundary rate rewards C_star C_h q t s hs control0).comp
      measurable_fst
  exact hboundary.prodMk
    (measurable_retainedSourcePairMap rate rewards C_star C_h q t s hs control0)

/-- Literal pullback of the jointly Borel source certificate along the actual
beta and the same two-source reconstruction. -/
def retainedJointCertificate : Set (X × ControlPair p) :=
  retainedBoundarySourcePairMap rate rewards C_star C_h q t s hs control0 ⁻¹'
    {z : ReferenceActivePhysicalStep.RoundInput p rate × (SourceInput p × SourceInput p) |
      z.2 ∈ pairedSourceFibreEvent p rate z.1}

local notation "certificate" => retainedJointCertificate rate rewards C_star C_h q t s hs control0

theorem measurableSet_retainedJointCertificate : MeasurableSet certificate :=
  (measurable_retainedBoundarySourcePairMap rate rewards C_star C_h q t s hs control0)
    (ReferenceSourceControlKernel.measurableSet_pairedSourceFibreEvent_joint p rate)

private theorem retained_control_certificate (x : X) (controls : ControlPair p)
    (hc : controls ∈ ReferenceLaterOptionalControlResampling.pairedControlFibreEvent (β x)) :
    (x, controls) ∈ certificate := by
  apply Set.mem_iUnion.mpr
  refine ⟨q, ?_⟩
  change sourceCoordinatorIndex p (pairMap (x, controls)).1 = q ∧
    sourceCoordinatorIndex p (pairMap (x, controls)).2 = q ∧
    (fixedControlSplit p q (β x).time (pairMap (x, controls)).1).2 =
      (fixedControlSplit p q (β x).time (pairMap (x, controls)).2).2 ∧
    ((fixedControlSplit p q (β x).time (pairMap (x, controls)).1).1,
      (fixedControlSplit p q (β x).time (pairMap (x, controls)).2).1) ∈
      ReferenceLaterOptionalControlResampling.pairedControlFibreEvent (β x)
  rw [retainedIncomingBoundary_time]
  refine ⟨fixedControlSplit_symm_coordinatorIndex p q t controls.1 x.val x.property.1,
    fixedControlSplit_symm_coordinatorIndex p q t controls.2 x.val x.property.1, ?_, ?_⟩
  · exact congrArg Prod.snd (retainedSourcePairMap_split rate rewards C_star C_h q t s hs
      control0 (x, controls)).1 |>.trans
        (congrArg Prod.snd (retainedSourcePairMap_split rate rewards C_star C_h q t s hs
          control0 (x, controls)).2).symm
  · simpa only [(retainedSourcePairMap_split rate rewards C_star C_h q t s hs control0
      (x, controls)).1, (retainedSourcePairMap_split rate rewards C_star C_h q t s hs control0
      (x, controls)).2] using hc

/-- AE validity is obtained with the original subtype point held fixed in
the composition product, rather than by a fixed-boundary whole-source redraw. -/
theorem ae_retainedJointCertificate : ∀ᵐ z ∂Λ, z ∈ certificate := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_retainedJointCertificate rate rewards C_star C_h q t s hs control0)
  apply Filter.Eventually.of_forall
  intro x
  filter_upwards [ReferenceLaterOptionalControlResampling.ae_pairedControlFibreEvent
    (p := p) (rate := rate) (β x)] with controls hc
  exact retained_control_certificate rate rewards C_star C_h q t s hs control0 x controls hc

/-- Actual original-source frames from F's certificate. The full private
coordinate equality includes all private arrays and the original J scalar. -/
theorem ae_retained_frames :
    ∀ᵐ z ∂Λ,
      let sources := pairMap z
      sourceCoordinatorIndex p sources.1 = q ∧
      sourceCoordinatorIndex p sources.2 = q ∧
      (e sources.1).2 = z.1.val ∧ (e sources.2).2 = z.1.val ∧
      sources.1.2 = sources.2.2 ∧ sources.1.1.1 = sources.2.1.1 ∧
      (∀ j : Fin (M p), (sources.1.1.2 j).1 = (sources.2.1.2 j).1) ∧
      (∀ j : Fin (M p), j ≠ q → sources.1.1.2 j = sources.2.1.2 j) ∧
      (∀ v : ReferenceSelectedAffinePairLaw.Other t,
        (sources.1.1.2 q).2 v = (sources.2.1.2 q).2 v) ∧
      (∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2.1).2.1 label =
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2.2).2.1 label) ∧
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2.1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p z.2.2).2.2 := by
  filter_upwards [ae_retainedJointCertificate rate rewards C_star C_h q t s hs control0]
    with z hz
  obtain ⟨q', hleft, hright, hprivate, hid, hforward, hrows, htimes, hscalar, haffine⟩ :=
    pairedSourceFibreEvent_frames p rate (β z.1) (pairMap z) hz
  have hq : q' = q := hleft.symm.trans
    (retainedSourcePairMap_mem rate rewards C_star C_h q t s hs control0 z).1.1
  rw [hq] at hleft hright hrows htimes hscalar haffine
  have hsplit := retainedSourcePairMap_split rate rewards C_star C_h q t s hs control0 z
  refine ⟨hleft, hright, congrArg Prod.snd hsplit.1, congrArg Prod.snd hsplit.2,
    hprivate, hid, hforward, hrows, ?_, ?_, ?_⟩
  · exact htimes
  · have hscalar' : ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (e (pairMap z).1).1).2.1 label =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (e (pairMap z).2).1).2.1 label := hscalar
    rw [hsplit.1, hsplit.2] at hscalar'
    exact hscalar'
  · have haffine' :
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (e (pairMap z).1).1).2.2 =
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
          (e (pairMap z).2).1).2.2 := haffine
    rw [hsplit.1, hsplit.2] at haffine'
    exact haffine'

/-- Equality of computed evidence and physical effects for the TWO ACTUAL
generated incoming inputs, each with its own source-generated seed and prefix. -/
theorem ae_retained_generated_effects :
    ∀ᵐ z ∂Λ,
      ReferenceActivePhysicalHorizon.computedEvidence
          (retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 z.1 z.2.1) =
        ReferenceActivePhysicalHorizon.computedEvidence
          (retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 z.1 z.2.2) ∧
      let left := ReferenceActivePhysicalStep.step
        (retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 z.1 z.2.1)
      let right := ReferenceActivePhysicalStep.step
        (retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 z.1 z.2.2)
      left.next = right.next ∧
        left.preparation.arms.actions = right.preparation.arms.actions ∧
        left.preparation.feedback.feedback = right.preparation.feedback.feedback ∧
        left.ownEntries = right.ownEntries ∧
        left.coordinator = right.coordinator ∧ left.followers = right.followers := by
  filter_upwards [ae_retainedJointCertificate rate rewards C_star C_h q t s hs control0]
    with z hz
  rw [retainedGeneratedNextInput_eq_roundInputAtSource rate rewards C_star C_h q t s hs
      control0 z.1 z.2.1,
    retainedGeneratedNextInput_eq_roundInputAtSource rate rewards C_star C_h q t s hs
      control0 z.1 z.2.2]
  exact pairedSourceFibreEvent_effects p rate (β z.1) (pairMap z) hz

end Bandits.Support.ReferenceRetainedSourceCoupling

end
