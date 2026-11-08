/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceTotalSourcePairCoupling
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Conditional resampling of the whole original source

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-426`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-46`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

This internal measure construction disintegrates the accepted fixed-calendar
source-pair law by its first original source. The measurable spaces are the
existing real-subtype and finite product spaces. On an active source stratum,
the boundary certificate uses the actual retained remainder and its generated
incoming boundary. The complement and natural terminal branch are diagonal.

The conditional kernel is a version defined up to source-null inputs. Its
library null choices are not operational protocol defaults. This module does
not construct a logical learner, prove an adapted slow-set law, iterate the
kernel, or establish physical execution congruence or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped ENNReal

namespace Bandits.Support.ReferenceTotalSourceDisintegration

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev StratumIndex := @ReferenceTotalSourcePairCoupling.StratumIndex

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p × ExtendedPrivateCoordinates p)
  infer_instance

local instance controlPairMeasurableSpace (p : Parameters) :
    MeasurableSpace (ReferenceLaterOptionalControlResampling.ControlPair p) :=
  inferInstanceAs (MeasurableSpace (TimeControl p × TimeControl p))

/- These instances certify the existing spaces; none supplies a new
measurable structure or replaces a continuous coordinate by a discrete one. -/
instance scalar_standardBorelSpace : StandardBorelSpace ContinuousLearningRows.Scalar :=
  (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)).standardBorel

instance scalar_nonempty : Nonempty ContinuousLearningRows.Scalar :=
  ⟨⟨0, le_rfl, zero_lt_one⟩⟩

private instance affineSample_discreteMeasurableSpace (B : ℕ) :
    DiscreteMeasurableSpace (AffineChannelLaw.Sample B) := ⟨fun _ => trivial⟩

instance affineSample_standardBorelSpace (B : ℕ) :
    StandardBorelSpace (AffineChannelLaw.Sample B) :=
  standardBorelSpace_of_discreteMeasurableSpace

instance sourceInput_standardBorelSpace (p : Parameters) : StandardBorelSpace (SourceInput p) := by
  have : StandardBorelSpace (TimeControl p) := by
    change StandardBorelSpace (ContinuousLearningRows.Slice p × ContinuousLearningRows.AffineSamples p)
    infer_instance
  have : StandardBorelSpace (CompletePublicTable.CompleteRow p) := by
    change StandardBorelSpace (CompletePublicTable.ForwardRow p × (Fin p.T → TimeControl p))
    infer_instance
  have : StandardBorelSpace (ExtendedPrivateCoordinates p) := by
    change StandardBorelSpace (PrivateSourceStreams.PrivateCoordinates p ×
      (PlayerRoundScalars p × CoordinatorTargetScalars p))
    infer_instance
  change StandardBorelSpace
    (CompletePublicTable.PublishedOutput p × ExtendedPrivateCoordinates p)
  infer_instance

instance sourceInput_nonempty (p : Parameters) : Nonempty (SourceInput p) := by
  let zero : ContinuousLearningRows.Scalar := ⟨0, le_rfl, zero_lt_one⟩
  exact ⟨((fun _ _ => false, fun _ => (fun _ _ => false,
    fun _ => (fun _ => zero, fun _ => (fun _ => 0, 0)))),
    ((fun _ _ => (zero, zero, zero), zero), (fun _ => zero, fun _ => zero)))⟩

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (control0 : TimeControl p)

local notation "μ₀" => sourceInputLaw p
local notation "ρ" => ReferenceTotalSourcePairCoupling.totalSourcePairLaw
  rate rewards C_star C_h t control0

instance totalSourcePairLaw_probability : IsProbabilityMeasure ρ :=
  ⟨ReferenceTotalSourcePairCoupling.totalSourcePairLaw_mass
    rate rewards C_star C_h t control0⟩

/-- A conditional kernel on the original complete source, literally the
library disintegration of the accepted total source-pair measure. -/
def sourceKernel : Kernel (SourceInput p) (SourceInput p) := (ρ).condKernel

local notation "K" => sourceKernel rate rewards C_star C_h t control0

instance sourceKernel_markov : IsMarkovKernel K := by
  unfold sourceKernel
  infer_instance

theorem measurable_sourceKernel_eval (C : Set (SourceInput p)) (hC : MeasurableSet C) :
    Measurable (fun z => K z C) := Kernel.measurable_coe K hC

/-- The finite calendar parameter is jointly Borel with the source. Rewards,
rate, constants and the baseline control remain fixed throughout this family. -/
theorem measurable_sourceKernel_eval_joint (C : Set (SourceInput p))
    (hC : MeasurableSet C) :
    Measurable (fun z : Fin p.T × SourceInput p =>
      sourceKernel rate rewards C_star C_h z.1 control0 z.2 C) :=
  measurable_from_prod_countable_right fun u =>
    measurable_sourceKernel_eval rate rewards C_star C_h u control0 C hC

theorem sourceKernel_disintegrate : (μ₀).compProd K = ρ := by
  have hfst : (ρ).fst = μ₀ :=
    ReferenceTotalSourcePairCoupling.totalSourcePairLaw_fst
      rate rewards C_star C_h t control0
  change (μ₀).compProd (ρ).condKernel = ρ
  rw [← hfst]
  exact Measure.disintegrate _ _

theorem sourceKernel_stationary : K ∘ₘ μ₀ = μ₀ := by
  rw [← Measure.snd_compProd, sourceKernel_disintegrate]
  exact ReferenceTotalSourcePairCoupling.totalSourcePairLaw_snd
    rate rewards C_star C_h t control0

private theorem compProd_restrict_first {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (ν : Measure α) [SFinite ν]
    (κ : Kernel α β) [IsSFiniteKernel κ] (E : Set α) (hE : MeasurableSet E) :
    (ν.restrict E).compProd κ = (ν.compProd κ).restrict (Prod.fst ⁻¹' E) := by
  rw [← Set.prod_univ]
  change ((Kernel.const Unit (ν.restrict E)) ⊗ₖ Kernel.prodMkLeft Unit κ) () = _
  rw [← Kernel.restrict_const hE, Kernel.compProd_restrict_left hE]
  rfl

theorem sourceKernel_restrict_stratum (i : StratumIndex t) :
    ((μ₀).restrict (ReferenceTotalSourcePairCoupling.sourceStratumEvent
      rate rewards C_star C_h t i)).compProd K =
      ReferenceTotalSourcePairCoupling.sourceStratumPairLaw
        rate rewards C_star C_h t control0 i := by
  rw [compProd_restrict_first _ _ _
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 i), sourceKernel_disintegrate]
  exact ReferenceTotalSourcePairCoupling.totalSourcePairLaw_restrict_stratum
    rate rewards C_star C_h t control0 i

theorem sourceKernel_restrict_complement :
    ((μ₀).restrict (ReferenceTotalSourcePairCoupling.activeSourceSet
      rate rewards C_star C_h t)ᶜ).compProd K =
      ((μ₀).restrict (ReferenceTotalSourcePairCoupling.activeSourceSet
        rate rewards C_star C_h t)ᶜ).map
          ReferenceTotalSourcePairCoupling.sourceDiagonalMap := by
  rw [compProd_restrict_first _ _ _
    (ReferenceTotalSourcePairCoupling.measurableSet_activeSourceSet
      rate rewards C_star C_h t control0).compl, sourceKernel_disintegrate]
  exact ReferenceTotalSourcePairCoupling.totalSourcePairLaw_restrict_activeComplement
    rate rewards C_star C_h t control0

/-- The full jointly Borel frame retains every private array and the original
J scalar, IDs, all forward rows, other rows/times, and current nonassignment
scalar and affine coordinates. -/
theorem ae_sourceKernel_frames :
    ∀ᵐ z ∂μ₀, ∀ᵐ z' ∂K z,
      (z, z') ∈ ReferenceTotalSourcePairCoupling.sourceFrameSet t := by
  apply (Measure.ae_compProd_iff
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceFrameSet t)).mp
  rw [sourceKernel_disintegrate]
  exact ReferenceTotalSourcePairCoupling.ae_totalSourcePairLaw_sourceFrames
    rate rewards C_star C_h t control0

theorem ae_sourceKernel_stratum_frames (i : StratumIndex t) :
    ∀ᵐ z ∂(μ₀).restrict (ReferenceTotalSourcePairCoupling.sourceStratumEvent
      rate rewards C_star C_h t i), ∀ᵐ z' ∂K z,
      (z, z') ∈ ReferenceTotalSourcePairCoupling.sourceFrameCell t i.1 ∧
      z' ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
        rate rewards C_star C_h t i := by
  have hE := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i
  apply (Measure.ae_compProd_iff
    ((ReferenceTotalSourcePairCoupling.measurableSet_sourceFrameCell t i.1).inter
      (measurable_snd hE))).mp
  rw [sourceKernel_restrict_stratum]
  have hsnd : ∀ᵐ z ∂ReferenceTotalSourcePairCoupling.sourceStratumPairLaw
      rate rewards C_star C_h t control0 i,
      z.2 ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
        rate rewards C_star C_h t i := by
    apply (ae_map_iff measurable_snd.aemeasurable hE).mp
    rw [ReferenceTotalSourcePairCoupling.sourceStratumPairLaw_snd]
    exact ae_restrict_mem hE
  filter_upwards [ReferenceTotalSourcePairCoupling.ae_sourceStratum_sourceFrames
    rate rewards C_star C_h t control0 i, hsnd] with z hz hz'
  exact ⟨hz, hz'⟩

/-- On the complement the kernel is diagonal almost everywhere. This asserts
no pointwise uniqueness on source-null inputs. -/
theorem ae_sourceKernel_complement :
    ∀ᵐ z ∂(μ₀).restrict (ReferenceTotalSourcePairCoupling.activeSourceSet
      rate rewards C_star C_h t)ᶜ, K z = Measure.dirac z := by
  have hdiag : ∀ᵐ z ∂((μ₀).restrict
      (ReferenceTotalSourcePairCoupling.activeSourceSet rate rewards C_star C_h t)ᶜ).compProd K,
      z.1 = z.2 := by
    rw [sourceKernel_restrict_complement]
    apply (ae_map_iff
      (ReferenceTotalSourcePairCoupling.measurable_sourceDiagonalMap (p := p)).aemeasurable
      (measurableSet_eq_fun measurable_fst measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  filter_upwards [Measure.ae_ae_of_ae_compProd hdiag] with z hz
  calc
    K z = (K z).map id := Measure.map_id.symm
    _ = (K z).map (fun _ => z) := Measure.map_congr (hz.mono fun _ h => h.symm)
    _ = Measure.dirac z := by rw [Measure.map_const, measure_univ, one_smul]

/-- Natural terminal time has no current control and uses the identity kernel. -/
def terminalSourceKernel (p : Parameters) : Kernel (SourceInput p) (SourceInput p) := Kernel.id

instance terminalSourceKernel_markov (p : Parameters) : IsMarkovKernel (terminalSourceKernel p) := by
  unfold terminalSourceKernel
  infer_instance

theorem terminalSourceKernel_disintegrate (p : Parameters) :
    (sourceInputLaw p).compProd (terminalSourceKernel p) =
      ReferenceTotalSourcePairCoupling.terminalSourcePairLaw p := by
  rw [terminalSourceKernel, Measure.compProd_id]
  rfl

section RetainedBoundary

open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceRetainedSourceCoupling

variable (i : StratumIndex t)

/-- A Borel subtype of the original source: original J, actual initialization
crossing, and actual elapsed boundary. No operational state is supplied. -/
abbrev SourceStratum :=
  {z : SourceInput p // z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
    rate rewards C_star C_h t i}

local notation "E" => ReferenceTotalSourcePairCoupling.sourceStratumEvent
  rate rewards C_star C_h t i
local notation "Z" => SourceStratum rate rewards C_star C_h t i
local notation "X" => RetainedLaunchStart rate rewards C_star C_h (Prod.fst i) t
  (Fin.val (Prod.snd i)) (Nat.lt_succ_iff.mp (Fin.isLt (Prod.snd i))) control0
local notation "Λ" => retainedCoupling rate rewards C_star C_h (Prod.fst i) t
  (Fin.val (Prod.snd i)) (Nat.lt_succ_iff.mp (Fin.isLt (Prod.snd i))) control0
local notation "pairMap" => retainedSourcePairMap rate rewards C_star C_h (Prod.fst i) t
  (Fin.val (Prod.snd i)) (Nat.lt_succ_iff.mp (Fin.isLt (Prod.snd i))) control0

/-- The inherited, unnormalized source restriction on the actual event. -/
def sourceStratumMeasure : Measure Z := Measure.comap Subtype.val μ₀

instance sourceStratumMeasure_finite :
    IsFiniteMeasure (sourceStratumMeasure rate rewards C_star C_h t i) := by
  unfold sourceStratumMeasure
  infer_instance

include control0 in
theorem sourceStratumMeasure_map :
    (sourceStratumMeasure rate rewards C_star C_h t i).map Subtype.val = (μ₀).restrict E :=
  map_comap_subtype_coe
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 i) μ₀

/-- Literally apply the admitted source selector to the three original event
conjuncts. There is no boundary parameter and no off-event extension. -/
def sourceRetainedInput (z : Z) : X :=
  retainedLaunchStartInputOfSource rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0 z.val
    ((sourceCoordinatorIndex_eq_selectedRowIndex p z.val).symm.trans z.property.1)
    z.property.2.1 z.property.2.2

theorem sourceRetainedInput_val (z : Z) :
    (sourceRetainedInput rate rewards C_star C_h t control0 i z).val =
      (fixedControlSplit p i.1 t z.val).2 :=
  retainedLaunchStartInputOfSource_val rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0 z.val
    ((sourceCoordinatorIndex_eq_selectedRowIndex p z.val).symm.trans z.property.1)
    z.property.2.1 z.property.2.2

theorem measurable_sourceRetainedInput :
    Measurable (sourceRetainedInput rate rewards C_star C_h t control0 i) := by
  have hvalue : Measurable (fun z : Z => (fixedControlSplit p i.1 t z.val).2) :=
    measurable_snd.comp ((fixedControlSplit p i.1 t).measurable.comp measurable_subtype_coe)
  exact hvalue.subtype_mk

/-- The actual generated incoming boundary on the original source event. -/
def sourceIncomingBoundary (z : Z) : ReferenceActivePhysicalStep.RoundInput p rate :=
  retainedIncomingBoundary rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0
    (sourceRetainedInput rate rewards C_star C_h t control0 i z)

theorem measurable_sourceIncomingBoundary :
    Measurable (sourceIncomingBoundary rate rewards C_star C_h t control0 i) :=
  (measurable_retainedIncomingBoundary rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0).comp
      (measurable_sourceRetainedInput rate rewards C_star C_h t control0 i)

theorem sourceIncomingBoundary_time (z : Z) :
    (sourceIncomingBoundary rate rewards C_star C_h t control0 i z).time = t := rfl

/-- Restoring this source's whole rows and original J in the template gives
the input actually generated from its corrected seed and active prefix. -/
theorem sourceIncomingBoundary_generatedNextInput (z : Z) :
    retainedGeneratedNextInput rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0
      (sourceRetainedInput rate rewards C_star C_h t control0 i z)
      (fixedControlSplit p i.1 t z.val).1 =
    roundInputAtSource p rate (sourceIncomingBoundary rate rewards C_star C_h t control0 i z)
      z.val :=
  retainedGeneratedNextInput_eq_of_source rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0 z.val
    ((sourceCoordinatorIndex_eq_selectedRowIndex p z.val).symm.trans z.property.1)
    z.property.2.1 z.property.2.2

/-- Keep the event source as a subtype while applying the same source kernel. -/
def sourceStratumCoupling : Measure (Z × SourceInput p) :=
  (sourceStratumMeasure rate rewards C_star C_h t i).compProd
    ((K).comap Subtype.val measurable_subtype_coe)

/-- Forgetting only the subtype proof recovers exactly the accepted cell law. -/
theorem sourceStratumCoupling_map :
    (sourceStratumCoupling rate rewards C_star C_h t control0 i).map
      (Prod.map Subtype.val id) =
      ReferenceTotalSourcePairCoupling.sourceStratumPairLaw
        rate rewards C_star C_h t control0 i := by
  have hE := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i
  have hforget : Measurable (Prod.map (Subtype.val : Z → SourceInput p) (id : SourceInput p → _)) :=
    measurable_subtype_coe.prodMap measurable_id
  ext C hC
  rw [Measure.map_apply hforget hC, sourceStratumCoupling,
    Measure.compProd_apply (hforget hC),
    ← sourceKernel_restrict_stratum rate rewards C_star C_h t control0 i,
    Measure.compProd_apply hC]
  change (∫⁻ z : Z, K z.val (Prod.mk z.val ⁻¹' C) ∂Measure.comap Subtype.val μ₀) =
    ∫⁻ z in E, K z (Prod.mk z ⁻¹' C) ∂μ₀
  exact lintegral_subtype_comap (μ := μ₀) hE (fun z => K z (Prod.mk z ⁻¹' C))

private def retainedStratumPairMap : X × ReferenceLaterOptionalControlResampling.ControlPair p →
    Z × SourceInput p := fun z =>
  (⟨(pairMap z).1, (retainedSourcePairMap_mem rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0 z).1⟩, (pairMap z).2)

private theorem measurable_retainedStratumPairMap :
    Measurable (retainedStratumPairMap rate rewards C_star C_h t control0 i) := by
  have hpair := measurable_retainedSourcePairMap rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0
  exact (measurable_fst.comp hpair).subtype_mk.prodMk (measurable_snd.comp hpair)

/-- Recovering the first source's retained point recovers the SAME latent
point of the original retained construction, including every private array. -/
private theorem sourceRetainedInput_recover
    (z : X × ReferenceLaterOptionalControlResampling.ControlPair p) :
    sourceRetainedInput rate rewards C_star C_h t control0 i
      (retainedStratumPairMap rate rewards C_star C_h t control0 i z).1 = z.1 := by
  apply Subtype.ext
  rw [sourceRetainedInput_val]
  exact congrArg Prod.snd (retainedSourcePairMap_split rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0 z).1

private theorem sourceStratumCoupling_eq_retained :
    sourceStratumCoupling rate rewards C_star C_h t control0 i =
      (Λ).map (retainedStratumPairMap rate rewards C_star C_h t control0 i) := by
  have hE := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i
  have hforget : MeasurableEmbedding
      (Prod.map (Subtype.val : Z → SourceInput p) (id : SourceInput p → SourceInput p)) :=
    (MeasurableEmbedding.subtype_coe hE).prodMap MeasurableEmbedding.id
  apply hforget.map_injective
  rw [sourceStratumCoupling_map,
    Measure.map_map hforget.measurable
      (measurable_retainedStratumPairMap rate rewards C_star C_h t control0 i)]
  rfl

/-- Pull back S's JOINT Borel certificate along the actual varying boundary
and both original sources. Fixed-boundary sections alone do not give this. -/
def sourceRetainedCertificate : Set (Z × SourceInput p) :=
  (fun z => (sourceIncomingBoundary rate rewards C_star C_h t control0 i z.1,
    (z.1.val, z.2))) ⁻¹'
      {z : ReferenceActivePhysicalStep.RoundInput p rate × (SourceInput p × SourceInput p) |
        z.2 ∈ pairedSourceFibreEvent p rate z.1}

theorem measurableSet_sourceRetainedCertificate :
    MeasurableSet (sourceRetainedCertificate rate rewards C_star C_h t control0 i) := by
  have hboundary : Measurable (fun z : Z × SourceInput p =>
      sourceIncomingBoundary rate rewards C_star C_h t control0 i z.1) :=
    (measurable_sourceIncomingBoundary rate rewards C_star C_h t control0 i).comp measurable_fst
  have hsource : Measurable (fun z : Z × SourceInput p => (z.1.val, z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  exact (hboundary.prodMk hsource)
    (ReferenceSourceControlKernel.measurableSet_pairedSourceFibreEvent_joint p rate)

theorem ae_sourceStratumCoupling_retainedCertificate :
    ∀ᵐ z ∂sourceStratumCoupling rate rewards C_star C_h t control0 i,
      z ∈ sourceRetainedCertificate rate rewards C_star C_h t control0 i := by
  rw [sourceStratumCoupling_eq_retained]
  apply (ae_map_iff
    (measurable_retainedStratumPairMap rate rewards C_star C_h t control0 i).aemeasurable
    (measurableSet_sourceRetainedCertificate rate rewards C_star C_h t control0 i)).mpr
  filter_upwards [ae_retainedJointCertificate rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0] with z hz
  change pairMap z ∈ pairedSourceFibreEvent p rate
    (retainedIncomingBoundary rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0
      (sourceRetainedInput rate rewards C_star C_h t control0 i
        (retainedStratumPairMap rate rewards C_star C_h t control0 i z).1))
  rw [sourceRetainedInput_recover]
  exact hz

/-- Conditional compatibility with the ACTUAL retained boundary computed
from the first original source. The measure is the inherited restriction,
without normalization or a positive-cell-mass assumption. -/
theorem ae_sourceKernel_retainedCertificate :
    ∀ᵐ z ∂sourceStratumMeasure rate rewards C_star C_h t i, ∀ᵐ z' ∂K z.val,
      (z.val, z') ∈ pairedSourceFibreEvent p rate
        (sourceIncomingBoundary rate rewards C_star C_h t control0 i z) := by
  exact (Measure.ae_compProd_iff
    (μ := sourceStratumMeasure rate rewards C_star C_h t i)
    (κ := (K).comap Subtype.val measurable_subtype_coe)
    (measurableSet_sourceRetainedCertificate rate rewards C_star C_h t control0 i)).mp
      (ae_sourceStratumCoupling_retainedCertificate rate rewards C_star C_h t control0 i)

end RetainedBoundary

end Bandits.Support.ReferenceTotalSourceDisintegration

end
