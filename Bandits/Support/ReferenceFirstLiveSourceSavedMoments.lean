/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveRecordingSourceCylinder

/-!
# Original-source continuing first-live saved moments

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,246-264`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:376-408`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module integrates the current saved emission of one actually unoccupied
follower over the original continuing-source cylinder. Both source and
remainder measures are inherited unnormalized comaps. This does not identify
the authentic source history, restrict at the first overflow, or close a
manuscript conditional-law statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceContinuingRecordingPhysicalReward

namespace Bandits.Support.ReferenceFirstLiveSourceSavedMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)


local notation "X" => ReferenceFirstLiveRecordingReadoutMeasurability.SourceX rate rewards C_star C_h q t s hs control0
local notation "XPlus" => ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs control0
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t s hs control0
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "ctrlLaw" => ContinuousLearningRows.timeControlLaw p

variable (i : Fin (p.m - 1))

local notation "Xi" => ReferenceFirstLiveRecordingReadoutMeasurability.XFollower rate rewards C_star C_h q t s hs control0 i
local notation "ZPlus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t s hs control0
local notation "μCPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0
local notation "μZPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t s hs control0

/-- The exact original source stratum, restricted to this continuing and
actually unoccupied prepared follower. -/
@[expose] abbrev SourceFollower :=
  {z : Z // ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch rate rewards C_star C_h q t s hs
    control0 i (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z)}

local notation "Zi" => SourceFollower rate rewards C_star C_h q t s hs control0 i

/-- The inherited unnormalized remainder measure on the literal follower
subtype. -/
@[expose] def followerRemainderMeasure : Measure Xi :=
  Measure.comap Subtype.val
    (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0)

/-- The inherited unnormalized original-source measure on the literal source
follower subtype. -/
@[expose] def followerSourceMeasure : Measure Zi :=
  Measure.comap Subtype.val
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))

local notation "μCi" => followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i
local notation "μZi" => followerSourceMeasure rate rewards C_star C_h q t s hs control0 i

instance followerRemainderMeasure_finite : IsFiniteMeasure μCi := by
  unfold followerRemainderMeasure
  infer_instance

instance followerSourceMeasure_finite : IsFiniteMeasure μZi := by
  unfold followerSourceMeasure
  infer_instance

/-- The literal Borel event for the actual continuing and unoccupied prepared
follower. -/
@[expose] def followerBranchSet : Set X :=
  {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
    rate rewards C_star C_h q t s hs control0 i x}

@[expose] def followerBranchPlusSet : Set XPlus :=
  {x : XPlus | x.val ∈ followerBranchSet rate rewards C_star C_h q t s hs control0 i}

@[expose] def sourceFollowerBranchPlusSet : Set ZPlus :=
  {z : ZPlus | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0 z.val ∈
    followerBranchSet rate rewards C_star C_h q t s hs control0 i}

/-- The same focal event pulled back to the original source stratum. -/
private def sourceFollowerSet : Set Z :=
  {z : Z | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
    rate rewards C_star C_h q t s hs control0 i
    (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z)}

private def sourceContinuingSet : Set Z :=
  {z : Z | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
    rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z)}

local notation "Fset" => followerBranchSet rate rewards C_star C_h q t s hs control0 i
local notation "Fplus" => followerBranchPlusSet rate rewards C_star C_h q t s hs control0 i
local notation "FzPlus" => sourceFollowerBranchPlusSet rate rewards C_star C_h q t s hs control0 i

/-- The actual continuing-follower predicate is Borel on the original
remainder, including its actual prepared unoccupied-state test. -/
theorem measurableSet_followerBranch : MeasurableSet Fset :=
  ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingFollowerBranch
    rate rewards C_star C_h q t s hs control0 i

private theorem measurableSet_followerBranchPlus : MeasurableSet Fplus :=
  (measurableSet_followerBranch rate rewards C_star C_h q t s hs control0 i).preimage
    measurable_subtype_coe

private theorem measurableSet_followerBranchZPlus : MeasurableSet FzPlus :=
  (measurableSet_followerBranch rate rewards C_star C_h q t s hs control0 i).preimage
    ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained rate rewards C_star C_h q t s hs control0).comp
      measurable_subtype_coe)

private theorem measurableSet_sourceFollowerSet : MeasurableSet (sourceFollowerSet rate rewards C_star C_h q t s hs control0 i) :=
  (ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingFollowerBranch
    rate rewards C_star C_h q t s hs control0 i).preimage
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained rate rewards C_star C_h q t s hs control0)

private theorem measurableSet_sourceContinuingSet : MeasurableSet (sourceContinuingSet rate rewards C_star C_h q t s hs control0) :=
  (ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingBranch
    rate rewards C_star C_h q t s hs control0).preimage
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained rate rewards C_star C_h q t s hs control0)

/-- The literal selected payload on this follower fibre. -/
@[expose] def selectedBaselinePayload (x : Xi) :
    ReferenceActivePhysicalStep.Payload rate :=
  ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0)
    (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0) i x)

/-- The assigned arm is read from this same selected baseline payload. -/
@[expose] def assignedArm (x : Xi) : Fin p.K :=
  (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x).assignment.assigned
    (bufferFollowerIndex i)

/-- The recording rate varies with the actual selected payload and its anchor. -/
@[expose] def xi (x : Xi) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val
    (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x).anchor
    (assignedArm rate rewards C_star C_h q t s hs control0 i x)

/-- The current rounded reward on the actual assigned arm. -/
@[expose] def rho (x : Xi) : ℝ :=
  ((rewards t (assignedArm rate rewards C_star C_h q t s hs control0 i x)).val : ℝ) /
    (D p : ℝ)

/-- The exact quantized value associated with the varying actual rate and
assigned arm. -/
@[expose] def value (x : Xi) : ℝ :=
  QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
    (xi rate rewards C_star C_h q t s hs control0 i x)
    (rho rate rewards C_star C_h q t s hs control0 i x)

/-- A common lower recording-rate bound, independent of the retained source. -/
@[expose] def beta : ℝ := CanonicalRecordingRates.beta p rate.eta.val

/-- The actual current saved emission on the original whole control. Older
buffer entries, replacement random variables and rounded surrogates are not
included. -/
@[expose] def f (x : Xi) (u : TimeControl p) : ℝ :=
  ReferenceFirstLiveRecordingReadoutMeasurability.currentNormalizedSavedContribution
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0) i
    (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0) i x, u)

/-- Evaluate the same saved emission on the source's unmodified current
control. -/
@[expose] def sourceSaved (z : Zi) : ℝ :=
  f rate rewards C_star C_h q t s hs control0 i
    ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val, z.property⟩
    (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)

/-- The source readout is literally M's normalized current emission on the
original physical record, using the same selected actual baseline payload. -/
theorem sourceSaved_eq_originalCurrentRecord (z : Zi) :
    sourceSaved rate rewards C_star C_h q t s hs control0 i z =
      ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val)
        (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i
          ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val, z.property⟩) i := by
  change ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val)
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val))
      (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i
        ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val,
          z.property⟩) i = _
  rw [ReferenceFirstLiveRecordingSourceCylinder.sourceRecordAtControl_eq_original rate rewards C_star C_h q t s hs control0 z.val]

/-- The source follower subtype maps to the same literal follower remainder
and original whole control. -/
@[expose] def followerSourceSplit (z : Zi) : Xi × TimeControl p :=
  (⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val, z.property⟩,
    ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)

private def sourceFollowerToContinuing (z : Zi) : ZPlus := ⟨z.val, z.property.1⟩

private theorem measurable_sourceFollowerToContinuing :
    Measurable (sourceFollowerToContinuing rate rewards C_star C_h q t s hs control0 i) := by
  have hval : Measurable (fun z : Zi => (z.val : Z)) := by
    exact measurable_subtype_coe
  exact hval.subtype_mk

theorem measurable_followerSourceSplit :
    Measurable (followerSourceSplit rate rewards C_star C_h q t s hs control0 i) := by
  exact (((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained rate rewards C_star C_h q t s hs control0).comp
      measurable_subtype_coe).subtype_mk.prodMk
    ((ReferenceFirstLiveRecordingSourceCylinder.measurable_originalControl rate rewards C_star C_h q t s hs).comp
      measurable_subtype_coe))

/-- The nested source subtype is exactly the restriction of C's continuing
source subtype to the Borel focal follower branch. -/
private theorem followerSourceMeasure_map_to_continuing :
    (μZi).map (sourceFollowerToContinuing rate rewards C_star C_h q t s hs control0 i) =
      (μZPlus).restrict FzPlus := by
  let hbranch := ReferenceFirstLiveRecordingSourceCylinder.measurableSet_sourceBranch rate rewards C_star C_h q t s hs control0
  let hfocal := measurableSet_followerBranch rate rewards C_star C_h q t s hs control0 i
  have hsubset : sourceFollowerSet rate rewards C_star C_h q t s hs control0 i ⊆
      sourceContinuingSet rate rewards C_star C_h q t s hs control0 := by
    intro z hz
    exact hz.1
  have hval : MeasurableEmbedding (Subtype.val : ZPlus → Z) :=
    MeasurableEmbedding.subtype_coe hbranch
  have himage : (Subtype.val : ZPlus → Z) '' FzPlus =
      sourceFollowerSet rate rewards C_star C_h q t s hs control0 i := by
    ext z
    constructor
    · rintro ⟨zplus, hz, rfl⟩
      exact hz
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz, rfl⟩
  apply hval.map_injective
  rw [Measure.map_map hval.measurable
    (measurable_sourceFollowerToContinuing rate rewards C_star C_h q t s hs control0 i)]
  rw [show (Subtype.val : ZPlus → Z) ∘
      sourceFollowerToContinuing rate rewards C_star C_h q t s hs control0 i =
      (Subtype.val : Zi → Z) from rfl]
  rw [show (μZi).map (Subtype.val : Zi → Z) =
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)).restrict
        (sourceFollowerSet rate rewards C_star C_h q t s hs control0 i) from
    map_comap_subtype_coe
      (measurableSet_sourceFollowerSet rate rewards C_star C_h q t s hs control0 i)
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))]
  have hpre : (Subtype.val : ZPlus → Z) ⁻¹'
      ((Subtype.val : ZPlus → Z) '' FzPlus) = FzPlus :=
    hval.injective.preimage_image FzPlus
  rw [← hpre, ← hval.restrict_map μZPlus ((Subtype.val : ZPlus → Z) '' FzPlus)]
  rw [show (μZPlus).map (Subtype.val : ZPlus → Z) =
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)).restrict
      (sourceContinuingSet rate rewards C_star C_h q t s hs control0) from
        map_comap_subtype_coe
          (measurableSet_sourceContinuingSet rate rewards C_star C_h q t s hs control0)
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))]
  rw [himage, Measure.restrict_restrict_of_subset hsubset]

/-- The follower remainder inclusion is a measurable embedding into C's
continuing branch, with image given by the actual focal predicate. -/
private theorem measurableEmbedding_followerAsPlus :
    MeasurableEmbedding
      (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
        (s := s) (hs := hs) (control0 := control0) i) := by
  let E : Xi ≃ᵐ Fplus := {
    toEquiv := {
      toFun := fun x =>
        ⟨ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
          (s := s) (hs := hs) (control0 := control0) i x, x.property⟩
      invFun := fun y => ⟨y.val.val, y.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; cases y; rfl
    }
    measurable_toFun := by
      exact (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
        (s := s) (hs := hs) (control0 := control0) i).subtype_mk
    measurable_invFun := by
      exact (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  }
  have hF := measurableSet_followerBranchPlus rate rewards C_star C_h q t s hs control0 i
  change MeasurableEmbedding ((Subtype.val : Fplus → XPlus) ∘ E)
  exact (MeasurableEmbedding.subtype_coe hF).comp E.measurableEmbedding

/-- The corresponding inherited source product split on the exact follower
subtype. It is obtained by restricting C's accepted continuing split with
the Borel actual focal branch. -/
theorem followerSourceSplit_product :
    (μZi).map (followerSourceSplit rate rewards C_star C_h q t s hs control0 i) =
      (followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i).prod ctrlLaw := by
  let split := followerSourceSplit rate rewards C_star C_h q t s hs control0 i
  let focalIncl := ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0) i
  let forget : Xi × TimeControl p → XPlus × TimeControl p :=
    Prod.map focalIncl id
  have hforget : MeasurableEmbedding forget :=
    (measurableEmbedding_followerAsPlus rate rewards C_star C_h q t s hs control0 i).prodMap
      MeasurableEmbedding.id
  have hsource := followerSourceMeasure_map_to_continuing
    rate rewards C_star C_h q t s hs control0 i
  have hleft :
      ((μZi).map split).map forget =
        ((μZPlus).restrict FzPlus).map
          (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0) := by
    rw [Measure.map_map hforget.measurable (measurable_followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i)]
    rw [show forget ∘ split =
      ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0 ∘
        sourceFollowerToContinuing rate rewards C_star C_h q t s hs control0 i from rfl]
    rw [← Measure.map_map (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs
      control0) (measurable_sourceFollowerToContinuing rate rewards C_star C_h q t s hs
        control0 i), hsource]
  have hfocalProduct :
      {xu : XPlus × TimeControl p | xu.1 ∈ Fplus} = Fplus ×ˢ Set.univ := by
    ext xu
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
  have hleft' :
      ((μZPlus).restrict FzPlus).map
          (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0) =
        ((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0).prod ctrlLaw).restrict (Fplus ×ˢ Set.univ) := by
    rw [show FzPlus =
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0) ⁻¹'
        {xu : XPlus × TimeControl p | xu.1 ∈ Fplus} from by
          ext z
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_ofPred_eq,
            ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit, Set.mem_setOf_eq]
          rfl]
    rw [← Measure.restrict_map (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs
      control0) (show MeasurableSet {xu : XPlus × TimeControl p | xu.1 ∈ Fplus} from
        (measurableSet_followerBranchPlus rate rewards C_star C_h q t s hs control0 i).preimage
          measurable_fst)]
    rw [ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product rate rewards C_star C_h q t s hs control0, hfocalProduct]
  have hright :
      ((followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i).prod ctrlLaw).map forget =
        ((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0).prod ctrlLaw).restrict (Fplus ×ˢ Set.univ) := by
    rw [← Measure.map_prod_map (followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i) ctrlLaw
      (measurableEmbedding_followerAsPlus rate rewards C_star C_h q t s hs control0 i).measurable
      measurable_id, Measure.map_id]
    rw [show (μCi).map focalIncl = (μCPlus).restrict Fplus from by
      let hbranch := ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingBranch rate rewards C_star C_h q t s hs
        control0
      have hval : MeasurableEmbedding (Subtype.val : XPlus → X) :=
        MeasurableEmbedding.subtype_coe hbranch
      have himage : (Subtype.val : XPlus → X) '' Fplus = Fset := by
        ext x
        constructor
        · rintro ⟨xp, hf, rfl⟩
          exact hf
        · intro hf
          exact ⟨⟨x, hf.1⟩, hf, rfl⟩
      have hsubset : Fset ⊆
          {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
            rate rewards C_star C_h q t s hs control0 x} := by
        intro x hx
        exact hx.1
      apply hval.map_injective
      rw [Measure.map_map hval.measurable
        (measurableEmbedding_followerAsPlus rate rewards C_star C_h q t s hs control0 i).measurable]
      rw [show (Subtype.val : XPlus → X) ∘ focalIncl = (Subtype.val : Xi → X) from rfl]
      rw [show (μCi).map (Subtype.val : Xi → X) =
          (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict Fset from
        map_comap_subtype_coe (measurableSet_followerBranch rate rewards C_star C_h q t s hs
          control0 i) μC]
      have hpre : (Subtype.val : XPlus → X) ⁻¹'
          ((Subtype.val : XPlus → X) '' Fplus) = Fplus :=
        hval.injective.preimage_image Fplus
      rw [← hpre, ← hval.restrict_map μCPlus ((Subtype.val : XPlus → X) '' Fplus)]
      have hmapC :
          (ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0).map
              (Subtype.val : XPlus → X) =
            (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict
              {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
                rate rewards C_star C_h q t s hs control0 x} := by
        unfold ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
        exact map_comap_subtype_coe hbranch
          (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0)
      have hsubsetImage :
          (Subtype.val : XPlus → X) '' Fplus ⊆
            {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
              rate rewards C_star C_h q t s hs control0 x} := by
        rw [himage]
        exact hsubset
      have hrestrict :
          ((ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict
            {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
              rate rewards C_star C_h q t s hs control0 x}).restrict
              ((Subtype.val : XPlus → X) '' Fplus) =
          (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict
            ((Subtype.val : XPlus → X) '' Fplus) :=
        Measure.restrict_restrict_of_subset hsubsetImage
      rw [hmapC]
      calc
        (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict Fset =
            (ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict
              ((Subtype.val : XPlus → X) '' Fplus) := by rw [← himage]
        _ = ((ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs control0).restrict
              {x : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
                rate rewards C_star C_h q t s hs control0 x}).restrict
              ((Subtype.val : XPlus → X) '' Fplus) := hrestrict.symm]
    rw [Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
  apply hforget.map_injective
  rw [hleft, hleft', hright]

/-- At every point of the literal actual follower subtype, the actual-input
producer supplies M's continuing-recording hypotheses. The source readout is
then identified with the same candidate record and selected payload. -/
theorem actual_follower_saved_moments (x : Xi) :
    let z := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val.1
    let n := t.val - s
    let hspan : s + (n + 1) ≤ p.T := by
      have ht := t.isLt
      dsimp [n]
      omega
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
      (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts rate rewards C_star C_h q t s hs control0 x.val).1
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h
      (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts rate rewards C_star C_h q t s hs control0 x.val).1
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      have helapsedZ : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
        simpa [z] using
          (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts rate rewards C_star C_h q t s hs control0 x.val).2
      change ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
          (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts rate rewards C_star C_h q t s hs control0 x.val).1) s
      simpa only [helapsedZ] using seed.activeAtStart
    let candidate := ReferenceContinuingDataCandidateLogging.candidateInput initial z.1.2 q
      rewards s n hspan hmode
    ((0 < xi rate rewards C_star C_h q t s hs control0 i x ∧
      0 < beta rate ∧ beta rate ≤ xi rate rewards C_star C_h q t s hs control0 i x ∧
      0 ≤ rho rate rewards C_star C_h q t s hs control0 i x ∧
      rho rate rewards C_star C_h q t s hs control0 i x ≤ 1) ∧
      Measurable (f rate rewards C_star C_h q t s hs control0 i x) ∧
      Integrable (f rate rewards C_star C_h q t s hs control0 i x) ctrlLaw ∧
      Integrable (fun u => f rate rewards C_star C_h q t s hs control0 i x u ^ 2) ctrlLaw ∧
      (∫ u, f rate rewards C_star C_h q t s hs control0 i x u ∂ctrlLaw) =
        xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ∧
      (∫ u, f rate rewards C_star C_h q t s hs control0 i x u ^ 2 ∂ctrlLaw) =
        xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ^ 2 ∧
      rho rate rewards C_star C_h q t s hs control0 i x -
          xi rate rewards C_star C_h q t s hs control0 i x /
            (rate.eta.val * (D p : ℝ)) ≤
        ∫ u, f rate rewards C_star C_h q t s hs control0 i x u ∂ctrlLaw ∧
      (∫ u, f rate rewards C_star C_h q t s hs control0 i x u ∂ctrlLaw) ≤
        rho rate rewards C_star C_h q t s hs control0 i x ∧
      (∫ u, f rate rewards C_star C_h q t s hs control0 i x u ^ 2 ∂ctrlLaw) ≤
        rho rate rewards C_star C_h q t s hs control0 i x ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 i x ∧
      (∫ u, f rate rewards C_star C_h q t s hs control0 i x u ^ 2 ∂ctrlLaw) ≤
        1 / xi rate rewards C_star C_h q t s hs control0 i x ∧
      ∀ u, 0 ≤ f rate rewards C_star C_h q t s hs control0 i x u ∧
        f rate rewards C_star C_h q t s hs control0 i x u ≤ 1 / beta rate) := by
  classical
  intro z n hspan initial seed hmode candidate
  rcases x.property with ⟨hcontinuing, hcurrent⟩
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hpending, hcontrols, hdata, hfirst, hseed, hseedAccepted,
      hseedS, hseedDelta, hseedBacklog, hseedLastDown, hseedUnoccupied,
      hseedLocal, hseedValid, hseedPairwise, hseedTime, hseedDecoder, hmodeActual⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
      rate rewards C_star C_h q t s hs control0 x.val hcontinuing
  have htimeVal : candidate.time.val = t.val := by
    change s + n = t.val
    omega
  have htime : candidate.time = t := Fin.ext htimeVal
  have hinputEq :
      ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 x.val = candidate := by
    dsimp [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
      candidate, initial, z, n]
  have hcurrentUnoccupied : (states i).status = .unoccupied := by
    have hcurrentCandidate :
        match ((ReferenceActivePhysicalStep.prepare candidate).followers.followers i).configuration with
        | .ordinary state _ => state.status = .unoccupied
        | .dagger => False := by
      rw [← hinputEq]
      exact hcurrent
    rw [ho i] at hcurrentCandidate
    exact hcurrentCandidate
  let xp := ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0) i x
  have hpayload : selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x = r.payload := by
    exact ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_of_continuing
      xp r owned base d hsStart c arm (by
        change (ReferenceActivePhysicalStep.prepare candidate).coordinator = _
        exact hcoord)
  have hmoments :=
    ReferenceContinuingSavedIncrementMoments.actual_continuing_saved_increment_moments
      initial z.1.2 q rewards s n hspan hmode seed.followers seed.memory hfirst hseed
      hseedUnoccupied hseedValid hseedPairwise hseedTime r owned base d hsStart c arm
      hcoord states memories ho henabled i hcurrentUnoccupied
  rcases hmoments with ⟨hscalar, hmarker, hmeas, hInt, hSqInt, hFirst, hSecond,
      hLower, hUpper, hSqRho, hSqOne, hBounds⟩
  rcases hscalar with ⟨hxiM, hbetaM, hbetaLeM, hrho0M, hrho1M⟩
  let armM := r.payload.assignment.assigned (bufferFollowerIndex i)
  let xiM := CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor armM
  let betaM := CanonicalRecordingRates.beta p rate.eta.val
  let rhoM := ((rewards candidate.time armM).val : ℝ) / (D p : ℝ)
  let valueM := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xiM rhoM
  let g : TimeControl p → ℝ := fun u =>
    ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
      (ReferenceContinuingDataCandidateLogging.candidateRecord initial z.1.2 q rewards s n hspan hmode u)
      r.payload i
  have hxiEq : xi rate rewards C_star C_h q t s hs control0 i x = xiM := by
    change CanonicalRecordingRates.xi p rate.eta.val
      (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x).anchor
      (assignedArm rate rewards C_star C_h q t s hs control0 i x) = xiM
    unfold assignedArm
    rw [hpayload]
  have hbetaEq : beta rate = betaM := rfl
  have hrhoEq : rho rate rewards C_star C_h q t s hs control0 i x = rhoM := by
    change ((rewards t (assignedArm rate rewards C_star C_h q t s hs control0 i x)).val : ℝ) /
      (D p : ℝ) = rhoM
    unfold assignedArm
    rw [hpayload]
    unfold rhoM
    rw [htime]
  have hvalueEq : value rate rewards C_star C_h q t s hs control0 i x = valueM := by
    simp [value, hxiEq, hrhoEq, xiM, rhoM, valueM]
  have hfun : (fun u => f rate rewards C_star C_h q t s hs control0 i x u) = g := by
    funext u
    have hcandidateRecord :
        ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCandidateRecord x.val u =
          ReferenceContinuingDataCandidateLogging.candidateRecord initial z.1.2 q rewards s n hspan hmode u := by
      rfl
    change ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
          x.val u)
        (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x) i = _
    rw [ReferenceFirstLiveRecordingReadoutMeasurability.sourceNormalizedSavedContribution_eq_candidateRecord
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0) x.val u
      (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x) i]
    rw [hpayload]
    exact congrArg (fun record =>
      ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution record r.payload i)
      hcandidateRecord
  have hfunSq : (fun u => f rate rewards C_star C_h q t s hs control0 i x u ^ 2) =
      fun u => g u ^ 2 := by
    funext u
    exact congrArg (fun y : ℝ => y ^ 2) (congrFun hfun u)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hxiEq] using hxiM
  · simpa [hbetaEq] using hbetaM
  · simpa [hxiEq, hbetaEq] using hbetaLeM
  · simpa [hrhoEq] using hrho0M
  · simpa [hrhoEq] using hrho1M
  · simpa only [hfun] using hmeas
  · simpa only [hfun] using hInt
  · simpa only [hfunSq] using hSqInt
  · rw [hfun, hxiEq, hvalueEq]
    exact hFirst
  · rw [hfunSq, hxiEq, hvalueEq]
    exact hSecond
  · rw [hfun, hrhoEq, hxiEq]
    exact hLower
  · rw [hfun, hrhoEq]
    exact hUpper
  · rw [hfunSq, hrhoEq, hxiEq]
    exact hSqRho
  · rw [hfunSq, hxiEq]
    exact hSqOne
  · intro u
    simpa only [hfun, hbetaEq] using hBounds u

private theorem measurable_evalFin :
    Measurable (fun y : (Fin p.K → ℝ) × Fin p.K => y.1 y.2) := by
  classical
  have hterm (a : Fin p.K) :
      Measurable (fun y : (Fin p.K → ℝ) × Fin p.K => if y.2 = a then y.1 a else 0) := by
    apply Measurable.ite
    · exact (measurableSet_singleton a).preimage measurable_snd
    · exact (measurable_pi_apply a).comp measurable_fst
    · exact measurable_const
  have hsum : Measurable (fun y : (Fin p.K → ℝ) × Fin p.K =>
      ∑ a : Fin p.K, if y.2 = a then y.1 a else 0) :=
    Finset.measurable_fun_sum Finset.univ (fun a _ => hterm a)
  convert hsum using 1
  funext y
  simp

/-- The selected payload's actual canonical rate vector and actual assigned
arm give the varying rate on this follower fibre. -/
theorem measurable_xi :
    Measurable (xi rate rewards C_star C_h q t s hs control0 i) := by
  let xp := ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0) i
  let rv := fun x : Xi => AssignmentPayloadDerivedMeasurability.inputRate
    (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x)
  let arm := assignedArm rate rewards C_star C_h q t s hs control0 i
  have hrv : Measurable rv := by
    change Measurable (fun x : Xi =>
      AssignmentPayloadDerivedMeasurability.inputRate
        (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
          (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q)
            (t := t) (s := s) (hs := hs) (control0 := control0) i x)))
    exact (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselineInputRate
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0)).comp
      (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
        (s := s) (hs := hs) (control0 := control0) i)
  have harm : Measurable arm := by
    change Measurable (fun x : Xi =>
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselineAssignedArm
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q)
        (t := t) (s := s) (hs := hs) (control0 := control0) i
        (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q)
          (t := t) (s := s) (hs := hs) (control0 := control0) i x))
    exact (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselineAssignedArm
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0) i).comp
      (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
        (s := s) (hs := hs) (control0 := control0) i)
  have hxiEq : (xi rate rewards C_star C_h q t s hs control0 i) =
      fun x => rv x (arm x) := by
    funext x
    change CanonicalRecordingRates.xi p rate.eta.val
      (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x).anchor
      (assignedArm rate rewards C_star C_h q t s hs control0 i x) =
        AssignmentPayloadDerivedMeasurability.inputRate
          (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x)
          (assignedArm rate rewards C_star C_h q t s hs control0 i x)
    rw [AssignmentPayloadDerivedMeasurability.inputRate]
    exact (selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x).rate_eq_canonical _ |>.symm
  rw [hxiEq]
  exact measurable_evalFin.comp (hrv.prodMk harm)

/-- The whole-table rounded reward is evaluated at the same varying assigned
arm as the recording rate. -/
theorem measurable_rho :
    Measurable (rho rate rewards C_star C_h q t s hs control0 i) := by
  have harm := measurable_xi rate rewards C_star C_h q t s hs control0 i
  have harmArm : Measurable (assignedArm rate rewards C_star C_h q t s hs control0 i) := by
    change Measurable (fun x : Xi =>
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselineAssignedArm
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q)
        (t := t) (s := s) (hs := hs) (control0 := control0) i
        (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q)
          (t := t) (s := s) (hs := hs) (control0 := control0) i x))
    exact (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselineAssignedArm
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
      (s := s) (hs := hs) (control0 := control0) i).comp
      (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
        (s := s) (hs := hs) (control0 := control0) i)
  have hreward : Measurable (fun a : Fin p.K => ((rewards t a).val : ℝ)) :=
    measurable_of_countable _
  change Measurable (fun x : Xi => ((rewards t (assignedArm rate rewards C_star C_h q t s hs control0 i x)).val : ℝ) /
    (D p : ℝ))
  exact (hreward.comp harmArm).div_const (D p : ℝ)

/-- The literal floor and cast in the quantized value remain Borel as both
the selected rate and whole-table reward vary over the follower subtype. -/
theorem measurable_value :
    Measurable (value rate rewards C_star C_h q t s hs control0 i) := by
  have hxi := measurable_xi rate rewards C_star C_h q t s hs control0 i
  have hrho := measurable_rho rate rewards C_star C_h q t s hs control0 i
  have hscale : Measurable (fun x : Xi =>
      (D p : ℝ) * rate.eta.val * rho rate rewards C_star C_h q t s hs control0 i x) :=
    measurable_const.mul hrho
  have harg : Measurable (fun x : Xi =>
      ((D p : ℝ) * rate.eta.val * rho rate rewards C_star C_h q t s hs control0 i x) /
        xi rate rewards C_star C_h q t s hs control0 i x) :=
    hscale.div hxi
  have hfloor : Measurable (fun x : Xi => Nat.floor
      (((D p : ℝ) * rate.eta.val * rho rate rewards C_star C_h q t s hs control0 i x) /
        xi rate rewards C_star C_h q t s hs control0 i x)) := Nat.measurable_floor.comp harg
  have hcast : Measurable (fun x : Xi =>
      (Nat.floor (((D p : ℝ) * rate.eta.val *
        rho rate rewards C_star C_h q t s hs control0 i x) /
        xi rate rewards C_star C_h q t s hs control0 i x) : ℝ)) :=
    (measurable_of_countable _).comp hfloor
  change Measurable (fun x : Xi =>
    (Nat.floor (((D p : ℝ) * rate.eta.val *
      rho rate rewards C_star C_h q t s hs control0 i x) /
      xi rate rewards C_star C_h q t s hs control0 i x) : ℝ) /
      (rate.eta.val * (D p : ℝ)))
  exact hcast.div_const (rate.eta.val * (D p : ℝ))

/-- J's jointly Borel actual current saved emission on the literal follower
subtype; its square uses the same real-valued readout. -/
theorem measurable_followerSavedReadout :
    Measurable (fun z : Xi × TimeControl p => f rate rewards C_star C_h q t s hs control0 i z.1 z.2) := by
  change Measurable (fun z : Xi × TimeControl p =>
    ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) z.1.val z.2)
      (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
        (ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) i z.1)) i)
  exact ReferenceFirstLiveRecordingReadoutMeasurability.measurable_follower_current_saved_contribution
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) i

theorem measurable_followerSavedReadout_sq :
    Measurable (fun z : Xi × TimeControl p => (f rate rewards C_star C_h q t s hs control0 i z.1 z.2) ^ 2) :=
  (measurable_followerSavedReadout rate rewards C_star C_h q t s hs control0 i).pow_const 2

/-- The actual source readout and square are Borel on the literal inherited
source follower subtype. -/
theorem measurable_sourceSaved : Measurable (sourceSaved rate rewards C_star C_h q t s hs control0 i) := by
  have h := (measurable_followerSavedReadout rate rewards C_star C_h q t s hs control0 i).comp
    (measurable_followerSourceSplit rate rewards C_star C_h q t s hs control0 i)
  convert h using 1
  funext z
  rfl

theorem measurable_sourceSaved_sq :
    Measurable (fun z : Zi => sourceSaved rate rewards C_star C_h q t s hs control0 i z ^ 2) :=
  (measurable_sourceSaved rate rewards C_star C_h q t s hs control0 i).pow_const 2

private theorem follower_saved_pointwise_bounds (x : Xi) (u : TimeControl p) :
    0 ≤ f rate rewards C_star C_h q t s hs control0 i x u ∧
      f rate rewards C_star C_h q t s hs control0 i x u ≤ 1 / beta rate := by
  rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
    ⟨_, _, _, _, _, _, _, _, _, _, hbounds⟩
  exact hbounds u

/-- Uniform finite-measure integrability of the actual follower emission on
the inherited remainder/control product. -/
theorem followerProduct_saved_integrable :
    Integrable (fun z : Xi × TimeControl p => f rate rewards C_star C_h q t s hs control0 i z.1 z.2)
      ((followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i).prod ctrlLaw) := by
  have hbound : ∀ z : Xi × TimeControl p,
      ‖f rate rewards C_star C_h q t s hs control0 i z.1 z.2‖ ≤ 1 / beta rate := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i z.1 z.2).1]
    exact (follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i z.1 z.2).2
  exact Integrable.of_bound
    (measurable_followerSavedReadout rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable
    (1 / beta rate) (Filter.Eventually.of_forall hbound)

/-- Uniform finite-measure integrability of the square on the same inherited
remainder/control product. -/
theorem followerProduct_saved_sq_integrable :
    Integrable (fun z : Xi × TimeControl p =>
      (f rate rewards C_star C_h q t s hs control0 i z.1 z.2) ^ 2)
      ((followerRemainderMeasure rate rewards C_star C_h q t s hs control0 i).prod ctrlLaw) := by
  have hbound : ∀ z : Xi × TimeControl p,
      ‖(f rate rewards C_star C_h q t s hs control0 i z.1 z.2) ^ 2‖ ≤ (1 / beta rate) ^ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i z.1 z.2
    have hbeta : 0 ≤ 1 / beta rate := (div_pos (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
    nlinarith
  exact Integrable.of_bound
    (measurable_followerSavedReadout_sq rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable
    ((1 / beta rate) ^ 2) (Filter.Eventually.of_forall hbound)

/-- The source readout and its square are integrable under the exact inherited
source comap, by the same pointwise rate bound. -/
theorem followerSource_saved_integrable : Integrable
    (sourceSaved rate rewards C_star C_h q t s hs control0 i) μZi := by
  have hbound : ∀ z : Zi, ‖sourceSaved rate rewards C_star C_h q t s hs control0 i z‖ ≤ 1 / beta rate := by
    intro z
    change ‖f rate rewards C_star C_h q t s hs control0 i
      ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val,
        z.property⟩
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i _ _).1]
    exact (follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i _ _).2
  exact Integrable.of_bound (measurable_sourceSaved rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable
    (1 / beta rate) (Filter.Eventually.of_forall hbound)

theorem followerSource_saved_sq_integrable : Integrable
    (fun z : Zi => (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2) μZi := by
  have hbound : ∀ z : Zi,
      ‖(sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2‖ ≤ (1 / beta rate) ^ 2 := by
    intro z
    change ‖(f rate rewards C_star C_h q t s hs control0 i
      ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val,
        z.property⟩
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := follower_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i
      ⟨ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control0 z.val,
        z.property⟩
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z.val)
    have hbeta : 0 ≤ 1 / beta rate := (div_pos (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
    nlinarith
  exact Integrable.of_bound (measurable_sourceSaved_sq rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable
    ((1 / beta rate) ^ 2) (Filter.Eventually.of_forall hbound)

/-- The pointwise scalar envelope follows from the actual selected payload:
M supplies positivity and the rounding interval, while the canonical rate
constructor supplies its probability upper bound. -/
private theorem follower_scalar_envelope (x : Xi) :
    0 < xi rate rewards C_star C_h q t s hs control0 i x ∧
      beta rate ≤ xi rate rewards C_star C_h q t s hs control0 i x ∧
      0 ≤ rho rate rewards C_star C_h q t s hs control0 i x ∧
      rho rate rewards C_star C_h q t s hs control0 i x ≤ 1 ∧
      0 ≤ value rate rewards C_star C_h q t s hs control0 i x ∧
      value rate rewards C_star C_h q t s hs control0 i x ≤ 1 / beta rate ∧
      xi rate rewards C_star C_h q t s hs control0 i x ≤ 1 := by
  rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
    ⟨⟨hxi, hbeta, hbetaXi, hrho0, hrho1⟩, _, _, _, _, _, _, _, _, _, _⟩
  have hvalue0 := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
    (xi rate rewards C_star C_h q t s hs control0 i x)
    (rho rate rewards C_star C_h q t s hs control0 i x) rate.eta.property
  have hvalueLe := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 i x)
    (rho rate rewards C_star C_h q t s hs control0 i x) (beta rate)
    (D_pos p) rate.eta.property hxi ⟨hrho0, hrho1⟩
    (CanonicalRecordingRates.beta_pos p rate.eta.property) hbetaXi
  let payload := selectedBaselinePayload rate rewards C_star C_h q t s hs control0 i x
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap payload.anchor payload.anchor_pos
  have hrate : rates.rate (assignedArm rate rewards C_star C_h q t s hs control0 i x) =
      xi rate rewards C_star C_h q t s hs control0 i x := rfl
  refine ⟨hxi, hbetaXi, hrho0, hrho1, ?_, ?_, ?_⟩
  · simpa [value] using hvalue0
  · simpa [value, beta] using hvalueLe
  · rw [← hrate]
    exact rates.rate_le_one _

private theorem integrable_cell_xi_value :
    Integrable (fun x : Xi =>
      xi rate rewards C_star C_h q t s hs control0 i x *
        value rate rewards C_star C_h q t s hs control0 i x) μCi := by
  have hmeas := (measurable_xi rate rewards C_star C_h q t s hs control0 i).mul
    (measurable_value rate rewards C_star C_h q t s hs control0 i)
  have hbound : ∀ x : Xi, ‖xi rate rewards C_star C_h q t s hs control0 i x *
      value rate rewards C_star C_h q t s hs control0 i x‖ ≤ 1 / beta rate := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨hxi, _, _, _, hv0, hv1, hxi1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxi.le hv0)]
    calc
      xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ≤
        1 * value rate rewards C_star C_h q t s hs control0 i x :=
          mul_le_mul_of_nonneg_right hxi1 hv0
      _ = value rate rewards C_star C_h q t s hs control0 i x := one_mul _
      _ ≤ 1 / beta rate := hv1
  exact Integrable.of_bound hmeas.aestronglyMeasurable (1 / beta rate)
    (Filter.Eventually.of_forall hbound)

private theorem integrable_cell_xi_value_sq :
    Integrable (fun x : Xi =>
      xi rate rewards C_star C_h q t s hs control0 i x *
        (value rate rewards C_star C_h q t s hs control0 i x) ^ 2) μCi := by
  have hmeas := (measurable_xi rate rewards C_star C_h q t s hs control0 i).mul
    ((measurable_value rate rewards C_star C_h q t s hs control0 i).pow_const 2)
  have hbound : ∀ x : Xi, ‖xi rate rewards C_star C_h q t s hs control0 i x *
      (value rate rewards C_star C_h q t s hs control0 i x) ^ 2‖ ≤ (1 / beta rate) ^ 2 := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨hxi, _, _, _, hv0, hv1, hxi1⟩
    have hbeta0 : 0 ≤ 1 / beta rate := (div_pos (by norm_num)
      (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxi.le (sq_nonneg _))]
    calc
      xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ≤
        1 * (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 :=
          mul_le_mul_of_nonneg_right hxi1 (sq_nonneg _)
      _ = (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 := one_mul _
      _ ≤ (1 / beta rate) ^ 2 := by nlinarith
  exact Integrable.of_bound hmeas.aestronglyMeasurable ((1 / beta rate) ^ 2)
    (Filter.Eventually.of_forall hbound)

private theorem integrable_cell_rho :
    Integrable (rho rate rewards C_star C_h q t s hs control0 i) μCi := by
  have hbound : ∀ x : Xi,
      ‖rho rate rewards C_star C_h q t s hs control0 i x‖ ≤ 1 := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨_, _, hrho0, hrho1, _, _, _⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hrho0]
    exact hrho1
  exact Integrable.of_bound
    (measurable_rho rate rewards C_star C_h q t s hs control0 i).aestronglyMeasurable
    1 (Filter.Eventually.of_forall hbound)

private theorem integrable_cell_rho_rounding_lower :
    Integrable (fun x : Xi => rho rate rewards C_star C_h q t s hs control0 i x -
      xi rate rewards C_star C_h q t s hs control0 i x /
        (rate.eta.val * (D p : ℝ))) μCi := by
  have hmeas := (measurable_rho rate rewards C_star C_h q t s hs control0 i).sub
    ((measurable_xi rate rewards C_star C_h q t s hs control0 i).div_const
      (rate.eta.val * (D p : ℝ)))
  have hc : 0 < rate.eta.val * (D p : ℝ) := mul_pos rate.eta.property (by exact_mod_cast D_pos p)
  have hbound : ∀ x : Xi,
      ‖rho rate rewards C_star C_h q t s hs control0 i x -
        xi rate rewards C_star C_h q t s hs control0 i x /
          (rate.eta.val * (D p : ℝ))‖ ≤ 1 + 1 / (rate.eta.val * (D p : ℝ)) := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨_, _, hrho0, hrho1, _, _, hxi1⟩
    have hfrac0 : 0 ≤ xi rate rewards C_star C_h q t s hs control0 i x /
        (rate.eta.val * (D p : ℝ)) := div_nonneg (le_of_lt
          (follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x).1) hc.le
    have hfrac1 : xi rate rewards C_star C_h q t s hs control0 i x /
        (rate.eta.val * (D p : ℝ)) ≤ 1 / (rate.eta.val * (D p : ℝ)) :=
      div_le_div_of_nonneg_right hxi1 hc.le
    rw [Real.norm_eq_abs]
    apply (abs_le).2
    constructor <;> nlinarith
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 + 1 / (rate.eta.val * (D p : ℝ))) (Filter.Eventually.of_forall hbound)

private theorem integrable_cell_rho_sq_div_xi :
    Integrable (fun x : Xi => (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
      xi rate rewards C_star C_h q t s hs control0 i x) μCi := by
  have hmeas := (measurable_rho rate rewards C_star C_h q t s hs control0 i).pow_const 2 |>.div
    (measurable_xi rate rewards C_star C_h q t s hs control0 i)
  have hbound : ∀ x : Xi,
      ‖(rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
        xi rate rewards C_star C_h q t s hs control0 i x‖ ≤ 1 / beta rate := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨hxi, hbetaXi, hrho0, hrho1, _, _, _⟩
    have hbeta : 0 < beta rate := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hrhoSq : (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 ≤ 1 := by
      nlinarith
    have hdiv : (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
        xi rate rewards C_star C_h q t s hs control0 i x ≤ 1 / beta rate := by
      calc
        _ ≤ 1 / xi rate rewards C_star C_h q t s hs control0 i x :=
          div_le_div_of_nonneg_right hrhoSq hxi.le
        _ ≤ 1 / beta rate := one_div_le_one_div_of_le hbeta hbetaXi
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hxi.le)]
    exact hdiv
  exact Integrable.of_bound hmeas.aestronglyMeasurable (1 / beta rate)
    (Filter.Eventually.of_forall hbound)

private theorem integrable_cell_inv_xi :
    Integrable (fun x : Xi => 1 / xi rate rewards C_star C_h q t s hs control0 i x) μCi := by
  have hmeas : Measurable (fun x : Xi =>
      (1 : ℝ) / xi rate rewards C_star C_h q t s hs control0 i x) :=
    measurable_const.div (measurable_xi rate rewards C_star C_h q t s hs control0 i)
  have hbound : ∀ x : Xi,
      ‖1 / xi rate rewards C_star C_h q t s hs control0 i x‖ ≤ 1 / beta rate := by
    intro x
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨hxi, hbetaXi, _, _, _, _, _⟩
    have hbeta : 0 < beta rate := CanonicalRecordingRates.beta_pos p rate.eta.property
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) hxi.le)]
    exact one_div_le_one_div_of_le hbeta hbetaXi
  exact Integrable.of_bound hmeas.aestronglyMeasurable (1 / beta rate)
    (Filter.Eventually.of_forall hbound)

/-- Exact first-moment transfer on every measurable remainder cell. The source
integral uses the original source subtype and the RHS uses its inherited
unnormalized remainder comap. -/
theorem sourceSaved_firstMoment_cell_integral (Aset : Set X) (hA : MeasurableSet Aset) :
    (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
      sourceSaved rate rewards C_star C_h q t s hs control0 i z ∂μZi) =
      ∫ x in {x : Xi | x.val ∈ Aset},
        xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ∂μCi := by
  classical
  let split := followerSourceSplit rate rewards C_star C_h q t s hs control0 i
  let sourceCell : Set Zi := {z | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
    rate rewards C_star C_h q t s hs control0 z.val ∈ Aset}
  let cell : Set Xi := {x | x.val ∈ Aset}
  let H : Xi × TimeControl p → ℝ :=
    (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
    (fun y => f rate rewards C_star C_h q t s hs control0 i y.1 y.2)
  have hsourceCell : MeasurableSet sourceCell := hA.preimage
    ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained
      rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe)
  have hcell : MeasurableSet cell := hA.preimage measurable_subtype_coe
  have hcellProd : MeasurableSet (cell ×ˢ (Set.univ : Set (TimeControl p))) :=
    hcell.prod MeasurableSet.univ
  have hH : Measurable H :=
    (measurable_followerSavedReadout rate rewards C_star C_h q t s hs control0 i).indicator hcellProd
  have hHint : Integrable H (Measure.prod μCi ctrlLaw) := by
    dsimp [H]
    exact (followerProduct_saved_integrable rate rewards C_star C_h q t s hs control0 i).indicator hcellProd
  have hcellPreimage (z : Zi) :
      split z ∈ cell ×ˢ (Set.univ : Set (TimeControl p)) ↔ z ∈ sourceCell := by
    change ((split z).1.val ∈ Aset ∧ (split z).2 ∈ Set.univ) ↔
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset
    simp [split, followerSourceSplit]
  have hsourceIndicator : sourceCell.indicator
      (sourceSaved rate rewards C_star C_h q t s hs control0 i) = H ∘ split := by
    funext z
    by_cases hz : z ∈ sourceCell
    · have hmem : split z ∈ cell ×ˢ (Set.univ : Set (TimeControl p)) :=
        (hcellPreimage z).2 hz
      change sourceCell.indicator
          (sourceSaved rate rewards C_star C_h q t s hs control0 i) z =
        (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
          (fun y => f rate rewards C_star C_h q t s hs control0 i y.1 y.2) (split z)
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hmem]
      rfl
    · have hmem : split z ∉ cell ×ˢ (Set.univ : Set (TimeControl p)) :=
        fun h => hz ((hcellPreimage z).1 h)
      change sourceCell.indicator
          (sourceSaved rate rewards C_star C_h q t s hs control0 i) z =
        (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
          (fun y => f rate rewards C_star C_h q t s hs control0 i y.1 y.2) (split z)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hmem]
  have hsplit := measurable_followerSourceSplit rate rewards C_star C_h q t s hs control0 i
  have hfiber : ∀ x : Xi,
      (∫ u, H (x, u) ∂ctrlLaw) =
        cell.indicator (fun x => xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x) x := by
    intro x
    by_cases hx : x ∈ cell
    · have hfun : (fun u => H (x, u)) =
        (fun u => f rate rewards C_star C_h q t s hs control0 i x u) := by
        funext u
        simp [H, hx]
      rw [hfun]
      rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
        ⟨_, _, _, _, hfirst, _, _, _, _, _, _⟩
      simpa [Set.indicator_of_mem hx] using hfirst
    · have hfun : (fun u => H (x, u)) = fun _ => (0 : ℝ) := by
        funext u
        simp [H, hx]
      rw [hfun]
      rw [Set.indicator_of_notMem hx]
      simp
  calc
    _ = ∫ z, sourceCell.indicator
        (sourceSaved rate rewards C_star C_h q t s hs control0 i) z ∂μZi := by
      rw [← integral_indicator hsourceCell]
    _ = ∫ z, H (split z) ∂μZi := by
      rw [hsourceIndicator]
      simp only [Function.comp_apply]
    _ = ∫ y, H y ∂(Measure.map split μZi) :=
      (MeasureTheory.integral_map hsplit.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ y, H y ∂(Measure.prod μCi ctrlLaw) := by
      rw [followerSourceSplit_product rate rewards C_star C_h q t s hs control0 i]
    _ = ∫ x, ∫ u, H (x, u) ∂ctrlLaw ∂μCi := integral_prod H hHint
    _ = ∫ x, cell.indicator (fun x =>
        xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x) x ∂μCi := by
      congr 1
      funext x
      exact hfiber x
    _ = ∫ x in cell, xi rate rewards C_star C_h q t s hs control0 i x *
        value rate rewards C_star C_h q t s hs control0 i x ∂μCi := by
      rw [integral_indicator hcell]

/-- Exact square-moment transfer on the same arbitrary measurable cell. -/
theorem sourceSaved_secondMoment_cell_integral (Aset : Set X) (hA : MeasurableSet Aset) :
    (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
      (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2 ∂μZi) =
      ∫ x in {x : Xi | x.val ∈ Aset},
        xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ∂μCi := by
  classical
  let split := followerSourceSplit rate rewards C_star C_h q t s hs control0 i
  let sourceCell : Set Zi := {z | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
    rate rewards C_star C_h q t s hs control0 z.val ∈ Aset}
  let cell : Set Xi := {x | x.val ∈ Aset}
  let H : Xi × TimeControl p → ℝ :=
    (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
    (fun y => (f rate rewards C_star C_h q t s hs control0 i y.1 y.2) ^ 2)
  have hsourceCell : MeasurableSet sourceCell := hA.preimage
    ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRetained
      rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe)
  have hcell : MeasurableSet cell := hA.preimage measurable_subtype_coe
  have hcellProd : MeasurableSet (cell ×ˢ (Set.univ : Set (TimeControl p))) :=
    hcell.prod MeasurableSet.univ
  have hH : Measurable H :=
    (measurable_followerSavedReadout_sq rate rewards C_star C_h q t s hs control0 i).indicator hcellProd
  have hHint : Integrable H (Measure.prod μCi ctrlLaw) := by
    dsimp [H]
    exact (followerProduct_saved_sq_integrable rate rewards C_star C_h q t s hs control0 i).indicator hcellProd
  have hcellPreimage (z : Zi) :
      split z ∈ cell ×ˢ (Set.univ : Set (TimeControl p)) ↔ z ∈ sourceCell := by
    change ((split z).1.val ∈ Aset ∧ (split z).2 ∈ Set.univ) ↔
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset
    simp [split, followerSourceSplit]
  have hsourceIndicator : sourceCell.indicator
      (fun z => (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2) = H ∘ split := by
    funext z
    by_cases hz : z ∈ sourceCell
    · have hmem : split z ∈ cell ×ˢ (Set.univ : Set (TimeControl p)) :=
        (hcellPreimage z).2 hz
      change sourceCell.indicator
          (fun z => (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2) z =
        (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
          (fun y => (f rate rewards C_star C_h q t s hs control0 i y.1 y.2) ^ 2) (split z)
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hmem]
      rfl
    · have hmem : split z ∉ cell ×ˢ (Set.univ : Set (TimeControl p)) :=
        fun h => hz ((hcellPreimage z).1 h)
      change sourceCell.indicator
          (fun z => (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2) z =
        (cell ×ˢ (Set.univ : Set (TimeControl p))).indicator
          (fun y => (f rate rewards C_star C_h q t s hs control0 i y.1 y.2) ^ 2) (split z)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hmem]
  have hsplit := measurable_followerSourceSplit rate rewards C_star C_h q t s hs control0 i
  have hfiber : ∀ x : Xi,
      (∫ u, H (x, u) ∂ctrlLaw) =
        cell.indicator (fun x => xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2) x := by
    intro x
    by_cases hx : x ∈ cell
    · have hfun : (fun u => H (x, u)) =
        (fun u => (f rate rewards C_star C_h q t s hs control0 i x u) ^ 2) := by
        funext u
        simp [H, hx]
      rw [hfun]
      rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
        ⟨_, _, _, _, _, hsecond, _, _, _, _, _⟩
      simpa [Set.indicator_of_mem hx] using hsecond
    · have hfun : (fun u => H (x, u)) = fun _ => (0 : ℝ) := by
        funext u
        simp [H, hx]
      rw [hfun]
      rw [Set.indicator_of_notMem hx]
      simp
  calc
    _ = ∫ z, sourceCell.indicator
        (fun z => (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2) z ∂μZi := by
      rw [← integral_indicator hsourceCell]
    _ = ∫ z, H (split z) ∂μZi := by
      rw [hsourceIndicator]
      simp only [Function.comp_apply]
    _ = ∫ y, H y ∂(Measure.map split μZi) :=
      (MeasureTheory.integral_map hsplit.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ y, H y ∂(Measure.prod μCi ctrlLaw) := by
      rw [followerSourceSplit_product rate rewards C_star C_h q t s hs control0 i]
    _ = ∫ x, ∫ u, H (x, u) ∂ctrlLaw ∂μCi := integral_prod H hHint
    _ = ∫ x, cell.indicator (fun x =>
        xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2) x ∂μCi := by
      congr 1
      funext x
      exact hfiber x
    _ = ∫ x in cell, xi rate rewards C_star C_h q t s hs control0 i x *
        (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ∂μCi := by
      rw [integral_indicator hcell]

/-- The integrated source bounds hold on the same original source/remainder
cells as the exact first and square identities. -/
theorem sourceSaved_integrated_cell_bounds (Aset : Set X) (hA : MeasurableSet Aset) :
    (∫ x in {x : Xi | x.val ∈ Aset},
      rho rate rewards C_star C_h q t s hs control0 i x -
        xi rate rewards C_star C_h q t s hs control0 i x /
          (rate.eta.val * (D p : ℝ)) ∂μCi) ≤
        (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
          sourceSaved rate rewards C_star C_h q t s hs control0 i z ∂μZi) ∧
    (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
      sourceSaved rate rewards C_star C_h q t s hs control0 i z ∂μZi) ≤
        (∫ x in {x : Xi | x.val ∈ Aset},
          rho rate rewards C_star C_h q t s hs control0 i x ∂μCi) ∧
    (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
      (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2 ∂μZi) ≤
        (∫ x in {x : Xi | x.val ∈ Aset},
          (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
            xi rate rewards C_star C_h q t s hs control0 i x ∂μCi) ∧
    (∫ x in {x : Xi | x.val ∈ Aset},
      (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
        xi rate rewards C_star C_h q t s hs control0 i x ∂μCi) ≤
      (∫ x in {x : Xi | x.val ∈ Aset},
        1 / xi rate rewards C_star C_h q t s hs control0 i x ∂μCi) := by
  let cell : Set Xi := {x | x.val ∈ Aset}
  have hcell : MeasurableSet cell := hA.preimage measurable_subtype_coe
  have hfirstLower (x : Xi) :
      rho rate rewards C_star C_h q t s hs control0 i x -
          xi rate rewards C_star C_h q t s hs control0 i x /
            (rate.eta.val * (D p : ℝ)) ≤
        xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x := by
    rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
      ⟨_, _, _, _, hfirst, _, hlower, _, _, _, _⟩
    exact hlower.trans_eq hfirst
  have hfirstUpper (x : Xi) :
      xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ≤
        rho rate rewards C_star C_h q t s hs control0 i x := by
    rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
      ⟨_, _, _, _, hfirst, _, _, hupper, _, _, _⟩
    rw [← hfirst]
    exact hupper
  have hsecondUpper (x : Xi) :
      xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ≤
        (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 i x := by
    rcases actual_follower_saved_moments rate rewards C_star C_h q t s hs control0 i x with
      ⟨_, _, _, _, _, hsecond, _, _, hupper, _, _⟩
    rw [← hsecond]
    exact hupper
  have hrhoSqUpper (x : Xi) :
      (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 i x ≤
        1 / xi rate rewards C_star C_h q t s hs control0 i x := by
    rcases follower_scalar_envelope rate rewards C_star C_h q t s hs control0 i x with
      ⟨hxi, _, hrho0, hrho1, _, _, _⟩
    have hrhoSq : (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 ≤ 1 := by
      nlinarith
    exact div_le_div_of_nonneg_right hrhoSq hxi.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∫ x in cell, xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ∂μCi :=
        setIntegral_mono_on (integrable_cell_rho_rounding_lower rate rewards C_star C_h q t s hs control0 i).integrableOn
          (integrable_cell_xi_value rate rewards C_star C_h q t s hs control0 i).integrableOn
          hcell (fun x _ => hfirstLower x)
      _ = ∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
          sourceSaved rate rewards C_star C_h q t s hs control0 i z ∂μZi :=
        (sourceSaved_firstMoment_cell_integral rate rewards C_star C_h q t s hs control0 i Aset hA).symm
  · calc
      (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
          sourceSaved rate rewards C_star C_h q t s hs control0 i z ∂μZi) =
        ∫ x in cell, xi rate rewards C_star C_h q t s hs control0 i x *
          value rate rewards C_star C_h q t s hs control0 i x ∂μCi :=
        sourceSaved_firstMoment_cell_integral rate rewards C_star C_h q t s hs control0 i Aset hA
      _ ≤ ∫ x in cell, rho rate rewards C_star C_h q t s hs control0 i x ∂μCi :=
        setIntegral_mono_on (integrable_cell_xi_value rate rewards C_star C_h q t s hs control0 i).integrableOn
          (integrable_cell_rho rate rewards C_star C_h q t s hs control0 i).integrableOn
          hcell (fun x _ => hfirstUpper x)
  · calc
      (∫ z in {z : Zi | ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val ∈ Aset},
          (sourceSaved rate rewards C_star C_h q t s hs control0 i z) ^ 2 ∂μZi) =
        ∫ x in cell, xi rate rewards C_star C_h q t s hs control0 i x *
          (value rate rewards C_star C_h q t s hs control0 i x) ^ 2 ∂μCi :=
        sourceSaved_secondMoment_cell_integral rate rewards C_star C_h q t s hs control0 i Aset hA
      _ ≤ ∫ x in cell, (rho rate rewards C_star C_h q t s hs control0 i x) ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 i x ∂μCi :=
        setIntegral_mono_on (integrable_cell_xi_value_sq rate rewards C_star C_h q t s hs control0 i).integrableOn
          (integrable_cell_rho_sq_div_xi rate rewards C_star C_h q t s hs control0 i).integrableOn
          hcell (fun x _ => hsecondUpper x)
  · exact setIntegral_mono_on
      (integrable_cell_rho_sq_div_xi rate rewards C_star C_h q t s hs control0 i).integrableOn
      (integrable_cell_inv_xi rate rewards C_star C_h q t s hs control0 i).integrableOn
      hcell (fun x _ => hrhoSqUpper x)

/-- At `s=t`, the accepted continuing branch and this focal follower subtype
are empty; the inherited unnormalized measures are therefore zero. -/
theorem follower_measures_eq_zero_of_s_eq_t (hfirst : s = t.val) :
    μCi = 0 ∧ μZi = 0 := by
  have hempty := ReferenceFirstLiveRecordingBranchMeasurability.continuingRecordingBranch_eq_empty_of_offset_eq_zero
    rate rewards C_star C_h q t s hs control0 (by omega)
  let : IsEmpty Xi := ⟨fun x => by
    have hx' : (x.val : X) ∈ {y : X | ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
        rate rewards C_star C_h q t s hs control0 y} := x.property.1
    rw [hempty] at hx'
    simpa using hx'⟩
  let : IsEmpty Zi := ⟨fun z => isEmptyElim
    ((followerSourceSplit rate rewards C_star C_h q t s hs control0 i z).1)⟩
  exact ⟨Measure.eq_zero_of_isEmpty μCi, Measure.eq_zero_of_isEmpty μZi⟩

end Bandits.Support.ReferenceFirstLiveSourceSavedMoments

end
