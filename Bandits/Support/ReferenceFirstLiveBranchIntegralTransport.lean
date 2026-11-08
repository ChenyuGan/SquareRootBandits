/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue

import Mathlib.Tactic

/-!
# Original-source transport for one continuing first-live branch

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

This module pushes the inherited, unnormalized continuing first-live source
measure back to its literal original-source event. It then identifies the
actual numerical queue readouts and the accepted weighted and exponential
steps on that same event. The carrier keeps the existing nonempty-pending
continuing branch; birth and empty-pending rounds are outside this transport.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveBranchIntegralTransport

abbrev Parameters := ReferenceFirstLiveConditionalWeightedDrift.Parameters
abbrev RateInput := ReferenceFirstLiveConditionalWeightedDrift.RateInput
abbrev RewardTable := ReferenceFirstLiveConditionalWeightedDrift.RewardTable
abbrev TimeControl := ReferenceFirstLiveConditionalWeightedDrift.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "i0" => ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t i0
local notation "muZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t i0
local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rate rewards C_star C_h q t s hs control0
local notation "B" => ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
  rate rewards C_star C_h q t s hs control0
def continuingSourceBranchSet : Set Z := {z : Z | B (ret z)}
local notation "BZ" => continuingSourceBranchSet rate rewards C_star C_h q t s hs control0
local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "n" => t.val - s
local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate
local notation "G" => ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
  rate rewards C_star C_h q t s hs control0

include control0 in
private theorem measurableSet_sourceStratum : MeasurableSet
    (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0) :=
  ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i0

include control0 in
private theorem measurableSet_continuingBranch : MeasurableSet BZ :=
  ReferenceFirstLiveRecordingSourceCylinder.measurableSet_sourceBranch
    rate rewards C_star C_h q t s hs control0

private theorem branchSubtype_map :
    (muPlus).map (Subtype.val : Zplus → Z) = (muZ).restrict BZ := by
  change Measure.map (Subtype.val : Zplus → Z)
      (Measure.comap (Subtype.val : Zplus → Z) muZ) = Measure.restrict muZ BZ
  exact map_comap_subtype_coe
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0) muZ

include control0 in
private theorem sourceStratumMeasure_map :
    (muZ).map (Subtype.val : Z → S) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0) :=
  ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
    rate rewards C_star C_h t control0 i0

/- The stratum witness is the actual source event. Unfolding it fixes the
original selected J, crossing, and elapsed start; no resampling occurs here. -/
theorem sourceStratum_mem_iff (omega : S) :
    omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
        rate rewards C_star C_h t i0 ↔
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega = q ∧
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).completed = s := by
  rfl

def originalBranchEvent : Set S := Subtype.val '' BZ

def forgetBranch (z : Zplus) : S := z.val.val

theorem mem_originalBranchEvent_iff (omega : S) :
    omega ∈ originalBranchEvent rate rewards C_star C_h q t s hs control0 ↔
      ∃ hE : omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
          rate rewards C_star C_h t i0,
        B (ret (⟨omega, hE⟩ : Z)) := by
  constructor
  · rintro ⟨z, hz, hω⟩
    subst omega
    refine ⟨z.property, ?_⟩
    change B (ret z) at hz
    exact hz
  · rintro ⟨hE, hB⟩
    exact ⟨⟨omega, hE⟩, hB, rfl⟩

theorem measurableSet_originalBranchEvent :
    MeasurableSet (originalBranchEvent rate rewards C_star C_h q t s hs control0) := by
  change MeasurableSet (Subtype.val '' BZ)
  exact (MeasurableEmbedding.subtype_coe (measurableSet_sourceStratum
    rate rewards C_star C_h q t s hs control0)).measurableSet_image.mpr
      (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0)

theorem measurableEmbedding_forgetBranch :
    MeasurableEmbedding
      (forgetBranch rate rewards C_star C_h q t s hs control0) := by
  exact (MeasurableEmbedding.subtype_coe
      (measurableSet_sourceStratum rate rewards C_star C_h q t s hs control0)).comp
    (MeasurableEmbedding.subtype_coe
      (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0))

theorem branchSourceMeasure_map_original :
    (muPlus).map (forgetBranch rate rewards C_star C_h q t s hs control0) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (originalBranchEvent rate rewards C_star C_h q t s hs control0) := by
  let hOuter := MeasurableEmbedding.subtype_coe
    (measurableSet_sourceStratum rate rewards C_star C_h q t s hs control0)
  let hInner := MeasurableEmbedding.subtype_coe
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0)
  have hPre : (Subtype.val : Z → S) ⁻¹'
      originalBranchEvent rate rewards C_star C_h q t s hs control0 = BZ := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨y, hy, hEq⟩
      have hzy : y = z := Subtype.ext hEq
      simpa [hzy] using hy
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hImage :
      (Subtype.val : Z → S) '' BZ =
        originalBranchEvent rate rewards C_star C_h q t s hs control0 := rfl
  have hSubset :
      originalBranchEvent rate rewards C_star C_h q t s hs control0 ⊆
        ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0 := by
    rintro omega ⟨z, hz, rfl⟩
    exact z.property
  calc
    (muPlus).map (forgetBranch rate rewards C_star C_h q t s hs control0) =
        ((muPlus).map (Subtype.val : Zplus → Z)).map (Subtype.val : Z → S) := by
      change (muPlus).map (Subtype.val ∘ Subtype.val) =
        ((muPlus).map (Subtype.val : Zplus → Z)).map (Subtype.val : Z → S)
      exact (Measure.map_map hOuter.measurable hInner.measurable).symm
    _ = ((muZ).restrict BZ).map (Subtype.val : Z → S) := by
      rw [branchSubtype_map rate rewards C_star C_h q t s hs control0]
    _ = ((muZ).map (Subtype.val : Z → S)).restrict
        (originalBranchEvent rate rewards C_star C_h q t s hs control0) := by
      have hOuterRestrict := hOuter.restrict_map muZ
        (originalBranchEvent rate rewards C_star C_h q t s hs control0)
      rw [hPre] at hOuterRestrict
      exact hOuterRestrict.symm
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0)).restrict
        (originalBranchEvent rate rewards C_star C_h q t s hs control0) := by
      rw [sourceStratumMeasure_map rate rewards C_star C_h q t s hs control0]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (originalBranchEvent rate rewards C_star C_h q t s hs control0) :=
      Measure.restrict_restrict_of_subset hSubset

theorem branchSourceMeasure_mass_original :
    muPlus Set.univ =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (originalBranchEvent rate rewards C_star C_h q t s hs control0) := by
  calc
    muPlus Set.univ =
        ((muPlus).map (forgetBranch rate rewards C_star C_h q t s hs control0)) Set.univ := by
      rw [Measure.map_apply
        (measurableEmbedding_forgetBranch rate rewards C_star C_h q t s hs control0).measurable
        MeasurableSet.univ]
      simp
    _ = _ := by
      rw [branchSourceMeasure_map_original rate rewards C_star C_h q t s hs control0]
      simp [Measure.restrict_apply]

theorem integral_originalBranch (f : S → ℝ) :
    (∫ z : Zplus, f (z.val.val) ∂muPlus) =
      ∫ omega in originalBranchEvent rate rewards C_star C_h q t s hs control0,
        f omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let h := measurableEmbedding_forgetBranch rate rewards C_star C_h q t s hs control0
  calc
    (∫ z : Zplus, f (forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus) =
        ∫ omega, f omega ∂((muPlus).map
          (forgetBranch rate rewards C_star C_h q t s hs control0)) := (h.integral_map f).symm
    _ = _ := by
      rw [branchSourceMeasure_map_original rate rewards C_star C_h q t s hs control0]

theorem lintegral_originalBranch (f : S → ℝ≥0∞) :
    (∫⁻ z : Zplus, f (z.val.val) ∂muPlus) =
      ∫⁻ omega in originalBranchEvent rate rewards C_star C_h q t s hs control0,
        f omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let h := measurableEmbedding_forgetBranch rate rewards C_star C_h q t s hs control0
  calc
    (∫⁻ z : Zplus, f (forgetBranch rate rewards C_star C_h q t s hs control0 z) ∂muPlus) =
        ∫⁻ omega, f omega ∂((muPlus).map
          (forgetBranch rate rewards C_star C_h q t s hs control0)) := (h.lintegral_map f).symm
    _ = _ := by
      rw [branchSourceMeasure_map_original rate rewards C_star C_h q t s hs control0]

theorem integrableOn_originalBranch_iff (f : S → ℝ) :
    IntegrableOn f (originalBranchEvent rate rewards C_star C_h q t s hs control0)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) ↔
      Integrable (fun z : Zplus => f (z.val.val)) muPlus := by
  change Integrable f
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (originalBranchEvent rate rewards C_star C_h q t s hs control0)) ↔ _
  rw [← branchSourceMeasure_map_original rate rewards C_star C_h q t s hs control0]
  exact (measurableEmbedding_forgetBranch
    rate rewards C_star C_h q t s hs control0).integrable_map_iff

theorem actualSourceCells_span (z : Z) :
    ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      (n + 1) ≤ p.T := by
  have he : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
    z.property.2.2
  rw [he]
  omega

def actualSourceCells (z : Z) :
    List (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
    z.property.2.1 (n + 1) (actualSourceCells_span rate rewards C_star C_h q t s hs z)

def actualPotentialBefore (z : Z) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m Q
    (RecordedQueueRun.run Q ((actualSourceCells rate rewards C_star C_h q t s hs z).take n))

def actualPotentialAfter (z : Z) : ℝ :=
  RecordedWeightedDrift.weightedSquarePotential p.m Q
    (RecordedQueueRun.run Q ((actualSourceCells rate rewards C_star C_h q t s hs z).take (n + 1)))

def actualWeightedBacklogBefore (z : Z) : ℝ :=
  RecordedWeightedDrift.weightedBacklog p.m Q
    (RecordedQueueRun.run Q ((actualSourceCells rate rewards C_star C_h q t s hs z).take n))

def actualOverflowFalseSet : Set Z :=
  {z | (RecordedQueueRun.run Q
    ((actualSourceCells rate rewards C_star C_h q t s hs z).take n)).overflow = false}

def actualNormalizedBacklogBefore (j : Fin p.K) (z : Z) : ℝ :=
  StoppedQueueBound.normalizedBacklog Q
    (RecordedQueueRun.run Q ((actualSourceCells rate rewards C_star C_h q t s hs z).take n)) j

def actualNormalizedBacklogAfter (j : Fin p.K) (z : Z) : ℝ :=
  StoppedQueueBound.normalizedBacklog Q
    (RecordedQueueRun.run Q ((actualSourceCells rate rewards C_star C_h q t s hs z).take (n + 1))) j

def actualExpBacklogBefore (j : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta * actualNormalizedBacklogBefore rate rewards C_star C_h q t s hs j z)

def actualExpBacklogAfter (j : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta * actualNormalizedBacklogAfter rate rewards C_star C_h q t s hs j z)

theorem actualSourceCells_eq_sourceCells (z : Zplus) :
    actualSourceCells rate rewards C_star C_h q t s hs z.val =
      ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0 z := by
  rfl

private theorem actualPotentialBefore_eq (z : Zplus) :
    actualPotentialBefore rate rewards C_star C_h q t s hs z.val =
      ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
        rate rewards C_star C_h q t s hs control0 z := by
  rw [actualPotentialBefore, actualSourceCells_eq_sourceCells]
  rfl

private theorem actualPotentialAfter_eq (z : Zplus) :
    actualPotentialAfter rate rewards C_star C_h q t s hs z.val =
      ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
        rate rewards C_star C_h q t s hs control0 z := by
  rw [actualPotentialAfter, actualSourceCells_eq_sourceCells]
  rfl

private theorem actualWeightedBacklogBefore_eq (z : Zplus) :
    actualWeightedBacklogBefore rate rewards C_star C_h q t s hs z.val =
      ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0 z := by
  rw [actualWeightedBacklogBefore, actualSourceCells_eq_sourceCells]
  rfl

private theorem actualOverflowFalse_iff (z : Zplus) :
    z.val ∈ actualOverflowFalseSet rate rewards C_star C_h q t s hs ↔ z ∈ G := by
  change (RecordedQueueRun.run Q
      ((actualSourceCells rate rewards C_star C_h q t s hs z.val).take n)).overflow = false ↔ _
  rw [actualSourceCells_eq_sourceCells]
  rfl

private theorem actualExpBacklogBefore_eq (j : Fin p.K) (z : Zplus) :
    actualExpBacklogBefore rate rewards C_star C_h q t s hs j z.val =
      ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  rw [actualExpBacklogBefore, actualNormalizedBacklogBefore,
    actualSourceCells_eq_sourceCells]
  rw [ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore]
  congr 1
  exact congrArg (fun x : ℝ => beta * x)
    (ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_eq_normalized
      rate rewards C_star C_h q t s hs control0 j z).symm

private theorem actualExpBacklogAfter_eq (j : Fin p.K) (z : Zplus) :
    actualExpBacklogAfter rate rewards C_star C_h q t s hs j z.val =
      ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter
        rate rewards C_star C_h q t s hs control0 j z := by
  rw [actualExpBacklogAfter, actualNormalizedBacklogAfter,
    actualSourceCells_eq_sourceCells]
  rw [ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter]
  congr 1
  exact congrArg (fun x : ℝ => beta * x)
    (ReferenceFirstLiveQueueEnergyEnvelope.backlogAfter_eq_normalized
      rate rewards C_star C_h q t s hs control0 j z).symm

theorem integrableOn_branch_iff {f : Z → ℝ} :
    IntegrableOn f BZ muZ ↔ Integrable (fun z : Zplus => f z.val) muPlus := by
  change Integrable f ((muZ).restrict BZ) ↔ _
  rw [← map_comap_subtype_coe
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0) muZ]
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0)).integrable_map_iff

theorem integralOn_branch (f : Z → ℝ) :
    (∫ z in BZ, f z ∂muZ) = ∫ z : Zplus, f z.val ∂muPlus := by
  change (∫ z in BZ, f z ∂muZ) =
    ∫ z : {z : Z // z ∈ BZ}, f z.val ∂Measure.comap (Subtype.val : {z : Z // z ∈ BZ} → Z) muZ
  exact (integral_subtype_comap
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0) f).symm

theorem integrableOn_actualPotentialBefore :
    IntegrableOn (actualPotentialBefore rate rewards C_star C_h q t s hs)
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus => actualPotentialBefore rate rewards C_star C_h q t s hs z.val) =
        ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
          rate rewards C_star C_h q t s hs control0 := by
    funext z
    exact actualPotentialBefore_eq rate rewards C_star C_h q t s hs control0 z
  rw [hEq]
  exact ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialBefore
    rate rewards C_star C_h q t s hs control0

theorem integrableOn_actualPotentialAfter :
    IntegrableOn (actualPotentialAfter rate rewards C_star C_h q t s hs)
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus => actualPotentialAfter rate rewards C_star C_h q t s hs z.val) =
        ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
          rate rewards C_star C_h q t s hs control0 := by
    funext z
    exact actualPotentialAfter_eq rate rewards C_star C_h q t s hs control0 z
  rw [hEq]
  exact ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialAfter
    rate rewards C_star C_h q t s hs control0

theorem integrableOn_actualPotentialDifference :
    IntegrableOn
      (fun z : Z => actualPotentialAfter rate rewards C_star C_h q t s hs z -
        actualPotentialBefore rate rewards C_star C_h q t s hs z)
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus =>
        actualPotentialAfter rate rewards C_star C_h q t s hs z.val -
          actualPotentialBefore rate rewards C_star C_h q t s hs z.val) =
        (fun z : Zplus =>
          ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
              rate rewards C_star C_h q t s hs control0 z -
            ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
              rate rewards C_star C_h q t s hs control0 z) := by
    funext z
    rw [actualPotentialAfter_eq, actualPotentialBefore_eq]
  rw [hEq]
  exact ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialDifference
    rate rewards C_star C_h q t s hs control0

theorem integrableOn_actualGoodWeightedBacklog :
    IntegrableOn
      ((actualOverflowFalseSet rate rewards C_star C_h q t s hs).indicator
        (actualWeightedBacklogBefore rate rewards C_star C_h q t s hs))
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus =>
        (actualOverflowFalseSet rate rewards C_star C_h q t s hs).indicator
          (actualWeightedBacklogBefore rate rewards C_star C_h q t s hs) z.val) =
        (G).indicator (ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
          rate rewards C_star C_h q t s hs control0) := by
    funext z
    by_cases hz : z ∈ G
    · have hz' : z.val ∈ actualOverflowFalseSet rate rewards C_star C_h q t s hs :=
        (actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 z).2 hz
      simp [Set.indicator, hz, hz', actualWeightedBacklogBefore_eq
        rate rewards C_star C_h q t s hs control0 z]
    · have hz' : z.val ∉ actualOverflowFalseSet rate rewards C_star C_h q t s hs :=
        fun h => hz ((actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 z).1 h)
      simp [Set.indicator, hz, hz']
  rw [hEq]
  exact (ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0).indicator
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t s hs control0)

theorem integral_actualPotentialDifference :
    (∫ z in BZ,
      actualPotentialAfter rate rewards C_star C_h q t s hs z -
        actualPotentialBefore rate rewards C_star C_h q t s hs z ∂muZ) =
      ∫ z : Zplus,
        ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
            rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
            rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus,
        actualPotentialAfter rate rewards C_star C_h q t s hs z.val -
          actualPotentialBefore rate rewards C_star C_h q t s hs z.val ∂muPlus :=
      integralOn_branch rate rewards C_star C_h q t s hs control0 _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [actualPotentialAfter_eq rate rewards C_star C_h q t s hs control0 z,
        actualPotentialBefore_eq rate rewards C_star C_h q t s hs control0 z]

theorem integral_actualPotentialBefore :
    (∫ z in BZ, actualPotentialBefore rate rewards C_star C_h q t s hs z ∂muZ) =
      ∫ z : Zplus,
        ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
          rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus,
        actualPotentialBefore rate rewards C_star C_h q t s hs z.val ∂muPlus :=
      integralOn_branch rate rewards C_star C_h q t s hs control0 _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact actualPotentialBefore_eq rate rewards C_star C_h q t s hs control0 z

theorem integral_actualPotentialAfter :
    (∫ z in BZ, actualPotentialAfter rate rewards C_star C_h q t s hs z ∂muZ) =
      ∫ z : Zplus,
        ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
          rate rewards C_star C_h q t s hs control0 z ∂muPlus := by
  calc
    _ = ∫ z : Zplus,
        actualPotentialAfter rate rewards C_star C_h q t s hs z.val ∂muPlus :=
      integralOn_branch rate rewards C_star C_h q t s hs control0 _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact actualPotentialAfter_eq rate rewards C_star C_h q t s hs control0 z

theorem integral_actualGoodWeightedBacklog :
    (∫ z in BZ,
      (actualOverflowFalseSet rate rewards C_star C_h q t s hs).indicator
        (actualWeightedBacklogBefore rate rewards C_star C_h q t s hs) z ∂muZ) =
      ∫ z : Zplus,
      (G).indicator (ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
          rate rewards C_star C_h q t s hs control0) z ∂muPlus := by
  rw [integralOn_branch rate rewards C_star C_h q t s hs control0]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ G
  · have hz' : z.val ∈ actualOverflowFalseSet rate rewards C_star C_h q t s hs :=
      (actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 z).2 hz
    simp [Set.indicator, hz, hz', actualWeightedBacklogBefore_eq
      rate rewards C_star C_h q t s hs control0 z]
  · have hz' : z.val ∉ actualOverflowFalseSet rate rewards C_star C_h q t s hs :=
      fun h => hz ((actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 z).1 h)
    simp [Set.indicator, hz, hz']

theorem integrableOn_actualExpBacklogBefore (j : Fin p.K) :
    IntegrableOn (actualExpBacklogBefore rate rewards C_star C_h q t s hs j)
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus => actualExpBacklogBefore rate rewards C_star C_h q t s hs j z.val) =
        ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore
          rate rewards C_star C_h q t s hs control0 j := by
    funext z
    exact actualExpBacklogBefore_eq rate rewards C_star C_h q t s hs control0 j z
  rw [hEq]
  exact ReferenceFirstLiveConditionalExponentialQueue.integrable_expBacklogBefore
    rate rewards C_star C_h q t s hs control0 j

theorem integrableOn_actualExpBacklogAfter (j : Fin p.K) :
    IntegrableOn (actualExpBacklogAfter rate rewards C_star C_h q t s hs j)
      BZ muZ := by
  apply (integrableOn_branch_iff rate rewards C_star C_h q t s hs control0).2
  have hEq :
      (fun z : Zplus => actualExpBacklogAfter rate rewards C_star C_h q t s hs j z.val) =
        ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter
          rate rewards C_star C_h q t s hs control0 j := by
    funext z
    exact actualExpBacklogAfter_eq rate rewards C_star C_h q t s hs control0 j z
  rw [hEq]
  exact ReferenceFirstLiveConditionalExponentialQueue.integrable_expBacklogAfter
    rate rewards C_star C_h q t s hs control0 j

theorem integral_actualExpBacklogBefore (j : Fin p.K) :
    (∫ z in BZ, actualExpBacklogBefore rate rewards C_star C_h q t s hs j z ∂muZ) =
      ∫ z : Zplus,
        ReferenceFirstLiveConditionalExponentialQueue.expBacklogBefore
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  rw [integralOn_branch rate rewards C_star C_h q t s hs control0]
  congr 1
  funext z
  exact actualExpBacklogBefore_eq rate rewards C_star C_h q t s hs control0 j z

theorem integral_actualExpBacklogAfter (j : Fin p.K) :
    (∫ z in BZ, actualExpBacklogAfter rate rewards C_star C_h q t s hs j z ∂muZ) =
      ∫ z : Zplus,
        ReferenceFirstLiveConditionalExponentialQueue.expBacklogAfter
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  rw [integralOn_branch rate rewards C_star C_h q t s hs control0]
  congr 1
  funext z
  exact actualExpBacklogAfter_eq rate rewards C_star C_h q t s hs control0 j z

private theorem branchSourceMeasure_strictPast_mass :
    muPlus G = muZ (BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs) := by
  let hInner := MeasurableEmbedding.subtype_coe
    (measurableSet_continuingBranch rate rewards C_star C_h q t s hs control0)
  have hG : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
      rate rewards C_star C_h q t s hs control0
  have hImage :
      (Subtype.val : Zplus → Z) '' G =
        BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property,
        (actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 y).1 hy⟩
    · rintro ⟨hzB, hzG⟩
      refine ⟨⟨z, hzB⟩,
        (actualOverflowFalse_iff rate rewards C_star C_h q t s hs control0 ⟨z, hzB⟩).2 hzG,
        rfl⟩
  have hImageMeas : MeasurableSet ((Subtype.val : Zplus → Z) '' G) :=
    hInner.measurableSet_image.mpr hG
  calc
    muPlus G = muPlus ((Subtype.val : Zplus → Z) ⁻¹'
        ((Subtype.val : Zplus → Z) '' G)) := by
      congr 1
      exact (Set.preimage_image_eq G hInner.injective).symm
    _ = ((muPlus).map (Subtype.val : Zplus → Z)) ((Subtype.val : Zplus → Z) '' G) :=
      (hInner.map_apply muPlus ((Subtype.val : Zplus → Z) '' G)).symm
    _ = ((muZ).restrict BZ) ((Subtype.val : Zplus → Z) '' G) := by
      rw [branchSubtype_map rate rewards C_star C_h q t s hs control0]
    _ = muZ ((Subtype.val : Zplus → Z) '' G) := by
      rw [Measure.restrict_apply hImageMeas]
      congr 1
      exact Set.inter_eq_left.mpr (by
        rintro z ⟨y, hy, rfl⟩
        exact y.property)
    _ = muZ (BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs) := by
      rw [← hImage]

theorem branchSourceMeasure_strictPast_real :
    (muPlus).real G =
      (muZ).real (BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs) := by
  change ENNReal.toReal (muPlus G) =
    ENNReal.toReal (muZ (BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs))
  exact congrArg ENNReal.toReal
    (branchSourceMeasure_strictPast_mass rate rewards C_star C_h q t s hs control0)

theorem integral_actualExpBacklogAfter_step (j : Fin p.K) :
    (∫ z in BZ,
      actualExpBacklogAfter rate rewards C_star C_h q t s hs j z ∂muZ) ≤
      (∫ z in BZ,
        actualExpBacklogBefore rate rewards C_star C_h q t s hs j z ∂muZ) +
        (muZ).real (BZ ∩ actualOverflowFalseSet rate rewards C_star C_h q t s hs) := by
  rw [integral_actualExpBacklogAfter rate rewards C_star C_h q t s hs control0 j,
    integral_actualExpBacklogBefore rate rewards C_star C_h q t s hs control0 j,
    ← branchSourceMeasure_strictPast_real rate rewards C_star C_h q t s hs control0]
  exact ReferenceFirstLiveConditionalExponentialQueue.integral_expBacklogAfter_step
    rate rewards C_star C_h q t s hs control0 j

end Bandits.Support.ReferenceFirstLiveBranchIntegralTransport

end
