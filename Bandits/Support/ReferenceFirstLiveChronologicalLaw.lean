/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPairIdentity
public import Bandits.Support.ReferenceFirstLiveObservedKernelSourceLaw
public import Bandits.Support.ReferenceFirstLiveChronologicalProposalLaw
public import Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# First-LIVE chronological one-step observed law

On the continuing and empty-pending original source restrictions, the
complete-past observed recorder/FAST pair is the same pair stored by the
date-`t` entry of the existing chronological prefix on computed clear PRE.
The original unnormalized source laws therefore transport arbitrary bounded
Borel tests of that intrinsic entry to the accepted same-family correlated
observed-slice kernel. The proposal and residual-refresh laws remain on their
separate accepted test spaces.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveChronologicalLaw

open ReferenceFirstLiveChronologicalProposalLaw
open ReferenceFirstLiveChronologicalPairIdentity
open ReferenceFirstLivePastPairKernelTransport
open ReferenceFirstLivePostUpdateProposalLaw

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev SourcePlus (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
abbrev EmptySource (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0
abbrev TaggedSource (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  SourcePlus rate rewards C_star C_h q t s hs control0 ⊕
    EmptySource rate rewards C_star C_h q t s hs control0
abbrev PastObservationPair (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePastPairKernelTransport.PastObservationPair
    rate rewards C_star C_h q t s hs control0
abbrev LiveRemainder (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePostUpdateProposalLaw.LiveRemainder
    rate rewards C_star C_h q t s hs control0

variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

/-- The actual continuing-source complete-past recorder/FAST observation,
with only its final pair read from the same date-`t` chronological entry. -/
public def continuingChronologicalPairObservation
    (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    PastObservationPair rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 za.1
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inl split.1
  let entry := chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
    (.inl za.1) za.2
  (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (x, (split.2.2, za.2)),
    (entry.numerical.2.1, some entry.fastArm))

/-- The actual empty-pending complete-past recorder/FAST observation, with
only its final pair read from the same date-`t` chronological entry. -/
public def emptyChronologicalPairObservation
    (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    PastObservationPair rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 za.1
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inr split.1
  let entry := chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
    (.inr za.1) za.2
  (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (x, (split.2.2, za.2)),
    (entry.numerical.2.1, some entry.fastArm))

/-- The strict-past clear gate on the retained continuing original source. -/
public def continuingChronologicalPairClear
    (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) : Prop :=
  (liveNumericalPast rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
      rate rewards C_star C_h q t s hs control0 (.inl za.1))).2.1 = false

/-- The strict-past clear gate on the retained empty-pending original source. -/
public def emptyChronologicalPairClear
    (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) : Prop :=
  (liveNumericalPast rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
      rate rewards C_star C_h q t s hs control0 (.inr za.1))).2.1 = false

/-- The nested gate in the accepted continuing map is the original computed
strict-past numerical PRE state. -/
public theorem continuingChronologicalPair_clearGate_eq_map
    (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    continuingChronologicalPairClear rate rewards C_star C_h q t s hs control0 za =
      ((continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1
        = false) := by
  rfl

/-- The nested gate in the accepted empty-pending map is the original
computed strict-past numerical PRE state. -/
public theorem emptyChronologicalPair_clearGate_eq_map
    (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    emptyChronologicalPairClear rate rewards C_star C_h q t s hs control0 za =
      ((emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1
        = false) := by
  rfl

/-- On computed clear PRE the actual continuing map's marker and reserved
FAST coordinate are exactly the fields of its intrinsic chronological entry.
The first observation component, including the complete recorder past, the
current family, the full auxiliary array, and all numerical observations, is
retained literally. -/
public theorem continuingChronologicalPairObservation_eq_map_of_clear
    (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
        rate rewards C_star C_h q t s hs control0 (.inl za.1))).2.1 = false) :
    continuingChronologicalPairObservation rate rewards C_star C_h q t s hs control0 za =
      continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za := by
  have hcell := originalSource_clear_chronological_pair_cell rate rewards C_star C_h q t s hs
    control0 (.inl za.1) za.2 hclear
  rcases hcell with ⟨_, hmarker, _, hreserved, _⟩
  change
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
        (.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2.2, za.2)),
      ((chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
        (.inl za.1) za.2).numerical.2.1,
        some (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
          (.inl za.1) za.2).fastArm)) =
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
        (.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2.2, za.2)),
      ReferenceFirstLiveCanonicalProposalJointLaw.liveMarkerFastPair
        rate rewards C_star C_h q t s hs control0
        (.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hmarker
    · exact hreserved.symm

/-- On computed clear PRE the actual empty-pending map's marker and reserved
FAST coordinate are exactly the fields of its intrinsic chronological entry.
The complete recorder observation and all original auxiliary coordinates
remain unchanged. -/
public theorem emptyChronologicalPairObservation_eq_map_of_clear
    (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
        rate rewards C_star C_h q t s hs control0 (.inr za.1))).2.1 = false) :
    emptyChronologicalPairObservation rate rewards C_star C_h q t s hs control0 za =
      emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za := by
  have hcell := originalSource_clear_chronological_pair_cell rate rewards C_star C_h q t s hs
    control0 (.inr za.1) za.2 hclear
  rcases hcell with ⟨_, hmarker, _, hreserved, _⟩
  change
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
        (.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          ((ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2.2, za.2)),
      ((chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
        (.inr za.1) za.2).numerical.2.1,
        some (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0
          (.inr za.1) za.2).fastArm)) =
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
        (.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          ((ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2.2, za.2)),
      ReferenceFirstLiveCanonicalProposalJointLaw.liveMarkerFastPair
        rate rewards C_star C_h q t s hs control0
        (.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h q t s hs control0 za.1).1,
          (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
            rate rewards C_star C_h q t s hs control0 za.1).2))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hmarker
    · exact hreserved.symm

/-- Transport the bounded clear-PRE continuing observed-kernel law onto the
same intrinsic chronological current entry. The right side is the accepted
same-remainder, same-family correlated recorder/FAST kernel mixture. -/
public theorem continuingSource_clear_chronological_pair_integral
    (_hpos : s < t.val)
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let obs := continuingChronologicalPairObservation rate rewards C_star C_h q t s hs control0
    let clear := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (liveNumericalPast rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
        rate rewards C_star C_h q t s hs control0 (.inl za.1))).2.1 = false
    (∀ za, clear za = ((continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1
      = false)) ∧
    (∀ za, clear za → obs za =
      continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za) ∧
    Integrable (fun za => if clear za then F (obs za) else 0) (μ.prod aux) ∧
    Measurable (fun z : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1, z.2)) ∧
    Integrable (fun z : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inl z.1, z.2))
      (ν.prod ((ContinuousLearningRows.affineSamplesLaw p).prod aux)) ∧
    (∫ za, (if clear za then F (obs za) else 0) ∂(μ.prod aux)) =
      ∫ x, ∫ family, ∫ a, ∫ y,
        (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (Sum.inl x : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
          then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inl x, (family, a))
        ∂aux ∂ContinuousLearningRows.affineSamplesLaw p ∂ν := by
  dsimp only
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let obs := continuingChronologicalPairObservation rate rewards C_star C_h q t s hs control0
  let clear := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    (liveNumericalPast rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
      rate rewards C_star C_h q t s hs control0 (.inl za.1))).2.1 = false
  let testMap := continuingPastPairTestMap rate rewards C_star C_h q t s hs control0
  have hsource := ReferenceFirstLiveObservedKernelSourceLaw.continuingSource_clear_observed_kernel_integral
    rate rewards C_star C_h q t s hs control0 F hF C hC
  rcases hsource with ⟨hsourceInt, hkernelMeas, hkernelInt, hsourceLaw⟩
  have hgate : ∀ za, clear za = ((testMap za).1.2.2.2.2.1 = false) := by
    intro za
    exact continuingChronologicalPair_clearGate_eq_map
      rate rewards C_star C_h q t s hs control0 za
  have htest : ∀ za,
      (if clear za then F (obs za) else 0) =
        (if (testMap za).1.2.2.2.2.1 = false then F (testMap za) else 0) := by
    intro za
    by_cases hclear : clear za
    · have hmap : (testMap za).1.2.2.2.2.1 = false := hgate za ▸ hclear
      have hobs : obs za = testMap za :=
        continuingChronologicalPairObservation_eq_map_of_clear
          rate rewards C_star C_h q t s hs control0 za hclear
      rw [ite_eq_left hclear, ite_eq_left hmap, hobs]
    · have hmap : ¬ ((testMap za).1.2.2.2.2.1 = false) := by
        intro hm
        exact hclear (hgate za ▸ hm)
      rw [ite_eq_right hclear, ite_eq_right hmap]
  have htransportedInt := hsourceInt.congr
    (Filter.Eventually.of_forall fun za => (htest za).symm)
  refine ⟨hgate, ?_, htransportedInt, ?_, ?_, ?_⟩
  · intro za hclear
    exact continuingChronologicalPairObservation_eq_map_of_clear
      rate rewards C_star C_h q t s hs control0 za hclear
  · simpa only [ν, aux] using hkernelMeas
  · simpa only [ν, aux] using hkernelInt
  · calc
      (∫ za, (if clear za then F (obs za) else 0) ∂(μ.prod aux)) =
          ∫ za, (if (testMap za).1.2.2.2.2.1 = false
            then F (testMap za) else 0) ∂(μ.prod aux) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall htest
      _ = _ := by simpa only [μ, ν, aux] using hsourceLaw

/-- Transport the bounded clear-PRE empty-pending observed-kernel law onto the
same intrinsic chronological current entry. The branch remains its original
unnormalized source restriction. -/
public theorem emptySource_clear_chronological_pair_integral
    (_hpos : s < t.val)
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let obs := emptyChronologicalPairObservation rate rewards C_star C_h q t s hs control0
    let clear := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (liveNumericalPast rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
        rate rewards C_star C_h q t s hs control0 (.inr za.1))).2.1 = false
    (∀ za, clear za = ((emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1
      = false)) ∧
    (∀ za, clear za → obs za =
      emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za) ∧
    Integrable (fun za => if clear za then F (obs za) else 0) (μ.prod aux) ∧
    Measurable (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1, z.2)) ∧
    Integrable (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
        rate rewards C_star C_h q t s hs control0 ×
          (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) =>
      ∫ y, (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1 : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
        then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inr z.1, z.2))
      (ν.prod ((ContinuousLearningRows.affineSamplesLaw p).prod aux)) ∧
    (∫ za, (if clear za then F (obs za) else 0) ∂(μ.prod aux)) =
      ∫ x, ∫ family, ∫ a, ∫ y,
        (if (liveNumericalPast rate rewards C_star C_h q t s hs control0
            (Sum.inr x : LiveRemainder rate rewards C_star C_h q t s hs control0)).2.1 = false
          then F y else 0)
        ∂actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0
          (Sum.inr x, (family, a))
        ∂aux ∂ContinuousLearningRows.affineSamplesLaw p ∂ν := by
  dsimp only
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let obs := emptyChronologicalPairObservation rate rewards C_star C_h q t s hs control0
  let clear := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    (liveNumericalPast rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
      rate rewards C_star C_h q t s hs control0 (.inr za.1))).2.1 = false
  let testMap := emptyPastPairTestMap rate rewards C_star C_h q t s hs control0
  have hsource := ReferenceFirstLiveObservedKernelSourceLaw.emptySource_clear_observed_kernel_integral
    rate rewards C_star C_h q t s hs control0 F hF C hC
  rcases hsource with ⟨hsourceInt, hkernelMeas, hkernelInt, hsourceLaw⟩
  have hgate : ∀ za, clear za = ((testMap za).1.2.2.2.2.1 = false) := by
    intro za
    exact emptyChronologicalPair_clearGate_eq_map rate rewards C_star C_h q t s hs
      control0 za
  have htest : ∀ za,
      (if clear za then F (obs za) else 0) =
        (if (testMap za).1.2.2.2.2.1 = false then F (testMap za) else 0) := by
    intro za
    by_cases hclear : clear za
    · have hmap : (testMap za).1.2.2.2.2.1 = false := hgate za ▸ hclear
      have hobs : obs za = testMap za :=
        emptyChronologicalPairObservation_eq_map_of_clear
          rate rewards C_star C_h q t s hs control0 za hclear
      rw [ite_eq_left hclear, ite_eq_left hmap, hobs]
    · have hmap : ¬ ((testMap za).1.2.2.2.2.1 = false) := by
        intro hm
        exact hclear (hgate za ▸ hm)
      rw [ite_eq_right hclear, ite_eq_right hmap]
  have htransportedInt := hsourceInt.congr
    (Filter.Eventually.of_forall fun za => (htest za).symm)
  refine ⟨hgate, ?_, htransportedInt, ?_, ?_, ?_⟩
  · intro za hclear
    exact emptyChronologicalPairObservation_eq_map_of_clear
      rate rewards C_star C_h q t s hs control0 za hclear
  · simpa only [ν, aux] using hkernelMeas
  · simpa only [ν, aux] using hkernelInt
  · calc
      (∫ za, (if clear za then F (obs za) else 0) ∂(μ.prod aux)) =
          ∫ za, (if (testMap za).1.2.2.2.2.1 = false
            then F (testMap za) else 0) ∂(μ.prod aux) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall htest
      _ = _ := by simpa only [μ, ν, aux] using hsourceLaw

end Bandits.Support.ReferenceFirstLiveChronologicalLaw

end
