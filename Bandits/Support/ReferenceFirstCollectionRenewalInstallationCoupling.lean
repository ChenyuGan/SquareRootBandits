/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSampleInstallation
public import Bandits.Support.ReferenceFirstCollectionRenewalInsertedSourceLaw

/-!
# Couple the first renewal installation to the original source

The analytical whole-source renewal lift is mapped to a literal pair
consisting of its original source and auxiliary array, together with the
source after inserting the same candidate assignment vector. The pair keeps
the original product law as its first marginal and the original restricted
source law as its second marginal. Its support preserves the actual strict
physical past and the original analytical draw. Almost every pair also
carries the actual successful local start and installation from the inserted
source.

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-69,399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This result concerns the first renewal sampler call and reconstructed stored
registers. It does not establish a joint score-and-queue budget, service-pass
success, true calendar scores, later sampler calls, or a full logical and
physical chronological coupling.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling

open ConstructorDimensions
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFibreExtension
open ReferenceFirstCollectionRenewalInsertedSourceLaw
open ReferenceFirstCollectionRenewalPastLocality
open ReferenceFirstCollectionRenewalVectorInsertion
open BootstrapPrivateRoundStreams
open ReferenceCompletePhysicalHistory
open ReferenceFirstCollectionSamplerCall
open LaterAssignmentStartOperation
open LaterAssignmentStartMeasurability
open CoordinatorAssignmentRegisterInstall
open AssignmentScoreReconstruction
open AssignmentParameterFibreKernel
open CoordinatorRoundDispatch
open CoordinatorLocalArmChoice
open CoordinatorLiveChoiceRecorderStep
open scoped BigOperators

variable {p : ConstructorDimensions.Parameters}

private instance measurableEqContinuousScalar :
    MeasurableEq ContinuousControlSlice.Scalar where
  measurableSet_diagonal := by
    have hreal : MeasurableSet {z : ContinuousControlSlice.Scalar ×
        ContinuousControlSlice.Scalar | (z.1 : ℝ) = (z.2 : ℝ)} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hset : {z : ContinuousControlSlice.Scalar ×
        ContinuousControlSlice.Scalar | z.1 = z.2} =
        {z | (z.1 : ℝ) = (z.2 : ℝ)} := by
      ext z
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [Set.diagonal, hset]
    exact hreal

private instance measurableEqProd {α β : Type*} [MeasurableSpace α] [MeasurableEq α]
    [MeasurableSpace β] [MeasurableEq β] : MeasurableEq (α × β) where
  measurableSet_diagonal := by
    have hleft : MeasurableSet {z : (α × β) × (α × β) | z.1.1 = z.2.1} := by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hright : MeasurableSet {z : (α × β) × (α × β) | z.1.2 = z.2.2} := by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hdiag : Set.diagonal (α × β) =
        {z : (α × β) × (α × β) | z.1.1 = z.2.1} ∩
          {z : (α × β) × (α × β) | z.1.2 = z.2.2} := by
      ext z
      simp [Set.mem_diagonal_iff, Prod.ext_iff]
    rw [hdiag]
    exact hleft.inter hright

private instance measurableEqPi {ι : Type*} [Fintype ι] {α : ι → Type*}
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

-- The physical source measurable space is the product structure used by the
-- source-law modules. Those modules keep it local because each needs it only
-- while constructing its own law.
local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private instance sourceInputMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableEq
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The original renewal-call subtype. -/
abbrev Source (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
    rate rewards C_star C_h u t

private instance renewalSourceMeasurableEq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableEq (Source rate rewards C_star C_h u t) where
  measurableSet_diagonal := by
    rw [Set.diagonal]
    have hset :
        {z : Source rate rewards C_star C_h u t ×
          Source rate rewards C_star C_h u t | z.1 = z.2} =
        {z | z.1.val = z.2.val} := by
      ext z
      exact Subtype.ext_iff
    rw [hset]
    exact measurableSet_eq_fun
      (measurable_subtype_coe.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)

private instance auxiliaryArrayMeasurableEq (p : ConstructorDimensions.Parameters) :
    MeasurableEq (AuxiliaryArray p) := by
  change MeasurableEq
    (ReferenceFirstCollectionAuxiliarySeeds.Coordinate p →
      ContinuousControlSlice.Scalar)
  infer_instance

private instance renewalBaseMeasurableEq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableEq (RenewalBase rate rewards C_star C_h u t) := by
  change MeasurableEq
    (Source rate rewards C_star C_h u t × AuxiliaryArray p)
  infer_instance

/-- The whole original auxiliary seed array, including its renewal cell. -/
abbrev AuxiliaryArray :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.AuxiliaryArray

/-- The original source and the whole auxiliary array. -/
abbrev RenewalBase (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalFibreExtension.RenewalBase
    rate rewards C_star C_h u t

/-- The source/vector carrier used by the renewal fibre extension. -/
abbrev RenewalLift (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalVectorInsertion.W
    rate rewards C_star C_h u t

/-- The existing unnormalized source-indexed renewal lift. -/
abbrev renewalLiftLaw (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalVectorInsertion.Lambda
    rate rewards C_star C_h u t

/-- Keep the original source and full auxiliary array, and insert the same
candidate vector into the original selected-row control at time `t`. -/
def pair (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (wv : RenewalLift rate rewards C_star C_h u t) :
    RenewalBase rate rewards C_star C_h u t × Source rate rewards C_star C_h u t :=
  (wv.1, ReferenceFirstCollectionRenewalVectorInsertion.put
    rate rewards C_star C_h u t wv.1.1 wv.2)

/-- The pushforward of the existing lift by the literal insertion pair. -/
def pairLaw (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Measure (RenewalBase rate rewards C_star C_h u t ×
      Source rate rewards C_star C_h u t) :=
  (renewalLiftLaw rate rewards C_star C_h u t).map
    (pair rate rewards C_star C_h u t)

/-- The literal pair map is measurable on the whole product carrier. -/
theorem measurable_pair (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Measurable (pair rate rewards C_star C_h u t) := by
  change Measurable (fun wv : RenewalLift rate rewards C_star C_h u t =>
    (wv.1, ReferenceFirstCollectionRenewalVectorInsertion.put
      rate rewards C_star C_h u t wv.1.1 wv.2))
  exact measurable_fst.prodMk <|
    (ReferenceFirstCollectionRenewalVectorInsertion.measurable_put
      rate rewards C_star C_h u t).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

/-- The pair law remains finite, including when the renewal cell has zero
mass. -/
theorem pairLaw_finite (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    IsFiniteMeasure (pairLaw rate rewards C_star C_h u t) := by
  unfold pairLaw renewalLiftLaw
  infer_instance

private def pairInverse (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (b : RenewalBase rate rewards C_star C_h u t ×
      Source rate rewards C_star C_h u t) :
    RenewalLift rate rewards C_star C_h u t :=
  (b.1, ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val)

private theorem measurable_av (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Measurable (fun z : Source rate rewards C_star C_h u t =>
      ReferenceFirstCollectionRenewalVectorInsertion.av t z.val) := by
  let S := BootstrapPrivateRoundStreams.SourceInput p
  have hq : Measurable (fun s : S =>
      ReferenceFirstCollectionRenewalVectorInsertion.q s) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hrows : Measurable (fun s : S => s.1.2) :=
    measurable_snd.comp (measurable_fst : Measurable (fun s : S => s.1))
  have hbranch : ∀ j : Fin (M p), Measurable (fun s : S => s.1.2 j) := by
    intro j
    exact (measurable_pi_apply j).comp hrows
  have hselected : Measurable (fun s : S =>
      s.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q s)) := by
    exact (measurable_from_prod_countable_right
        (f := fun z : Fin (M p) × S => z.2.1.2 z.1) hbranch).comp
      (hq.prodMk measurable_id)
  change Measurable (fun z : Source rate rewards C_star C_h u t =>
    LaterAssignmentStartOperation.ownAssignmentVector
      (z.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)) t)
  exact (LaterAssignmentStartMeasurability.measurable_ownAssignmentVector t).comp
    (hselected.comp measurable_subtype_coe)

private theorem measurable_pairInverse
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Measurable (pairInverse rate rewards C_star C_h u t) := by
  change Measurable (fun b : RenewalBase rate rewards C_star C_h u t ×
    Source rate rewards C_star C_h u t =>
      (b.1, ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val))
  exact measurable_fst.prodMk <|
    (measurable_av rate rewards C_star C_h u t).comp
      measurable_snd

private theorem pairInverse_pair
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (wv : RenewalLift rate rewards C_star C_h u t) :
    pairInverse rate rewards C_star C_h u t
        (pair rate rewards C_star C_h u t wv) = wv := by
  rcases wv with ⟨base, v⟩
  rcases base with ⟨z, a⟩
  apply Prod.ext
  · rfl
  · change ReferenceFirstCollectionRenewalVectorInsertion.av t
      (ReferenceFirstCollectionRenewalVectorInsertion.put
        rate rewards C_star C_h u t z v).val = v
    rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    exact ReferenceFirstCollectionRenewalVectorInsertion.av_insert t z.val v

private theorem range_pair_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Set.range (pair rate rewards C_star C_h u t) =
      {b | pair rate rewards C_star C_h u t
        (pairInverse rate rewards C_star C_h u t b) = b} := by
  ext b
  constructor
  · rintro ⟨wv, rfl⟩
    change pair rate rewards C_star C_h u t
      (pairInverse rate rewards C_star C_h u t
        (pair rate rewards C_star C_h u t wv)) =
      pair rate rewards C_star C_h u t wv
    rw [pairInverse_pair]
  · intro h
    exact ⟨pairInverse rate rewards C_star C_h u t b, h⟩

private theorem measurableSet_range_pair
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableSet (Set.range (pair rate rewards C_star C_h u t)) := by
  rw [range_pair_eq]
  exact measurableSet_eq_fun
    ((measurable_pair rate rewards C_star C_h u t).comp
      (measurable_pairInverse rate rewards C_star C_h u t)) measurable_id

/-- Inserting the current assignment vector is recoverable from the second
source, so the literal pair map is a measurable embedding. -/
theorem pair_measurableEmbedding
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableEmbedding (pair rate rewards C_star C_h u t) :=
  MeasurableEmbedding.of_measurable_inverse
    (measurable_pair rate rewards C_star C_h u t)
    (measurableSet_range_pair rate rewards C_star C_h u t)
    (measurable_pairInverse rate rewards C_star C_h u t)
    (pairInverse_pair rate rewards C_star C_h u t)

/-- The first marginal retains the original source and the entire original
auxiliary array. -/
theorem pairLaw_map_fst
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (pairLaw rate rewards C_star C_h u t).map Prod.fst =
      ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw
        rate rewards C_star C_h u t := by
  rw [pairLaw, Measure.map_map measurable_fst
    (measurable_pair rate rewards C_star C_h u t)]
  change (renewalLiftLaw rate rewards C_star C_h u t).map
    (fun wv : RenewalLift rate rewards C_star C_h u t => wv.1) = _
  exact ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_map_fst
    rate rewards C_star C_h u t

/-- Forgetting the inserted vector recovers the restricted original source
law. This equality is derived from the literal insertion map and subtype
embedding, not postulated as a second-marginal law. -/
theorem pairLaw_map_value
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (pairLaw rate rewards C_star C_h u t).map
      (fun b : RenewalBase rate rewards C_star C_h u t ×
        Source rate rewards C_star C_h u t => b.2.val) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) := by
  have hfun :
      (fun wv : RenewalLift rate rewards C_star C_h u t =>
        (ReferenceFirstCollectionRenewalVectorInsertion.put
          rate rewards C_star C_h u t wv.1.1 wv.2).val) =
      (fun wv : RenewalLift rate rewards C_star C_h u t =>
        ReferenceFirstCollectionRenewalVectorInsertion.insert t
          wv.1.1.val wv.2) := by
    funext wv
    exact ReferenceFirstCollectionRenewalVectorInsertion.put_val
      rate rewards C_star C_h u t wv.1.1 wv.2
  calc
    _ = (renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv : RenewalLift rate rewards C_star C_h u t =>
          (ReferenceFirstCollectionRenewalVectorInsertion.put
            rate rewards C_star C_h u t wv.1.1 wv.2).val) := by
      rw [pairLaw]
      simpa only [Function.comp_def, pair] using
        (Measure.map_map
        (measurable_subtype_coe.comp measurable_snd)
        (measurable_pair rate rewards C_star C_h u t))
    _ = (renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv : RenewalLift rate rewards C_star C_h u t =>
          ReferenceFirstCollectionRenewalVectorInsertion.insert t
            wv.1.1.val wv.2) := by rw [hfun]
    _ = _ :=
      renewalLiftLaw_map_inserted_source rate rewards C_star C_h u t

/-- The second marginal is the original renewal-source law. Injectivity of
the measurable subtype embedding recovers it from the value marginal. -/
theorem pairLaw_map_snd
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (pairLaw rate rewards C_star C_h u t).map Prod.snd =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t := by
  apply MeasurableEmbedding.map_injective
    (MeasurableEmbedding.subtype_coe
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t))
  calc
    ((pairLaw rate rewards C_star C_h u t).map Prod.snd).map Subtype.val =
        (pairLaw rate rewards C_star C_h u t).map
          (fun b : RenewalBase rate rewards C_star C_h u t ×
            Source rate rewards C_star C_h u t => b.2.val) := by
      rw [Measure.map_map measurable_subtype_coe measurable_snd]
      rfl
    _ = _ := by
      rw [pairLaw_map_value]
      exact (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val
        rate rewards C_star C_h u t).symm

/-- The total mass is the original renewal-event mass on every cell,
including empty and null cells; no normalization or positivity is used. -/
theorem pairLaw_univ
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    pairLaw rate rewards C_star C_h u t Set.univ =
        ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw
          rate rewards C_star C_h u t Set.univ ∧
      pairLaw rate rewards C_star C_h u t Set.univ =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t Set.univ ∧
      pairLaw rate rewards C_star C_h u t Set.univ =
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
            rate rewards C_star C_h u t) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      pairLaw rate rewards C_star C_h u t Set.univ =
          ((pairLaw rate rewards C_star C_h u t).map Prod.fst) Set.univ := by
        simp [Measure.map_apply measurable_fst MeasurableSet.univ]
      _ = _ := congrArg (fun μ : Measure _ => μ Set.univ)
        (pairLaw_map_fst rate rewards C_star C_h u t)
  · calc
      pairLaw rate rewards C_star C_h u t Set.univ =
          ((pairLaw rate rewards C_star C_h u t).map Prod.snd) Set.univ := by
        simp [Measure.map_apply measurable_snd MeasurableSet.univ]
      _ = _ := congrArg (fun μ : Measure _ => μ Set.univ)
        (pairLaw_map_snd rate rewards C_star C_h u t)
  · calc
      pairLaw rate rewards C_star C_h u t Set.univ =
          ((pairLaw rate rewards C_star C_h u t).map
            (fun b : RenewalBase rate rewards C_star C_h u t ×
              Source rate rewards C_star C_h u t => b.2.val)) Set.univ := by
        symm
        exact Measure.map_apply
          (measurable_subtype_coe.comp measurable_snd) MeasurableSet.univ
      _ = _ := by
        rw [pairLaw_map_value]
        exact Measure.restrict_apply_univ
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
            rate rewards C_star C_h u t)

private theorem inserted_source_chronology
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : Source rate rewards C_star C_h u t) (a : AuxiliaryArray p)
    (v : ReferenceFirstCollectionRenewalVectorInsertion.V p) :
    let z' := ReferenceFirstCollectionRenewalVectorInsertion.put
      rate rewards C_star C_h u t z v
    z'.val.1.1 = z.val.1.1 ∧
    z'.val.2 = z.val.2 ∧
    ReferenceFirstCollectionRenewalVectorInsertion.q z'.val =
      ReferenceFirstCollectionRenewalVectorInsertion.q z.val ∧
    (∀ j, j ≠ ReferenceFirstCollectionRenewalVectorInsertion.q z.val →
      z'.val.1.2 j = z.val.1.2 j) ∧
    (z'.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).1 =
      (z.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).1 ∧
    (∀ r : Fin p.T, r ≠ t →
      (z'.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).2 r =
        (z.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).2 r) ∧
    (∀ label : Bandits.Support.LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (ReferenceFirstCollectionRenewalVectorInsertion.c t z'.val).1 label.val =
        (ReferenceFirstCollectionRenewalVectorInsertion.c t z.val).1 label.val) ∧
    (ReferenceFirstCollectionRenewalVectorInsertion.c t z'.val).2 =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t z.val).2 ∧
    ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z'.val =
        some (u, (t, ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t z)) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t z =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t z' ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t z.val =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
          rate rewards C_star C_h t z'.val ∧
    (∀ player : Fin p.m, ∀ v' : Fin p.T, v'.val < t.val →
      ReferenceCompletePhysicalHistory.completeOwnHistory
          rate z.val rewards C_star C_h player v' =
        ReferenceCompletePhysicalHistory.completeOwnHistory
          rate z'.val rewards C_star C_h player v') ∧
    (∃ n : ℕ,
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + n =
        t.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.val rewards C_star C_h).take n).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z'.val rewards C_star C_h).take n).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z a =
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z' a := by
  dsimp only
  let z' := ReferenceFirstCollectionRenewalVectorInsertion.put
    rate rewards C_star C_h u t z v
  let suffix := ReferenceFirstCollectionRenewalVectorInsertion.suffix
    t z.val v
  have hvalue : z'.val = ReferenceFirstCollectionRenewalVectorInsertion.insert
      t z.val v :=
    ReferenceFirstCollectionRenewalVectorInsertion.put_val
      rate rewards C_star C_h u t z v
  have hsource : z'.val =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z.val t suffix := by
    rw [hvalue]
    exact ReferenceFirstCollectionRenewalVectorInsertion.insert_eq_replaceSelectedControlSuffix
      t z.val v
  have hcall := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t z
  have hcallUpdate :=
    ReferenceFirstCollectionRenewalPastLocality.firstCollectionCall_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val u t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z) suffix hcall
  have hparameterUpdate :=
    ReferenceFirstCollectionRenewalPastLocality.renewalCallParameter_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z suffix
  have hzSubtype : z' = ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
      rate rewards C_star C_h u t z suffix := by
    apply Subtype.ext
    exact hsource
  have hsourcePut :
      (ReferenceFirstCollectionRenewalVectorInsertion.put
        rate rewards C_star C_h u t z v).val =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z.val t suffix := by
    simpa only [z'] using hsource
  have hzSubtypePut : ReferenceFirstCollectionRenewalVectorInsertion.put
      rate rewards C_star C_h u t z v =
      ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
        rate rewards C_star C_h u t z suffix := by
    simpa only [z'] using hzSubtype
  have hfreeze :=
    ReferenceFirstCollectionRenewalPastLocality.oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val u t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z) suffix hcall
  have hsample :=
    ReferenceFirstCollectionRenewalPastLocality.renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z suffix a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
        t z.val v).1
  · simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
        t z.val v).2.1
  · simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
        t z.val v).2.2
  · intro j hj
    simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      ReferenceFirstCollectionRenewalVectorInsertion.insert_other_row
        t z.val v j hj
  · simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      ReferenceFirstCollectionRenewalVectorInsertion.insert_selected_forward
        t z.val v
  · intro r hr
    simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      ReferenceFirstCollectionRenewalVectorInsertion.insert_other_time
        t z.val v r hr
  · intro label
    simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      ReferenceFirstCollectionRenewalVectorInsertion.insert_nonAssignmentScalars
        t z.val v label
  · simpa only [ReferenceFirstCollectionRenewalVectorInsertion.put_val] using
      ReferenceFirstCollectionRenewalVectorInsertion.insert_affineSamples
        t z.val v
  · rw [hsourcePut]
    exact hcallUpdate
  · rw [hzSubtypePut]
    exact hparameterUpdate
  · rw [hsourcePut]
    exact hfreeze
  · intro player v' hbefore
    rw [hsourcePut]
    exact ReferenceFirstCollectionRenewalPastLocality.strict_past_own_history_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val t suffix player v' hbefore
  · rw [hsourcePut]
    exact ReferenceFirstCollectionRenewalPastLocality.strict_past_evidence_of_firstCollectionCall
        rate rewards C_star C_h z.val u t
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t z) suffix hcall
  · rw [hzSubtypePut]
    exact hsample

/-- Almost every pair point satisfies the full actual prefix and insertion
identities. In particular, the selected replacement cannot change any
strictly earlier own history or the literal evidence prefix ending at `t`. -/
theorem ae_pairLaw_chronological_support
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : RenewalBase rate rewards C_star C_h u t ×
      Source rate rewards C_star C_h u t ∂pairLaw rate rewards C_star C_h u t,
    let z := b.1.1
    let a := b.1.2
    let z' := b.2
    z'.val.1.1 = z.val.1.1 ∧
    z'.val.2 = z.val.2 ∧
    ReferenceFirstCollectionRenewalVectorInsertion.q z'.val =
      ReferenceFirstCollectionRenewalVectorInsertion.q z.val ∧
    (∀ j, j ≠ ReferenceFirstCollectionRenewalVectorInsertion.q z.val →
      z'.val.1.2 j = z.val.1.2 j) ∧
    (z'.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).1 =
      (z.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).1 ∧
    (∀ r : Fin p.T, r ≠ t →
      (z'.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).2 r =
        (z.val.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q z.val)).2 r) ∧
    (∀ label : Bandits.Support.LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (ReferenceFirstCollectionRenewalVectorInsertion.c t z'.val).1 label.val =
        (ReferenceFirstCollectionRenewalVectorInsertion.c t z.val).1 label.val) ∧
    (ReferenceFirstCollectionRenewalVectorInsertion.c t z'.val).2 =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t z.val).2 ∧
    ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z'.val =
        some (u, (t, ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t z)) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t z =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t z' ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t z.val =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
          rate rewards C_star C_h t z'.val ∧
    (∀ player : Fin p.m, ∀ v : Fin p.T, v.val < t.val →
      ReferenceCompletePhysicalHistory.completeOwnHistory
          rate z.val rewards C_star C_h player v =
        ReferenceCompletePhysicalHistory.completeOwnHistory
          rate z'.val rewards C_star C_h player v) ∧
    (∃ n : ℕ,
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + n =
        t.val ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.val rewards C_star C_h).take n).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z'.val rewards C_star C_h).take n).map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z a =
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z' a := by
  have hrange : ∀ᵐ b : RenewalBase rate rewards C_star C_h u t ×
      Source rate rewards C_star C_h u t ∂pairLaw rate rewards C_star C_h u t,
      b ∈ Set.range (pair rate rewards C_star C_h u t) := by
    change ∀ᵐ b ∂(renewalLiftLaw rate rewards C_star C_h u t).map
      (pair rate rewards C_star C_h u t), _
    exact MeasureTheory.ae_map_mem_range
      (measurableSet_range_pair rate rewards C_star C_h u t)
      (measurable_pair rate rewards C_star C_h u t).aemeasurable
  filter_upwards [hrange] with b hb
  rcases hb with ⟨wv, rfl⟩
  rcases wv with ⟨⟨z, a⟩, v⟩
  simpa only [pair] using
    inserted_source_chronology rate rewards C_star C_h u t z a v

private theorem ae_map_exists_preimage
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : MeasurableEmbedding f)
    {P : α → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ y ∂μ.map f, ∃ x, f x = y ∧ P x := by
  have hbad : μ {x | ¬P x} = 0 := MeasureTheory.ae_iff.mp hP
  obtain ⟨N, hN, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hbad
  have himageMeas : MeasurableSet (f '' N) := hf.measurableSet_image' hNmeas
  have himageZero : (μ.map f) (f '' N) = 0 := by
    rw [hf.map_apply μ (f '' N), hf.injective.preimage_image]
    exact hNzero
  have hrangeZero : (μ.map f) (Set.range f)ᶜ = 0 := by
    rw [hf.map_apply μ (Set.range f)ᶜ]
    simp
  have hdisj : Disjoint (f '' N) (Set.range f)ᶜ := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨x, hx, rfl⟩ hy
    exact hy ⟨x, rfl⟩
  have hcoverZero : (μ.map f) ((f '' N) ∪ (Set.range f)ᶜ) = 0 := by
    rw [measure_union hdisj hf.measurableSet_range.compl, himageZero, hrangeZero]
    simp
  have hgood : ((f '' N) ∪ (Set.range f)ᶜ)ᶜ ∈ ae (μ.map f) :=
    MeasureTheory.compl_mem_ae_iff.mpr hcoverZero
  filter_upwards [hgood] with y hy
  have hyImage : y ∉ f '' N := fun h => hy (Or.inl h)
  have hyRangeCompl : y ∉ (Set.range f)ᶜ := fun h => hy (Or.inr h)
  have hyRange : y ∈ Set.range f := by
    by_contra hy
    exact hyRangeCompl hy
  rcases hyRange with ⟨x, rfl⟩
  refine ⟨x, rfl, ?_⟩
  by_contra hPx
  apply hyImage
  exact ⟨x, hN (by simpa using hPx), rfl⟩

/-- On the same pair-law support, the actual inserted-source witness gives
the real successful local start, clock-data installation, selection, and
literal physical post-choice computation. All slow-set fields are identified
with the draw from the original whole auxiliary array. -/
theorem ae_pairLaw_actual_installation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : RenewalBase rate rewards C_star C_h u t ×
      Source rate rewards C_star C_h u t ∂pairLaw rate rewards C_star C_h u t,
    let z := b.1.1
    let a := b.1.2
    let z' := b.2
    let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t z a
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t z',
      let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved
      let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
        CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
      let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
        x.payload ell d.instruction d.out d.reconstruction_eq
      let v := LaterAssignmentStartOperation.ownAssignmentVector
        d.record.input.row d.instruction.time
      let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart
          x.payload ell d.instruction x.row,
          ∃ hlocal : output.localConsistency = consistent,
            LaterAssignmentStartOperation.laterAssignmentStart
                x.payload ell d.instruction x.row consistent =
              .success output hlocal ∧
            v = output.assignmentVector ∧
            output.reconstruction = d.out ∧
            AssignmentParameterFibreKernel.successfulSlowSet p par v =
              some output.slowSet ∧
            output.slowSet = U ∧
            output.payload.slowSet = U ∧
            let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                output := {
              priorClock := x.clock
              pending := x.ledger.pending
              proposalParameterValid := d.core.clock_parameter_valid
              priorClockValid := d.core.clock_registers_valid
              startTimeValid := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  d.instruction_time] using d.core.clock_start_time_valid
              result := d.started
              startRound_eq := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  ReferenceActivePhysicalStep.collectionClock,
                  d.instruction_time] using d.clock_eq
              assignmentStart_eq := d.instruction_eq
              priorSigma_eq := d.core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                calc
                  x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                  _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                  _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
            let installed := CoordinatorAssignmentRegisterInstall.installLater
              output clockData
            installed.registers.payload = output.payload ∧
            output.assignmentVector = installed.assignmentVector ∧
            installed.reconstruction = d.out ∧
            installed.registers.payload.anchor =
              AssignmentScoreReconstruction.currentWeight d.out ∧
            (∀ arm, installed.registers.payload.queues arm =
              AssignmentScoreReconstruction.initialQueue d.out arm) ∧
            (∀ i, installed.retainedBaseScore i =
              AssignmentScoreReconstruction.sourceScore d.out
                (output.payload.assignment.assigned i)) ∧
            installed.registers.payload.slowSet = U ∧
            ∃ selection : CoordinatorRoundDispatch.ArmSelection
                installed.registers.payload d.started d.instruction.time
                installed.registers.complementWeights d.record.input.row,
              CoordinatorLocalArmChoice.coordinatorArmChoice
                  installed.registers.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.instruction.time installed.registers.complementWeights d.record.input.row =
                some selection.arm ∧
              CoordinatorRoundDispatch.dispatchCollection x =
                .laterChosen d.core consistent d.started d.clock_eq d.instruction
                  d.instruction_eq output hlocal clockData installed selection ∧
              d.record.output.preparation =
                ReferenceActivePhysicalStep.prepare d.record.input ∧
              d.record.output.preparation.coordinator =
                .collection d.old d.ledger clock u
                  (CoordinatorRoundDispatch.dispatchCollection x) ∧
              d.record.output.preparation.coordinator.arm = selection.arm ∧
              d.record.output.coordinator =
                ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started ∧
              d.record.output.next.coordinator =
                (ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started).configuration := by
  have hsource :=
    ReferenceFirstCollectionRenewalSampleInstallation.ae_renewalLiftLaw_inserted_installation
      rate rewards C_star C_h u t
  have hpair := ae_map_exists_preimage
    (pair_measurableEmbedding rate rewards C_star C_h u t) hsource
  filter_upwards [hpair] with b hb
  rcases hb with ⟨wv, hpairEq, hinstalled⟩
  subst b
  dsimp only at hinstalled
  rcases hinstalled with ⟨d, consistent, output, hlocal, hstart, hv, houtputVector,
    hrec, hsample, hslow, hpayloadSlow, htail⟩
  let z := wv.1.1
  let a := wv.1.2
  let z' := ReferenceFirstCollectionRenewalVectorInsertion.put
    rate rewards C_star C_h u t z wv.2
  let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
    rate rewards C_star C_h u t z a
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
    CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
    x.payload ell d.instruction d.out d.reconstruction_eq
  let v := LaterAssignmentStartOperation.ownAssignmentVector
    d.record.input.row d.instruction.time
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  have hdraw := inserted_source_chronology rate rewards C_star C_h u t z a wv.2
  dsimp only [z, a, z'] at hdraw
  rcases hdraw with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, haux⟩
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have htailPayload := htail.1
  have htailInstalledVector := htail.2.1
  have htailReconstruction := htail.2.2.1
  have hanchor := htail.2.2.2.1
  have hqueues := htail.2.2.2.2.1
  have hbase := htail.2.2.2.2.2.1
  have htailSlow := htail.2.2.2.2.2.2.1
  have hselection := htail.2.2.2.2.2.2.2
  have hvOutput : v = output.assignmentVector := hv.trans houtputVector.symm
  have houtputInstalled : output.assignmentVector = installed.assignmentVector :=
    houtputVector.trans htailInstalledVector.symm
  have hslowOriginal : output.slowSet = U := hslow.trans haux.symm
  have hpayloadOriginal : output.payload.slowSet = U := hpayloadSlow.trans haux.symm
  have htailSlowOriginal : installed.registers.payload.slowSet = U := htailSlow.trans haux.symm
  exact ⟨d, consistent, output, hlocal, hstart, hvOutput, hrec, hsample,
    hslowOriginal, hpayloadOriginal, htailPayload, houtputInstalled,
    htailReconstruction, hanchor, hqueues, hbase, htailSlowOriginal, hselection⟩

end Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling

end
