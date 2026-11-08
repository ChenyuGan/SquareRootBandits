/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSBandits.Support.ReferenceFirstCollectionRenewalFibreExtension.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalInstalledServiceTail
public import Bandits.Support.ReferenceFirstLiveAllArmAcceptedConditionalMoments

/-!
# Retained non-assignment controls at the first renewal call

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/05_binary_transport.tex:352-423`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-215`.

On the actual first-renewal pair law, the selected-row suffix erasure, the
whole original auxiliary array, both complete assignment vectors, and the
inserted current-row non-assignment remainder are kept as literal source
coordinates. The renewal event restriction and assignment fibre kernel are
transported through that erasure. The resulting remainder has its original
scalar-affine product law independently of all retained coordinates, including
the original auxiliary array. No conditional recording law or manuscript
filtration is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
open Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension
open Bandits.Support.ReferenceFirstCollectionRenewalPastLocality
open Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion
open Bandits.Support.ReferenceSourceCurrentControlFreshness
open Bandits.Support.LaunchAssignmentCoordinateSplit
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds
open Bandits.Support.AssignmentParameterFibreKernel
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.ReferenceCompletePhysicalHistory

namespace Bandits.Support.ReferenceFirstCollectionRenewalControlFactor

abbrev Params := Bandits.Support.ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := Bandits.Support.ContinuousLearningRows.TimeControl

local instance sourceInputMeasurableSpace (p : Params) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Params}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : TimeControl p)

abbrev Source {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.Source
    rate rewards C_star C_h u t

abbrev RenewalBase {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
    rate rewards C_star C_h u t

abbrev Pair {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) := RenewalBase rate rewards C_star C_h u t ×
  Source rate rewards C_star C_h u t

abbrev AuxiliaryArray (p : Params) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.AuxiliaryArray p

abbrev AssignmentVector (p : Params) := CheckedAssignmentSample.AssignmentVector p

abbrev Remainder (p : Params) :=
  LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
    ContinuousLearningRows.AffineSamples p

abbrev RetainedCoordinates (p : Params) :=
  (((BootstrapPrivateRoundStreams.SourceInput p × AuxiliaryArray p) ×
      AssignmentVector p) × AssignmentVector p)

abbrev RetainedBase {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ((Source rate rewards C_star C_h u t × AssignmentVector p) ×
      AuxiliaryArray p)

abbrev RetainedBaseAndRemainder {p : Params} (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (u t : Fin p.T) :=
  RetainedBase rate rewards C_star C_h u t ×
  Remainder p


private abbrev X {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) := RetainedBase rate rewards C_star C_h u t

private abbrev V (p : Params) := AssignmentVector p

private abbrev O (p : Params) := Remainder p

private abbrev H (p : Params) := RetainedCoordinates p

private def erasedRenewalSource (z : Source rate rewards C_star C_h u t) :
    Source rate rewards C_star C_h u t :=
  Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix rate rewards C_star C_h u t z (fun _ => control0)

private theorem erasedRenewalSource_val
    (z : Source rate rewards C_star C_h u t) :
    (erasedRenewalSource rate rewards C_star C_h u t control0 z).val =
      Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val := by
  rw [erasedRenewalSource, Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix_val]
  rfl

private abbrev retainedBaseCoordinateLaw {p : Params} (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (u t : Fin p.T)
    (control0 : TimeControl p) :=
  (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t).map
      (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)

private abbrev retainedRemainderLaw (p : Params) :=
  (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)

private theorem renewalEvent_iff_erased
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    source ∈ Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
      Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t p control0 t source ∈
        Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t := by
  simpa [Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t] using
    (Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h source u t (fun _ => control0))

private theorem erased_strict_own_history
    (z : Source rate rewards C_star C_h u t) (player : Fin p.m)
    (v : Fin p.T) (hv : v.val < t.val) :
    ReferenceCompletePhysicalHistory.completeOwnHistory rate z.val rewards
        C_star C_h player v =
      ReferenceCompletePhysicalHistory.completeOwnHistory rate
        (erasedRenewalSource rate rewards C_star C_h u t control0 z).val
        rewards C_star C_h player v := by
  rw [erasedRenewalSource_val]
  exact Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.strict_past_own_history_of_replaceSelectedControlSuffix
    rate rewards C_star C_h z.val t (fun _ => control0) player v hv

private def selectedControl (source : BootstrapPrivateRoundStreams.SourceInput p) :
    TimeControl p := Bandits.Support.ReferenceSourceCurrentControlFreshness.u_t p t source

private theorem measurable_selectedControl :
    Measurable (selectedControl (p := p) t) := by
  exact Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_u_t t

private theorem measurable_selectedVector :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t source) := by
  have hq : Measurable (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.q (p := p)) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hrows : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p => source.1.2) :=
    measurable_snd.comp (measurable_fst : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p => source.1))
  have hbranch : ∀ j : Fin (ConstructorDimensions.M p),
      Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        source.1.2 j) := by
    intro j
    exact (measurable_pi_apply j).comp hrows
  have hselected : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        source.1.2 (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.q source)) :=
    (measurable_from_prod_countable_right
      (f := fun z : Fin (ConstructorDimensions.M p) ×
          BootstrapPrivateRoundStreams.SourceInput p => z.2.1.2 z.1) hbranch).comp
      (hq.prodMk measurable_id)
  change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
    LaterAssignmentStartOperation.ownAssignmentVector
      (source.1.2 (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.q source)) t)
  exact (LaterAssignmentStartMeasurability.measurable_ownAssignmentVector t).comp
    hselected

private theorem measurable_erasedRenewalSource :
    Measurable (erasedRenewalSource rate rewards C_star C_h u t control0) := by
  apply Measurable.subtype_mk
  change Measurable (Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t
    p control0 t ∘ Subtype.val)
  exact (Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_c_t
    (p := p) control0 t).comp measurable_subtype_coe

private def sourceRemainder (z : Source rate rewards C_star C_h u t) : O p :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)).2

private theorem measurable_sourceRemainder :
    Measurable (fun z : Source rate rewards C_star C_h u t =>
      sourceRemainder rate rewards C_star C_h u t z) := by
  exact measurable_snd.comp
    ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable.comp
      ((measurable_selectedControl (p := p) (t := t)).comp
        measurable_subtype_coe))

private theorem sourceRemainder_put
    (z : Source rate rewards C_star C_h u t) (v : V p) :
    sourceRemainder rate rewards C_star C_h u t
        (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v) =
      sourceRemainder rate rewards C_star C_h u t z := by
  rw [sourceRemainder, sourceRemainder, Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.put_val]
  apply Prod.ext
  · apply funext
    intro label
    rw [Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.currentControl_insert]
    rw [Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.controlAssignmentSplit_ctrl]
  · rw [Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.currentControl_insert]
    rw [Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.controlAssignmentSplit_ctrl]

private theorem renewalSource_map_erased_currentControl :
    (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
          Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)) =
      ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let Evt := Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t
  let pref := Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let ctl := selectedControl (p := p) t
  have hEvtMeas : MeasurableSet Evt :=
    Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t
  have hpre : Evt = pref ⁻¹' Evt := by
    ext source
    exact renewalEvent_iff_erased rate rewards C_star C_h u t control0 source
  have hpairMeas : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (pref source, ctl source)) :=
    (Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_c_t (p := p) control0 t).prodMk
      (measurable_selectedControl (p := p) (t := t))
  have hpairPre :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        (pref source, ctl source)) ⁻¹' (Evt ×ˢ Set.univ) = Evt := by
    ext source
    change ((pref source, ctl source) ∈ Evt ×ˢ Set.univ) ↔ source ∈ Evt
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    have hmem := congrArg (fun event => source ∈ event) hpre
    exact Iff.of_eq (by simpa only [Set.mem_preimage] using hmem.symm)
  have hpairFresh :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        (pref source, ctl source)) =
        (fun source =>
          (Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t p control0 t source,
            Bandits.Support.ReferenceSourceCurrentControlFreshness.u_t p t source)) := by
    funext source
    rfl
  have hraw : (μ.restrict Evt).map (fun source => (pref source, ctl source)) =
      ((μ.map pref).restrict Evt).prod
        (ContinuousLearningRows.timeControlLaw p) := by
    calc
      _ = (μ.map (fun source => (pref source, ctl source))).restrict
          (Evt ×ˢ Set.univ) := by
        rw [Measure.restrict_map hpairMeas (hEvtMeas.prod MeasurableSet.univ), hpairPre]
      _ = ((μ.map pref).prod (ContinuousLearningRows.timeControlLaw p)).restrict
          (Evt ×ˢ Set.univ) := by
        have hfresh := Bandits.Support.ReferenceSourceCurrentControlFreshness.source_joint_prefix_control
          (p := p) control0 t
        rw [hpairFresh]
        simpa [pref] using
          congrArg (fun m => m.restrict (Evt ×ˢ Set.univ)) hfresh
      _ = ((μ.map pref).restrict Evt).prod
          (ContinuousLearningRows.timeControlLaw p) := by
        rw [← Measure.prod_restrict Evt Set.univ, Measure.restrict_univ]
  have hprefixVal :
      ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (erasedRenewalSource rate rewards C_star C_h u t control0)).map
        Subtype.val = (μ.map pref).restrict Evt := by
    calc
      _ = (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (fun z => pref z.val) := by
        have hmap :
            ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
              (erasedRenewalSource rate rewards C_star C_h u t control0)).map Subtype.val =
              (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
                (Subtype.val ∘ erasedRenewalSource rate rewards C_star C_h u t control0) :=
          Measure.map_map measurable_subtype_coe
            (measurable_erasedRenewalSource rate rewards C_star C_h u t control0)
        have hfunctions :
            (fun z : Source rate rewards C_star C_h u t =>
              (erasedRenewalSource rate rewards C_star C_h u t control0 z).val) =
            (fun z => pref z.val) := by
          funext z
          exact erasedRenewalSource_val rate rewards C_star C_h u t control0 z
        exact hmap.trans (congrArg
          (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).map f) hfunctions)
      _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          Subtype.val).map pref := by
        have hcompose : (fun z : Source rate rewards C_star C_h u t => pref z.val) =
            pref ∘ Subtype.val := rfl
        rw [hcompose, Measure.map_map
          (Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_c_t
            (p := p) control0 t) measurable_subtype_coe]
      _ = (μ.restrict Evt).map pref := by
        rw [Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val]
      _ = (μ.map pref).restrict Evt := by
        have hrestrict : μ.restrict Evt = μ.restrict (pref ⁻¹' Evt) :=
          congrArg (fun event : Set (BootstrapPrivateRoundStreams.SourceInput p) =>
            μ.restrict event) hpre
        calc
          _ = (μ.restrict (pref ⁻¹' Evt)).map pref :=
            congrArg (fun measure => measure.map pref) hrestrict
          _ = (μ.map pref).restrict Evt :=
            (Measure.restrict_map
              (Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_c_t
                (p := p) control0 t) hEvtMeas).symm
  have hvalJoint :
      ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
          Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))).map (Prod.map Subtype.val id) =
        ((μ.map pref).restrict Evt).prod
          (ContinuousLearningRows.timeControlLaw p) := by
    calc
      _ = (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (fun z => (pref z.val, ctl z.val)) := by
        change ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).map
            (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
              Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))).map
            (fun z => (z.1.val, z.2)) = _
        have hmap :
            ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
              (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
                Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))).map
              (fun z => (z.1.val, z.2)) =
              (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
                ((fun z => (z.1.val, z.2)) ∘
                  (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
                    Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))) :=
          Measure.map_map
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
          ((measurable_erasedRenewalSource rate rewards C_star C_h u t control0).prodMk
            ((measurable_selectedControl (p := p) (t := t)).comp measurable_subtype_coe))
        have hfunctions :
            (fun z : Source rate rewards C_star C_h u t =>
              ((erasedRenewalSource rate rewards C_star C_h u t control0 z).val,
                Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)) =
            (fun z => (pref z.val, ctl z.val)) := by
          funext z
          exact Prod.ext
            (erasedRenewalSource_val rate rewards C_star C_h u t control0 z) rfl
        exact hmap.trans (congrArg
          (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).map f) hfunctions)
      _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          Subtype.val).map (fun source => (pref source, ctl source)) := by
        rw [Measure.map_map hpairMeas measurable_subtype_coe]
        rfl
      _ = (μ.restrict Evt).map (fun source => (pref source, ctl source)) := by
        rw [Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val]
      _ = _ := hraw
  have hrightMapped :
      (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
          (ContinuousLearningRows.timeControlLaw p)).map
        (Prod.map Subtype.val id) =
        ((μ.map pref).restrict Evt).prod
          (ContinuousLearningRows.timeControlLaw p) := by
    calc
      _ = (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).map
          (erasedRenewalSource rate rewards C_star C_h u t control0)).map Subtype.val).prod
          ((ContinuousLearningRows.timeControlLaw p).map id) :=
        (Measure.map_prod_map
          ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).map
            (erasedRenewalSource rate rewards C_star C_h u t control0))
          (ContinuousLearningRows.timeControlLaw p)
          measurable_subtype_coe measurable_id).symm
      _ = _ := by rw [Measure.map_id, hprefixVal]
  exact ((MeasurableEmbedding.subtype_coe hEvtMeas).prodMap
      (MeasurableEmbedding.id (α := TimeControl p))).map_injective
    (hvalJoint.trans hrightMapped.symm)

private theorem renewalSource_map_erased_split :
    (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (fun z => ((erasedRenewalSource rate rewards C_star C_h u t control0 z,
            Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t z.val),
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)).2)) =
      (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
        (ContinuousControlSlice.assignmentLaw p.K)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)) := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let μp := (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
    (erasedRenewalSource rate rewards C_star C_h u t control0)
  have hjoint := renewalSource_map_erased_currentControl
    rate rewards C_star C_h u t control0
  have hsplit := (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv
    p).map_eq
  have hmap :
      (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
          e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))) =
        μp.prod ((ContinuousControlSlice.assignmentLaw p.K).prod
          ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
            (ContinuousLearningRows.affineSamplesLaw p)) ) := by
    calc
      _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
            Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))).map (Prod.map id e) := by
        have hmap :
            ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
              (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
                Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))).map
              (Prod.map id e) =
              (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).map
              ((Prod.map id e) ∘
                (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
                  Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))) :=
          Measure.map_map (measurable_id.prodMap e.measurable)
          ((measurable_erasedRenewalSource rate rewards C_star C_h u t control0).prodMk
            ((measurable_selectedControl (p := p) (t := t)).comp measurable_subtype_coe))
        simpa only [Function.comp_def, Prod.map_apply', id_def] using hmap.symm
      _ = (μp.prod (ContinuousLearningRows.timeControlLaw p)).map
          (Prod.map id e) := by rw [hjoint]
      _ = _ := by
        rw [← Measure.map_prod_map μp (ContinuousLearningRows.timeControlLaw p)
          measurable_id e.measurable, Measure.map_id, hsplit]
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μp (ContinuousControlSlice.assignmentLaw p.K)
      ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
        (ContinuousLearningRows.affineSamplesLaw p)))
  have hcoordinates :
      (fun z => ((erasedRenewalSource rate rewards C_star C_h u t control0 z,
          Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t z.val), (e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)).2)) =
        (fun z => MeasurableEquiv.prodAssoc.symm
          ((erasedRenewalSource rate rewards C_star C_h u t control0 z,
            e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)))) := by
    funext z
    rw [Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av_eq_controlSplit t z.val]
    rfl
  calc
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
        (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
          e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)))).map MeasurableEquiv.prodAssoc.symm := by
      have hpairMeas : Measurable (fun z : Source rate rewards C_star C_h u t =>
          (erasedRenewalSource rate rewards C_star C_h u t control0 z,
            e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val))) :=
        (measurable_erasedRenewalSource rate rewards C_star C_h u t control0).prodMk
          (e.measurable.comp
            ((measurable_selectedControl (p := p) (t := t)).comp measurable_subtype_coe))
      have hmapAssoc :
          ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t).map
            (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
              e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)))).map
              MeasurableEquiv.prodAssoc.symm =
          (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t).map
            (MeasurableEquiv.prodAssoc.symm ∘
              (fun z => (erasedRenewalSource rate rewards C_star C_h u t control0 z,
                e (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t z.val)))) :=
        Measure.map_map hassoc.measurable hpairMeas
      have hfunctions := congrArg
        (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).map f) hcoordinates
      exact hfunctions.trans hmapAssoc.symm
    _ = ((μp.prod (ContinuousControlSlice.assignmentLaw p.K)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p))) := by
      have hmapAssoc := congrArg (fun measure => measure.map MeasurableEquiv.prodAssoc.symm) hmap
      exact hmapAssoc.trans hassoc.map_eq

public def retainedControlCoordinates
    (b : Pair rate rewards C_star C_h u t) : RetainedCoordinates p :=
  (((Bandits.Support.ReferenceSourceCurrentControlFreshness.c_t p control0 t b.1.1.val, b.1.2), Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t b.1.1.val),
    Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val)

public def insertedControlRemainder
    (b : Pair rate rewards C_star C_h u t) : Remainder p :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val)).2

private theorem measurable_retainedControlCoordinates :
    Measurable (retainedControlCoordinates rate rewards C_star C_h u t control0) := by
  have hbase : Measurable
      (fun b : Pair rate rewards C_star C_h u t => b.1.1.val) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  have hprefix := (Bandits.Support.ReferenceSourceCurrentControlFreshness.measurable_c_t (p := p) control0 t).comp hbase
  have haux : Measurable
      (fun b : Pair rate rewards C_star C_h u t => b.1.2) :=
    measurable_snd.comp measurable_fst
  have hv0 := (measurable_selectedVector (p := p) (t := t)).comp hbase
  have hv1 : Measurable (fun b : Pair rate rewards C_star C_h u t => Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) :=
    (measurable_selectedVector (p := p) (t := t)).comp
      (measurable_subtype_coe.comp measurable_snd)
  exact (((hprefix.prodMk haux).prodMk hv0).prodMk hv1)

private theorem measurable_insertedControlRemainder :
    Measurable (insertedControlRemainder rate rewards C_star C_h u t) := by
  exact measurable_snd.comp
    ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable.comp
      ((measurable_selectedControl (p := p) (t := t)).comp
        (measurable_subtype_coe.comp measurable_snd)))

private def sourceCoordinates (z : Source rate rewards C_star C_h u t) :
    (Source rate rewards C_star C_h u t × V p) × O p :=
  ((erasedRenewalSource rate rewards C_star C_h u t control0 z, Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av t z.val),
    sourceRemainder rate rewards C_star C_h u t z)

private theorem measurable_sourceCoordinates :
    Measurable (sourceCoordinates rate rewards C_star C_h u t control0) := by
  exact ((measurable_erasedRenewalSource rate rewards C_star C_h u t control0).prodMk
      ((measurable_selectedVector (p := p) (t := t)).comp measurable_subtype_coe)).prodMk
    (measurable_sourceRemainder rate rewards C_star C_h u t)

private def moveAuxCoordinate
    (z : ((Source rate rewards C_star C_h u t × V p) × O p) × AuxiliaryArray p) :
    ((Source rate rewards C_star C_h u t × V p) × AuxiliaryArray p) × O p :=
  ((z.1.1, z.2), z.1.2)

private theorem measurable_moveAuxCoordinate :
    Measurable (moveAuxCoordinate rate rewards C_star C_h u t) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private def baseCoordinates (b : RenewalBase rate rewards C_star C_h u t) :
    RetainedBaseAndRemainder rate rewards C_star C_h u t :=
  moveAuxCoordinate rate rewards C_star C_h u t (sourceCoordinates
    rate rewards C_star C_h u t control0 b.1, b.2)

private theorem measurable_baseCoordinates :
    Measurable (baseCoordinates rate rewards C_star C_h u t control0) := by
  exact (measurable_moveAuxCoordinate rate rewards C_star C_h u t).comp
    (((measurable_sourceCoordinates rate rewards C_star C_h u t control0).comp
        measurable_fst).prodMk measurable_snd)

private def retainedAssignmentKernel :
    ProbabilityTheory.Kernel (X rate rewards C_star C_h u t) (V p) :=
  Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t |>.comap
    (fun x : X rate rewards C_star C_h u t => (x.1.1, x.2))
    (show Measurable (fun x : X rate rewards C_star C_h u t => (x.1.1, x.2)) from by
      exact (measurable_fst.comp measurable_fst).prodMk measurable_snd)

private instance retainedAssignmentKernel_markov :
    ProbabilityTheory.IsMarkovKernel
      (retainedAssignmentKernel rate rewards C_star C_h u t) := by
  unfold retainedAssignmentKernel
  infer_instance

private def retainedAssignmentKernelOnBase :
    ProbabilityTheory.Kernel
      (X rate rewards C_star C_h u t × O p) (V p) :=
  (retainedAssignmentKernel rate rewards C_star C_h u t).comap Prod.fst measurable_fst

private instance retainedAssignmentKernelOnBase_markov :
    ProbabilityTheory.IsMarkovKernel
      (retainedAssignmentKernelOnBase rate rewards C_star C_h u t) := by
  unfold retainedAssignmentKernelOnBase
  infer_instance

private theorem renewalKernel_eq_erasedKernel :
    Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t =
      (retainedAssignmentKernelOnBase rate rewards C_star C_h u t).comap
        (baseCoordinates rate rewards C_star C_h u t control0)
        (measurable_baseCoordinates rate rewards C_star C_h u t control0) := by
  ext b s hs
  let suffix : Fin p.T → TimeControl p := fun _ => control0
  have hparameter := Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.renewalCallParameter_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t b.1 suffix
  have hsample := Bandits.Support.ReferenceFirstCollectionRenewalPastLocality.renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t b.1 suffix b.2
  rw [Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply,
    Kernel.comap_apply, retainedAssignmentKernelOnBase, Kernel.comap_apply,
    retainedAssignmentKernel, Kernel.comap_apply,
    Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel_apply]
  simp only [baseCoordinates, moveAuxCoordinate, sourceCoordinates,
    erasedRenewalSource]
  rw [← hparameter, ← hsample]

private theorem map_comap_compProd_finite
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : ProbabilityTheory.Kernel β γ)
    [ProbabilityTheory.IsMarkovKernel κ] (f : α → β) (hf : Measurable f) :
    (μ.compProd (κ.comap f hf)).map (Prod.map f id) =
      (μ.map f).compProd κ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  have hpre : (Prod.map f id) ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ×ˢ t := by
    ext z
    simp
  rw [hpre, Measure.compProd_apply_prod (hs.preimage hf) ht,
    Measure.compProd_apply_prod hs ht]
  simp_rw [Kernel.comap_apply]
  exact (MeasureTheory.setLIntegral_map hs
    (ProbabilityTheory.Kernel.measurable_coe κ ht) hf).symm

private theorem compProd_independent_remainder
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsFiniteMeasure μ] (ρ : Measure β) [IsProbabilityMeasure ρ]
    (κ : ProbabilityTheory.Kernel α γ) [ProbabilityTheory.IsMarkovKernel κ] :
    (((μ.prod ρ).compProd (κ.comap Prod.fst measurable_fst)).map
        (fun z : (α × β) × γ => ((z.1.1, z.2), z.1.2))) =
      (μ.compProd κ).prod ρ := by
  let κfirst : ProbabilityTheory.Kernel (α × β) γ :=
    κ.comap Prod.fst measurable_fst
  let κsecond : ProbabilityTheory.Kernel (α × γ) β :=
    ProbabilityTheory.Kernel.const (α × γ) ρ
  let reorder : (α × β) × γ → (α × γ) × β :=
    fun z => ((z.1.1, z.2), z.1.2)
  have hmeasReorder : Measurable reorder := by fun_prop
  have hleftKernel :
      (ProbabilityTheory.Kernel.const α ρ ⊗ₖ κfirst) =
        (κ ×ₖ ProbabilityTheory.Kernel.const α ρ).map Prod.swap := by
    apply ProbabilityTheory.Kernel.ext
    intro x
    apply Measure.ext_prod
    intro a b ha hb
    rw [ProbabilityTheory.Kernel.compProd_apply_prod ha hb,
      ProbabilityTheory.Kernel.map_apply _ measurable_swap x,
      Measure.map_apply measurable_swap (ha.prod hb),
      Set.preimage_swap_prod,
      ProbabilityTheory.Kernel.prod_apply_prod]
    simp [κfirst, ProbabilityTheory.Kernel.comap_apply,
      ProbabilityTheory.Kernel.const_apply, mul_comm]
  have hrightKernel :
      (κ ⊗ₖ κsecond) = κ ×ₖ ProbabilityTheory.Kernel.const α ρ := by
    apply ProbabilityTheory.Kernel.ext
    intro x
    apply Measure.ext_prod
    intro a b ha hb
    rw [ProbabilityTheory.Kernel.compProd_apply_prod ha hb,
      ProbabilityTheory.Kernel.prod_apply_prod]
    simp [κsecond, ProbabilityTheory.Kernel.const_apply, mul_comm]
  have hcompose : reorder ∘ MeasurableEquiv.prodAssoc.symm =
      MeasurableEquiv.prodAssoc.symm ∘ (Prod.map id Prod.swap) := by
    funext z
    rcases z with ⟨x, ⟨b, c⟩⟩
    rfl
  calc
    _ = ((μ.compProd (ProbabilityTheory.Kernel.const α ρ)).compProd κfirst).map
        reorder := by
      rw [Measure.compProd_const]
    _ = (μ.compProd (ProbabilityTheory.Kernel.const α ρ ⊗ₖ κfirst)).map
        (MeasurableEquiv.prodAssoc.symm ∘ (Prod.map id Prod.swap)) := by
      rw [← Measure.compProd_assoc]
      rw [Measure.map_map hmeasReorder (by fun_prop)]
      exact congrArg
        (fun f => (μ.compProd
          (ProbabilityTheory.Kernel.const α ρ ⊗ₖ κfirst)).map f) hcompose
    _ = (μ.compProd ((κ ×ₖ ProbabilityTheory.Kernel.const α ρ).map Prod.swap)).map
        (MeasurableEquiv.prodAssoc.symm ∘ (Prod.map id Prod.swap)) := by
      rw [hleftKernel]
    _ = (μ.compProd (κ ×ₖ ProbabilityTheory.Kernel.const α ρ)).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.compProd_map measurable_swap]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg
        (fun f => (μ.compProd
          (κ ×ₖ ProbabilityTheory.Kernel.const α ρ)).map f)
      funext z
      rcases z with ⟨x, ⟨b, c⟩⟩
      rfl
    _ = (μ.compProd (κ ⊗ₖ κsecond)).map MeasurableEquiv.prodAssoc.symm := by
      rw [hrightKernel]
    _ = (μ.compProd κ).compProd κsecond := by
      rw [Measure.compProd_assoc]
    _ = (μ.compProd κ).prod ρ := by
      rw [Measure.compProd_const]

private def retainedReorder
    (xv : X rate rewards C_star C_h u t × V p) : H p :=
  ((((xv.1.1.1).val, xv.1.2), xv.1.1.2), xv.2)

private theorem measurable_retainedReorder :
    Measurable (retainedReorder rate rewards C_star C_h u t) := by
  have hsource := measurable_subtype_coe.comp
    (measurable_fst.comp (measurable_fst.comp (measurable_fst :
      Measurable (fun xv : X rate rewards C_star C_h u t × V p => xv.1))))
  have haux : Measurable
      (fun xv : X rate rewards C_star C_h u t × V p => xv.1.2) :=
    measurable_snd.comp measurable_fst
  have hv0 : Measurable
      (fun xv : X rate rewards C_star C_h u t × V p => xv.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  exact (((hsource.prodMk haux).prodMk hv0).prodMk measurable_snd)

private def splitKernelCoordinates
    (z : (X rate rewards C_star C_h u t × O p) × V p) :
    (X rate rewards C_star C_h u t × V p) × O p :=
  ((z.1.1, z.2), z.1.2)

private theorem measurable_splitKernelCoordinates :
    Measurable (splitKernelCoordinates rate rewards C_star C_h u t) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private def splitReorder
    (z : (X rate rewards C_star C_h u t × O p) × V p) : H p × O p :=
  (retainedReorder rate rewards C_star C_h u t
      (splitKernelCoordinates rate rewards C_star C_h u t z).1,
    (splitKernelCoordinates rate rewards C_star C_h u t z).2)

private theorem measurable_splitReorder :
    Measurable (splitReorder rate rewards C_star C_h u t) := by
  exact (measurable_retainedReorder rate rewards C_star C_h u t).comp
      (measurable_fst.comp
        (measurable_splitKernelCoordinates rate rewards C_star C_h u t)) |>.prodMk
    (measurable_snd.comp
      (measurable_splitKernelCoordinates rate rewards C_star C_h u t))

private def liftCoordinates
    (wv : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) : H p × O p :=
  splitReorder rate rewards C_star C_h u t
    (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id wv)

private theorem measurable_liftCoordinates :
    Measurable (liftCoordinates rate rewards C_star C_h u t control0) := by
  exact (measurable_splitReorder rate rewards C_star C_h u t).comp
    ((measurable_baseCoordinates rate rewards C_star C_h u t control0).prodMap
      measurable_id)

private theorem retainedBaseLaw_factorization :
    (Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t).map
        (baseCoordinates rate rewards C_star C_h u t control0) =
      (retainedBaseCoordinateLaw rate rewards C_star C_h u t control0).prod
        (retainedRemainderLaw p) := by
  let μPV := ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
    (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
      (ContinuousControlSlice.assignmentLaw p.K)
  let μAux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let ρ := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  have hmove : MeasurePreserving (moveAuxCoordinate rate rewards C_star C_h u t)
      ((μPV.prod ρ).prod μAux)
      ((μPV.prod μAux).prod ρ) := by
    let h₁ := measurePreserving_prodAssoc μPV ρ μAux
    let h₂ : MeasurePreserving (Prod.map id Prod.swap)
        (μPV.prod (ρ.prod μAux)) (μPV.prod (μAux.prod ρ)) :=
      (MeasurePreserving.id μPV).prod
        (Measure.measurePreserving_swap (μ := ρ) (ν := μAux))
    let h₃ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μPV μAux ρ)
    have hcomp := h₃.comp (h₂.comp h₁)
    convert hcomp using 1; rfl
  have hmap :
      (Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t).map
        (fun w => (sourceCoordinates rate rewards C_star C_h u t control0 w.1, w.2)) =
      (μPV.prod ρ).prod μAux := by
    calc
      _ = (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).prod μAux).map
          (Prod.map (sourceCoordinates rate rewards C_star C_h u t control0) id)) := by
        rfl
      _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
          (sourceCoordinates rate rewards C_star C_h u t control0)).prod μAux :=
        (by simpa only [Measure.map_id] using (Measure.map_prod_map
          (Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t)
          μAux
          (measurable_sourceCoordinates rate rewards C_star C_h u t control0)
          measurable_id).symm)
      _ = _ := by
        have hsource := renewalSource_map_erased_split
          rate rewards C_star C_h u t control0
        have hprod := congrArg (fun m => m.prod μAux) hsource
        convert hprod using 1; rfl
  have hcoords :
      (fun w => baseCoordinates rate rewards C_star C_h u t control0 w) =
      moveAuxCoordinate rate rewards C_star C_h u t ∘
        (fun z => (sourceCoordinates rate rewards C_star C_h u t control0 z.1, z.2)) := by
    funext w
    rfl
  calc
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).prod μAux).map
        (fun z => baseCoordinates rate rewards C_star C_h u t control0 z) := by rfl
    _ = (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).prod μAux).map
        (fun z => (sourceCoordinates rate rewards C_star C_h u t control0 z.1, z.2))).map
        (moveAuxCoordinate rate rewards C_star C_h u t) := by
      have hfunctions := congrArg
        (fun f => ((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).prod μAux).map f) hcoords
      have hpairMeas : Measurable (fun z : RenewalBase rate rewards C_star C_h u t =>
          (sourceCoordinates rate rewards C_star C_h u t control0 z.1, z.2)) :=
        ((measurable_sourceCoordinates rate rewards C_star C_h u t control0).comp
          measurable_fst).prodMk measurable_snd
      exact hfunctions.trans (Measure.map_map hmove.measurable hpairMeas).symm
    _ = ((μPV.prod ρ).prod μAux).map
        (moveAuxCoordinate rate rewards C_star C_h u t) := by
      have hmap' := congrArg (fun m => m.map (moveAuxCoordinate rate rewards C_star C_h u t)) hmap
      simpa [Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw] using hmap'
    _ = (μPV.prod μAux).prod ρ := hmove.map_eq

private theorem liftLaw_baseFactorized :
    (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id) =
      ((retainedBaseCoordinateLaw rate rewards C_star C_h u t control0).prod
        (retainedRemainderLaw p)).compProd
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t) := by
  have hkernel := renewalKernel_eq_erasedKernel
    rate rewards C_star C_h u t control0
  calc
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t).compProd
        ((retainedAssignmentKernelOnBase rate rewards C_star C_h u t).comap
          (baseCoordinates rate rewards C_star C_h u t control0)
          (measurable_baseCoordinates rate rewards C_star C_h u t control0))).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id) := by
      change (Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw rate rewards C_star C_h u t).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id) = _
      rw [Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw, hkernel]
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t).map
        (baseCoordinates rate rewards C_star C_h u t control0)).compProd
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t) :=
      map_comap_compProd_finite
        (Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw rate rewards C_star C_h u t)
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)
        (baseCoordinates rate rewards C_star C_h u t control0)
        (measurable_baseCoordinates rate rewards C_star C_h u t control0)
    _ = _ := by
      rw [retainedBaseLaw_factorization rate rewards C_star C_h u t control0]

private theorem liftLaw_retainedCoordinates_factorized :
    (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (liftCoordinates rate rewards C_star C_h u t control0) =
      (((retainedBaseCoordinateLaw rate rewards C_star C_h u t control0).compProd
        (retainedAssignmentKernel rate rewards C_star C_h u t)).map
        (retainedReorder rate rewards C_star C_h u t)).prod
        (retainedRemainderLaw p) := by
  let μBase :=
    (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
      (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
  let ρ := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  have hbase := liftLaw_baseFactorized rate rewards C_star C_h u t control0
  have hsplit := compProd_independent_remainder μBase ρ
    (retainedAssignmentKernel rate rewards C_star C_h u t)
  have hcompose :
      splitReorder rate rewards C_star C_h u t =
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id) ∘
          splitKernelCoordinates rate rewards C_star C_h u t := by
    funext z
    rfl
  have hcoordinates :
      liftCoordinates rate rewards C_star C_h u t control0 =
        ((Prod.map (retainedReorder rate rewards C_star C_h u t) id) ∘
          splitKernelCoordinates rate rewards C_star C_h u t) ∘
          (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id) := by
    funext wv
    rfl
  have hmapCoordinates :
      (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map
        (liftCoordinates rate rewards C_star C_h u t control0) =
      (((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
          rate rewards C_star C_h u t).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
        (splitKernelCoordinates rate rewards C_star C_h u t)).map
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id) := by
    have houter : Measurable
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id ∘
          splitKernelCoordinates rate rewards C_star C_h u t) :=
      (measurable_retainedReorder rate rewards C_star C_h u t).prodMap measurable_id |>.comp
        (measurable_splitKernelCoordinates rate rewards C_star C_h u t)
    have hmiddle : Measurable (splitKernelCoordinates rate rewards C_star C_h u t) :=
      measurable_splitKernelCoordinates rate rewards C_star C_h u t
    have hbaseMap :
        ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
          (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
          (Prod.map (retainedReorder rate rewards C_star C_h u t) id ∘
            splitKernelCoordinates rate rewards C_star C_h u t) =
          (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            ((Prod.map (retainedReorder rate rewards C_star C_h u t) id ∘
              splitKernelCoordinates rate rewards C_star C_h u t) ∘
              (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)) :=
      Measure.map_map houter
        ((measurable_baseCoordinates rate rewards C_star C_h u t control0).prodMap measurable_id)
    have hsplitMap :
        (((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
            (splitKernelCoordinates rate rewards C_star C_h u t)).map
            (Prod.map (retainedReorder rate rewards C_star C_h u t) id) =
          ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
            (Prod.map (retainedReorder rate rewards C_star C_h u t) id ∘
              splitKernelCoordinates rate rewards C_star C_h u t) :=
      Measure.map_map ((measurable_retainedReorder rate rewards C_star C_h u t).prodMap measurable_id)
        hmiddle
    calc
      _ = (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (((Prod.map (retainedReorder rate rewards C_star C_h u t) id) ∘
              splitKernelCoordinates rate rewards C_star C_h u t) ∘
              (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)) :=
          congrArg
            (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
              rate rewards C_star C_h u t).map f) hcoordinates
      _ = ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
            (Prod.map (retainedReorder rate rewards C_star C_h u t) id ∘
              splitKernelCoordinates rate rewards C_star C_h u t) := hbaseMap.symm
      _ = (((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
            (splitKernelCoordinates rate rewards C_star C_h u t)).map
            (Prod.map (retainedReorder rate rewards C_star C_h u t) id) := hsplitMap.symm
  calc
    _ = (((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
        (splitKernelCoordinates rate rewards C_star C_h u t)).map
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id) := by
      exact hmapCoordinates
    _ = (((μBase.prod ρ).compProd
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map
        (splitKernelCoordinates rate rewards C_star C_h u t)).map
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id) := by
      rw [hbase]
    _ = ((μBase.compProd (retainedAssignmentKernel rate rewards C_star C_h u t)).prod ρ).map
        (Prod.map (retainedReorder rate rewards C_star C_h u t) id) := by
      have hsplit' := congrArg
        (fun measure => measure.map (Prod.map (retainedReorder rate rewards C_star C_h u t) id))
        hsplit
      convert hsplit' using 1; rfl
    _ = ((μBase.compProd (retainedAssignmentKernel rate rewards C_star C_h u t)).map
        (retainedReorder rate rewards C_star C_h u t)).prod ρ := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map
          (μBase.compProd (retainedAssignmentKernel rate rewards C_star C_h u t))
          ρ
          (measurable_retainedReorder rate rewards C_star C_h u t)
          measurable_id).symm

private theorem liftLaw_retainedMarginal :
    (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv => ((baseCoordinates rate rewards C_star C_h u t control0 wv.1).1,
          wv.2)) =
      (retainedBaseCoordinateLaw rate rewards C_star C_h u t control0).compProd
        (retainedAssignmentKernel rate rewards C_star C_h u t) := by
  let μBase :=
    (((Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map
      (erasedRenewalSource rate rewards C_star C_h u t control0)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
  let ρ := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  have hbase := liftLaw_baseFactorized rate rewards C_star C_h u t control0
  have hsplit := compProd_independent_remainder μBase ρ
    (retainedAssignmentKernel rate rewards C_star C_h u t)
  have hfst :
      (fun z : (X rate rewards C_star C_h u t × O p) × V p =>
        (z.1.1, z.2)) = Prod.fst ∘
          splitKernelCoordinates rate rewards C_star C_h u t := by
    funext z
    rfl
  calc
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
        (fun z : (X rate rewards C_star C_h u t × O p) × V p => (z.1.1, z.2)) := by
      have hmap :
          ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
            rate rewards C_star C_h u t).map
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)).map
              (fun z : (X rate rewards C_star C_h u t × O p) × V p => (z.1.1, z.2)) =
            (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
              rate rewards C_star C_h u t).map
              ((fun z : (X rate rewards C_star C_h u t × O p) × V p => (z.1.1, z.2)) ∘
                (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id)) :=
          Measure.map_map ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
            ((measurable_baseCoordinates rate rewards C_star C_h u t control0).prodMap measurable_id)
      have hfunctions :
          (fun wv : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
              rate rewards C_star C_h u t =>
            ((baseCoordinates rate rewards C_star C_h u t control0 wv.1).1, wv.2)) =
          (fun z : (X rate rewards C_star C_h u t × O p) × V p => (z.1.1, z.2)) ∘
            (Prod.map (baseCoordinates rate rewards C_star C_h u t control0) id) := by
        funext wv
        rfl
      exact (congrArg
        (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
          rate rewards C_star C_h u t).map f) hfunctions).trans hmap.symm
    _ = ((μBase.prod ρ).compProd
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map
        (fun z : (X rate rewards C_star C_h u t × O p) × V p => (z.1.1, z.2)) := by
      rw [hbase]
    _ = (((μBase.prod ρ).compProd
        (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map
        (splitKernelCoordinates rate rewards C_star C_h u t)).map Prod.fst := by
      have hmap :
          (((μBase.prod ρ).compProd
            (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map
            (splitKernelCoordinates rate rewards C_star C_h u t)).map Prod.fst =
          ((μBase.prod ρ).compProd
            (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map
            (Prod.fst ∘ splitKernelCoordinates rate rewards C_star C_h u t) :=
        Measure.map_map measurable_fst
          (measurable_splitKernelCoordinates rate rewards C_star C_h u t)
      have hfunctions := congrArg
        (fun f => ((μBase.prod ρ).compProd
          (retainedAssignmentKernelOnBase rate rewards C_star C_h u t)).map f) hfst
      exact hfunctions.trans hmap.symm
    _ = ((μBase.compProd (retainedAssignmentKernel rate rewards C_star C_h u t)).prod ρ).map
        Prod.fst := by
      have hsplit' := congrArg (fun measure => measure.map Prod.fst) hsplit
      convert hsplit' using 1; rfl
    _ = μBase.compProd (retainedAssignmentKernel rate rewards C_star C_h u t) := by
      have hρ : IsProbabilityMeasure ρ := by
        dsimp [ρ]
        infer_instance
      let := hρ
      simp [Measure.map_fst_prod]

private theorem liftRetainedCoordinates_eq_pair
    (wv : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    liftCoordinates rate rewards C_star C_h u t control0 wv =
      (retainedControlCoordinates rate rewards C_star C_h u t control0
          (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv),
        insertedControlRemainder rate rewards C_star C_h u t
          (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv)) := by
  apply Prod.ext
  · simp only [liftCoordinates, splitReorder, splitKernelCoordinates, retainedReorder,
      baseCoordinates, sourceCoordinates, moveAuxCoordinate, retainedControlCoordinates,
      Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair,
      Prod.map_apply',
      erasedRenewalSource_val,
      Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.put_val,
      Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.av_insert,
      id_def]
  · change sourceRemainder rate rewards C_star C_h u t wv.1.1 =
      sourceRemainder rate rewards C_star C_h u t
        (Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion.put
          rate rewards C_star C_h u t wv.1.1 wv.2)
    exact (sourceRemainder_put rate rewards C_star C_h u t wv.1.1 wv.2).symm

private theorem pairLaw_retainedMap_eq_kernelMap :
    (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map
        (retainedControlCoordinates rate rewards C_star C_h u t control0) =
      ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
        (fun wv => ((baseCoordinates rate rewards C_star C_h u t control0 wv.1).1,
          wv.2))).map (retainedReorder rate rewards C_star C_h u t) := by
  rw [Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw]
  let proj : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t → X rate rewards C_star C_h u t × V p :=
    fun wv => ((baseCoordinates rate rewards C_star C_h u t control0 wv.1).1, wv.2)
  have hfunctions :
      (fun wv => retainedControlCoordinates rate rewards C_star C_h u t control0
        (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t wv)) =
      retainedReorder rate rewards C_star C_h u t ∘ proj := by
    funext wv
    have hcoords := congrArg Prod.fst
      (liftRetainedCoordinates_eq_pair rate rewards C_star C_h u t control0 wv)
    simpa [proj, liftCoordinates, splitReorder, splitKernelCoordinates] using hcoords.symm
  have hmapLeft :
      ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map
        (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t)).map
        (retainedControlCoordinates rate rewards C_star C_h u t control0) =
      (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map ((retainedControlCoordinates rate rewards C_star C_h u t control0) ∘
        Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t) :=
    Measure.map_map (measurable_retainedControlCoordinates rate rewards C_star C_h u t control0)
      (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.measurable_pair
        rate rewards C_star C_h u t)
  have hbaseMeas : Measurable
      (fun wv : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
          rate rewards C_star C_h u t =>
        baseCoordinates rate rewards C_star C_h u t control0 wv.1) :=
    (measurable_baseCoordinates rate rewards C_star C_h u t control0).comp measurable_fst
  have hprojMeas : Measurable proj :=
    (measurable_fst.comp hbaseMeas).prodMk measurable_snd
  have hmapRight :
      ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map proj).map (retainedReorder rate rewards C_star C_h u t) =
      (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map (retainedReorder rate rewards C_star C_h u t ∘ proj) :=
    Measure.map_map (measurable_retainedReorder rate rewards C_star C_h u t) hprojMeas
  calc
    _ = (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map ((retainedControlCoordinates rate rewards C_star C_h u t control0) ∘
        Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair
          rate rewards C_star C_h u t) := hmapLeft
    _ = (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map (retainedReorder rate rewards C_star C_h u t ∘ proj) :=
      congrArg (fun f => (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map f) hfunctions
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map proj).map (retainedReorder rate rewards C_star C_h u t) :=
      hmapRight.symm

/-- On the actual first-renewal pair law, the inserted current-row scalar and
affine remainder keeps its original product law independently of the selected
suffix erasure, the whole auxiliary array, and both complete assignment
vectors. The proof uses the actual renewal event restriction and the actual
assignment fibre kernel, including when the restricted law has mass zero. -/
theorem pairLaw_retained_nonAssignment_product :
    (Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map
        (fun b : Pair rate rewards C_star C_h u t =>
          (retainedControlCoordinates rate rewards C_star C_h u t control0 b,
            insertedControlRemainder rate rewards C_star C_h u t b)) =
      ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t).map
        (retainedControlCoordinates rate rewards C_star C_h u t control0)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)) := by
  let law := Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
    rate rewards C_star C_h u t
  let insertPair := Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pair
    rate rewards C_star C_h u t
  let combined := fun b : Pair rate rewards C_star C_h u t =>
    (retainedControlCoordinates rate rewards C_star C_h u t control0 b,
      insertedControlRemainder rate rewards C_star C_h u t b)
  have hcombined : Measurable combined :=
    Measurable.prodMk
      (measurable_retainedControlCoordinates rate rewards C_star C_h u t control0)
      (measurable_insertedControlRemainder rate rewards C_star C_h u t)
  have hpair : Measurable insertPair :=
    Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.measurable_pair
      rate rewards C_star C_h u t
  have hfunction : combined ∘ insertPair =
      liftCoordinates rate rewards C_star C_h u t control0 := by
    funext wv
    exact (liftRetainedCoordinates_eq_pair rate rewards C_star C_h u t control0 wv).symm
  let proj := fun wv : Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t =>
    ((baseCoordinates rate rewards C_star C_h u t control0 wv.1).1, wv.2)
  calc
    _ = law.map (combined ∘ insertPair) := by
      change (law.map insertPair).map combined = _
      exact Measure.map_map hcombined hpair
    _ = law.map (liftCoordinates rate rewards C_star C_h u t control0) :=
      congrArg (fun f => law.map f) hfunction
    _ = ((law.map proj).map (retainedReorder rate rewards C_star C_h u t)).prod
        (retainedRemainderLaw p) := by
      rw [liftLaw_retainedCoordinates_factorized rate rewards C_star C_h u t control0,
        liftLaw_retainedMarginal rate rewards C_star C_h u t control0]
    _ = ((Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).map
        (retainedControlCoordinates rate rewards C_star C_h u t control0)).prod
        ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
          (ContinuousLearningRows.affineSamplesLaw p)) := by
      have hmap := pairLaw_retainedMap_eq_kernelMap rate rewards C_star C_h u t control0
      simpa [law, proj, retainedRemainderLaw] using
        congrArg (fun measure => measure.prod
          ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
            (ContinuousLearningRows.affineSamplesLaw p))) hmap.symm

end Bandits.Support.ReferenceFirstCollectionRenewalControlFactor

end
