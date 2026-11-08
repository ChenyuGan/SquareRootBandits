/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion

/-!
# The original source law after first collection renewal insertion

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The analytical extension first retains the whole original source and then
supplies an independent candidate assignment vector. On each original private
coordinator-index stratum, the first-renewal event is invariant under changing
the current selected control. Splitting that control into its assignment
vector and the remaining continuous coordinates therefore shows that
inserting a candidate with the original cube law preserves the unnormalized
restriction of the original whole-source law.

The result is internal source-law evidence for the chronological first-
collection-renewal coupling. It does not assert physical installation or close
any manuscript section.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
open Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.LaunchAssignmentCoordinateSplit
open Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalInsertedSourceLaw

private abbrev Source := BootstrapPrivateRoundStreams.SourceInput
private abbrev Vector := ReferenceLaunchAssignmentLaw.AssignmentVector
private abbrev TimeControl := ContinuousLearningRows.TimeControl

private def zeroTimeControl {p : ConstructorDimensions.Parameters} : TimeControl p :=
  (fun _ => ⟨0, by norm_num⟩, fun _ => ((fun _ => 0), 0))

private abbrev firstRenewalEvent {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set (Source p) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
    rate rewards C_star C_h u t

private def replaceControlVector {p : ConstructorDimensions.Parameters}
    (control : TimeControl p) (v : Vector p) : TimeControl p :=
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  e.symm (v, (e control).2)

private theorem measurable_replaceControlVector {p : ConstructorDimensions.Parameters} :
    Measurable (fun z : TimeControl p × Vector p => replaceControlVector z.1 z.2) := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  exact e.symm.measurable.comp
    (measurable_snd.prodMk (measurable_snd.comp (e.measurable.comp measurable_fst)))

private def renewalRemainderEvent {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p))
    (control0 : TimeControl p) :
    Set (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  {r | r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control0, r) ∈ firstRenewalEvent rate rewards C_star C_h u t}

private theorem measurableSet_renewalRemainderEvent
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p))
    (control0 : TimeControl p) :
    MeasurableSet (renewalRemainderEvent rate rewards C_star C_h u t q control0) := by
  have hsection : Measurable
      (fun r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t =>
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (control0, r)) := by
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_id)
  exact (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
      p q t).inter
    (hsection (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t))

private theorem replaceSelectedControlSuffix_update
    {p : ConstructorDimensions.Parameters} (source : Source p) (t : Fin p.T)
    (control : TimeControl p) :
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t
      (Function.update
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2)
        t control) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control := by
  unfold ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
  rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p source
      · subst j
        simp only [Function.update_self]
        apply Prod.ext
        · rfl
        · funext s
          by_cases hbefore : s.val < t.val
          · have hne : s ≠ t := by
              intro h
              subst s
              omega
            simp [hne]
          · by_cases heq : s = t
            · subst s
              simp
            · simp [hbefore, heq]
      · simp [hj]
  · rfl

private theorem insert_eq_split_controlReplacement
    {p : ConstructorDimensions.Parameters} (t : Fin p.T) (q : Fin (M p))
    (source : Source p) (v : Vector p)
    (hq : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q) :
    ReferenceFirstCollectionRenewalVectorInsertion.insert t source v =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (replaceControlVector
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1 v,
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hq
  have hcontrol : ReferenceFirstCollectionRenewalVectorInsertion.ctrl t source v =
      replaceControlVector (split source).1 v := by
    unfold ReferenceFirstCollectionRenewalVectorInsertion.ctrl
      ReferenceFirstCollectionRenewalVectorInsertion.c
      ReferenceFirstCollectionRenewalVectorInsertion.q replaceControlVector
    rw [hselected, ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
  change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source
      (ReferenceFirstCollectionRenewalVectorInsertion.ctrl t source v) = _
  rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t source _ hq, hcontrol]

private theorem renewalEvent_split_control_iff
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p))
    (control0 control : TimeControl p)
    (r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)
    (hr : r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control, r) ∈ firstRenewalEvent rate rewards C_star C_h u t ↔
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control0, r) ∈ firstRenewalEvent rate rewards C_star C_h u t := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let source := split.symm (control, r)
  have hq : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control r hr
  have hreplacement :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t source control0 hq
  have hsplit : split source = (control, r) := split.apply_symm_apply (control, r)
  have hsourceReplacement :
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0 =
        split.symm (control0, r) := by
    rw [← hreplacement, hsplit]
  have hlocality :=
    ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h source u t
      (Function.update ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2)
        t control0)
  rw [replaceSelectedControlSuffix_update, hsourceReplacement] at hlocality
  exact hlocality

private theorem renewalEventStratum_preimage
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p))
    (control0 : TimeControl p) :
    firstRenewalEvent rate rewards C_star C_h u t ∩
        ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t) ⁻¹'
        (Set.univ ×ˢ renewalRemainderEvent rate rewards C_star C_h u t q control0) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  ext source
  constructor
  · rintro ⟨hevent, hstratum⟩
    have hsplitStratum :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum_eq_preimage p q t
    rw [hsplitStratum] at hstratum
    change split source ∈ Set.univ ×ˢ
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t at hstratum
    have hr : (split source).2 ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t :=
      hstratum.2
    have hsource : split.symm (split source) = source := split.symm_apply_apply source
    have hdefault := (renewalEvent_split_control_iff rate rewards C_star C_h u t q
      control0 (split source).1 (split source).2 hr).mp (by rw [hsource]; exact hevent)
    change split source ∈ Set.univ ×ˢ
      renewalRemainderEvent rate rewards C_star C_h u t q control0
    exact ⟨trivial, ⟨hr, hdefault⟩⟩
  · intro h
    change split source ∈ Set.univ ×ˢ
      renewalRemainderEvent rate rewards C_star C_h u t q control0 at h
    rcases h with ⟨_, ⟨hr, hdefault⟩⟩
    have hsource : source = split.symm (split source) := (split.symm_apply_apply source).symm
    have hevent := (renewalEvent_split_control_iff rate rewards C_star C_h u t q
      control0 (split source).1 (split source).2 hr).mpr hdefault
    have hstratum : source ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q := by
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum_eq_preimage p q t]
      change split source ∈ Set.univ ×ˢ
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t
      exact ⟨trivial, hr⟩
    exact ⟨by rw [hsource]; exact hevent, hstratum⟩

private theorem renewalEventStratum_map_split
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p))
    (control0 : TimeControl p) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)).map
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t) =
      (ContinuousLearningRows.timeControlLaw p).prod
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
          (renewalRemainderEvent rate rewards C_star C_h u t q control0)) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let stratum := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q
  let remainderStratum :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t
  let remainderEvent := renewalRemainderEvent rate rewards C_star C_h u t q control0
  let targetCylinder : Set (TimeControl p ×
      ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
    Set.univ ×ˢ remainderEvent
  have htarget : MeasurableSet targetCylinder :=
    MeasurableSet.univ.prod
      (measurableSet_renewalRemainderEvent rate rewards C_star C_h u t q control0)
  have hpreimage : firstRenewalEvent rate rewards C_star C_h u t ∩ stratum =
      split ⁻¹' targetCylinder := by
    exact renewalEventStratum_preimage rate rewards C_star C_h u t q control0
  have hsourceRestrict :
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict stratum).restrict
          (split ⁻¹' targetCylinder) =
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum) := by
    rw [Measure.restrict_restrict (split.measurable htarget)]
    congr 1
    rw [hpreimage]
    exact Set.inter_eq_left.mpr (by
      intro source hs
      have hs' : source ∈ firstRenewalEvent rate rewards C_star C_h u t ∩ stratum := by
        rw [hpreimage]
        exact hs
      exact hs'.2)
  have hsplit := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map
    p q t
  calc
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict stratum).restrict
          (split ⁻¹' targetCylinder)).map split := by rw [hsourceRestrict]
    _ = Measure.restrict
          (Measure.map split ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict stratum))
          targetCylinder := by
      exact (Measure.restrict_map
        (μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict stratum)
        split.measurable htarget).symm
    _ = Measure.restrict
          ((ContinuousLearningRows.timeControlLaw p).prod
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
              remainderStratum)) targetCylinder := by rw [hsplit]
    _ = (ContinuousLearningRows.timeControlLaw p).prod
          ((ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict
            remainderEvent) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
      have hsub : remainderEvent ⊆ remainderStratum := by
        intro r hr
        exact hr.1
      rw [Measure.restrict_restrict_of_subset hsub]

private theorem replaceControlVector_map
    {p : ConstructorDimensions.Parameters} :
    ((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun z : TimeControl p × Vector p => replaceControlVector z.1 z.2) =
      ContinuousLearningRows.timeControlLaw p := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let vectorLaw := ContinuousControlSlice.assignmentLaw p.K
  let remainderLaw :=
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
      (ContinuousLearningRows.affineSamplesLaw p)
  let splitLaw := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hsplit : (ContinuousLearningRows.timeControlLaw p).map e =
      vectorLaw.prod remainderLaw := splitLaw.map_eq
  have hdropReorder : MeasurePreserving
      (fun z : (Vector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
          ContinuousLearningRows.AffineSamples p)) × Vector p =>
        (z.1.1, (z.2, z.1.2)))
      ((vectorLaw.prod remainderLaw).prod vectorLaw)
      (vectorLaw.prod (vectorLaw.prod remainderLaw)) := by
    exact ((MeasurePreserving.id vectorLaw).prod
      (Measure.measurePreserving_swap (μ := remainderLaw) (ν := vectorLaw))).comp
        (measurePreserving_prodAssoc vectorLaw remainderLaw vectorLaw)
  have hdrop :
      ((vectorLaw.prod remainderLaw).prod vectorLaw).map
        (fun z : (Vector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
          ContinuousLearningRows.AffineSamples p)) × Vector p => (z.2, z.1.2)) =
        vectorLaw.prod remainderLaw := by
    calc
      _ = (Measure.map Prod.snd
          (Measure.map (fun z : (Vector p ×
            (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
              ContinuousLearningRows.AffineSamples p)) × Vector p =>
                (z.1.1, (z.2, z.1.2)))
            ((vectorLaw.prod remainderLaw).prod vectorLaw))) := by
        rw [Measure.map_map measurable_snd hdropReorder.measurable]
        rfl
      _ = (Measure.map Prod.snd (vectorLaw.prod (vectorLaw.prod remainderLaw))) := by
        rw [hdropReorder.map_eq]
      _ = vectorLaw.prod remainderLaw := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hpush :
      ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
        (fun z : TimeControl p × Vector p => (z.2, (e z.1).2)) =
      vectorLaw.prod remainderLaw := by
    have hsplitProd :
        ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
            (Prod.map e id) =
      ((ContinuousLearningRows.timeControlLaw p).map e).prod vectorLaw := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (ContinuousLearningRows.timeControlLaw p) vectorLaw
          e.measurable measurable_id).symm
    calc
      _ = (((ContinuousLearningRows.timeControlLaw p).map e).prod vectorLaw).map
          (fun z : (Vector p × (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p ×
            ContinuousLearningRows.AffineSamples p)) × Vector p => (z.2, z.1.2)) := by
        rw [← hsplitProd]
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = vectorLaw.prod remainderLaw := by rw [hsplit, hdrop]
  calc
    _ = ((((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
          (fun z : TimeControl p × Vector p => (z.2, (e z.1).2))).map e.symm) := by
        rw [Measure.map_map e.symm.measurable (by fun_prop)]
        rfl
    _ = ContinuousLearningRows.timeControlLaw p := by
        rw [hpush, ← hsplit]
        exact e.map_symm_map

private def controlRemainderVectorEquiv {p : ConstructorDimensions.Parameters}
    (q : Fin (M p)) (t : Fin p.T) :
    ((TimeControl p ×
        ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) × Vector p) ≃ᵐ
      ((TimeControl p × Vector p) ×
        ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

private theorem controlRemainderVector_map
    {p : ConstructorDimensions.Parameters} (q : Fin (M p)) (t : Fin p.T)
    (remainderLaw : Measure (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t))
    [SFinite remainderLaw] :
    MeasurePreserving (controlRemainderVectorEquiv (p := p) q t)
      (((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod
        (ContinuousControlSlice.assignmentLaw p.K))
      (((ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.assignmentLaw p.K)).prod remainderLaw) := by
  exact (measurePreserving_prodAssoc (ContinuousLearningRows.timeControlLaw p)
      (ContinuousControlSlice.assignmentLaw p.K) remainderLaw).symm.comp
    (((MeasurePreserving.id (ContinuousLearningRows.timeControlLaw p)).prod
      (Measure.measurePreserving_swap (μ := remainderLaw)
        (ν := ContinuousControlSlice.assignmentLaw p.K))).comp
      (measurePreserving_prodAssoc (ContinuousLearningRows.timeControlLaw p) remainderLaw
        (ContinuousControlSlice.assignmentLaw p.K)))

private theorem insertedSource_stationary_stratum
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (q : Fin (M p)) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun sv : Source p × Vector p =>
          ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let stratum := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q
  let remainderEvent := renewalRemainderEvent rate rewards C_star C_h u t q zeroTimeControl
  let remainderLaw :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderLaw p q t).restrict remainderEvent
  let vectorLaw := ContinuousControlSlice.assignmentLaw p.K
  let replace := replaceControlVector (p := p)
  let replacePair := fun z : TimeControl p × Vector p => replace z.1 z.2
  let splitMap := fun sv : Source p × Vector p => (split sv.1, sv.2)
  let targetMap := fun z : (TimeControl p ×
      ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) × Vector p =>
    split.symm (replace z.1.1 z.2, z.1.2)
  let reorderedTargetMap := fun z : (TimeControl p × Vector p) ×
      ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t =>
    split.symm (replace z.1.1 z.1.2, z.2)
  have hsplit := renewalEventStratum_map_split rate rewards C_star C_h u t q
    zeroTimeControl
  have hsourceVector :
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw).map splitMap =
        ((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw := by
    calc
      _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).map split).prod vectorLaw := by
        change Measure.map (Prod.map split id)
          (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw) = _
        have h := (Measure.map_prod_map
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)) vectorLaw
          split.measurable measurable_id).symm
        simpa only [Measure.map_id] using h
      _ = _ := by rw [hsplit]
  have hstratum : ∀ᵐ s ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum), s ∈ stratum := by
    have hmem := ae_restrict_mem (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
      (s := firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)
      ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t).inter
        (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q))
    filter_upwards [hmem] with s hs
    exact hs.2
  have hstratumPair : ∀ᵐ sv ∂
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw),
        sv.1 ∈ stratum := by
    have hrectangle : MeasurableSet (stratum ×ˢ (Set.univ : Set (Vector p))) :=
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q).prod
        MeasurableSet.univ
    have hprod := (Measure.ae_prod_mem_iff_ae_ae_mem
      (μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum))
      (ν := vectorLaw) hrectangle).mpr (by
      filter_upwards [hstratum] with s hs
      filter_upwards [] with v
      exact ⟨hs, trivial⟩)
    filter_upwards [hprod] with sv h
    exact h.1
  have hinsert : ∀ᵐ sv ∂
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw),
        ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2 =
          targetMap (splitMap sv) := by
    filter_upwards [hstratumPair] with sv hq
    have hq' : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sv.1 = q := hq
    exact insert_eq_split_controlReplacement t q sv.1 sv.2 hq'
  have hmove := controlRemainderVector_map (p := p) q t remainderLaw
  have htargetMeasurable : Measurable targetMap := by
    exact split.symm.measurable.comp
      ((measurable_replaceControlVector.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst))
  have hreorderedTargetMeasurable : Measurable reorderedTargetMap := by
    exact split.symm.measurable.comp
      ((measurable_replaceControlVector.comp
          ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd)
  have hreplacePairMeasurable : Measurable replacePair := by
    exact measurable_replaceControlVector
  have hreplaceRemainderMeasurable : Measurable
      (Prod.map replacePair
        (id : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t →
          ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)) := by
    exact (hreplacePairMeasurable.comp measurable_fst).prodMk measurable_snd
  have hreplaceRemainderMap :
      Measure.map (Prod.map replacePair
          (id : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t →
            ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t))
          (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw) =
        ((Measure.map replacePair ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw)).prod
          remainderLaw) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map
        ((ContinuousLearningRows.timeControlLaw p).prod vectorLaw) remainderLaw
        hreplacePairMeasurable measurable_id).symm
  calc
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw).map
          (targetMap ∘ splitMap) := by
        exact Measure.map_congr hinsert
    _ = ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum)).prod vectorLaw).map
          splitMap).map targetMap := by
        rw [Measure.map_map htargetMeasurable (by fun_prop)]
    _ = (((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw).map
          targetMap := by rw [hsourceVector]
    _ = ((((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).prod vectorLaw).map
          (controlRemainderVectorEquiv (p := p) q t)).map reorderedTargetMap := by
        rw [Measure.map_map hreorderedTargetMeasurable
          (controlRemainderVectorEquiv (p := p) q t).measurable]
        rfl
    _ = (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw).map
          reorderedTargetMap := by rw [hmove.map_eq]
    _ = Measure.map split.symm
          (Measure.map (Prod.map replacePair id)
            (((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).prod remainderLaw)) := by
        rw [Measure.map_map split.symm.measurable hreplaceRemainderMeasurable]
        rfl
    _ = Measure.map split.symm
          ((((ContinuousLearningRows.timeControlLaw p).prod vectorLaw).map
            (fun z => replace z.1 z.2)).prod remainderLaw) := by
        rw [hreplaceRemainderMap]
    _ = ((ContinuousLearningRows.timeControlLaw p).prod remainderLaw).map split.symm := by
        rw [replaceControlVector_map]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t ∩ stratum) := by
        rw [← hsplit]
        exact split.map_symm_map

private theorem renewalEventStrata_sum
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    Measure.sum (fun q : Fin (M p) =>
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t ∩
          ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p q)) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t) := by
  let event := firstRenewalEvent rate rewards C_star C_h u t
  let stratum := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p
  have hdis : Pairwise (fun q r => Disjoint (event ∩ stratum q) (event ∩ stratum r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro source hq hr
    rcases hq with ⟨_, hqIndex⟩
    rcases hr with ⟨_, hrIndex⟩
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q at hqIndex
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = r at hrIndex
    exact hqr (hqIndex.symm.trans hrIndex)
  have hmeas : ∀ q : Fin (M p), MeasurableSet (event ∩ stratum q) := by
    intro q
    exact (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t).inter
      (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlSourceStratum p q)
  have hcover : (⋃ q : Fin (M p), event ∩ stratum q) = event := by
    ext source
    constructor
    · intro h
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp h
      exact hq.1
    · intro hevent
      refine Set.mem_iUnion.mpr ⟨
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source, ?_⟩
      exact ⟨hevent, rfl⟩
  calc
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (⋃ q : Fin (M p), event ∩ stratum q) :=
        (Measure.restrict_iUnion hdis hmeas).symm
    _ = _ := by rw [hcover]

private theorem insertedSource_stationary
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t)).prod
      (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun sv : Source p × Vector p =>
          ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t) := by
  let event := firstRenewalEvent rate rewards C_star C_h u t
  let stratum := ReferenceFixedTimeSourceControlCoupling.fixedControlSourceStratum p
  have hsum := renewalEventStrata_sum rate rewards C_star C_h u t
  calc
    _ = ((Measure.sum (fun q : Fin (M p) =>
          (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (event ∩ stratum q))).prod
          (ContinuousControlSlice.assignmentLaw p.K)).map
            (fun sv : Source p × Vector p =>
              ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2) := by
        rw [hsum]
    _ = Measure.sum (fun q : Fin (M p) =>
          (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (event ∩ stratum q)).prod
            (ContinuousControlSlice.assignmentLaw p.K)).map
              (fun sv : Source p × Vector p =>
                ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2)) := by
        rw [Measure.prod_sum_left]
        exact Measure.map_sum
          (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert
            (p := p) (t := t)).aemeasurable
    _ = Measure.sum (fun q : Fin (M p) =>
          (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (event ∩ stratum q)) := by
        congr 1
        funext q
        exact insertedSource_stationary_stratum rate rewards C_star C_h u t q
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict event := hsum

private theorem renewalLiftLaw_map_original_source_vector
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (ReferenceFirstCollectionRenewalVectorInsertion.Lambda
      rate rewards C_star C_h u t).map
        (fun wv : ReferenceFirstCollectionRenewalVectorInsertion.W
          rate rewards C_star C_h u t => (wv.1.1.val, wv.2)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (firstRenewalEvent rate rewards C_star C_h u t)).prod
          (ContinuousControlSlice.assignmentLaw p.K) := by
  have hprojection : Measurable (fun wv :
      ReferenceFirstCollectionRenewalVectorInsertion.W rate rewards C_star C_h u t =>
        (wv.1.1.val, wv.2)) := by
    exact (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd
  apply Measure.ext_prod
  intro A B hA hB
  have hrectangle :=
    ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_original_source_vector_rectangle
      rate rewards C_star C_h u t A hA B hB
  have hset : (fun wv : ReferenceFirstCollectionRenewalVectorInsertion.W
      rate rewards C_star C_h u t => (wv.1.1.val, wv.2)) ⁻¹' (A ×ˢ B) =
      {wv | wv.1.1.val ∈ A ∧ wv.2 ∈ B} := by
    ext wv
    simp
  rw [Measure.map_apply hprojection (hA.prod hB), hset, Measure.prod_prod,
    Measure.restrict_apply hA]
  simpa only [firstRenewalEvent] using hrectangle

/-- Push the actual candidate whole vector into the original source. This is
an equality of unnormalized finite measures on the complete original source
carrier, with the literal first collection renewal event and no mass premise. -/
theorem renewalLiftLaw_map_inserted_source
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (ReferenceFirstCollectionRenewalVectorInsertion.Lambda
      rate rewards C_star C_h u t).map
        (fun wv : ReferenceFirstCollectionRenewalVectorInsertion.W
          rate rewards C_star C_h u t =>
            ReferenceFirstCollectionRenewalVectorInsertion.insert t wv.1.1.val wv.2) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) := by
  let sourceVectorMap := fun wv :
      ReferenceFirstCollectionRenewalVectorInsertion.W rate rewards C_star C_h u t =>
        (wv.1.1.val, wv.2)
  let insertMap := fun sv : Source p × Vector p =>
    ReferenceFirstCollectionRenewalVectorInsertion.insert t sv.1 sv.2
  have hsourceVectorMeasurable : Measurable sourceVectorMap := by
    exact (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd
  have hsourceVector :=
    renewalLiftLaw_map_original_source_vector rate rewards C_star C_h u t
  calc
    _ = ((ReferenceFirstCollectionRenewalVectorInsertion.Lambda
          rate rewards C_star C_h u t).map sourceVectorMap).map insertMap := by
        rw [Measure.map_map
          (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert
            (p := p) (t := t)) hsourceVectorMeasurable]
        rfl
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t)).prod
          (ContinuousControlSlice.assignmentLaw p.K)).map insertMap := by
        rw [hsourceVector]
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (firstRenewalEvent rate rewards C_star C_h u t) :=
        insertedSource_stationary rate rewards C_star C_h u t

end Bandits.Support.ReferenceFirstCollectionRenewalInsertedSourceLaw

end
