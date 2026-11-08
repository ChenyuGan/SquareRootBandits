/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextPriorReadout

import Mathlib.MeasureTheory.Integral.Prod
import Lean.Elab.Tactic.Omega

/-!
# Whole next-control law on the original renewal source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

All restrictions below retain their original mass, including zero mass. The
source, selected private index, and full retained remainder are the existing
ones. These probability results assert no physical recording or marker law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open scoped MeasureTheory Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw

open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFixedTimeSourceControlCoupling
open ReferenceSourceCurrentControlFreshness
open ReferenceGeneratedPrefixSuffixInvariance
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstCollectionRenewalNextPriorReadout

abbrev Source {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextPriorReadout.Source rate rewards C_star C_h u t

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => Source rate rewards C_star C_h u t
local notation "E" => renewalCallEvent rate rewards C_star C_h u t
local notation "ν" => renewalSourceLaw rate rewards C_star C_h u t
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "κ" => ContinuousLearningRows.timeControlLaw p
local notation "e" => nextPriorObserver rate rewards C_star C_h u t control0

/-- The actual renewal event is invariant in both directions under arbitrary
replacement of the selected control suffix beginning strictly after `t`. -/
theorem renewalCallEvent_iff_nextSuffix (hq : t.val + 1 < p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    source ∈ E ↔
      replaceSelectedControlSuffix source ⟨t.val + 1, hq⟩ suffix ∈ E := by
  let lifted := fun v : Fin p.T => if v.val < t.val + 1 then
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
    else suffix v
  have heq : replaceSelectedControlSuffix source t lifted =
      replaceSelectedControlSuffix source ⟨t.val + 1, hq⟩ suffix := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext row
        by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p source
        · subst row
          simp only [replaceSelectedControlSuffix, Function.update_self]
          congr 1
          funext v
          change (if v.val < t.val then _ else lifted v) =
            (if v.val < t.val + 1 then _ else suffix v)
          by_cases hv : v.val < t.val
          · have hv' : v.val < t.val + 1 := by omega
            simp [hv, hv', lifted]
          · simp [hv, lifted]
        · simp only [replaceSelectedControlSuffix, Function.update_of_ne hr]
    · rfl
  rw [← heq]
  exact ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
    rate rewards C_star C_h source u t lifted

/-- The original measurable renewal event is a next-prefix event. -/
theorem renewalCallEvent_nextPrefix (hq : t.val + 1 < p.T) :
    E = (c_t p control0 ⟨t.val + 1, hq⟩) ⁻¹' E := by
  ext source
  exact renewalCallEvent_iff_nextSuffix rate rewards C_star C_h u t hq source
    (fun _ => control0)

/-- The existing observer is measurable on the original renewal subtype. -/
theorem measurable_nextPriorObserver : Measurable e := by
  have hval : Measurable (fun z : Z => (e z).val) := by
    simp only [nextPriorObserver_val]
    exact (measurable_sourcePrefix control0 (t.val + 1)).comp measurable_subtype_coe
  exact hval.subtype_mk

/-- The whole next current control, without any projection to a physical slice. -/
def nextControl (hq : t.val + 1 < p.T) (z : Z) :
    ContinuousLearningRows.TimeControl p := u_t p ⟨t.val + 1, hq⟩ z.val

theorem measurable_nextControl (hq : t.val + 1 < p.T) :
    Measurable (nextControl rate rewards C_star C_h u t hq) :=
  (measurable_u_t (p := p) ⟨t.val + 1, hq⟩).comp measurable_subtype_coe

/-- The literal existing next-prior field; its offset excludes the next control. -/
abbrev nextPriorField : MeasurableSpace Z :=
  MeasurableSpace.comap Subtype.val (sourcePrefixFiltration control0 (t.val + 2))

/-- The field equality uses the actual successor equation of the source filtration. -/
theorem nextPriorField_eq_comap :
    nextPriorField rate rewards C_star C_h u t control0 =
      MeasurableSpace.comap e (inferInstance : MeasurableSpace Z) := by
  change MeasurableSpace.comap Subtype.val
      (sourcePrefixFiltration control0 (t.val + 2)) =
    MeasurableSpace.comap e (MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)))
  rw [show t.val + 2 = (t.val + 1) + 1 by omega,
    sourcePrefixFiltration_succ, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]
  congr 1
  funext z
  exact (nextPriorObserver_val rate rewards C_star C_h u t control0 z).symm

/-- Direct restriction of the ambient whole-control product law. -/
theorem nextControl_ambient_joint (hq : t.val + 1 < p.T) :
    ((μ).restrict E).map (fun source =>
      (c_t p control0 ⟨t.val + 1, hq⟩ source,
        u_t p ⟨t.val + 1, hq⟩ source)) =
      (((μ).restrict E).map (c_t p control0 ⟨t.val + 1, hq⟩)).prod κ := by
  let c := c_t p control0 ⟨t.val + 1, hq⟩
  let U := u_t p ⟨t.val + 1, hq⟩
  have hc : Measurable c := measurable_c_t control0 _
  have hU : Measurable U := measurable_u_t _
  have hE := measurableSet_renewalCallEvent rate rewards C_star C_h u t
  have hpre := renewalCallEvent_nextPrefix rate rewards C_star C_h u t control0 hq
  have hp : (fun source => (c source, U source)) ⁻¹' (E ×ˢ Set.univ) = E := by
    ext source
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact Set.ext_iff.mp hpre source |>.symm
  calc
    _ = ((μ).map (fun source => (c source, U source))).restrict (E ×ˢ Set.univ) := by
      rw [Measure.restrict_map (hc.prodMk hU) (hE.prod MeasurableSet.univ), hp]
    _ = (((μ).map c).prod κ).restrict (E ×ˢ Set.univ) := by
      rw [source_joint_prefix_control]
    _ = (((μ).map c).restrict E).prod κ := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = _ := by rw [Measure.restrict_map hc hE, ← hpre]

/-- The next prefix and whole next control have the product law under the
same original finite renewal measure, with no normalization or positivity input. -/
theorem nextControl_joint_prefix (hq : t.val + 1 < p.T) :
    (ν).map (fun z => (e z, nextControl rate rewards C_star C_h u t hq z)) =
      ((ν).map e).prod κ := by
  let U := nextControl rate rewards C_star C_h u t hq
  let c := c_t p control0 ⟨t.val + 1, hq⟩
  have he := measurable_nextPriorObserver rate rewards C_star C_h u t control0
  have hU := measurable_nextControl rate rewards C_star C_h u t hq
  have hc : Measurable c := measurable_c_t control0 _
  have heval : (fun z : Z => (e z).val) = c ∘ Subtype.val := by
    funext z
    exact nextPriorObserver_val rate rewards C_star C_h u t control0 z
  have hpref : ((ν).map e).map Subtype.val = ((μ).restrict E).map c := by
    rw [Measure.map_map measurable_subtype_coe he]
    change (ν).map (fun z => (e z).val) = _
    rw [heval, ← Measure.map_map hc measurable_subtype_coe,
      renewalSourceLaw_map_val]
  apply ((MeasurableEmbedding.subtype_coe
    (measurableSet_renewalCallEvent rate rewards C_star C_h u t)).prodMap
      (MeasurableEmbedding.id (α := ContinuousLearningRows.TimeControl p))).map_injective
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    Measure.map_id, hpref, Measure.map_map
      (measurable_subtype_coe.prodMap measurable_id) (he.prodMk hU)]
  have hfun : Prod.map Subtype.val id ∘ (fun z : Z => (e z, U z)) =
      (fun source => (c source, u_t p ⟨t.val + 1, hq⟩ source)) ∘ Subtype.val := by
    funext z
    exact Prod.ext (congrFun heval z) rfl
  rw [hfun, ← Measure.map_map
    (hc.prodMk (measurable_u_t _)) measurable_subtype_coe, renewalSourceLaw_map_val]
  exact nextControl_ambient_joint rate rewards C_star C_h u t control0 hq

/-- Changing only the next control preserves actual renewal membership. -/
theorem renewalCallEvent_iff_replaceNextControl (hq : t.val + 1 < p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    source ∈ E ↔ replaceSourceControl p ⟨t.val + 1, hq⟩ source control ∈ E := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let suffix := fun v : Fin p.T => if v = q then control else
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
  have heq : replaceSelectedControlSuffix source q suffix =
      replaceSourceControl p q source control := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext row
        by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p source
        · subst row
          simp only [replaceSelectedControlSuffix, replaceSourceControl,
            sourceCoordinatorIndex_eq_selectedRowIndex, Function.update_self]
          congr 1
          funext v
          by_cases hv : v = q
          · subst v
            simp [suffix]
          · simp [suffix, hv]
        · simp only [replaceSelectedControlSuffix, replaceSourceControl,
            sourceCoordinatorIndex_eq_selectedRowIndex, Function.update_of_ne hr]
    · rfl
  rw [← heq]
  exact renewalCallEvent_iff_nextSuffix rate rewards C_star C_h u t hq source suffix

/-- The same renewal measure restricted to one actual private coordinator index. -/
def privateRenewalLaw (ell : Fin (M p)) : Measure Z :=
  (ν).restrict {z | sourceCoordinatorIndex p z.val = ell}

/-- Exhaustive retained coordinates together with the actual renewal event,
tested after inserting the fixed baseline into the one removed control. -/
def nextRemainderEvent (hq : t.val + 1 < p.T) (ell : Fin (M p)) :
    Set (FixedControlRemainder p ell ⟨t.val + 1, hq⟩) :=
  {r | r ∈ fixedControlRemainderStratum p ell ⟨t.val + 1, hq⟩ ∧
    (fixedControlSplit p ell ⟨t.val + 1, hq⟩).symm (control0, r) ∈ E}

theorem measurableSet_nextRemainderEvent (hq : t.val + 1 < p.T)
    (ell : Fin (M p)) :
    MeasurableSet (nextRemainderEvent rate rewards C_star C_h u t control0 hq ell) :=
  (measurableSet_fixedControlRemainderStratum p ell _).inter
    (((fixedControlSplit p ell _).symm.measurable.comp
      (measurable_const.prodMk measurable_id))
        (measurableSet_renewalCallEvent rate rewards C_star C_h u t))

/-- Actual source-event factorization through the existing full remainder. -/
theorem nextRemainderEvent_factor (hq : t.val + 1 < p.T) (ell : Fin (M p)) :
    E ∩ fixedControlSourceStratum p ell =
      fixedControlSplit p ell ⟨t.val + 1, hq⟩ ⁻¹'
        (Set.univ ×ˢ nextRemainderEvent rate rewards C_star C_h u t control0 hq ell) := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let split := fixedControlSplit p ell q
  ext source
  have hs : source ∈ fixedControlSourceStratum p ell ↔
      (split source).2 ∈ fixedControlRemainderStratum p ell q := by
    rw [fixedControlSourceStratum_eq_preimage p ell q]
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  change (source ∈ E ∧ source ∈ fixedControlSourceStratum p ell) ↔
    (True ∧ (split source).2 ∈ fixedControlRemainderStratum p ell q ∧
      split.symm (control0, (split source).2) ∈ E)
  constructor
  · rintro ⟨hE, hS⟩
    refine ⟨trivial, hs.mp hS, ?_⟩
    rw [fixedControlSplit_replaceSourceControl p ell q source control0 hS]
    exact (renewalCallEvent_iff_replaceNextControl rate rewards C_star C_h u t
      hq source control0).mp hE
  · rintro ⟨_, hS, hE⟩
    have hS' := hs.mpr hS
    refine ⟨?_, hS'⟩
    rw [fixedControlSplit_replaceSourceControl p ell q source control0 hS'] at hE
    exact (renewalCallEvent_iff_replaceNextControl rate rewards C_star C_h u t
      hq source control0).mpr hE

/-- Splitting a private stratum retains precisely its original renewal mass. -/
theorem nextControl_private_ambient (hq : t.val + 1 < p.T) (ell : Fin (M p)) :
    ((μ).restrict (E ∩ fixedControlSourceStratum p ell)).map
        (fixedControlSplit p ell ⟨t.val + 1, hq⟩) =
      (κ).prod ((fixedControlRemainderLaw p ell ⟨t.val + 1, hq⟩).restrict
        (nextRemainderEvent rate rewards C_star C_h u t control0 hq ell)) := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let split := fixedControlSplit p ell q
  let R := nextRemainderEvent rate rewards C_star C_h u t control0 hq ell
  have hR : MeasurableSet R :=
    measurableSet_nextRemainderEvent rate rewards C_star C_h u t control0 hq ell
  have hfactor := nextRemainderEvent_factor rate rewards C_star C_h u t control0 hq ell
  have hrestriction : (μ).restrict (E ∩ fixedControlSourceStratum p ell) =
      ((μ).restrict (fixedControlSourceStratum p ell)).restrict
        (split ⁻¹' (Set.univ ×ˢ R)) := by
    rw [← hfactor]
    exact (Measure.restrict_restrict_of_subset Set.inter_subset_right).symm
  rw [hrestriction, ← Measure.restrict_map split.measurable
    (MeasurableSet.univ.prod hR), fixedControlSplit_privateStratum_map,
    ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict hR]
  congr 2
  exact Set.inter_eq_left.mpr (fun _ hr => hr.1)

/-- Pushforward of the subtype's private-index restriction to the original source. -/
theorem privateRenewalLaw_map_val (ell : Fin (M p)) :
    (privateRenewalLaw rate rewards C_star C_h u t ell).map Subtype.val =
      (μ).restrict (E ∩ fixedControlSourceStratum p ell) := by
  change ((ν).restrict (Subtype.val ⁻¹' fixedControlSourceStratum p ell)).map
    Subtype.val = _
  rw [← Measure.restrict_map measurable_subtype_coe
    (measurableSet_fixedControlSourceStratum p ell), renewalSourceLaw_map_val,
    Measure.restrict_restrict (measurableSet_fixedControlSourceStratum p ell),
    Set.inter_comm]

/-- The whole next control is independent of the exhaustive retained source
on every private-index stratum, under the original unnormalized measure. -/
theorem nextControl_private_joint (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (ell : Fin (M p)) :
    (privateRenewalLaw rate rewards C_star C_h u t ell).map
        (fun z => fixedControlSplit p ell ⟨t.val + 1, hq⟩ z.val) =
      (κ).prod ((privateRenewalLaw rate rewards C_star C_h u t ell).map
        (fun z => (fixedControlSplit p ell ⟨t.val + 1, hq⟩ z.val).2)) := by
  let split := fixedControlSplit p ell ⟨t.val + 1, hq⟩
  let ρ := (fixedControlRemainderLaw p ell ⟨t.val + 1, hq⟩).restrict
    (nextRemainderEvent rate rewards C_star C_h u t control0 hq ell)
  have hjoint : (privateRenewalLaw rate rewards C_star C_h u t ell).map
      (fun z => split z.val) = (κ).prod ρ := by
    change (privateRenewalLaw rate rewards C_star C_h u t ell).map
      (split ∘ Subtype.val) = _
    rw [← Measure.map_map split.measurable measurable_subtype_coe,
      privateRenewalLaw_map_val]
    exact nextControl_private_ambient rate rewards C_star C_h u t control0 hq ell
  have hsnd : (privateRenewalLaw rate rewards C_star C_h u t ell).map
      (fun z => (split z.val).2) = ρ := by
    change (privateRenewalLaw rate rewards C_star C_h u t ell).map
      (Prod.snd ∘ (split ∘ Subtype.val)) = _
    rw [← Measure.map_map measurable_snd (split.measurable.comp measurable_subtype_coe),
      show (privateRenewalLaw rate rewards C_star C_h u t ell).map
        (split ∘ Subtype.val) = (κ).prod ρ from hjoint,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [hjoint, hsnd]

/-- Inverse-map recovery of each original private-index renewal restriction. -/
theorem nextControl_private_inverse (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (ell : Fin (M p)) :
    ((κ).prod ((privateRenewalLaw rate rewards C_star C_h u t ell).map
      (fun z => (fixedControlSplit p ell ⟨t.val + 1, hq⟩ z.val).2))).map
        (fixedControlSplit p ell ⟨t.val + 1, hq⟩).symm =
      (μ).restrict (E ∩ fixedControlSourceStratum p ell) := by
  rw [← nextControl_private_joint rate rewards C_star C_h u t control0 hq ell,
    Measure.map_map (fixedControlSplit p ell _).symm.measurable
      (show Measurable (fun z : Z => fixedControlSplit p ell ⟨t.val + 1, hq⟩ z.val) from
        (fixedControlSplit p ell _).measurable.comp measurable_subtype_coe)]
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using
    privateRenewalLaw_map_val rate rewards C_star C_h u t ell

/-- Every original private index is included once; no stratum mass is dropped. -/
theorem privateRenewalLaw_sum :
    Measure.sum (privateRenewalLaw rate rewards C_star C_h u t) = ν := by
  have hdis : Pairwise (fun ell k : Fin (M p) =>
      Disjoint {z : Z | sourceCoordinatorIndex p z.val = ell}
        {z : Z | sourceCoordinatorIndex p z.val = k}) := by
    intro ell k hne
    exact Set.disjoint_left.mpr (fun _ h1 h2 => hne (h1.symm.trans h2))
  have hm : ∀ ell : Fin (M p), MeasurableSet
      {z : Z | sourceCoordinatorIndex p z.val = ell} := fun ell =>
    measurable_subtype_coe (measurableSet_fixedControlSourceStratum p ell)
  have hcover : (⋃ ell : Fin (M p),
      {z : Z | sourceCoordinatorIndex p z.val = ell}) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨sourceCoordinatorIndex p z.val, rfl⟩
  change Measure.sum (fun ell : Fin (M p) => (ν).restrict
    {z : Z | sourceCoordinatorIndex p z.val = ell}) = _
  rw [← Measure.restrict_iUnion hdis hm, hcover, Measure.restrict_univ]

/-- Summing the inverse split laws recovers the same whole original restriction. -/
theorem nextControl_private_inverse_sum (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measure.sum (fun ell : Fin (M p) =>
      ((κ).prod ((privateRenewalLaw rate rewards C_star C_h u t ell).map
        (fun z => (fixedControlSplit p ell ⟨t.val + 1, hq⟩ z.val).2))).map
          (fixedControlSplit p ell ⟨t.val + 1, hq⟩).symm) =
      (μ).restrict E := by
  simp_rw [nextControl_private_inverse rate rewards C_star C_h u t control0 hq,
    ← privateRenewalLaw_map_val rate rewards C_star C_h u t]
  rw [← Measure.map_sum measurable_subtype_coe.aemeasurable,
    privateRenewalLaw_sum, renewalSourceLaw_map_val]

/-- Measurability into the ambient renewal source from the exact next-prior field. -/
theorem measurable_nextPriorObserver_field :
    Measurable[nextPriorField rate rewards C_star C_h u t control0] e := by
  rw [nextPriorField_eq_comap]
  exact comap_measurable e

theorem nextPriorField_le :
    nextPriorField rate rewards C_star C_h u t control0 ≤
      (inferInstance : MeasurableSpace Z) := by
  rw [nextPriorField_eq_comap]
  exact (measurable_nextPriorObserver rate rewards C_star C_h u t control0).comap_le

/-- The product law after any measurable test of the next-prior observer. -/
theorem nextControl_joint_prefix_restrict (hq : t.val + 1 < p.T)
    (V : Set Z) (hV : MeasurableSet V) :
    ((ν).restrict (e ⁻¹' V)).map
        (fun z => (e z, nextControl rate rewards C_star C_h u t hq z)) =
      (((ν).map e).restrict V).prod κ := by
  have he := measurable_nextPriorObserver rate rewards C_star C_h u t control0
  have hU := measurable_nextControl rate rewards C_star C_h u t hq
  have hp : (fun z => (e z, nextControl rate rewards C_star C_h u t hq z)) ⁻¹'
      (V ×ˢ Set.univ) = e ⁻¹' V := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [← hp, ← Measure.restrict_map (he.prodMk hU) (hV.prod MeasurableSet.univ),
    nextControl_joint_prefix, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The bounded indicator of a Borel test of the observer and whole next control. -/
def nextControlTest (hq : t.val + 1 < p.T)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (e z, nextControl rate rewards C_star C_h u t hq z)

/-- Integral of the same test over the original whole-control probability law. -/
def nextControlSectionIntegral
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) : ℝ :=
  ∫ control, B.indicator (fun _ => (1 : ℝ)) (z, control) ∂κ

theorem measurable_nextControlSectionIntegral
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Measurable (nextControlSectionIntegral rate rewards C_star C_h u t B) := by
  have hf : Measurable (B.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hB
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

private theorem indicator_norm_le_one {α : Type*} (B : Set α) (x : α) :
    ‖B.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

theorem nextControlSectionIntegral_norm_le_one
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) :
    ‖nextControlSectionIntegral rate rewards C_star C_h u t B z‖ ≤ 1 := by
  exact (norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall (fun control => indicator_norm_le_one B (z, control)))).trans
      (by simp)

private theorem integrable_of_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {testLaw : Measure α} [IsFiniteMeasure testLaw]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f testLaw :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Every Borel indicator test is integrable under the finite original renewal law. -/
theorem integrable_nextControlTest (hq : t.val + 1 < p.T)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Integrable (nextControlTest rate rewards C_star C_h u t control0 hq B) ν := by
  exact integrable_of_measurable_norm_le_one _
    ((measurable_const.indicator hB).comp
      ((measurable_nextPriorObserver rate rewards C_star C_h u t control0).prodMk
        (measurable_nextControl rate rewards C_star C_h u t hq)))
    (fun z => indicator_norm_le_one B _)

/-- The candidate conditional law is measurable in the exact next-prior field. -/
theorem measurable_nextControlCandidate
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Measurable[nextPriorField rate rewards C_star C_h u t control0]
      (fun z => nextControlSectionIntegral rate rewards C_star C_h u t B (e z)) :=
  (measurable_nextControlSectionIntegral rate rewards C_star C_h u t B hB).comp
    (measurable_nextPriorObserver_field rate rewards C_star C_h u t control0)

theorem integrable_nextControlCandidate
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Integrable
      (fun z => nextControlSectionIntegral rate rewards C_star C_h u t B (e z)) ν :=
  integrable_of_measurable_norm_le_one _
    ((measurable_nextControlSectionIntegral rate rewards C_star C_h u t B hB).comp
      (measurable_nextPriorObserver rate rewards C_star C_h u t control0))
    (fun z => nextControlSectionIntegral_norm_le_one rate rewards C_star C_h u t B (e z))

private theorem nextControl_test_prefix_setIntegral (hq : t.val + 1 < p.T)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B)
    (V : Set Z) (hV : MeasurableSet V) :
    ∫ z in e ⁻¹' V, nextControlTest rate rewards C_star C_h u t control0 hq B z ∂ν =
      ∫ z in e ⁻¹' V,
        nextControlSectionIntegral rate rewards C_star C_h u t B (e z) ∂ν := by
  let pair := fun z : Z => (e z, nextControl rate rewards C_star C_h u t hq z)
  let f : Z × ContinuousLearningRows.TimeControl p → ℝ := B.indicator (fun _ => 1)
  let testLaw := (ν).restrict (e ⁻¹' V)
  let ρ := ((ν).map e).restrict V
  have he := measurable_nextPriorObserver rate rewards C_star C_h u t control0
  have hp := he.prodMk (measurable_nextControl rate rewards C_star C_h u t hq)
  have hf : Measurable f := measurable_const.indicator hB
  have hfint : Integrable f (ρ.prod κ) :=
    integrable_of_measurable_norm_le_one f hf (indicator_norm_le_one B)
  have hjoint : testLaw.map pair = ρ.prod κ :=
    nextControl_joint_prefix_restrict rate rewards C_star C_h u t control0 hq V hV
  have hprefix : testLaw.map e = ρ := (Measure.restrict_map he hV).symm
  calc
    _ = ∫ z, f (pair z) ∂testLaw := rfl
    _ = ∫ x, f x ∂(testLaw.map pair) :=
      (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, f x ∂(ρ.prod κ) := by rw [hjoint]
    _ = ∫ z, ∫ control, f (z, control) ∂κ ∂ρ := integral_prod f hfint
    _ = ∫ z, nextControlSectionIntegral rate rewards C_star C_h u t B z ∂(testLaw.map e) := by
      rw [hprefix]
      rfl
    _ = _ := integral_map he.aemeasurable
      (measurable_nextControlSectionIntegral rate rewards C_star C_h u t B hB).aestronglyMeasurable

/-- The conditional test law in set-integral form, for every next-prior event. -/
theorem nextControl_test_setIntegral (hq : t.val + 1 < p.T)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B)
    (G : Set Z) (hG : MeasurableSet[nextPriorField rate rewards C_star C_h u t control0] G) :
    ∫ z in G, nextControlTest rate rewards C_star C_h u t control0 hq B z ∂ν =
      ∫ z in G, nextControlSectionIntegral rate rewards C_star C_h u t B (e z) ∂ν := by
  rw [nextPriorField_eq_comap] at hG
  obtain ⟨V, hV, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hG
  exact nextControl_test_prefix_setIntegral rate rewards C_star C_h u t control0 hq B hB V hV

/-- Conditional law of every bounded Borel indicator test of the next prior
and the whole next control, directly under the same original renewal measure. -/
theorem nextControl_test_condExp (hq : t.val + 1 < p.T)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    (ν)[nextControlTest rate rewards C_star C_h u t control0 hq B |
      nextPriorField rate rewards C_star C_h u t control0] =ᵐ[ν]
      fun z => ∫ control, B.indicator (fun _ => (1 : ℝ)) (e z, control) ∂κ := by
  have hfint := integrable_nextControlTest rate rewards C_star C_h u t control0 hq B hB
  have hgint := integrable_nextControlCandidate rate rewards C_star C_h u t control0 B hB
  have hgmeas := measurable_nextControlCandidate rate rewards C_star C_h u t control0 B hB
  exact (ae_eq_condExp_of_forall_setIntegral_eq
    (nextPriorField_le rate rewards C_star C_h u t control0) hfint
    (fun _ _ _ => hgint.integrableOn)
    (fun G hG _ => (nextControl_test_setIntegral
      rate rewards C_star C_h u t control0 hq B hB G hG).symm)
    hgmeas.stronglyMeasurable.aestronglyMeasurable).symm

end Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw

end
