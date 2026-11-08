/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Lean.Elab.Tactic.Omega

/-!
# Whole-control freshness at every later date on the original renewal source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

Every law below uses the same original first-renewal source and its finite,
possibly zero, unnormalized event measure. A later date removes only that
date's complete selected control; every other source coordinate is retained.
These probability results assert no physical recording or queue theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open scoped MeasureTheory Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw

open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFixedTimeSourceControlCoupling
open ReferenceSourceCurrentControlFreshness
open ReferenceGeneratedPrefixSuffixInvariance
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstCollectionRenewalNextControlLaw

abbrev Source {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextControlLaw.Source rate rewards C_star C_h u t

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

/-- The original renewal event is invariant under an arbitrary selected-row
suffix replacement beginning at any date strictly after the first call date. -/
theorem renewalCallEvent_iff_futureSuffix (q : Fin p.T) (htq : t.val < q.val)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    source ∈ E ↔ replaceSelectedControlSuffix source q suffix ∈ E := by
  have hnext : t.val + 1 < p.T := by omega
  let next : Fin p.T := ⟨t.val + 1, hnext⟩
  let lifted := fun v : Fin p.T =>
    if v.val < q.val then
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
    else suffix v
  have heq : replaceSelectedControlSuffix source next lifted =
      replaceSelectedControlSuffix source q suffix := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext row
        by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p source
        · subst row
          simp only [replaceSelectedControlSuffix, Function.update_self]
          congr 1
          funext v
          change (if v.val < t.val + 1 then _ else lifted v) =
            (if v.val < q.val then _ else suffix v)
          by_cases hv : v.val < t.val + 1
          · have hvq : v.val < q.val := by omega
            simp only [ite_eq_left hv, ite_eq_left hvq]
          · by_cases hvq : v.val < q.val
            · simp only [ite_eq_right hv, ite_eq_left hvq, lifted]
            · simp only [ite_eq_right hv, ite_eq_right hvq, lifted]
        · simp only [replaceSelectedControlSuffix, Function.update_of_ne hr]
    · rfl
  rw [← heq]
  exact ReferenceFirstCollectionRenewalNextControlLaw.renewalCallEvent_iff_nextSuffix
    rate rewards C_star C_h u t hnext source lifted

/-- Replacing only the complete selected control at a later date preserves
membership in the event of the original first renewal call. -/
theorem renewalCallEvent_iff_replaceFutureControl (q : Fin p.T)
    (htq : t.val < q.val) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    source ∈ E ↔ replaceSourceControl p q source control ∈ E := by
  let suffix := fun v : Fin p.T =>
    if v = q then control else
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
  exact renewalCallEvent_iff_futureSuffix rate rewards C_star C_h u t q htq source suffix

/-- The original event is exactly the preimage of itself under the literal
later-date prefix replacement. -/
theorem renewalCallEvent_futurePrefix (q : Fin p.T) (htq : t.val < q.val) :
    E = (c_t p control0 q) ⁻¹' E := by
  ext source
  exact renewalCallEvent_iff_futureSuffix rate rewards C_star C_h u t q htq
    source (fun _ => control0)

/-- The literal later-date observer: replace the selected suffix beginning at
`q` by the fixed baseline and retain the original renewal subtype. -/
def futurePriorObserver (q : Fin p.T) (htq : t.val < q.val) (z : Z) : Z :=
  ⟨c_t p control0 q z.val, by
    change replaceSelectedControlSuffix z.val q (fun _ => control0) ∈ E
    exact (renewalCallEvent_iff_futureSuffix rate rewards C_star C_h u t
      q htq z.val (fun _ => control0)).mp z.property⟩

/-- The value of the observer is exactly the established coordinate prefix. -/
theorem futurePriorObserver_val (q : Fin p.T) (htq : t.val < q.val) (z : Z) :
    (futurePriorObserver rate rewards C_star C_h u t control0 q htq z).val =
      sourcePrefix control0 q.val z.val := by
  change replaceSelectedControlSuffix z.val q (fun _ => control0) = _
  exact (sourcePrefix_eq_suffix control0 q.val q.isLt z.val).symm

/-- Measurability of the actual observer on the original renewal subtype. -/
theorem measurable_futurePriorObserver (q : Fin p.T) (htq : t.val < q.val) :
    Measurable (futurePriorObserver rate rewards C_star C_h u t control0 q htq) := by
  have hval : Measurable (fun z : Z =>
      (futurePriorObserver rate rewards C_star C_h u t control0 q htq z).val) := by
    simp only [futurePriorObserver_val]
    exact (measurable_sourcePrefix control0 q.val).comp measurable_subtype_coe
  exact hval.subtype_mk

/-- The complete continuous selected control at the arbitrary later date. -/
def futureControl (q : Fin p.T) (z : Z) :
    ContinuousLearningRows.TimeControl p := u_t p q z.val

theorem measurable_futureControl (q : Fin p.T) :
    Measurable (futureControl rate rewards C_star C_h u t q) :=
  (measurable_u_t (p := p) q).comp measurable_subtype_coe

/-- The field at `q.val + 1` is the actual original-source prefix field that
retains selected controls strictly before `q.val`. -/
abbrev futurePriorField (q : Fin p.T) : MeasurableSpace Z :=
  MeasurableSpace.comap Subtype.val (sourcePrefixFiltration control0 (q.val + 1))

/-- The filtration successor equation identifies the field with the observer's
comap field; the whole control at `q` is excluded. -/
theorem futurePriorField_eq_comap (q : Fin p.T) (htq : t.val < q.val) :
    futurePriorField rate rewards C_star C_h u t control0 q =
      MeasurableSpace.comap (futurePriorObserver rate rewards C_star C_h u t
        control0 q htq) (inferInstance : MeasurableSpace Z) := by
  change MeasurableSpace.comap Subtype.val
      (sourcePrefixFiltration control0 (q.val + 1)) =
    MeasurableSpace.comap (futurePriorObserver rate rewards C_star C_h u t
      control0 q htq) (MeasurableSpace.comap Subtype.val
        (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)))
  rw [sourcePrefixFiltration_succ, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]
  congr 1

/-- Measurability of the observer with respect to its exact original-source
prefix field. -/
theorem measurable_futurePriorObserver_field (q : Fin p.T) (htq : t.val < q.val) :
    Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      (futurePriorObserver rate rewards C_star C_h u t control0 q htq) := by
  rw [futurePriorField_eq_comap rate rewards C_star C_h u t control0 q htq]
  exact comap_measurable _

theorem futurePriorField_le (q : Fin p.T) (htq : t.val < q.val) :
    futurePriorField rate rewards C_star C_h u t control0 q ≤
      (inferInstance : MeasurableSpace Z) := by
  rw [futurePriorField_eq_comap rate rewards C_star C_h u t control0 q htq]
  exact (measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq).comap_le

/-- Ambient whole-control freshness restricted to the original first-renewal
event. -/
theorem futureControl_ambient_joint (q : Fin p.T) (htq : t.val < q.val) :
    ((μ).restrict E).map (fun source =>
      (c_t p control0 q source, u_t p q source)) =
      (((μ).restrict E).map (c_t p control0 q)).prod κ := by
  let c := c_t p control0 q
  let U := u_t p q
  have hc : Measurable c := measurable_c_t control0 q
  have hU : Measurable U := measurable_u_t q
  have hE := measurableSet_renewalCallEvent rate rewards C_star C_h u t
  have hpre : E = c ⁻¹' E :=
    renewalCallEvent_futurePrefix rate rewards C_star C_h u t control0 q htq
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
    _ = (((μ).restrict E).map c).prod κ := by
      rw [Measure.restrict_map hc hE, ← hpre]
    _ = _ := rfl

/-- The observer and whole later control have the product law under the same
original finite, unnormalized renewal measure. -/
theorem futureControl_joint_prefix (q : Fin p.T) (htq : t.val < q.val) :
    (ν).map (fun z =>
      (futurePriorObserver rate rewards C_star C_h u t control0 q htq z,
        futureControl rate rewards C_star C_h u t q z)) =
      ((ν).map (futurePriorObserver rate rewards C_star C_h u t control0 q htq)).prod κ := by
  let e := futurePriorObserver rate rewards C_star C_h u t control0 q htq
  let U := futureControl rate rewards C_star C_h u t q
  let c := c_t p control0 q
  have he := measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq
  have hU := measurable_futureControl rate rewards C_star C_h u t q
  have hc : Measurable c := measurable_c_t control0 q
  have heval : (fun z : Z => (e z).val) = c ∘ Subtype.val := by
    funext z
    exact futurePriorObserver_val rate rewards C_star C_h u t control0 q htq z
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
      (fun source => (c source, u_t p q source)) ∘ Subtype.val := by
    funext z
    exact Prod.ext (congrFun heval z) rfl
  rw [hfun, ← Measure.map_map (hc.prodMk (measurable_u_t q))
    measurable_subtype_coe, renewalSourceLaw_map_val]
  exact futureControl_ambient_joint rate rewards C_star C_h u t control0 q htq

/-- Product law after every Borel test of the later-date observer. -/
theorem futureControl_joint_prefix_restrict (q : Fin p.T) (htq : t.val < q.val)
    (V : Set Z) (hV : MeasurableSet V) :
    ((ν).restrict ((futurePriorObserver rate rewards C_star C_h u t control0 q htq) ⁻¹' V)).map
        (fun z => (futurePriorObserver rate rewards C_star C_h u t control0 q htq z,
          futureControl rate rewards C_star C_h u t q z)) =
      (((ν).map (futurePriorObserver rate rewards C_star C_h u t control0 q htq)).restrict V).prod κ := by
  let e := futurePriorObserver rate rewards C_star C_h u t control0 q htq
  let U := futureControl rate rewards C_star C_h u t q
  have he := measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq
  have hU := measurable_futureControl rate rewards C_star C_h u t q
  have hp : (fun z => (e z, U z)) ⁻¹' (V ×ˢ Set.univ) = e ⁻¹' V := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [← hp, ← Measure.restrict_map (he.prodMk hU) (hV.prod MeasurableSet.univ),
    futureControl_joint_prefix, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The exact `q`-date whole-control coordinate factors through the existing
fixed-control split; the source stratum remains the original private `J`. -/
def futureRemainderEvent (q : Fin p.T) (ell : Fin (M p)) :
    Set (FixedControlRemainder p ell q) :=
  {r | r ∈ fixedControlRemainderStratum p ell q ∧
    (fixedControlSplit p ell q).symm (control0, r) ∈ E}

theorem measurableSet_futureRemainderEvent (q : Fin p.T) (ell : Fin (M p)) :
    MeasurableSet (futureRemainderEvent rate rewards C_star C_h u t control0 q ell) :=
  (measurableSet_fixedControlRemainderStratum p ell q).inter
    (((fixedControlSplit p ell q).symm.measurable.comp
      (measurable_const.prodMk measurable_id))
        (measurableSet_renewalCallEvent rate rewards C_star C_h u t))

/-- Exact factorization of the original renewal event and private stratum
through the lossless `q`-control split. -/
theorem futureRemainderEvent_factor (q : Fin p.T) (htq : t.val < q.val)
    (ell : Fin (M p)) :
    E ∩ fixedControlSourceStratum p ell =
      fixedControlSplit p ell q ⁻¹'
        (Set.univ ×ˢ futureRemainderEvent rate rewards C_star C_h u t control0 q ell) := by
  let split := fixedControlSplit p ell q
  let R := futureRemainderEvent rate rewards C_star C_h u t control0 q ell
  have hs : ∀ source, source ∈ fixedControlSourceStratum p ell ↔
      (split source).2 ∈ fixedControlRemainderStratum p ell q := by
    intro source
    rw [fixedControlSourceStratum_eq_preimage p ell q]
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  ext source
  change (source ∈ E ∧ source ∈ fixedControlSourceStratum p ell) ↔
    (True ∧ (split source).2 ∈ fixedControlRemainderStratum p ell q ∧
      split.symm (control0, (split source).2) ∈ E)
  constructor
  · rintro ⟨hE, hS⟩
    refine ⟨trivial, (hs source).mp hS, ?_⟩
    rw [fixedControlSplit_replaceSourceControl p ell q source control0 hS]
    exact (renewalCallEvent_iff_replaceFutureControl rate rewards C_star C_h u t
      q htq source control0).mp hE
  · rintro ⟨_, hS, hE⟩
    have hS' := (hs source).mpr hS
    refine ⟨?_, hS'⟩
    rw [fixedControlSplit_replaceSourceControl p ell q source control0 hS'] at hE
    exact (renewalCallEvent_iff_replaceFutureControl rate rewards C_star C_h u t
      q htq source control0).mpr hE

/-- The ambient split law on each actual private stratum, retaining its exact
mass and the full original remainder. -/
theorem futureControl_private_ambient (q : Fin p.T) (htq : t.val < q.val)
    (ell : Fin (M p)) :
    ((μ).restrict (E ∩ fixedControlSourceStratum p ell)).map
        (fixedControlSplit p ell q) =
      (κ).prod ((fixedControlRemainderLaw p ell q).restrict
        (futureRemainderEvent rate rewards C_star C_h u t control0 q ell)) := by
  let split := fixedControlSplit p ell q
  let R := futureRemainderEvent rate rewards C_star C_h u t control0 q ell
  have hR : MeasurableSet R :=
    measurableSet_futureRemainderEvent rate rewards C_star C_h u t control0 q ell
  have hfactor := futureRemainderEvent_factor rate rewards C_star C_h u t control0 q htq ell
  have hrestriction : (μ).restrict (E ∩ fixedControlSourceStratum p ell) =
      ((μ).restrict (fixedControlSourceStratum p ell)).restrict
        (split ⁻¹' (Set.univ ×ˢ R)) := by
    rw [← hfactor]
    exact (Measure.restrict_restrict_of_subset Set.inter_subset_right).symm
  rw [hrestriction, ← Measure.restrict_map split.measurable
    (MeasurableSet.univ.prod hR), fixedControlSplit_privateStratum_map,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict hR]
  congr 2
  exact Set.inter_eq_left.mpr (fun _ hr => hr.1)

/-- Under the existing original private-renewal law, the `q` control is
independent of the complete split remainder, with no mass normalization. -/
theorem futureControl_private_joint (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (htq : t.val < q.val)
    (ell : Fin (M p)) :
    (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map
        (fun z => fixedControlSplit p ell q z.val) =
      (κ).prod ((ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
        rate rewards C_star C_h u t ell).map
          (fun z => (fixedControlSplit p ell q z.val).2)) := by
  let split := fixedControlSplit p ell q
  let ρ := (fixedControlRemainderLaw p ell q).restrict
    (futureRemainderEvent rate rewards C_star C_h u t control0 q ell)
  have hjoint : (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map (fun z => split z.val) = (κ).prod ρ := by
    change (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map (split ∘ Subtype.val) = _
    rw [← Measure.map_map split.measurable measurable_subtype_coe,
      ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw_map_val]
    exact futureControl_private_ambient rate rewards C_star C_h u t control0 q htq ell
  have hsnd : (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map (fun z => (split z.val).2) = ρ := by
    change (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map
        (Prod.snd ∘ (split ∘ Subtype.val)) = _
    rw [← Measure.map_map measurable_snd
      (split.measurable.comp measurable_subtype_coe),
      show (ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
        rate rewards C_star C_h u t ell).map (split ∘ Subtype.val) = (κ).prod ρ from hjoint,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [hjoint, hsnd]

/-- Inverse reconstruction of one original private-stratum restriction. -/
theorem futureControl_private_inverse (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (htq : t.val < q.val)
    (ell : Fin (M p)) :
    ((κ).prod ((ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
      rate rewards C_star C_h u t ell).map
        (fun z => (fixedControlSplit p ell q z.val).2))).map
          (fixedControlSplit p ell q).symm =
      (μ).restrict (E ∩ fixedControlSourceStratum p ell) := by
  rw [← futureControl_private_joint rate rewards C_star C_h u t control0 q htq ell,
    Measure.map_map (fixedControlSplit p ell q).symm.measurable
      (show Measurable (fun z : Z => fixedControlSplit p ell q z.val) from
        (fixedControlSplit p ell q).measurable.comp measurable_subtype_coe)]
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using
    ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw_map_val
      rate rewards C_star C_h u t ell

/-- Summing every actual private index recovers the full original event
restriction; the exhaustive partition is the admitted one from the next-date
producer. -/
theorem futureControl_private_inverse_sum (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (htq : t.val < q.val) :
    Measure.sum (fun ell : Fin (M p) =>
      ((κ).prod ((ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw
        rate rewards C_star C_h u t ell).map
          (fun z => (fixedControlSplit p ell q z.val).2))).map
            (fixedControlSplit p ell q).symm) = (μ).restrict E := by
  simp_rw [futureControl_private_inverse rate rewards C_star C_h u t control0 q htq,
    ← ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw_map_val
      rate rewards C_star C_h u t]
  rw [← Measure.map_sum measurable_subtype_coe.aemeasurable,
    ReferenceFirstCollectionRenewalNextControlLaw.privateRenewalLaw_sum,
    renewalSourceLaw_map_val]

/-- The indicator of a Borel test of the original observer and whole later
control. -/
def futureControlTest (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (futurePriorObserver rate rewards C_star C_h u t control0 q htq z,
      futureControl rate rewards C_star C_h u t q z)

/-- Integral of the same test against the original whole-control probability
law, as a literal function of the retained prefix. -/
def futureControlSectionIntegral
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) : ℝ :=
  ∫ control, B.indicator (fun _ => (1 : ℝ)) (z, control) ∂κ

theorem measurable_futureControlSectionIntegral
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Measurable (futureControlSectionIntegral rate rewards C_star C_h u t B) := by
  have hf : Measurable (B.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hB
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

private theorem indicator_norm_le_one {α : Type*} (B : Set α) (x : α) :
    ‖B.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

theorem futureControlSectionIntegral_norm_le_one
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (z : Z) :
    ‖futureControlSectionIntegral rate rewards C_star C_h u t B z‖ ≤ 1 := by
  exact (norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall (fun control => indicator_norm_le_one B (z, control)))).trans
      (by simp)

private theorem integrable_of_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {testLaw : Measure α} [IsFiniteMeasure testLaw]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f testLaw :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Integrability of every Borel indicator test under the finite original
renewal measure. -/
theorem integrable_futureControlTest (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Integrable (futureControlTest rate rewards C_star C_h u t control0 q htq B) ν := by
  exact integrable_of_measurable_norm_le_one _
    ((measurable_const.indicator hB).comp
      ((measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq).prodMk
        (measurable_futureControl rate rewards C_star C_h u t q)))
    (fun z => indicator_norm_le_one B _)

/-- The candidate section integral is measurable in the exact later prefix
field. -/
theorem measurable_futureControlCandidate (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Measurable[futurePriorField rate rewards C_star C_h u t control0 q]
      (fun z => futureControlSectionIntegral rate rewards C_star C_h u t B
        (futurePriorObserver rate rewards C_star C_h u t control0 q htq z)) :=
  (measurable_futureControlSectionIntegral rate rewards C_star C_h u t B hB).comp
    (measurable_futurePriorObserver_field rate rewards C_star C_h u t control0 q htq)

theorem integrable_futureControlCandidate (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    Integrable (fun z => futureControlSectionIntegral rate rewards C_star C_h u t B
      (futurePriorObserver rate rewards C_star C_h u t control0 q htq z)) ν :=
  integrable_of_measurable_norm_le_one _
    ((measurable_futureControlSectionIntegral rate rewards C_star C_h u t B hB).comp
      (measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq))
    (fun z => futureControlSectionIntegral_norm_le_one rate rewards C_star C_h u t B
      (futurePriorObserver rate rewards C_star C_h u t control0 q htq z))

private theorem futureControl_test_prefix_setIntegral (q : Fin p.T)
    (htq : t.val < q.val) (B : Set (Z × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) (V : Set Z) (hV : MeasurableSet V) :
    ∫ z in (futurePriorObserver rate rewards C_star C_h u t control0 q htq) ⁻¹' V,
      futureControlTest rate rewards C_star C_h u t control0 q htq B z ∂ν =
    ∫ z in (futurePriorObserver rate rewards C_star C_h u t control0 q htq) ⁻¹' V,
      futureControlSectionIntegral rate rewards C_star C_h u t B
        (futurePriorObserver rate rewards C_star C_h u t control0 q htq z) ∂ν := by
  let e := futurePriorObserver rate rewards C_star C_h u t control0 q htq
  let U := futureControl rate rewards C_star C_h u t q
  let pair := fun z : Z => (e z, U z)
  let f : Z × ContinuousLearningRows.TimeControl p → ℝ := B.indicator (fun _ => 1)
  let testLaw := (ν).restrict (e ⁻¹' V)
  let ρ := ((ν).map e).restrict V
  have he := measurable_futurePriorObserver rate rewards C_star C_h u t control0 q htq
  have hp := he.prodMk (measurable_futureControl rate rewards C_star C_h u t q)
  have hf : Measurable f := measurable_const.indicator hB
  have hfint : Integrable f (ρ.prod κ) :=
    integrable_of_measurable_norm_le_one f hf (indicator_norm_le_one B)
  have hjoint : testLaw.map pair = ρ.prod κ :=
    futureControl_joint_prefix_restrict rate rewards C_star C_h u t control0 q htq V hV
  have hprefix : testLaw.map e = ρ := (Measure.restrict_map he hV).symm
  calc
    _ = ∫ z, f (pair z) ∂testLaw := rfl
    _ = ∫ x, f x ∂(testLaw.map pair) :=
      (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, f x ∂(ρ.prod κ) := by rw [hjoint]
    _ = ∫ z, ∫ control, f (z, control) ∂κ ∂ρ := integral_prod f hfint
    _ = ∫ z, futureControlSectionIntegral rate rewards C_star C_h u t B z
        ∂(testLaw.map e) := by
      rw [hprefix]
      rfl
    _ = _ := integral_map he.aemeasurable
      (measurable_futureControlSectionIntegral rate rewards C_star C_h u t B hB).aestronglyMeasurable

/-- Set-integral characterization for every measurable event in the later
original-source prefix field. -/
theorem futureControl_test_setIntegral (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B)
    (G : Set Z) (hG : MeasurableSet[futurePriorField rate rewards C_star C_h u t control0 q] G) :
    ∫ z in G, futureControlTest rate rewards C_star C_h u t control0 q htq B z ∂ν =
      ∫ z in G, futureControlSectionIntegral rate rewards C_star C_h u t B
        (futurePriorObserver rate rewards C_star C_h u t control0 q htq z) ∂ν := by
  rw [futurePriorField_eq_comap rate rewards C_star C_h u t control0 q htq] at hG
  obtain ⟨V, hV, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hG
  exact futureControl_test_prefix_setIntegral rate rewards C_star C_h u t control0 q
    htq B hB V hV

/-- Conditional expectation of every bounded Borel test of the observer and
whole later control, directly under the same original renewal measure. -/
theorem futureControl_test_condExp (q : Fin p.T) (htq : t.val < q.val)
    (B : Set (Z × ContinuousLearningRows.TimeControl p)) (hB : MeasurableSet B) :
    (ν)[futureControlTest rate rewards C_star C_h u t control0 q htq B |
      futurePriorField rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (futurePriorObserver rate rewards C_star C_h u t control0 q htq z, control) ∂κ := by
  have hfint := integrable_futureControlTest rate rewards C_star C_h u t control0 q htq B hB
  have hgint := integrable_futureControlCandidate rate rewards C_star C_h u t control0 q htq B hB
  have hgmeas := measurable_futureControlCandidate rate rewards C_star C_h u t control0 q htq B hB
  exact (ae_eq_condExp_of_forall_setIntegral_eq
    (futurePriorField_le rate rewards C_star C_h u t control0 q htq) hfint
    (fun _ _ _ => hgint.integrableOn)
    (fun G hG _ => (futureControl_test_setIntegral
      rate rewards C_star C_h u t control0 q htq B hB G hG).symm)
    hgmeas.stronglyMeasurable.aestronglyMeasurable).symm

/-- At `q=t+1`, the general literal observer is exactly the existing
next-date observer on the same original source subtype. -/
theorem futurePriorObserver_eq_nextPriorObserver (hq : t.val + 1 < p.T) :
    futurePriorObserver rate rewards C_star C_h u t control0 ⟨t.val + 1, hq⟩ (by simp) =
      ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 := by
  have hlater : t.val < (⟨t.val + 1, hq⟩ : Fin p.T).val := by simp
  funext z
  apply Subtype.ext
  rw [futurePriorObserver_val rate rewards C_star C_h u t control0 _ hlater,
    ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver_val]

/-- At `q=t+1`, the general field is exactly the existing next-date field. -/
theorem futurePriorField_eq_nextPriorField (hq : t.val + 1 < p.T) :
    futurePriorField rate rewards C_star C_h u t control0 ⟨t.val + 1, hq⟩ =
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0 := rfl

/-- At `q=t+1`, the whole control coordinate is the existing next control. -/
theorem futureControl_eq_nextControl (hq : t.val + 1 < p.T) (z : Z) :
    futureControl rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ z =
      ReferenceFirstCollectionRenewalNextControlLaw.nextControl
        rate rewards C_star C_h u t hq z := rfl

end Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw

end
