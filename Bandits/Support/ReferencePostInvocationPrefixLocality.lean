/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationNoncallGeometry

import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Borel readouts and causal projections of the actual post-invocation prefix

All constructions below use the existing post-invocation recursion. The causal
projection changes only the two physical source fields of its full observation.
Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
These are internal code-level results and do not assert a manuscript law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors hiding Record
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFixedTimeSourceControlCoupling
open ReferenceActiveHorizonMeasurability
open ReferenceLaterCollectionSourceReadoutMeasurability

namespace Bandits.Support.ReferencePostInvocationPrefixLocality

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Scalar := ContinuousControlSlice.Scalar

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤

local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private instance sumSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image

private instance listSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (List A) where
  measurableSet_singleton L := by
    have hi : Function.Injective (listObservationCoordinates (α := A)) := by
      intro B C h
      apply List.ext_getElem (congrArg Prod.fst h)
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have h := measurable_listObservationCoordinates (measurableSet_singleton (listObservationCoordinates L))
    convert h using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hi.eq_iff]

private instance optionSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit A) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit A).injective.eq_iff.symm

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have he := (comap_measurable (Equiv.optionEquivSumPUnit A)).comp hf
  have hi : MeasurableEmbedding (@Sum.inl A PUnit) := ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hi.measurable_comp_iff.mp he

private theorem measurable_option_cases {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) : Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

private theorem measurable_isSome {A : Type*} [MeasurableSpace A] : Measurable (Option.isSome : Option A → Bool) := by
  convert measurable_option_cases id measurable_id (fun _ => false) measurable_const
    (fun _ => true) measurable_const using 1
  funext o
  cases o <;> rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

open ReferencePostInvocationNoncallGeometry

-- All local readout notation keeps the same rate, rewards and shared constants.
local notation "numericalPre" => prefixNumerical rate rewards C_star C_h
local notation "recordAt" => actualRecord rate rewards C_star C_h
local notation "collectionDomain" => collectionDateDomain rate rewards C_star C_h
local notation "collectionRecordAt" => collectionRecord rate rewards C_star C_h
local notation "collectionInputAt" => collectionInput rate rewards C_star C_h
local notation "collectionPre" => collectionBefore rate rewards C_star C_h
local notation "collectionArgumentsAt" => collectionArguments rate rewards C_star C_h
local notation "collectionCellAt" => laterCollectionCell rate rewards C_star C_h
local notation "continuingRecordAt" => continuingRecord rate rewards C_star C_h
local notation "continuingCellWitness" => continuingSourceCell rate rewards C_star C_h
local notation "continuingPre" => continuingBefore rate rewards C_star C_h
local notation "continuingCellAt" => continuingLogicalCell rate rewards C_star C_h
local notation "noncallCellAt" => noncallDateCell rate rewards C_star C_h
local notation "noncallCalendarAt" => noncallCalendar rate rewards C_star C_h
local notation "generatedPrefix" => postInvocationPrefix rate rewards C_star C_h
local notation "nativeFirstCell" => actualFirstCell rate rewards C_star C_h

local notation "noCallAt" => ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h
local notation "originalPast" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h

/-- Numerical PRE is Borel on the entire source, including absent prefixes.
The inverse below simply restores the three fields of the accepted readout. -/
theorem measurable_prefixNumerical (n : Fin (p.T + 1)) : Measurable (numericalPre n) := by
  let decode := fun r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) =>
    (⟨r.1, r.2.1, r.2.2⟩ : RecordedQueueRun.RunState p.K)
  have h := LaterAssignmentFullOutputMeasurability.measurable_optionMap decode (measurable_of_countable decode) _
    ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n.val).mono le_rfl le_top)
  convert h using 1
  funext z
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
    prefixNumerical, Option.map_map, Function.comp_def]
  rfl

/-- The literal finite positive collection formula is Borel without an
envelope comparison or a replacement by the native fast-law formula. -/
theorem measurable_collectionFastDraw {X : Type*} [MeasurableSpace X]
    (anchor weight : X → Fin p.K → ℝ) (ha : Measurable anchor) (hw : Measurable weight)
    (hapos : ∀ x j, 0 < anchor x j) (hwpos : ∀ x j, 0 < weight x j)
    (U : SlowSet p) (scalar : X → Scalar) (hs : Measurable scalar) :
    Measurable (fun x => collectionFastDraw rate (anchor x) (weight x) (hapos x) (hwpos x) U (scalar x)) := by
  have hc (j : CanonicalFastSampling.FastArm U) : Measurable (fun x =>
      FastComplementLocality.localFastCandidateMass (anchor x) U (fun j => weight x j.val) j) := by
    unfold FastComplementLocality.localFastCandidateMass FiniteOrientationDisintegration.inverseAnchorSum
    exact ((measurable_pi_apply j.val).comp hw).div (measurable_const.add ((Finset.measurable_fun_sum U.val fun i _ =>
        measurable_const.div ((measurable_pi_apply i).comp ha)).mul ((measurable_pi_apply j.val).comp ha)))
  have hn : Measurable (fun x => FastComplementLocality.localFastNormalizer (anchor x) U (fun j => weight x j.val)) :=
    Finset.measurable_fun_sum Finset.univ fun j _ => hc j
  let masses (x : X) (k : Fin (p.K - p.m + 1)) := collectionFastMass rate
    (anchor x) (weight x) (hapos x) (hwpos x) U (CanonicalFastSampling.fastArmOrderIso U k)
  have hm (k) : Measurable (fun x => masses x k) := by
    exact (measurable_const.mul ((hc _).div hn)).add measurable_const
  apply measurable_to_countable'
  intro j
  have he : {x | collectionFastDraw rate (anchor x) (weight x) (hapos x) (hwpos x) U
      (scalar x) = j} = {x | ContinuousCategorical.lower (masses x)
        ((CanonicalFastSampling.fastArmOrderIso U).symm j) ≤ (scalar x).val ∧
      (scalar x).val < ContinuousCategorical.upper (masses x) ((CanonicalFastSampling.fastArmOrderIso U).symm j)} := by
    ext x
    change CanonicalFastSampling.fastArmOrderIso U (ContinuousCategorical.sample _ (masses x) _ (scalar x)) = j ↔ _
    rw [← OrderIso.eq_symm_apply]
    exact ContinuousCategorical.sample_eq_iff _ (fun k => collectionFastMass_nonneg rate _ _ _ _ U _) _ _ _
  change MeasurableSet {x | collectionFastDraw rate (anchor x) (weight x) (hapos x) (hwpos x) U (scalar x) = j}
  rw [he]
  exact (measurableSet_le (Finset.measurable_fun_sum _ fun k _ => hm k) (measurable_subtype_coe.comp hs)).inter
    (measurableSet_lt (measurable_subtype_coe.comp hs) (Finset.measurable_fun_sum _ fun k _ => hm k))

private theorem measurable_accepted {X : Type*} [MeasurableSpace X]
    (S : X → RecordedQueueRun.RunState p.K) (c : X → RecordedQueueRun.RoundInput p.K)
    (hS : Measurable S) (hc : Measurable (fun x =>
      numericalCoordinates (c x))) : Measurable (fun x => RecordedQueueRun.acceptedRecord Q (S x) (c x)) := by
  let f := fun v : RecordedQueueRun.RunState p.K × (Bool × (Fin p.K → ℕ)) =>
    fun a => if v.1.overflow then (false, 0) else if v.2.1 then (true, v.2.2 a) else (false, 0)
  exact (measurable_of_countable f).comp (hS.prodMk ((measurable_arrivalsFromNumerical rate).comp hc))

private theorem measurable_step {X : Type*} [MeasurableSpace X]
    (S : X → RecordedQueueRun.RunState p.K) (c : X → RecordedQueueRun.RoundInput p.K)
    (hS : Measurable S) (hc : Measurable (fun x =>
      numericalCoordinates (c x))) : Measurable (fun x => RecordedQueueRun.step Q (S x) (c x)) := by
  let update := fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
    let registers := fun a => QueueReplay.transition (4 * (Q).n) (v.1.registers a) (v.2 a)
    (⟨registers, v.1.overflow || decide (∃ a, 32 * (registers a).2 > (Q).D),
      fun a => v.1.records a ++ [v.2 a]⟩ : RecordedQueueRun.RunState p.K)
  exact (measurable_of_countable update).comp (hS.prodMk (measurable_accepted rate S c hS hc))

private theorem actualRecord_start (q : Fin p.T) (z : Source p) (r : Record rate) (hr : recordAt q z = some r) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val := by
  by_contra h
  have hn := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_none_iff
    rate rewards C_star C_h q z).mpr (Nat.lt_of_not_ge h)
  change recordAt q z = none at hn
  rw [hn] at hr
  cases hr

private theorem collectionCall_isSome (r : Record rate) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r).isSome =
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome := by
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
  split
  · split <;> simp_all only [Option.isSome_some, Option.isSome_none]
    split_ifs <;> rfl
  · rfl

private theorem measurable_collectionNumerical (q : Fin p.T) : Measurable (fun z : Source p =>
    (recordAt q z).bind (fun r => (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
        numericalCoordinates)) := by
  exact ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualReadout rate rewards C_star C_h
    _ (fun k => (measurable_actualReadout_numerical
      rate rewards C_star C_h k).comp (measurable_const.prodMk measurable_id)) q

theorem collectionDateDomain_iff (q : Fin p.T) (z : Source p) : z ∈ collectionDomain q ↔ ((recordAt q z).bind
        (fun r => (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
          numericalCoordinates)).isSome = true := by
  constructor
  · rintro ⟨r, hr, _, hc⟩
    simpa only [hr, Option.bind_some, Option.isSome_map] using (collectionCall_isSome rate r).symm.trans hc
  · intro h
    obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨c, hc, _⟩ := Option.map_eq_some_iff.mp hc
    exact collectionDateDomain_of_readout rate rewards C_star C_h q z r hr c hc

theorem measurableSet_collectionDateDomain (q : Fin p.T) : MeasurableSet (collectionDomain q) := by
  have he : collectionDomain q = {z | ((recordAt q z).bind
        (fun r => (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
          numericalCoordinates)).isSome = true} := by
    ext z
    exact collectionDateDomain_iff rate rewards C_star C_h q z
  rw [he]
  exact (measurableSet_singleton true).preimage (measurable_isSome.comp (measurable_collectionNumerical rate rewards C_star C_h q))

theorem measurable_collectionPhysical (q : Fin p.T) : Measurable (fun z :
    CollectionDateSource rate rewards C_star C_h q =>
      roundRecordCode (collectionRecordAt q z)) := by
  apply measurable_of_some
  convert (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h q).comp (measurable_subtype_coe (p := fun z =>
      z ∈ collectionDomain q)) using 1
  funext z
  simp only [Function.comp_apply, ReferenceCalendarActualControlCallbackSections.codeAt,
    (collectionRecord_spec rate rewards C_star C_h q z).1, Option.map_some]

theorem collectionInput_spec (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      (collectionRecordAt q z) = some (collectionInputAt q z) := by
  have hs := collectionRecord_spec rate rewards C_star C_h q z
  have hc := (collectionCall_isSome rate _).symm.trans hs.2.2
  have hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 (collectionRecordAt q z) = none := by
    cases h : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 (collectionRecordAt q z) with
    | none => rfl
    | some c => exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 _
        ⟨by rw [h]; rfl, hc⟩)
  have h : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (collectionRecordAt q z) = some (collectionInputAt q z) := (Option.some_get hs.2.1).symm
  simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.none_or] using h

theorem measurable_collectionInput (q : Fin p.T) : Measurable (fun z : CollectionDateSource rate rewards C_star C_h q =>
      numericalCoordinates (collectionInputAt q z)) := by
  apply measurable_of_some
  convert (measurable_collectionNumerical rate rewards C_star C_h q).comp
    (measurable_subtype_coe (p := fun z => z ∈ collectionDomain q)) using 1
  funext z
  simp only [Function.comp_apply, (collectionRecord_spec rate rewards C_star C_h q z).1,
    Option.bind_some, collectionInput_spec rate rewards C_star C_h q z, Option.map_some]

theorem collectionBefore_spec (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    numericalPre q.castSucc z.val = some (collectionPre q z) :=
  prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val
    (collection_launch rate rewards C_star C_h q z) (actualRecord_start rate rewards C_star C_h q z.val
      (collectionRecordAt q z) (collectionRecord_spec rate rewards C_star C_h q z).1)

theorem continuingBefore_spec (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :
    numericalPre q.castSucc z.val = some (continuingPre q z) :=
  prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val
    (continuing_launch rate rewards C_star C_h q z) (actualRecord_start rate rewards C_star C_h q z.val
      (continuingRecordAt q z) (continuingSourceCell_spec rate rewards C_star C_h q z).1)

theorem measurable_collectionBefore (q : Fin p.T) : Measurable (collectionPre q) := by
  apply measurable_of_some
  convert (measurable_prefixNumerical rate rewards C_star C_h q.castSucc).comp
    (measurable_subtype_coe (p := fun z => z ∈ collectionDomain q)) using 1
  funext z
  exact (collectionBefore_spec rate rewards C_star C_h q z).symm

theorem measurable_collectionAnchor (control0 : TimeControl p) (q : Fin p.T) : Measurable (fun z :
    CollectionDateSource rate rewards C_star C_h q => (collectionArgumentsAt q z).1.anchor) := by
  apply measurable_of_some
  have h := ReferenceFirstCollectionOldRecorderFoundation.incomingAnchor_measurable rate rewards C_star C_h control0 q
  have hh := h.mono ((sourcePrefixFiltration control0).le (q.val + 1)) le_rfl
  convert hh.comp (measurable_subtype_coe (p := fun z =>
    z ∈ collectionDomain q)) using 1
  funext z
  dsimp only [Function.comp_apply]
  rw [ReferenceFirstCollectionOldRecorderFoundation.incomingAnchor?,
    collectionArguments_incoming rate rewards C_star C_h q z, Option.map_some]

theorem measurable_laterCollectionCell (control0 : TimeControl p) (q : Fin p.T) (U : SlowSet p) :
    Measurable (fun v : CollectionDateSource rate rewards C_star C_h q × Auxiliary p =>
      collectionCellAt q v.1 U v.2) := by
  let X := CollectionDateSource rate rewards C_star C_h q × Auxiliary p
  let S := fun v : X => collectionPre q v.1
  let c := fun v : X => collectionInputAt q v.1
  let anchor := fun v : X => (collectionArgumentsAt q v.1).1.anchor
  have hb : Measurable S := (measurable_collectionBefore rate rewards C_star C_h q).comp measurable_fst
  have hn := (measurable_collectionInput rate rewards C_star C_h q).comp (measurable_fst : Measurable (Prod.fst : X → _))
  have ha := measurable_accepted rate S c hb hn
  have hafter := measurable_step rate S c hb hn
  have hanchor : Measurable anchor := (measurable_collectionAnchor rate rewards C_star C_h control0 q).comp measurable_fst
  have ho := (measurable_of_countable (fun s : RecordedQueueRun.RunState p.K => s.overflow)).comp hb
  have hcut := (measurableSet_singleton true).preimage ho
  have hcoin : Measurable (fun v : X => decide ((v.2 (q, 0)).val < 4 * p.m * rate.eta.val)) := by
    have h : Measurable (fun v : X => if (v.2 (q, 0)).val < 4 * p.m * rate.eta.val
        then true else false) := (measurable_const (a := true)).ite (measurableSet_lt
      (measurable_subtype_coe.comp ((measurable_pi_apply (q, 0)).comp
        (measurable_snd : Measurable (Prod.snd : X → _)))) measurable_const)
      (measurable_const (a := false))
    convert h using 1
    funext v
    by_cases h : (v.2 (q, 0)).val < 4 * p.m * rate.eta.val <;>
      simp only [h, decide_true, decide_false, ite_true, ite_false]
  have hp := (measurable_of_countable (fun b : Bool × Bool × Bool => b.1 && !b.2.1 && b.2.2)).comp
    ((measurable_fst.comp hn).prodMk (ho.prodMk hcoin))
  have hf := measurable_collectionFastDraw rate anchor _ hanchor
    ((measurable_of_countable (RecordedQueueRun.scoreWeight Q)).comp hb)
    (fun v => (collectionArgumentsAt q v.1).1.anchor_pos)
    (fun v => RecordedSlowRefresh.scoreWeight_pos Q (S v)) U
    (fun v => ReferenceSourceFastScalarDisintegration.sourceFastScalar p q v.1.val)
    ((ReferenceSourceFastScalarDisintegration.measurable_sourceFastScalar p q).comp
      (measurable_subtype_coe.comp measurable_fst))
  have hres := measurable_residualDraw_of_actualPrePost rate S
    (fun v => RecordedQueueRun.step Q (S v) (c v)) c hb hafter (fun _ => rfl)
    anchor hanchor (fun v => (collectionArgumentsAt q v.1).1.anchor_pos)
    (fun v => v.2 (q, 1)) ((measurable_pi_apply (q, 1)).comp measurable_snd)
  have hservice := (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
    fun j => RecordedQueueRun.recordService (4 * (Q).n) (v.1.registers j) (v.2 j))).comp (hb.prodMk ha)
  have hslow : @Measurable X (SlowSet p) inferInstance ⊤
      (fun v => if (S v).overflow then frozenSlowSet p else U) := measurable_const.ite hcut measurable_const
  have hfast : Measurable (fun v : X => if (S v).overflow then frozenFastArm p else
      (collectionFastDraw rate (anchor v) (RecordedQueueRun.scoreWeight Q (S v))
        (collectionArgumentsAt q v.1).1.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q (S v)) U
        (ReferenceSourceFastScalarDisintegration.sourceFastScalar p q v.1.val)).val) :=
    measurable_const.ite hcut (measurable_subtype_coe.comp hf)
  have hnext : Measurable (fun v : X => if (S v).overflow then frozenSlowSet p else
      if (c v).enabled && !(S v).overflow && decide ((v.2 (q, 0)).val < 4 * p.m * rate.eta.val) then
        residualDraw rate (S v) (c v) (anchor v) (collectionArgumentsAt q v.1).1.anchor_pos (v.2 (q, 1)) else U) :=
    measurable_const.ite hcut
    (hres.ite ((measurableSet_singleton true).preimage hp) (measurable_const (a := U)))
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (((measurable_collectionPhysical rate rewards C_star C_h q).comp
    measurable_fst).prodMk (hn.prodMk (hb.prodMk (hafter.prodMk (ha.prodMk
      (hservice.prodMk (hslow.prodMk (hfast.prodMk (hp.prodMk hnext)))))))))

private theorem measurable_appendLogicalCell {X : Type*} [MeasurableSpace X] (r : X → Record rate)
    (cell : ∀ x, ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (r x))
    (S : X → RecordedQueueRun.RunState p.K) (a : X → Auxiliary p)
    (hphysical : Measurable (fun x => roundRecordCode (r x)))
    (hinput : Measurable (fun x => (r x).input))
    (hnum : Measurable (fun x => numericalCoordinates (cell x).input))
    (hS : Measurable S) (ha : Measurable a) : Measurable (fun x => appendLogicalCell (r x) (cell x) (S x) (a x)) := by
  have hview : Measurable (fun x => (cell x).selected.view) := by
    have hm := measurable_fst.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hphysical)))
    have hs : Measurable (fun x => some (ReferenceLiveDispatchOutputMeasurability.encodeSelection
        (cell x).selected)) := by
      convert hm using 1
      funext x
      dsimp only [Function.comp_apply]
      rw [(roundRecordCode_front (r x)).1]
      have he : (r x).output.preparation.coordinator.selection =
          (ReferenceActivePhysicalStep.dispatch (r x).input).selection := by rw [(r x).output_eq]; rfl
      rw [← he, (cell x).selection_actual]
      rfl
    exact measurable_fst.comp (measurable_of_some _ hs)
  have hv := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp hview
  have hanchor := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp (measurable_fst.comp hv)
  have hslow : Measurable (fun x => (cell x).selected.view.payload.slowSet) := by
    have hm := ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp (measurable_fst.comp hv)
    apply measurable_to_countable'
    intro U
    have hval := measurable_subtype_coe.comp hm
    convert (measurableSet_singleton U.val).preimage hval using 1
    ext x
    exact Subtype.ext_iff
  have ht := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hinput
  have hscalar : Measurable (fun x => ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      ((r x).input.row.2 (r x).input.time).1) := by
    have heval : Measurable (fun v : Fin p.T × ContinuousLearningRows.LearningRow p => (v.2 v.1).1) :=
      measurable_from_prod_countable_right fun t => measurable_fst.comp (measurable_pi_apply t)
    exact (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast).comp
      (heval.comp (ht.prodMk (measurable_snd.comp (ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput))))
  have hreserved : Measurable (fun x => (reservedFastArm (r x) (cell x)).val) := by
    have hdraw : Measurable (fun v : Fin p.T × (ReferenceDownReception.ChoiceTimeView p rate.eta × Scalar) =>
        ReferenceRankInstallationRecorderFastLaw.reservedFastObservation rate v.1 v.2) :=
      measurable_from_prod_countable_right fun t =>
        ReferenceRankInstallationRecorderFastLaw.measurable_reservedFastObservation rate t
    have hm : Measurable (fun x => ReferenceRankInstallationRecorderFastLaw.reservedFastObservation rate
        (r x).input.time ((cell x).selected.view,
          ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast ((r x).input.row.2 (r x).input.time).1)) :=
      hdraw.comp (ht.prodMk (hview.prodMk hscalar))
    apply measurable_of_some
    convert hm.mono le_rfl (le_top : optionMeasurableSpace (A := Fin p.K) ≤ ⊤) using 1
    funext x
    simp only [ReferenceRankInstallationRecorderFastLaw.reservedFastObservation,
      dite_eq_left (cell x).choiceInputsValid]
    rfl
  have ho := (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp hS
  have hcut := (measurableSet_singleton true).preimage ho
  have harrivals := measurable_accepted rate S (fun x => (cell x).input) hS hnum
  have hafter := measurable_step rate S (fun x => (cell x).input) hS hnum
  have hservice := (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
    fun i => RecordedQueueRun.recordService (4 * (Q).n) (v.1.registers i) (v.2 i))).comp (hS.prodMk harrivals)
  have hp := (measurable_of_countable (fun v : Bool × Bool => !v.1 && v.2)).comp
    (ho.prodMk ((FollowerReleaseFinishMeasurability.measurable_completeRowProposalBitAt p rate.eta.val).comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput).prodMk ht)))
  have heval : Measurable (fun v : Fin p.T × Auxiliary p => v.2 (v.1, 1)) :=
    measurable_from_prod_countable_right fun t => measurable_pi_apply (t, 1)
  have hres := measurable_residualDraw_of_actualPrePost rate S _ (fun x => (cell x).input)
    hS hafter (fun _ => rfl) _ hanchor (fun x => (cell x).selected.view.payload.anchor_pos)
    _ (heval.comp (ht.prodMk ha))
  have hnext : Measurable (fun x => if (S x).overflow then frozenSlowSet p else
      if !(S x).overflow && FollowerCutoffScan.completeRowProposalBit p rate.eta.val (r x).input.row (r x).input.time then
        residualDraw rate (S x) (cell x).input (cell x).selected.view.payload.anchor
          (cell x).selected.view.payload.anchor_pos (a x ((r x).input.time, 1))
      else (cell x).selected.view.payload.slowSet) := (measurable_const (a := frozenSlowSet p)).ite hcut
    (hres.ite ((measurableSet_singleton true).preimage hp) hslow)
  apply measurable_comap_iff.mpr
  exact ht.prodMk (hphysical.prodMk (hnum.prodMk (hS.prodMk (hafter.prodMk
    (harrivals.prodMk (hservice.prodMk ((measurable_const.ite hcut hslow).prodMk
      ((measurable_const.ite hcut hreserved).prodMk (hp.prodMk hnext)))))))))

theorem measurable_continuingPhysical (q : Fin p.T) : Measurable (fun z :
    ContinuingLiveSource rate rewards C_star C_h q => roundRecordCode (continuingRecordAt q z)) := by
    apply measurable_of_some
    convert (ReferenceCalendarActualControlCallbackSections.measurable_codeAt rate rewards C_star C_h q).comp
      (measurable_subtype_coe (p := fun z => z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q)) using 1
    funext z
    simp only [Function.comp_apply, ReferenceCalendarActualControlCallbackSections.codeAt,
      (continuingSourceCell_spec rate rewards C_star C_h q z).1, Option.map_some]
theorem measurable_continuingInput (q : Fin p.T) : Measurable (fun z :
    ContinuingLiveSource rate rewards C_star C_h q => (continuingRecordAt q z).input) := by
    apply measurable_of_some
    convert (ReferenceFirstCollectionCorrectedNextPhysicalReadout.measurable_actualInput?
      rate rewards C_star C_h q).comp (measurable_subtype_coe (p := fun z =>
        z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q)) using 1
    funext z
    simp only [Function.comp_apply, ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?,
      (continuingSourceCell_spec rate rewards C_star C_h q z).1, Option.map_some]
theorem measurable_continuingNumerical (q : Fin p.T) : Measurable (fun z :
    ContinuingLiveSource rate rewards C_star C_h q => numericalCoordinates (continuingCellWitness q z).input) := by
    apply measurable_of_some
    convert (ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualNumerical
      rate rewards C_star C_h q).comp (measurable_subtype_coe (p := fun z =>
        z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q)) using 1
    funext z
    have hs := continuingSourceCell_spec rate rewards C_star C_h q z
    simp only [Function.comp_apply, ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt, hs.1, Option.bind_some,
      hs.2.1, Option.map_some, hs.2.2]
    rfl
theorem measurable_continuingBefore (q : Fin p.T) : Measurable (continuingPre q) := by
    apply measurable_of_some
    convert (measurable_prefixNumerical rate rewards C_star C_h q.castSucc).comp (measurable_subtype_coe (p := fun z =>
        z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q)) using 1
    funext z
    exact (continuingBefore_spec rate rewards C_star C_h q z).symm
theorem measurable_continuingLogicalCell (q : Fin p.T) : Measurable (fun v :
    ContinuingLiveSource rate rewards C_star C_h q × Auxiliary p =>
      continuingCellAt q v.1 v.2) := by
  exact measurable_appendLogicalCell (X := ContinuingLiveSource rate rewards C_star C_h q × Auxiliary p)
    rate (fun v => continuingRecordAt q v.1)
    (fun v => continuingCellWitness q v.1)
    (fun v => continuingPre q v.1) Prod.snd
    ((measurable_continuingPhysical rate rewards C_star C_h q).comp measurable_fst)
    ((measurable_continuingInput rate rewards C_star C_h q).comp measurable_fst)
    ((measurable_continuingNumerical rate rewards C_star C_h q).comp measurable_fst)
    ((measurable_continuingBefore rate rewards C_star C_h q).comp measurable_fst) measurable_snd

theorem measurable_noncallDateCell (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (fun v : SlowSet p × (Source p × Auxiliary p) =>
      noncallCellAt q v.2.1 v.2.2 v.1) := by
  apply measurable_from_prod_countable_right
  intro U
  let X := Source p × Auxiliary p
  let E := {v : X | v.1 ∈ collectionDomain q}
  have hE : MeasurableSet E := (measurableSet_collectionDateDomain rate rewards C_star C_h q).preimage measurable_fst
  have hc : Measurable (fun v : ↥E => laterCollectionCell? rate rewards C_star C_h q
      ⟨v.val.1, v.property⟩ U v.val.2) := by
    have hm : Measurable (fun v : ↥E =>
        (⟨v.val.1, v.property⟩ : CollectionDateSource rate rewards C_star C_h q)) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk
    have hp := hm.prodMk (measurable_snd.comp measurable_subtype_coe)
    have hn := (measurable_collectionInput rate rewards C_star C_h q).comp hm
    exact (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      ((measurable_laterCollectionCell rate rewards C_star C_h control0 q U).comp hp)).ite
      ((measurableSet_singleton true).preimage (measurable_fst.comp hn)) measurable_const
  have hcol := hc.dite (measurable_const (a := (none : Option (LogicalCell p rate)))) hE
  let L := {v : X | v.1 ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q}
  have hL : MeasurableSet L := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurableSet_actualDomain
    rate rewards C_star C_h q).preimage measurable_fst
  have hlive : Measurable (fun v : ↥L => some (continuingCellAt q ⟨v.val.1, v.property⟩ v.val.2)) := by
    have hm : Measurable (fun v : ↥L =>
        ((⟨v.val.1, v.property⟩ : ContinuingLiveSource rate rewards C_star C_h q), v.val.2)) :=
      ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk (measurable_snd.comp measurable_subtype_coe)
    have hh := (measurable_continuingLogicalCell rate rewards C_star C_h q).comp hm
    have hh' := LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hh
    convert hh' using 1
    funext v
    rfl
  exact hlive.dite (hcol.comp measurable_subtype_coe) hL

theorem measurable_appendNoncallDate (control0 : TimeControl p) (q : Fin p.T) :
    Measurable (fun v : (Source p × Auxiliary p) × (SlowSet p × List (LogicalCell p rate)) =>
      appendNoncallDate rate rewards C_star C_h q v.1.1 v.1.2 v.2) := by
  let X := (Source p × Auxiliary p) × (SlowSet p × List (LogicalCell p rate))
  have hc := (measurable_noncallDateCell rate rewards C_star C_h control0 q).comp
    (measurable_snd.fst.prodMk (measurable_fst : Measurable (Prod.fst : X → _)))
  have hn : Measurable (fun c : LogicalCell p rate => c.nextSlowSet) :=
    measurable_logicalCell_nextSlowSet.mono le_rfl le_top
  have happend : Measurable (fun v : List (LogicalCell p rate) × LogicalCell p rate => v.1 ++ [v.2]) :=
    (ReferenceFirstLiveCalendarMarkedTransition.measurable_appendCurrentTag rate).comp
      (measurable_fst.prodMk (measurable_inr.comp measurable_snd))
  convert measurable_option_cases _ hc _ measurable_snd _ ((hn.comp measurable_snd).prodMk (happend.comp
      (measurable_fst.snd.snd.prodMk measurable_snd))) using 1
  funext v
  unfold appendNoncallDate
  dsimp only [Function.comp_apply]
  cases noncallCellAt q v.1.1 v.1.2 v.2.1 <;> rfl

theorem measurable_noncallCalendar (control0 : TimeControl p) (t : Fin p.T) (k : ℕ) :
    Measurable (fun v : (Source p × Auxiliary p) × (SlowSet p × List (LogicalCell p rate)) =>
      noncallCalendarAt t v.1.1 v.1.2 v.2 k) := by
  induction k with
  | zero => exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_snd
  | succ k ih =>
      let X := (Source p × Auxiliary p) × (SlowSet p × List (LogicalCell p rate))
      have hstep : Measurable (fun v : X × (SlowSet p × List (LogicalCell p rate)) =>
          if h : t.val < k ∧ k < p.T then
            if noCallAt ⟨k, h.2⟩ v.1.1.1 then
              some (appendNoncallDate rate rewards C_star C_h ⟨k, h.2⟩ v.1.1.1 v.1.1.2 v.2)
            else none
          else some v.2) := by
        by_cases h : t.val < k ∧ k < p.T
        · simp only [dite_eq_left h]
          exact (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
            ((measurable_appendNoncallDate rate rewards C_star C_h control0 ⟨k, h.2⟩).comp
              (measurable_fst.fst.prodMk measurable_snd))).ite
            ((ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt rate rewards C_star C_h
              control0 ⟨k, h.2⟩).preimage measurable_fst.fst.fst) measurable_const
        · simp only [dite_eq_right h]
          exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_snd
      convert measurable_option_cases _ ih (fun _ : X => none) measurable_const _ hstep using 1
      funext v
      rw [noncallCalendar]
      cases noncallCalendarAt t v.1.1 v.1.2 v.2 k <;> rfl

theorem measurable_postInvocationPrefix (control0 : TimeControl p) (t : Fin p.T)
    (n : Fin (p.T + 1)) : Measurable (fun v : TransitionData rate t × Auxiliary p =>
      generatedPrefix t n v.1 v.2) := by
  exact (measurable_noncallCalendar rate rewards C_star C_h control0 t n.val).comp
    ((((measurable_insertedPhysicalSource rate t).comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_logicalCell_nextSlowSet.comp measurable_fst.snd.snd.snd).prodMk
        ((ReferenceFirstNextInstallationTransitionLaw.measurable_postHistory rate t).comp measurable_fst)))

theorem measurable_nonrenewedGeneratedObservation (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) : Measurable (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n) := by
  have hi := measurable_nonrenewedInitialObservation rate rewards C_star C_h control0 u t
  have hsource := measurable_fst.snd.comp (measurable_fst.comp hi)
  have hseed : Measurable (fun w => (nonrenewedFirstCell rate rewards C_star C_h control0 t u w).nextSlowSet) :=
    measurable_logicalCell_nextSlowSet.comp (measurable_nonrenewedFirstCell rate rewards C_star C_h control0 t u)
  have hhistory := measurable_snd.snd.comp hi
  have haux : Measurable (fun w :
      (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t × Auxiliary p) ×
        Vector p => fun i : PrefixAuxiliaryIndex n => w.1.2 i.val) :=
    Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp measurable_fst.snd)
  exact hi.prodMk (haux.prodMk (((measurable_prefixNumerical rate rewards C_star C_h n).comp hsource).prodMk
    ((measurable_noncallCalendar rate rewards C_star C_h control0 t n.val).comp
      ((hsource.prodMk measurable_fst.snd).prodMk (hseed.prodMk hhistory)))))

theorem measurable_renewedGeneratedObservation (control0 : TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) : Measurable (renewedGeneratedObservation rate rewards C_star C_h control0 u t n) := by
  have hi := measurable_renewedInitialObservation rate rewards C_star C_h control0 u t
  have hsource := measurable_fst.snd.comp (measurable_fst.comp hi)
  have hseed : Measurable (fun w => (renewedFirstCell rate rewards C_star C_h control0 t u w).nextSlowSet) :=
    measurable_logicalCell_nextSlowSet.comp (measurable_renewedFirstCell rate rewards C_star C_h control0 t u)
  have hhistory := measurable_snd.snd.comp hi
  have haux : Measurable (fun w :
      ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t =>
        fun i : PrefixAuxiliaryIndex n => w.1.2 i.val) :=
    Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp measurable_fst.snd)
  exact hi.prodMk (haux.prodMk (((measurable_prefixNumerical rate rewards C_star C_h n).comp hsource).prodMk
    ((measurable_noncallCalendar rate rewards C_star C_h control0 t n.val).comp
      ((hsource.prodMk measurable_fst.snd).prodMk (hseed.prodMk hhistory)))))

private theorem find_date {A : Type*} (L : List (Fin p.T × A)) (s : ℕ)
    (hd : ∀ k (hk : k < L.length), (L[k]).1.val = s + k) (q : Fin p.T) :
    L.find? (fun e => e.1 == q) = if s ≤ q.val then L[q.val - s]? else none := by
  induction L generalizing s with
  | nil => simp only [List.find?_nil, List.getElem?_nil, ite_self]
  | cons e L ih =>
      have he : e.1.val = s := by
        have h := hd 0 (by simp)
        change e.1.val = s + 0 at h
        simpa only [Nat.add_zero] using h
      have ht : ∀ k (hk : k < L.length), (L[k]).1.val = (s + 1) + k := by
        intro k hk
        have h := hd (k + 1) (by simpa using hk)
        change (L[k]).1.val = s + (k + 1) at h
        omega
      by_cases hq : e.1 = q
      · have hs : s = q.val := he.symm.trans (congrArg Fin.val hq)
        simp [hq, hs]
      · have hne : s ≠ q.val := fun h => hq (Fin.ext (he.trans h))
        rw [List.find?_cons, show (e.1 == q) = false from beq_eq_false_iff_ne.mpr hq, ih (s + 1) ht]
        by_cases hs : s ≤ q.val
        · have hs' : s + 1 ≤ q.val := by omega
          have hsub : q.val - s = (q.val - (s + 1)) + 1 := by omega
          simp only [hs, hs', ite_true, hsub, List.getElem?_cons_succ]
        · have hs' : ¬s + 1 ≤ q.val := by omega
          simp only [hs, hs', ite_false]

private theorem actualObservation_find (q : Fin p.T) (z : Source p) :
    (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z).find?
      (fun e => e.1 == q) = (recordAt q z).map (fun r => (r.input.time, (roundRecordCode r,
        ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r))) := by
  have hd : ∀ k (hk : k < (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z).length),
      ((ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z)[k]).1.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k := by
    intro k hk
    have h := ReferenceCompleteNumericalBranchObservation.branchCalendar_times rate rewards C_star C_h 0 z
    have hk' : k < p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      simpa only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar_length] using hk
    have hh := congrArg (fun L : List ℕ => L[k]?) h
    simp only [List.getElem?_map, List.getElem?_range' hk', Nat.one_mul] at hh
    change k < (ReferenceCompleteNumericalBranchObservation.branchCalendar rate rewards C_star C_h 0 z).length at hk
    rw [List.getElem?_eq_getElem hk] at hh
    exact Option.some.inj hh
  rw [find_date _ _ hd]
  unfold actualRecord
  split_ifs <;> simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem?_map, Option.map_none]

/-- Joint actual record code and optional numerical branch readout before
the boundary. The comparison never equates row-bearing raw records. -/
theorem actualObservation_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : Source p) : (recordAt q z).map (fun r => (r.input.time, (roundRecordCode r,
        ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r))) =
    (recordAt q (sourcePrefix control0 n z)).map (fun r => (r.input.time, (roundRecordCode r,
        ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r))) := by
  have hf (L : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate) :
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n L).find? (fun e => e.1 == q) =
        L.find? (fun e => e.1 == q) := by
    rw [ReferenceCompleteObservationPrefixInformation.datePrefix, List.find?_filter]
    congr 1
    funext e
    by_cases he : e.1 = q
    · simp [he, hqn]
    · simp [he]
  have h := congrArg (fun L : ReferenceCompleteFirstPhaseObservationRecovery.OBS rate =>
    L.find? (fun e => e.1 == q))
    (ReferenceCompleteObservationPrefixInformation.datePrefix_factor rate rewards C_star C_h control0 n hn z)
  rw [hf, hf, actualObservation_find rate rewards C_star C_h q z, actualObservation_find rate rewards C_star C_h q] at h
  exact h

theorem collectionNumerical_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : Source p) :
    (recordAt q z).bind (fun r => (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
        numericalCoordinates) = (recordAt q (sourcePrefix control0 n z)).bind
      (fun r => (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map numericalCoordinates) := by
  have he (r : Record rate) : ReferenceCompleteNumericalBranchObservation.rightProjection
        (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r) =
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map numericalCoordinates :=
    congrArg Prod.snd (ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r)
  have h := congrArg (fun o : Option (ReferenceCompleteNumericalBranchObservation.NumericalEntry rate) =>
    o.bind (fun e => ReferenceCompleteNumericalBranchObservation.rightProjection e.2.2))
    (actualObservation_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z)
  simpa only [Option.bind_map, Function.comp_def, he] using h

theorem collectionDateDomain_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : Source p) :
    z ∈ collectionDomain q ↔ sourcePrefix control0 n z ∈ collectionDomain q := by
  rw [collectionDateDomain_iff, collectionDateDomain_iff,
    collectionNumerical_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z]

private theorem numericalCoordinates_injective : Function.Injective (numericalCoordinates (p := p)) := by
  intro c d h
  cases c
  cases d
  simp_all only [numericalCoordinates, Prod.mk.injEq]

private theorem liveInput_branch_congr (r s : Record rate) (c d : RecordedQueueRun.RoundInput p.K)
    (hr : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c)
    (hs : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 s = some d)
    (h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r =
      ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 s) : c = d := by
  have he (v : Record rate) : ReferenceCompleteNumericalBranchObservation.leftProjection
        (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 v) =
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 v).map numericalCoordinates :=
    congrArg Prod.fst (ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 v)
  have hh := congrArg ReferenceCompleteNumericalBranchObservation.leftProjection h
  rw [he, he, hr, hs, Option.map_some, Option.map_some] at hh
  exact numericalCoordinates_injective (Option.some.inj hh)

theorem collectionInput_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : CollectionDateSource rate rewards C_star C_h q) :
    collectionInputAt q z = collectionInputAt q ⟨sourcePrefix control0 n z.val,
        (collectionDateDomain_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val).mp z.property⟩ := by
  have h := collectionNumerical_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val
  let z' : CollectionDateSource rate rewards C_star C_h q := ⟨sourcePrefix control0 n z.val,
      (collectionDateDomain_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val).mp z.property⟩
  rw [(collectionRecord_spec rate rewards C_star C_h q z).1,
    (collectionRecord_spec rate rewards C_star C_h q z').1, Option.bind_some, Option.bind_some,
    collectionInput_spec rate rewards C_star C_h q z, collectionInput_spec rate rewards C_star C_h q z',
    Option.map_some, Option.map_some] at h
  exact numericalCoordinates_injective (Option.some.inj h)

private theorem stateReadout_injective : Function.Injective
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (K := p.K)) := by
  intro S R h
  cases S
  cases R
  simp_all only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, Prod.mk.injEq]

/-- The complete numerical PRE, including every disabled physical date,
uses no selected control at or after its boundary. -/
theorem prefixNumerical_sourcePrefix (control0 : TimeControl p) (n : Fin (p.T + 1))
    (m : ℕ) (hnm : n.val ≤ m) (z : Source p) : numericalPre n z = numericalPre n (sourcePrefix control0 m z) := by
  by_cases ht : p.T ≤ m
  · rw [sourcePrefix_eq_self control0 m ht]
  · let q : Fin p.T := ⟨n.val, by omega⟩
    have hp := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable rate rewards C_star C_h control0 q
    rw [sourcePrefixFiltration_succ] at hp
    have h := hp.factorsThrough (sourcePrefix_sourcePrefix control0 q.val m hnm z).symm
    have he (w : Source p) : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h q w =
        (numericalPre n w).map ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout := by
      rw [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
        ← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells]
      simp only [prefixNumerical, Option.map_map, Function.comp_def, q]
    rw [he, he] at h
    exact (Option.map_injective stateReadout_injective) h

theorem laterCollectionCell_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : Auxiliary p) : collectionCellAt q z U a = collectionCellAt q ⟨sourcePrefix control0 n z.val,
        (collectionDateDomain_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val).mp z.property⟩ U a := by
  let z' : CollectionDateSource rate rewards C_star C_h q := ⟨sourcePrefix control0 n z.val,
      (collectionDateDomain_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val).mp z.property⟩
  have hi := collectionInput_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z
  change collectionInputAt q z = collectionInputAt q z' at hi
  have hb : collectionPre q z = collectionPre q z' := by
    have h := prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc n hqn.le z.val
    rw [collectionBefore_spec rate rewards C_star C_h q z, collectionBefore_spec rate rewards C_star C_h q z'] at h
    exact Option.some.inj h
  have hp : (collectionArgumentsAt q z).1 = (collectionArgumentsAt q z').1 := by
    have h : ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z.val =
        ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z'.val := by
      rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload_factor rate rewards C_star C_h control0 q z.val,
        ReferenceFirstCollectionOldRecorderFoundation.incomingPayload_factor rate rewards C_star C_h control0 q z'.val]
      exact congrArg (ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q)
        (sourcePrefix_sourcePrefix control0 q.val n hqn.le z.val).symm
    rw [collectionArguments_incoming rate rewards C_star C_h q z,
      collectionArguments_incoming rate rewards C_star C_h q z'] at h
    exact Option.some.inj h
  have hc : roundRecordCode (collectionRecordAt q z) = roundRecordCode (collectionRecordAt q z') := by
    have h := ReferenceFirstLiveChronologicalPrefixCausality.actualRecord_code_sourcePrefix
      rate rewards C_star C_h control0 n z.val q hqn
    rw [(collectionRecord_spec rate rewards C_star C_h q z).1,
      (collectionRecord_spec rate rewards C_star C_h q z').1, Option.map_some, Option.map_some] at h
    exact Option.some.inj h
  have hf : ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z'.val =
      ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z.val := by
    simp only [z', ReferenceSourceFastScalarDisintegration.sourceFastScalar, sourceCoordinatorIndex_eq_selectedRowIndex,
      sourcePrefix_selected,
      sourcePrefix_control, ite_eq_left hqn]
  change collectionCellAt q z U a = collectionCellAt q z' U a
  unfold laterCollectionCell
  simp only [hi, hb, hp, hc, hf]

theorem continuingDomain_sourcePrefix (control0 : TimeControl p) (n : ℕ)
    (q : Fin p.T) (hqn : q.val ≤ n) (z : Source p) :
    z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q ↔
      sourcePrefix control0 n z ∈
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q := by
  have hi : incoming rate rewards C_star C_h q z = incoming rate rewards C_star C_h q (sourcePrefix control0 n z) := by
    rw [incoming_factor rate rewards C_star C_h control0 q z, incoming_factor rate rewards C_star C_h control0 q
        (sourcePrefix control0 n z),
      sourcePrefix_sourcePrefix control0 q.val n hqn z]
  exact ⟨ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain_of_incoming_eq
      rate rewards C_star C_h q _ _ hi,
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain_of_incoming_eq
      rate rewards C_star C_h q _ _ hi.symm⟩

private theorem appendLogicalCell_code_congr (r s : Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (d : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
    (S : RecordedQueueRun.RunState p.K) (a : Auxiliary p)
    (ht : r.input.time = s.input.time)
    (hc : roundRecordCode r = roundRecordCode s)
    (hi : c.input = d.input) (hu : r.input.row.2 r.input.time = s.input.row.2 s.input.time) :
    appendLogicalCell r c S a = appendLogicalCell s d S a := by
  have hv : c.selected.view = d.selected.view := by
    have h := congrArg (fun code : RoundRecordCode (p := p) (rate := rate) => code.2.2.1.1) hc
    rw [(roundRecordCode_front r).1, (roundRecordCode_front s).1] at h
    have hr : (ReferenceActivePhysicalStep.dispatch r.input).selection = some c.selected := by
      simpa only [r.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using c.selection_actual
    have hs : (ReferenceActivePhysicalStep.dispatch s.input).selection = some d.selected := by
      simpa only [s.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using d.selection_actual
    rw [hr, hs, Option.map_some, Option.map_some] at h
    exact congrArg Prod.fst (Option.some.inj h)
  have hf : (reservedFastArm r c).val = (reservedFastArm s d).val := by
    unfold reservedFastArm
    rcases c with ⟨cs, cm, co, selected, ca, cl, cv, ci, ceq, cen, carm, cquant⟩
    rcases d with ⟨ds, dm, do_, selected', da, dl, dv, di, deq, den, darm, dquant⟩
    rcases selected with ⟨view, started, pending, cutoff, arm, choice⟩
    rcases selected' with ⟨view', started', pending', cutoff', arm', choice'⟩
    dsimp only at hv ⊢
    cases hv
    rw [hu]
  have hp : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val s.input.row s.input.time := by
    unfold FollowerCutoffScan.completeRowProposalBit CompletePublicTable.completeRowLearning
    rw [hu]
  unfold appendLogicalCell
  dsimp only
  rw [hp]
  simp only [ht, hc, hi, hv, hf]

theorem continuingLogicalCell_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : ContinuingLiveSource rate rewards C_star C_h q) (a : Auxiliary p) :
    continuingCellAt q z a = continuingCellAt q ⟨sourcePrefix control0 n z.val,
        (continuingDomain_sourcePrefix rate rewards C_star C_h control0 n q hqn.le z.val).mp z.property⟩ a := by
  let z' : ContinuingLiveSource rate rewards C_star C_h q := ⟨sourcePrefix control0 n z.val,
      (continuingDomain_sourcePrefix rate rewards C_star C_h control0 n q hqn.le z.val).mp z.property⟩
  let r := continuingRecordAt q z
  let s := continuingRecordAt q z'
  have hr := continuingSourceCell_spec rate rewards C_star C_h q z
  have hs := continuingSourceCell_spec rate rewards C_star C_h q z'
  have hobs := actualObservation_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z.val
  rw [hr.1, hs.1, Option.map_some, Option.map_some] at hobs
  have hentry := Option.some.inj hobs
  change (r.input.time, (roundRecordCode r, ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r)) =
    (s.input.time, (roundRecordCode s, ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 s)) at hentry
  have hc : roundRecordCode r = roundRecordCode s := congrArg (fun e => e.2.1) hentry
  have hi : (continuingCellWitness q z).input = (continuingCellWitness q z').input := by
    rw [hr.2.2, hs.2.2]
    exact liveInput_branch_congr rate r s _ _ hr.2.1 hs.2.1 (congrArg (fun e => e.2.2) hentry)
  have hb : continuingPre q z = continuingPre q z' := by
    have h := prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc n hqn.le z.val
    rw [continuingBefore_spec rate rewards C_star C_h q z, continuingBefore_spec rate rewards C_star C_h q z'] at h
    exact Option.some.inj h
  have ht : r.input.time = s.input.time := (continuingRecord_time rate rewards C_star C_h q z).trans
    (continuingRecord_time rate rewards C_star C_h q z').symm
  have hu : r.input.row.2 r.input.time = s.input.row.2 s.input.time := by
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z.val r hr.1
    have hg := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z'.val s hs.1
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1,
      hg.1, hg.2.1, hg.2.2.1, z', sourcePrefix_selected,
      sourcePrefix_control, ite_eq_left hqn]
  change appendLogicalCell r _ (continuingPre q z) a = appendLogicalCell s _ (continuingPre q z') a
  rw [hb]
  exact appendLogicalCell_code_congr rate r s _ _ _ a ht hc hi hu

/-- Locality holds for the actual total optional cell, with arbitrary incoming
logical set and with no clarity or generated-seed hypothesis. -/
theorem noncallDateCell_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (q : Fin p.T) (hqn : q.val < n) (z : Source p) (a : Auxiliary p) (U : SlowSet p) :
    noncallCellAt q z a U = noncallCellAt q (sourcePrefix control0 n z) a U := by
  have hL := continuingDomain_sourcePrefix rate rewards C_star C_h control0 n q hqn.le z
  have hC := collectionDateDomain_sourcePrefix rate rewards C_star C_h control0 n hn q hqn z
  unfold noncallDateCell
  by_cases hl : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q
  · rw [dite_eq_left hl, dite_eq_left (hL.mp hl)]
    exact congrArg some (continuingLogicalCell_sourcePrefix rate rewards C_star C_h control0 n hn q hqn ⟨z, hl⟩ a)
  · rw [dite_eq_right hl, dite_eq_right (mt hL.mpr hl)]
    by_cases hc : z ∈ collectionDomain q
    · rw [dite_eq_left hc, dite_eq_left (hC.mp hc)]
      unfold laterCollectionCell?
      rw [collectionInput_sourcePrefix rate rewards C_star C_h control0 n hn q hqn ⟨z, hc⟩,
        laterCollectionCell_sourcePrefix rate rewards C_star C_h control0 n hn q hqn ⟨z, hc⟩ U a]
    · rw [dite_eq_right hc, dite_eq_right (mt hC.mpr hc)]

theorem noncallCalendar_sourcePrefix (control0 : TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (t : Fin p.T) (z : Source p) (a : Auxiliary p) (initial : SlowSet p × List (LogicalCell p rate))
    (k : ℕ) (hkn : k ≤ n) :
    noncallCalendarAt t z a initial k = noncallCalendarAt t (sourcePrefix control0 n z) a initial k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [noncallCalendar, noncallCalendar, ih (by omega)]
      congr 1
      funext s
      split
      next h =>
        have hq : (⟨k, h.2⟩ : Fin p.T).val < n := by dsimp only; omega
        rw [← ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_sourcePrefix
          rate rewards C_star C_h control0 ⟨k, h.2⟩ n hq.le z]
        split
        · unfold appendNoncallDate
          rw [noncallDateCell_sourcePrefix rate rewards C_star C_h control0 n hn ⟨k, h.2⟩ hq z a s.1]
        · rfl
      next _ => rfl

theorem actualFirstCell_prefix_congr (control0 : TimeControl p) (t : Fin p.T)
    (z w : FirstInvocationSource rate rewards C_star C_h t)
    (hpre : sourcePrefix control0 (t.val + 1) z.val = sourcePrefix control0 (t.val + 1) w.val) (x : Scalar) :
    nativeFirstCell control0 t z x = nativeFirstCell control0 t w x := by
  let r := firstRecord rate rewards C_star C_h t z
  let s := firstRecord rate rewards C_star C_h t w
  have hr := firstSourceCell_spec rate rewards C_star C_h t z
  have hs := firstSourceCell_spec rate rewards C_star C_h t w
  have hobs := actualObservation_sourcePrefix rate rewards C_star C_h control0 (t.val + 1)
    (Nat.succ_le_of_lt t.isLt) t (Nat.lt_succ_self _) z.val
  rw [hpre] at hobs
  have hobs' := hobs.trans (actualObservation_sourcePrefix rate rewards C_star C_h control0 (t.val + 1)
    (Nat.succ_le_of_lt t.isLt) t (Nat.lt_succ_self _) w.val).symm
  rw [hr.1, hs.1, Option.map_some, Option.map_some] at hobs'
  have hentry := Option.some.inj hobs'
  have hc : roundRecordCode r = roundRecordCode s := congrArg (fun e => e.2.1) hentry
  have hi : (firstSourceCell rate rewards C_star C_h t z).input = (firstSourceCell rate rewards C_star C_h t w).input :=
    liveInput_branch_congr rate r s _ _ hr.2.2 hs.2.2 (congrArg (fun e => e.2.2) hentry)
  have htpre := congrArg (sourcePrefix control0 t.val) hpre
  simp only [sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (Nat.le_succ _)] at htpre
  have hb : firstBefore rate rewards C_star C_h control0 t z = firstBefore rate rewards C_star C_h control0 t w := by
    have hm := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable rate rewards C_star C_h control0 t
    rw [sourcePrefixFiltration_succ] at hm
    have h := hm.factorsThrough htpre
    rw [← ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore_eq_original
      rate rewards C_star C_h control0 t z.val,
      ← ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore_eq_original
      rate rewards C_star C_h control0 t w.val,
      firstBefore_spec rate rewards C_star C_h control0 t z,
      firstBefore_spec rate rewards C_star C_h control0 t w] at h
    exact stateReadout_injective (Option.some.inj h)
  have hcontrol : ReferenceSourceCurrentControlFreshness.u_t p t z.val =
      ReferenceSourceCurrentControlFreshness.u_t p t w.val := by
    have h := congrArg (ReferenceSourceCurrentControlFreshness.u_t p t) hpre
    simpa only [ReferenceSourceCurrentControlFreshness.u_t, sourcePrefix_selected,
      sourcePrefix_control, ite_eq_left (Nat.lt_succ_self _)] using h
  have hu : r.input.row.2 r.input.time = s.input.row.2 s.input.time :=
    (firstRecord_control rate rewards C_star C_h t z).trans
      (hcontrol.trans (firstRecord_control rate rewards C_star C_h t w).symm)
  simp only [actualFirstCell, hr.2.1, hs.2.1]
  rw [hb]
  exact appendLogicalCell_code_congr rate r s _ _ _ _ (hr.2.1.trans hs.2.1.symm) hc hi hu

theorem replaceSourceControl_comm (t q : Fin p.T) (htq : t ≠ q) (z : Source p) (c d : TimeControl p) :
    replaceSourceControl p t (replaceSourceControl p q z c) d =
    replaceSourceControl p q (replaceSourceControl p t z d) c := by
  apply Prod.ext
  · refine Prod.ext ?_ ?_
    · rfl
    · funext row
      by_cases hrow : row = sourceCoordinatorIndex p z
      · subst row
        simp only [replaceSourceControl, sourceCoordinatorIndex, Function.update_self]
        refine Prod.ext ?_ ?_
        · rfl
        · exact (Function.update_comm (β := fun _ : Fin p.T => TimeControl p) htq d c
            ((z.1.2 (sourceCoordinatorIndex p z)).2)).symm
      · change row ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 at hrow
        simp only [replaceSourceControl, sourceCoordinatorIndex, Function.update_of_ne hrow]
  · rfl

/-- Insertion at the installation date commutes with changing a distinct
future whole control, retaining all rows and all private coordinates. -/
theorem insert_futureControl (t q : Fin p.T) (htq : t ≠ q) (z : Source p) (v : Vector p) (c : TimeControl p) :
    ReferenceFirstCollectionRenewalVectorInsertion.insert t (replaceSourceControl p q z c) v =
    replaceSourceControl p q (ReferenceFirstCollectionRenewalVectorInsertion.insert t z v) c := by
  have hc : ReferenceFirstCollectionRenewalVectorInsertion.ctrl t (replaceSourceControl p q z c) v =
        ReferenceFirstCollectionRenewalVectorInsertion.ctrl t z v := by
    simp only [ReferenceFirstCollectionRenewalVectorInsertion.ctrl,
      ReferenceFirstCollectionRenewalVectorInsertion.c, ReferenceFirstCollectionRenewalVectorInsertion.q,
      replaceSourceControl,
      ActualInitializationPhysicalStep.selectedRowIndex,
      sourceCoordinatorIndex, Function.update_self,
      Function.update_of_ne htq]
  unfold ReferenceFirstCollectionRenewalVectorInsertion.insert
  rw [hc]
  exact replaceSourceControl_comm t q htq z c _

theorem nonrenewedEvent_futureControl_iff (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (z : Source p) (c : TimeControl p) : replaceSourceControl p q z c ∈
      ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t := by
  rw [← ReferenceFirstNextInvocationJointLift.event_sourcePrefix_iff rate rewards C_star C_h u t control0
      (replaceSourceControl p q z c),
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q t.val htq.le z c,
    ReferenceFirstNextInvocationJointLift.event_sourcePrefix_iff rate rewards C_star C_h u t control0 z]

theorem renewedEvent_futureControl_iff (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (z : Source p) (c : TimeControl p) : replaceSourceControl p q z c ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
    z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t := by
  have he (s : Source p) : sourcePrefix control0 t.val s ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t ↔
      s ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t := by
    rw [sourcePrefix_eq_suffix control0 t.val t.isLt]
    exact (ReferenceFirstCollectionRenewalPastLocality.renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h s u t (fun _ => control0)).symm
  rw [← he, ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q t.val htq.le z c, he]

def replaceNonrenewedSource (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t) (c : TimeControl p) :
    ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t := ⟨replaceSourceControl p q z.val c,
    (nonrenewedEvent_futureControl_iff rate rewards C_star C_h control0 u t q htq z.val c).mpr z.property⟩

def replaceRenewedSource (control0 : TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t) (c : TimeControl p) :
    ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t :=
  ⟨replaceSourceControl p q z.val c,
    (renewedEvent_futureControl_iff rate rewards C_star C_h control0 u t q htq z.val c).mpr z.property⟩

theorem insertedSource_futureControl_prefix (control0 : TimeControl p) (t q : Fin p.T) (htq : t ≠ q)
    (n : ℕ) (hnq : n ≤ q.val) (z : Source p) (v : Vector p)
    (c : TimeControl p) :
    sourcePrefix control0 n (ReferenceFirstCollectionRenewalVectorInsertion.insert t (replaceSourceControl p q z c) v) =
    sourcePrefix control0 n (ReferenceFirstCollectionRenewalVectorInsertion.insert t z v) := by
  rw [insert_futureControl t q htq z v c,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q n hnq]

theorem nonrenewedPostHistory_futureControl (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (a : Auxiliary p) (v : Vector p) (c : TimeControl p) :
    postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t
      ((replaceNonrenewedSource rate rewards C_star C_h control0 u t q htq z c, a), v)) =
      postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t ((z, a), v)) := by
  let z' := replaceNonrenewedSource rate rewards C_star C_h control0 u t q htq z c
  have hp := congrArg Prod.snd (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_replace_current
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) q htq.le z.val a c)
  change originalPast t.castSucc (z'.val, a) = originalPast t.castSucc (z.val, a) at hp
  have hi : sourcePrefix control0 (t.val + 1) (nonrenewedFirstSource rate rewards C_star C_h t u z' v).val =
    sourcePrefix control0 (t.val + 1) (nonrenewedFirstSource rate rewards C_star C_h t u z v).val :=
    insertedSource_futureControl_prefix control0 t q (Fin.ne_of_val_ne (Nat.ne_of_lt htq)) (t.val + 1) htq z.val v c
  have hc := actualFirstCell_prefix_congr rate rewards C_star C_h control0 t
    (nonrenewedFirstSource rate rewards C_star C_h t u z' v)
    (nonrenewedFirstSource rate rewards C_star C_h t u z v) hi (a (t, 1))
  change _ ++ [nativeFirstCell control0 t _ (a (t, 1))] = _ ++ [nativeFirstCell control0 t _ (a (t, 1))]
  dsimp only [nonrenewedTransition]
  rw [hp, hc]

theorem renewedPostHistory_futureControl (control0 : TimeControl p) (u t q : Fin p.T)
    (htq : t.val < q.val) (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (a : Auxiliary p) (v : Vector p) (c : TimeControl p) :
    postHistory (renewedTransition rate rewards C_star C_h control0 u t
      ((replaceRenewedSource rate rewards C_star C_h control0 u t q htq z c, a), v)) =
      postHistory (renewedTransition rate rewards C_star C_h control0 u t ((z, a), v)) := by
  let z' := replaceRenewedSource rate rewards C_star C_h control0 u t q htq z c
  let s := ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v
  let s' := ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z' v
  have hp := congrArg Prod.snd (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_replace_current
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) q htq.le z.val a c)
  change originalPast t.castSucc (z'.val, a) = originalPast t.castSucc (z.val, a) at hp
  have hi : sourcePrefix control0 (t.val + 1) s'.val = sourcePrefix control0 (t.val + 1) s.val := by
    simp only [s, s', ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    exact insertedSource_futureControl_prefix control0 t q (Fin.ne_of_val_ne (Nat.ne_of_lt htq))
      (t.val + 1) htq z.val v c
  have hc := actualFirstCell_prefix_congr rate rewards C_star C_h control0 t
    (renewedFirstSource rate rewards C_star C_h t u s') (renewedFirstSource rate rewards C_star C_h t u s) hi (a (t, 0))
  change _ ++ [nativeFirstCell control0 t _ (a (t, 0))] = _ ++ [nativeFirstCell control0 t _ (a (t, 0))]
  dsimp only [renewedTransition, ReferenceFirstCollectionRenewalInstallationCoupling.pair]
  rw [hp, hc]

theorem postInvocationPrefix_sourcePrefix_congr (control0 : TimeControl p) (t : Fin p.T)
    (n : Fin (p.T + 1)) (d e : TransitionData rate t) (a : Auxiliary p)
    (hs : sourcePrefix control0 n.val (insertedPhysicalSource rate d) =
      sourcePrefix control0 n.val (insertedPhysicalSource rate e))
    (hH : postHistory d = postHistory e) : generatedPrefix t n d a = generatedPrefix t n e a := by
  have hc : d.2.2.2 = e.2.2.2 := Option.some.inj ((postHistory_last rate t d).symm.trans
    ((congrArg List.getLast? hH).trans (postHistory_last rate t e)))
  have hseed : postSeed rate d = postSeed rate e := congrArg LogicalCell.nextSlowSet hc
  unfold postInvocationPrefix
  rw [noncallCalendar_sourcePrefix rate rewards C_star C_h control0 n.val
      (Nat.le_of_lt_succ n.isLt) t (insertedPhysicalSource rate d) a (postSeed rate d, postHistory d) n.val le_rfl,
    noncallCalendar_sourcePrefix rate rewards C_star C_h control0 n.val
      (Nat.le_of_lt_succ n.isLt) t (insertedPhysicalSource rate e) a (postSeed rate e, postHistory e) n.val le_rfl,
    hs, hseed, hH]

/-- Only the two complete source fields are replaced by their causal
prefixes. All remaining fields are the original observation's literal data. -/
def pastProjection (control0 : TimeControl p) (t : Fin p.T) (n : Fin (p.T + 1))
    (o : PrefixObservation rate t n) : PrefixObservation rate t n :=
  (((((sourcePrefix control0 n.val o.1.1.1.1), sourcePrefix control0 n.val o.1.1.1.2), o.1.1.2), o.1.2), o.2)

theorem measurable_pastProjection (control0 : TimeControl p) (t : Fin p.T)
    (n : Fin (p.T + 1)) : Measurable (pastProjection rate control0 t n) := by
  have hp := measurable_sourcePrefix control0 n.val
  exact ((((hp.comp measurable_fst.fst.fst.fst).prodMk
    (hp.comp measurable_fst.fst.fst.snd)).prodMk measurable_fst.fst.snd).prodMk
      measurable_fst.snd).prodMk measurable_snd

def nonrenewedPast (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (w : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      Auxiliary p) × Vector p) : PrefixObservation rate t n :=
  pastProjection rate control0 t n (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n w)

def renewedPast (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (w : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    PrefixObservation rate t n :=
  pastProjection rate control0 t n (renewedGeneratedObservation rate rewards C_star C_h control0 u t n w)

section RetainedAssembly

variable (control0 : TimeControl p) (t : Fin p.T) (n : Fin (p.T + 1))

/-- Literal assembly of the retained fields, shared by the two actual lifts. -/
private def transitionPast (z : Source p) (d : TransitionData rate t) (a : Auxiliary p) : PrefixObservation rate t n :=
  ((((sourcePrefix control0 n.val z, sourcePrefix control0 n.val (insertedPhysicalSource rate d)), d.1.2),
    (usedAuxiliary t a, postHistory d)), (fun i => a i.val, (numericalPre n (insertedPhysicalSource rate d),
        generatedPrefix t n d a)))

local notation "assembled" => transitionPast rate rewards C_star C_h control0 t n

private theorem prefixNumerical_congr (z w : Source p)
    (h : sourcePrefix control0 n.val z = sourcePrefix control0 n.val w) : numericalPre n z = numericalPre n w :=
  (prefixNumerical_sourcePrefix rate rewards C_star C_h control0 n n.val le_rfl z).trans
    ((congrArg (numericalPre n) h).trans
      (prefixNumerical_sourcePrefix rate rewards C_star C_h control0 n n.val le_rfl w).symm)

private theorem transitionPast_snd (z : Source p) (d : TransitionData rate t) (a : Auxiliary p) :
    (assembled z d a).2 = (fun i => a i.val, (numericalPre n (insertedPhysicalSource rate d),
        generatedPrefix t n d a)) := rfl

variable (z w : Source p) (d e : TransitionData rate t) (a : Auxiliary p)
  (ho : sourcePrefix control0 n.val z = sourcePrefix control0 n.val w)
  (hi : sourcePrefix control0 n.val (insertedPhysicalSource rate d) =
    sourcePrefix control0 n.val (insertedPhysicalSource rate e))
  (hv : d.1.2 = e.1.2) (hH : postHistory d = postHistory e)

include ho hi hv hH in
private theorem initialPast_congr : (assembled z d a).1 = (assembled w e a).1 :=
  Prod.ext (Prod.ext (Prod.ext ho hi) hv) (Prod.ext rfl hH)

include hi hH in
private theorem recursivePast_congr : (numericalPre n (insertedPhysicalSource rate d), generatedPrefix t n d a) =
    (numericalPre n (insertedPhysicalSource rate e), generatedPrefix t n e a) :=
  Prod.ext (prefixNumerical_congr rate rewards C_star C_h control0 n _ _ hi)
    (postInvocationPrefix_sourcePrefix_congr rate rewards C_star C_h control0 t n d e a hi hH)

include hi hH in
private theorem tailPast_congr : (assembled z d a).2 = (assembled w e a).2 := by
  rw [transitionPast_snd, transitionPast_snd]
  exact congrArg (fun x => ((fun i : PrefixAuxiliaryIndex n => a i.val), x))
    (recursivePast_congr rate rewards C_star C_h control0 t n d e a hi hH)

include ho hi hv hH in
private theorem transitionPast_congr : assembled z d a = assembled w e a :=
  Prod.ext (initialPast_congr rate rewards C_star C_h control0 t n z w d e a ho hi hv hH)
    (tailPast_congr rate rewards C_star C_h control0 t n z w d e a hi hH)

end RetainedAssembly

private theorem nonrenewedPast_eq (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (w : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t × Auxiliary p) × Vector p) :
    nonrenewedPast rate rewards C_star C_h control0 u t n w = transitionPast rate rewards C_star C_h
      control0 t n w.1.1.val (nonrenewedTransition rate rewards C_star C_h control0 u t w) w.1.2 := rfl

private theorem renewedPast_eq (control0 : TimeControl p) (u t : Fin p.T) (n : Fin (p.T + 1))
    (w : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    renewedPast rate rewards C_star C_h control0 u t n w = transitionPast rate rewards C_star C_h
      control0 t n w.1.1.val (renewedTransition rate rewards C_star C_h control0 u t w) w.1.2 := rfl

theorem nonrenewedPast_futureControl (control0 : TimeControl p) (u t q : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (a : Auxiliary p) (v : Vector p) (c : TimeControl p) : nonrenewedPast rate rewards C_star C_h control0 u t n
      ((replaceNonrenewedSource rate rewards C_star C_h control0 u t q (htn.trans_le hnq) z c, a), v) =
    nonrenewedPast rate rewards C_star C_h control0 u t n ((z, a), v) := by
  rw [nonrenewedPast_eq, nonrenewedPast_eq]
  apply transitionPast_congr
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q n.val hnq z.val c
  · exact insertedSource_futureControl_prefix control0 t q
      (Fin.ne_of_val_ne (Nat.ne_of_lt (htn.trans_le hnq))) n.val hnq z.val v c
  · rfl
  · exact nonrenewedPostHistory_futureControl rate rewards C_star C_h control0 u t q (htn.trans_le hnq) z a v c

theorem renewedPast_futureControl (control0 : TimeControl p) (u t q : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (a : Auxiliary p) (v : Vector p) (c : TimeControl p) : renewedPast rate rewards C_star C_h control0 u t n
      ((replaceRenewedSource rate rewards C_star C_h control0 u t q (htn.trans_le hnq) z c, a), v) =
    renewedPast rate rewards C_star C_h control0 u t n ((z, a), v) := by
  rw [renewedPast_eq, renewedPast_eq]
  apply transitionPast_congr
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q n.val hnq z.val c
  · change sourcePrefix control0 n.val
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t _ v).val =
        sourcePrefix control0 n.val
          (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t z v).val
    rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val, ReferenceFirstCollectionRenewalVectorInsertion.put_val]
    exact insertedSource_futureControl_prefix control0 t q
      (Fin.ne_of_val_ne (Nat.ne_of_lt (htn.trans_le hnq))) n.val hnq z.val v c
  · rfl
  · exact renewedPostHistory_futureControl rate rewards C_star C_h control0 u t q (htn.trans_le hnq) z a v c

/-- `false` is the literal nonrenewed event; `true` is the literal renewal event. -/
def branchEvent (b : Bool) (u t : Fin p.T) : Set (Source p) :=
  if b then ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t
  else ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t

abbrev BranchSource (b : Bool) (u t : Fin p.T) := ↥(branchEvent rate rewards C_star C_h b u t)
abbrev BranchLift (b : Bool) (u t : Fin p.T) := (BranchSource rate rewards C_star C_h b u t × Auxiliary p) × Vector p

variable (control0 : TimeControl p) (b : Bool) (u t : Fin p.T)

def branchTransition : BranchLift rate rewards C_star C_h b u t → TransitionData rate t := match b with
  | false => nonrenewedTransition rate rewards C_star C_h control0 u t
  | true => renewedTransition rate rewards C_star C_h control0 u t

def branchObservation (n : Fin (p.T + 1)) : BranchLift rate rewards C_star C_h b u t → PrefixObservation rate t n :=
  match b with
  | false => nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n
  | true => renewedGeneratedObservation rate rewards C_star C_h control0 u t n

def branchPast (n : Fin (p.T + 1)) (w : BranchLift rate rewards C_star C_h b u t) :=
  pastProjection rate control0 t n (branchObservation rate rewards C_star C_h control0 b u t n w)

local notation "Lift" => BranchLift rate rewards C_star C_h b u t
local notation "observation" => branchObservation rate rewards C_star C_h control0 b u t
local notation "past" => branchPast rate rewards C_star C_h control0 b u t

theorem measurable_branchObservation (n : Fin (p.T + 1)) : Measurable (observation n) := by
  cases b
  · exact measurable_nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n
  · exact measurable_renewedGeneratedObservation rate rewards C_star C_h control0 u t n

theorem measurable_branchPast (n : Fin (p.T + 1)) : Measurable (past n) :=
  (measurable_pastProjection rate control0 t n).comp
    (measurable_branchObservation rate rewards C_star C_h control0 b u t n)

variable (q : Fin p.T) (htq : t.val < q.val)

include control0 htq in
theorem branchEvent_futureControl_iff (z : Source p) (c : TimeControl p) :
    replaceSourceControl p q z c ∈ branchEvent rate rewards C_star C_h b u t ↔
      z ∈ branchEvent rate rewards C_star C_h b u t := by
  cases b
  · exact nonrenewedEvent_futureControl_iff rate rewards C_star C_h control0 u t q htq z c
  · exact renewedEvent_futureControl_iff rate rewards C_star C_h control0 u t q htq z c

def replaceBranchSource (z : BranchSource rate rewards C_star C_h b u t) (c : TimeControl p) :
    BranchSource rate rewards C_star C_h b u t := ⟨replaceSourceControl p q z.val c,
    (branchEvent_futureControl_iff rate rewards C_star C_h control0 b u t q htq z.val c).mpr z.property⟩

theorem branchPast_futureControl (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : BranchSource rate rewards C_star C_h b u t) (a : Auxiliary p)
    (v : Vector p) (c : TimeControl p) :
    past n ((replaceBranchSource rate rewards C_star C_h control0 b u t q htq z c, a), v) = past n ((z, a), v) := by
  cases b
  · exact nonrenewedPast_futureControl rate rewards C_star C_h control0 u t q n htn hnq z a v c
  · exact renewedPast_futureControl rate rewards C_star C_h control0 u t q n htn hnq z a v c

private theorem futureAuxiliarySplit_remainder_congr (proposal : Bool) (a a' : Auxiliary p)
    (h : ∀ j, j ≠ (q, if proposal then 0 else 1) → a j = a' j) :
    (futureAuxiliarySplit q proposal a).1 = (futureAuxiliarySplit q proposal a').1 := by
  cases proposal
  · funext j
    exact h j.val j.property
  · change (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit q
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar) (Equiv.swap (q, 0) (q, 1))) a)).1 =
      (ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit q
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar) (Equiv.swap (q, 0) (q, 1))) a')).1
    funext j
    change (Equiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar) (Equiv.swap (q, 0) (q, 1)) a) j.val =
      (Equiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => Scalar) (Equiv.swap (q, 0) (q, 1)) a') j.val
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq, Equiv.symm_swap]
    apply h
    intro he
    apply j.property
    exact (Equiv.swap_apply_eq_iff.mp he).trans (Equiv.swap_apply_left _ _)

theorem branchPast_auxiliary_one (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : BranchSource rate rewards C_star C_h b u t) (a a' : Auxiliary p)
    (v : Vector p) (proposal : Bool)
    (h : ∀ j, j ≠ (q, if proposal then 0 else 1) → a j = a' j) : past n ((z, a), v) = past n ((z, a'), v) := by
  have he := futureAuxiliarySplit_remainder_congr q proposal a a' h
  have hr (a : Auxiliary p) := (futureAuxiliarySplit q proposal).symm_apply_apply a
  rw [← hr a, ← hr a']
  change past n
    ((z, (futureAuxiliarySplit q proposal).symm ((futureAuxiliarySplit q proposal a).1, (futureAuxiliarySplit q proposal a).2)), v) =
    past n
      ((z, (futureAuxiliarySplit q proposal).symm ((futureAuxiliarySplit q proposal a').1, (futureAuxiliarySplit q proposal a').2)), v)
  rw [← he]
  cases b
  · exact congrArg (pastProjection rate control0 t n)
      (nonrenewedGeneratedObservation_futureAuxiliary_ext rate rewards C_star C_h control0 u t q n htn hnq proposal z _ v _ _)
  · exact congrArg (pastProjection rate control0 t n)
      (renewedGeneratedObservation_futureAuxiliary_ext rate rewards C_star C_h control0 u t q n htn hnq proposal z _ v _ _)

/-- Both labels at the tested date can change together; every other entry stays literal. -/
theorem branchPast_auxiliary_pair (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val)
    (z : BranchSource rate rewards C_star C_h b u t) (a a' : Auxiliary p)
    (v : Vector p) (h : ∀ j, j.1 ≠ q → a j = a' j) : past n ((z, a), v) = past n ((z, a'), v) := by
  let middle := Function.update a (q, 0) (a' (q, 0))
  apply Eq.trans (branchPast_auxiliary_one rate rewards C_star C_h control0 b u t q n htn hnq z a middle v true
    (fun j hj => (Function.update_of_ne hj _ _).symm))
  apply branchPast_auxiliary_one rate rewards C_star C_h control0 b u t q n htn hnq z middle a' v false
  rintro ⟨date, label⟩ hj
  by_cases hd : date = q
  · subst date
    fin_cases label <;> simp_all [middle]
  · dsimp only [middle]
    rw [Function.update_of_ne (fun he => hd (congrArg Prod.fst he))]
    exact h _ hd

/-- A singleton erases one scalar; `{0,1}` erases the pair, retaining neither. -/
def auxiliarySplit (labels : Finset (Fin 2)) : Auxiliary p ≃ᵐ
    ({j : Fin p.T × Fin 2 // j.1 = q ∧ j.2 ∈ labels} → Scalar) ×
      ({j : Fin p.T × Fin 2 // ¬(j.1 = q ∧ j.2 ∈ labels)} → Scalar) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin p.T × Fin 2 => Scalar) (fun j => j.1 = q ∧ j.2 ∈ labels)

abbrev TestedAuxiliary (labels : Finset (Fin 2)) := {j : Fin p.T × Fin 2 // j.1 = q ∧ j.2 ∈ labels} → Scalar
abbrev ErasedAuxiliary (labels : Finset (Fin 2)) := {j : Fin p.T × Fin 2 // ¬(j.1 = q ∧ j.2 ∈ labels)} → Scalar

variable (i : Fin (M p)) (labels : Finset (Fin 2))

abbrev ErasedObserver := ((FixedControlRemainder p i q ×
    ErasedAuxiliary q labels) × Vector p) × PrefixObservation rate t q.castSucc

instance erasedObserverMeasurableSpace : MeasurableSpace (ErasedObserver rate t q i labels) :=
  MeasurableSpace.prod (MeasurableSpace.prod (MeasurableSpace.prod inferInstance inferInstance) inferInstance) inferInstance

local notation "Observer" => ErasedObserver rate t q i labels

def erasedObserver (w : Lift) : Observer :=
  ((((fixedControlSplit p i q w.1.1.val).2, (auxiliarySplit q labels w.1.2).2), w.2), past q.castSucc w)

local notation "observeErased" => erasedObserver rate rewards C_star C_h control0 b u t q i labels

theorem measurable_erasedObserver : Measurable (observeErased) :=
  ((((fixedControlSplit p i q).measurable.snd.comp (measurable_subtype_coe.comp measurable_fst.fst)).prodMk
      ((auxiliarySplit q labels).measurable.snd.comp measurable_fst.snd)).prodMk measurable_snd).prodMk
        (measurable_branchPast rate rewards C_star C_h control0 b u t q.castSucc)

/-- Intrinsic selected-index and original branch event on the actual split remainder. -/
abbrev AdmissibleObserver := {d : Observer // PrivateSourceStreams.coordinatorIndex p d.1.1.1.2.1.2 = i ∧
    (fixedControlSplit p i q).symm (control0, d.1.1.1) ∈ branchEvent rate rewards C_star C_h b u t}

local notation "Admissible" => AdmissibleObserver rate rewards C_star C_h control0 b u t q i labels

include htq in
theorem erasedObserver_admissible (w : Lift) (hi : sourceCoordinatorIndex p w.1.1.val = i) :
    PrivateSourceStreams.coordinatorIndex p (observeErased w).1.1.1.2.1.2 = i ∧ (fixedControlSplit p i q).symm
        (control0, (observeErased w).1.1.1) ∈ branchEvent rate rewards C_star C_h b u t := by
  refine ⟨hi, ?_⟩
  change (fixedControlSplit p i q).symm (control0, (fixedControlSplit p i q w.1.1.val).2) ∈ _
  rw [fixedControlSplit_replaceSourceControl p i q w.1.1.val control0 hi]
  exact (branchEvent_futureControl_iff rate rewards C_star C_h control0 b u t q htq w.1.1.val control0).mpr w.1.1.property

include htq in
theorem reconstructed_event (d : Admissible) (c : TimeControl p) : (fixedControlSplit p i q).symm (c, d.val.1.1.1) ∈
      branchEvent rate rewards C_star C_h b u t := by
  let z := (fixedControlSplit p i q).symm (control0, d.val.1.1.1)
  have hi : sourceCoordinatorIndex p z = i := by
    change PrivateSourceStreams.coordinatorIndex p z.2.1.2 = i
    rw [fixedControlSplit_symm_private]
    exact d.property.1
  have hs := fixedControlSplit_replaceSourceControl p i q z c hi
  rw [(fixedControlSplit p i q).apply_symm_apply] at hs
  rw [hs]
  exact (branchEvent_futureControl_iff rate rewards C_star C_h control0 b u t q htq z c).mpr d.property.2

/-- Restoration is event typed for every tested control/scalar, using the original event internally. -/
def restoreLiteralLift (x : Admissible × (TimeControl p × TestedAuxiliary q labels)) : Lift :=
  ((⟨(fixedControlSplit p i q).symm (x.2.1, x.1.val.1.1.1),
    reconstructed_event rate rewards C_star C_h control0 b u t q htq i labels x.1 x.2.1⟩,
      (auxiliarySplit q labels).symm (x.2.2, x.1.val.1.1.2)), x.1.val.1.2)

local notation "restoreLift" => restoreLiteralLift rate rewards C_star C_h control0 b u t q htq i labels

theorem measurable_restoreLiteralLift : Measurable (restoreLift) := (((fixedControlSplit p i q).symm.measurable.comp
    (measurable_snd.fst.prodMk (measurable_fst.fst.fst.comp (measurable_subtype_coe.comp measurable_fst)))).subtype_mk.prodMk
      ((auxiliarySplit q labels).symm.measurable.comp (measurable_snd.snd.prodMk
        (measurable_fst.fst.snd.comp (measurable_subtype_coe.comp measurable_fst))))).prodMk
          (measurable_fst.snd.comp (measurable_subtype_coe.comp measurable_fst))

theorem restoreLiteralLift_original (w : Lift) (hi : sourceCoordinatorIndex p w.1.1.val = i) : restoreLift
      (⟨observeErased w, erasedObserver_admissible rate rewards C_star C_h control0 b u t q htq i labels w hi⟩,
      ((fixedControlSplit p i q w.1.1.val).1, (auxiliarySplit q labels w.1.2).1)) = w :=
  Prod.ext (Prod.ext (Subtype.ext ((fixedControlSplit p i q).symm_apply_apply _))
    ((auxiliarySplit q labels).symm_apply_apply _)) rfl

/-- Whole original/inserted sources, V, private arrays/J and generated prefix are restored jointly. -/
theorem restoreLiteralLift_observation (n : Fin (p.T + 1)) (w : Lift) (hi : sourceCoordinatorIndex p w.1.1.val = i) :
    observation n (restoreLift (⟨observeErased w,
          erasedObserver_admissible rate rewards C_star C_h control0 b u t q htq i labels w hi⟩,
          ((fixedControlSplit p i q w.1.1.val).1, (auxiliarySplit q labels w.1.2).1))) = observation n w :=
  congrArg (observation n) (restoreLiteralLift_original rate rewards C_star C_h control0 b u t q htq i labels w hi)

private theorem restored_coordinates (d : Admissible) (c : TimeControl p) (s : TestedAuxiliary q labels) :
    (observeErased (restoreLift (d, (c, s)))).1 = d.val.1 := by
  change (((fixedControlSplit p i q ((fixedControlSplit p i q).symm (c, d.val.1.1.1))).2,
      (auxiliarySplit q labels ((auxiliarySplit q labels).symm (s, d.val.1.1.2))).2), d.val.1.2) = _
  rw [(fixedControlSplit p i q).apply_symm_apply, (auxiliarySplit q labels).apply_symm_apply]

/-- On the actual selected-index/event remainder, neither the tested physical
control nor any erased auxiliary scalar is used by the entire observer. -/
theorem restoreLiteralLift_observer_nonuse (d : Admissible) (c c' : TimeControl p) (s s' : TestedAuxiliary q labels) :
    observeErased (restoreLift (d, (c, s))) = observeErased (restoreLift (d, (c', s'))) := by
  let w := restoreLift (d, (c, s))
  let w' := restoreLift (d, (c', s'))
  have hi : sourceCoordinatorIndex p w'.1.1.val = i := by
    change PrivateSourceStreams.coordinatorIndex p ((fixedControlSplit p i q).symm (c', d.val.1.1.1)).2.1.2 = i
    rw [fixedControlSplit_symm_private]
    exact d.property.1
  have hs : replaceBranchSource rate rewards C_star C_h control0 b u t q htq w'.1.1 c = w.1.1 := by
    apply Subtype.ext
    have h := fixedControlSplit_replaceSourceControl p i q w'.1.1.val c hi
    change (fixedControlSplit p i q).symm (c, (fixedControlSplit p i q
        ((fixedControlSplit p i q).symm (c', d.val.1.1.1))).2) = _ at h
    rw [(fixedControlSplit p i q).apply_symm_apply] at h
    exact h.symm
  have hp := branchPast_futureControl rate rewards C_star C_h control0 b u t q htq q.castSucc htq le_rfl w'.1.1 w'.1.2 w'.2 c
  rw [hs] at hp
  have ha : past q.castSucc ((w.1.1, w.1.2), w.2) = past q.castSucc ((w.1.1, w'.1.2), w'.2) := by
    apply branchPast_auxiliary_pair rate rewards C_star C_h control0 b u t q q.castSucc htq le_rfl
    intro j hj
    change (auxiliarySplit q labels).symm (s, d.val.1.1.2) j = (auxiliarySplit q labels).symm (s', d.val.1.1.2) j
    change (if h : j.1 = q ∧ j.2 ∈ labels then s ⟨j, h⟩ else d.val.1.1.2 ⟨j, h⟩) =
      (if h : j.1 = q ∧ j.2 ∈ labels then s' ⟨j, h⟩ else d.val.1.1.2 ⟨j, h⟩)
    simp only [hj, false_and, dite_false]
  exact Prod.ext ((restored_coordinates rate rewards C_star C_h control0 b u t q htq i labels d c s).trans
    (restored_coordinates rate rewards C_star C_h control0 b u t q htq i labels d c' s').symm) (ha.trans hp)

/-- The actual event source, restricted to its original private selected row. -/
abbrev SelectedBranchLift := {w : Lift // sourceCoordinatorIndex p w.1.1.val = i}

def selectedErasedObserver (w : SelectedBranchLift rate rewards C_star C_h b u t i) : Admissible :=
  ⟨observeErased w.val,
    erasedObserver_admissible rate rewards C_star C_h control0 b u t q htq i labels w.val w.property⟩

theorem measurable_selectedErasedObserver :
    Measurable (selectedErasedObserver rate rewards C_star C_h control0 b u t q htq i labels) :=
  ((measurable_erasedObserver rate rewards C_star C_h control0 b u t q i labels).comp measurable_subtype_coe).subtype_mk

theorem selectedErasedObserver_reinsert (w : SelectedBranchLift rate rewards C_star C_h b u t i)
    (c : TimeControl p) (s : TestedAuxiliary q labels) : observeErased (restoreLift
        (selectedErasedObserver rate rewards C_star C_h control0 b u t q htq i labels w, (c, s))) =
    observeErased w.val := by
  have h := restoreLiteralLift_observer_nonuse rate rewards C_star C_h control0 b u t q htq i labels
    (selectedErasedObserver rate rewards C_star C_h control0 b u t q htq i labels w) c
    (fixedControlSplit p i q w.val.1.1.val).1 s
    (auxiliarySplit q labels w.val.1.2).1
  exact h.trans (congrArg (observeErased)
    (restoreLiteralLift_original rate rewards C_star C_h control0 b u t q htq i labels w.val w.property))

/-- Whole killed hidden list/incoming set and complete numerical PRE, including absence. -/
def erasedPrefixReadout (d : Observer) := (d.2.2.2.2, d.2.2.2.1)

theorem measurable_erasedPrefixReadout : Measurable (erasedPrefixReadout rate t q i labels) :=
  measurable_snd.snd.snd.snd.prodMk measurable_snd.snd.snd.fst

def erasedKillGate (d : Observer) : Prop := d.2.2.2.2.isSome = true ∧ noCallAt q d.2.1.1.1.2

include control0 in
theorem measurableSet_erasedKillGate : MeasurableSet {d | erasedKillGate rate rewards C_star C_h t q i labels d} := by
  have his := measurable_isSome.comp (measurable_snd.snd.snd.snd : Measurable (fun d : Observer => d.2.2.2.2))
  exact ((measurableSet_singleton true).preimage his).inter
    ((ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage
      measurable_snd.fst.fst.fst.snd)

theorem erasedPrefixReadout_actual (w : Lift) : erasedPrefixReadout rate t q i labels (observeErased w) =
      (generatedPrefix t q.castSucc (branchTransition rate rewards C_star C_h control0 b u t w) w.1.2,
      numericalPre q.castSucc
        (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w))) := by
  cases b <;> rfl

theorem erasedKillGate_actual (w : Lift) : erasedKillGate rate rewards C_star C_h t q i labels (observeErased w) ↔
    (generatedPrefix t q.castSucc (branchTransition rate rewards C_star C_h control0 b u t w) w.1.2).isSome = true ∧
      noCallAt q (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w)) := by
  cases b <;> exact and_congr_right (fun _ =>
    (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_sourcePrefix
      rate rewards C_star C_h control0 q q.val le_rfl _).symm)

end Bandits.Support.ReferencePostInvocationPrefixLocality

end
