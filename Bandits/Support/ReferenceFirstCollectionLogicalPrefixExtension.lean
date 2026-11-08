/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCollectionPathJoin
public import Bandits.Support.ReferenceFirstLiveFiniteCalendarJointLaw
public import Bandits.Support.ReferenceFirstCollectionOneRoundLogicalCell

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

/-!
# First-collection extension of the logical calendar prefix

The recursion extends the same first-LIVE cells through the first physical
collection, retaining the original source, arrays, and shared trigger.

Sources: ZIP4 `06_interruptions.tex:376-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw

open ReferenceFirstCollectionOneRoundLogicalCell
  (actualDomain ActualSource domainRecord domainRecord_spec domainRecord_mem actualPast actualPast_spec
    actualInput actual_data collectionLogicalCellAt cellWithScalar? cellWithScalar cellWithNext nextSet
    actualFast actualWeight)
open ReferenceFirstLiveChronologicalPrefixCausality (calendarPast calendarPast_eq_take_elapsed)
open ReferenceFirstLiveChronologicalPrefixFoundation (SlowSet)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceLaterCollectionSourceReadoutMeasurability (numericalCoordinates)
namespace Bandits.Support.ReferenceFirstCollectionLogicalPrefixExtension

variable {p : ConstructorDimensions.Parameters}

local instance sourceInputMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Cell (rate : RateInput p) := LogicalCell p rate
abbrev Observation (rate : RateInput p) := ReferenceFirstLiveCalendarMarkedTransition.Observation p rate

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)

local notation "fastAt" => ReferenceSourceFastScalarDisintegration.sourceFastScalar p
local notation "launchAt " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "suffixAt " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "Q" => queueParameters rate
local notation "liveTagAt" => currentCellTag rate rewards C_star C_h
local notation "livePast" => firstLiveChronologicalPrefix rate rewards C_star C_h
local notation "recordAt" => actualRecord rate rewards C_star C_h
local notation "inputAt" => actualInput rewards C_star C_h
local notation "numericalPast" => actualPast rewards C_star C_h
local notation "localCell" => cellWithScalar rewards C_star C_h

/-- The actual per-date invocation test. -/
public def noCallAt (t : Fin p.T) (z : Source p) : Prop :=
  match recordAt t z with
  | none => True
  | some record =>
      ReferenceFirstCollectionSamplerCall.collectionCallAt record = none

local notation "noCall" => noCallAt rate rewards C_star C_h

/-- No later collection assignment has been invoked strictly before boundary `n`. -/
public def NoCallBefore (n : Fin (p.T + 1)) (z : Source p) : Prop := ∀ t : Fin p.T, t.val < n.val → noCall t z

local notation "precall" => NoCallBefore rate rewards C_star C_h

public theorem noCallAt_iff_callAt_none (t : Fin p.T) (z : Source p) :
    noCall t z ↔ ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t z = none := by
  cases h : recordAt t z <;>
    simp [noCallAt, ReferenceCalendarCollectionCallControlLaw.callAt, h]

private theorem measurableSet_optionNone {A : Type*} [MeasurableSpace A] : MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[ (inferInstance : MeasurableSpace (A ⊕ PUnit)).comap (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext value
  cases value <;> simp

private instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance listMeasurableSingleton {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] : MeasurableSingletonClass (List A) where
  measurableSet_singleton L := by
    have hinj : Function.Injective (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := A)) := by
      intro B C h
      have hlen : B.length = C.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have h := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert h using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private instance optionMeasurableSingleton {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (MeasurableSet.singleton ((Equiv.optionEquivSumPUnit A) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit A).injective.eq_iff.symm

private theorem predictable_congr {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (control0 : TimeControl p) (t : Fin p.T) (f : Source p → A)
    (hf : Measurable[sourcePrefixFiltration control0 (t.val + 1)] f)
    (z z' : Source p) (hz : sourcePrefix control0 t.val z = sourcePrefix control0 t.val z') :
    f z = f z' := by
  rw [sourcePrefixFiltration_succ] at hf
  exact hf.factorsThrough hz

private theorem sourceFastScalar_prefix (control0 : TimeControl p) (t : Fin p.T)
    (n : ℕ) (ht : t.val < n) (z : Source p) :
    fastAt t (sourcePrefix control0 n z) = fastAt t z := by
  simp only [ReferenceSourceFastScalarDisintegration.sourceFastScalar,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    sourcePrefix_selected, sourcePrefix_control, ite_eq_left ht]

private theorem numericalCoordinates_injective : Function.Injective (numericalCoordinates (p := p)) := by
  intro a b h
  cases a; cases b
  simp_all only [numericalCoordinates, Prod.mk.injEq]

/-- The whole-source actual first-collection cell. -/
public def collectionCellAt (t : Fin p.T) (U : SlowSet p) (za : Source p × AuxiliaryArray p) : Option (Cell rate) :=
  ReferenceFirstCollectionOneRoundLogicalCell.sourceCell? (rate := rate) rewards C_star C_h t U
    (labelZero za.2) za.1 (fastAt t za.1) (za.2 (t, 1))

local notation "cellAt" => collectionCellAt rate rewards C_star C_h

public theorem measurable_collectionCellAt (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (fun v : SlowSet p × (Source p × AuxiliaryArray p) =>
      cellAt t v.1 v.2) := by
  classical
  let D := ActualSource (rate := rate) rewards C_star C_h t
  let X := SlowSet p × (Source p × AuxiliaryArray p)
  let E : Set X := {v | v.2.1 ∈ actualDomain (rate := rate) rewards C_star C_h t}
  have hE : MeasurableSet E := by
    exact (ReferenceFirstCollectionOneRoundLogicalCell.measurableSet_actualDomain
      (rate := rate) rewards C_star C_h t control0).preimage (measurable_fst.comp measurable_snd)
  have hd : Measurable (fun v : E =>
      (⟨v.val.2.1, v.property⟩ : D)) :=
    (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)).subtype_mk
  have hcoords : Measurable (fun v : E =>
      (v.val.1, ((⟨v.val.2.1, v.property⟩ : D), (labelZero v.val.2.2, v.val.2.2 (t, 1))))) := by
    exact measurable_fst.comp measurable_subtype_coe |>.prodMk (hd.prodMk ((measurable_labelZero p).comp
          (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)) |>.prodMk
        ((measurable_pi_apply (t, 1)).comp (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)))))
  have hpos := (ReferenceFirstCollectionOneRoundLogicalCell.measurable_collectionLogicalCellAt_varyingSlowSet
    (rate := rate) rewards C_star C_h t control0).comp hcoords
  simpa [collectionCellAt, ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?, collectionLogicalCellAt, E]
    using hpos.dite (measurable_const (a := (none : Option (Cell rate)))) hE

public theorem collectionCellAt_eq_sourceCell (t : Fin p.T) (U : SlowSet p) (za : Source p × AuxiliaryArray p) :
    cellAt t U za = ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?
        (rate := rate) rewards C_star C_h t U (labelZero za.2) za.1 (fastAt t za.1) (za.2 (t, 1)) := rfl

public theorem actualDomain_sourcePrefix (control0 : TimeControl p) (t : Fin p.T)
    (n : ℕ) (ht : t.val ≤ n) (z : Source p) :
    z ∈ actualDomain (rate := rate) rewards C_star C_h t ↔
      sourcePrefix control0 n z ∈ actualDomain (rate := rate) rewards C_star C_h t := by
  simp only [actualDomain, Set.mem_ofPred_eq]
  rw [ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector rewards C_star C_h t z,
    ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector rewards C_star C_h t
      (sourcePrefix control0 n z),
    ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_factor rate rewards C_star C_h control0 t z,
    ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_factor rate rewards C_star C_h control0 t
      (sourcePrefix control0 n z), sourcePrefix_sourcePrefix control0 t.val n ht]

private theorem domainInput_eq_of_code (t : Fin p.T) (z z' : ActualSource (rate := rate) rewards C_star C_h t)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode (domainRecord rewards C_star C_h t z) =
      ReferenceActiveHorizonMeasurability.roundRecordCode (domainRecord rewards C_star C_h t z')) :
    inputAt z.val t (domainRecord rewards C_star C_h t z) (domainRecord_spec rewards C_star C_h t z)
        (domainRecord_mem rewards C_star C_h t z) =
      inputAt z'.val t (domainRecord rewards C_star C_h t z') (domainRecord_spec rewards C_star C_h t z')
        (domainRecord_mem rewards C_star C_h t z') := by
  let r (w : ActualSource (rate := rate) rewards C_star C_h t) := domainRecord rewards C_star C_h t w
  let I (w : ActualSource (rate := rate) rewards C_star C_h t) :=
    inputAt w.val t (r w) (domainRecord_spec rewards C_star C_h t w) (domainRecord_mem rewards C_star C_h t w)
  have hf (w : ActualSource (rate := rate) rewards C_star C_h t) : some (numericalCoordinates (I w)) =
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalFromRecordCode
          (ReferenceActiveHorizonMeasurability.roundRecordCode (r w))
          (fun a => ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) := by
    obtain ⟨_, ht, hread, _⟩ := actual_data rewards C_star C_h w.val t (r w)
      (domainRecord_spec rewards C_star C_h t w) (domainRecord_mem rewards C_star C_h t w)
    have hfields := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t w.val (r w) (domainRecord_spec rewards C_star C_h t w)
    simpa only [hread, Option.map_some, Option.isSome_some, ite_true, ht, hfields.2.2.2] using
      ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization 0 (r w)
  apply numericalCoordinates_injective
  have hz := hf z
  change _ = ReferenceLaterCollectionSourceReadoutMeasurability.numericalFromRecordCode
    (ReferenceActiveHorizonMeasurability.roundRecordCode (domainRecord rewards C_star C_h t z)) _ at hz
  rw [hcode] at hz
  exact Option.some.inj (hz.trans (hf z').symm)

private theorem stateReadout_injective : Function.Injective
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (K := p.K)) := by
  intro a b h
  cases a; cases b
  simpa only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    Prod.mk.injEq, RecordedQueueRun.RunState.mk.injEq] using h

public theorem collectionCellAt_sourcePrefix (control0 : TimeControl p) (t : Fin p.T)
    (n : ℕ) (ht : t.val < n) (U : SlowSet p) (z : Source p) (a : AuxiliaryArray p) :
    cellAt t U (z, a) = cellAt t U (sourcePrefix control0 n z, a) := by
  classical
  let z' := sourcePrefix control0 n z
  have hdom := actualDomain_sourcePrefix rate rewards C_star C_h control0 t n (by omega) z
  by_cases hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t
  · have hz' : z' ∈ actualDomain (rate := rate) rewards C_star C_h t := hdom.mp hz
    let d : ActualSource (rate := rate) rewards C_star C_h t := ⟨z, hz⟩
    let d' : ActualSource (rate := rate) rewards C_star C_h t := ⟨z', hz'⟩
    let r := domainRecord rewards C_star C_h t d
    let r' := domainRecord rewards C_star C_h t d'
    have hr := domainRecord_spec rewards C_star C_h t d
    have hr' := domainRecord_spec rewards C_star C_h t d'
    have hm := domainRecord_mem rewards C_star C_h t d
    have hm' := domainRecord_mem rewards C_star C_h t d'
    have hphys : ReferenceActiveHorizonMeasurability.roundRecordCode r =
        ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
      have h := ReferenceFirstLiveChronologicalPrefixCausality.actualRecord_code_sourcePrefix
        rate rewards C_star C_h control0 n z t ht
      rw [hr, hr', Option.map_some, Option.map_some] at h
      exact Option.some.inj h
    have hinput := domainInput_eq_of_code rate rewards C_star C_h t d d' hphys
    change inputAt z t r hr hm = inputAt z' t r' hr' hm' at hinput
    have hbefore : RecordedQueueRun.run (Q) (numericalPast z t r hr hm) = RecordedQueueRun.run (Q)
        (numericalPast z' t r' hr' hm') := by
      have h := predictable_congr control0 t _ (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
          rate rewards C_star C_h control0 t) z z'
        (sourcePrefix_sourcePrefix control0 t.val n (by omega) z).symm
      simp only [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
        actualPast_spec rewards C_star C_h z t r hr hm,
        actualPast_spec rewards C_star C_h z' t r' hr' hm',
        Option.map_some] at h
      exact stateReadout_injective (Option.some.inj h)
    have hfast := sourceFastScalar_prefix control0 t n ht z
    change fastAt t z' = fastAt t z at hfast
    change cellAt t U (z, a) = cellAt t U (z', a)
    unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?
    rw [dite_eq_left hz, dite_eq_left hz']
    change collectionLogicalCellAt rewards C_star C_h z t r hr hm U (labelZero a) (a (t, 1)) =
      collectionLogicalCellAt rewards C_star C_h z' t r' hr' hm' U (labelZero a) (a (t, 1))
    unfold collectionLogicalCellAt cellWithScalar? cellWithScalar cellWithNext nextSet actualFast actualWeight
    simp only [hinput, hbefore, hphys, hfast]
  · have hz' : z' ∉ actualDomain (rate := rate) rewards C_star C_h t := mt hdom.mpr hz
    change cellAt t U (z, a) = cellAt t U (z', a)
    simp only [collectionCellAt, ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?, dite_eq_right hz, dite_eq_right hz']

public theorem collectionCellAt_auxiliary_ext (t : Fin p.T) (U : SlowSet p) (z : Source p)
    (a b : AuxiliaryArray p) (h0 : a (t, 0) = b (t, 0)) (h1 : a (t, 1) = b (t, 1)) :
    cellAt t U (z, a) = cellAt t U (z, b) := by
  classical
  unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?
  split
  · simp only [cellWithScalar?, cellWithScalar, cellWithNext, nextSet, labelZero, h0, h1]
    rfl
  · rfl

public theorem measurableSet_noCallAt (control0 : TimeControl p) (t : Fin p.T) :
    MeasurableSet {z : Source p | noCall t z} := by
  have hf : Measurable (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h t) :=
    (ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 t).mono
      ((sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  convert hf measurableSet_optionNone using 1
  ext z
  exact noCallAt_iff_callAt_none rate rewards C_star C_h t z

public theorem measurableSet_noCallBefore (control0 : TimeControl p) (n : Fin (p.T + 1)) :
    MeasurableSet {z : Source p | precall n z} := by
  simp only [NoCallBefore, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun t => MeasurableSet.iInter
    (fun _ => measurableSet_noCallAt rate rewards C_star C_h control0 t))

/-- The actual LIVE tag takes priority; otherwise use the generated incoming set when present. -/
public def prefixCandidate {X A B : Type*} (tag : X → Unit ⊕ B)
    (cell : A × X → Option B) (x : X) (state : Option A × List B) : Option B :=
  match tag x with
  | .inr c => some c
  | .inl _ => match state.1 with | none => none | some U => cell (U, x)

/-- A literal append-or-preserve update on a complete cell list and its next-set option. -/
public def prefixStep {X A B : Type*} (next : B → A) (tag : X → Unit ⊕ B)
    (cell : A × X → Option B) (x : X) (state : Option A × List B) : Option A × List B :=
  match prefixCandidate tag cell x state with
  | none => state
  | some c => (some (next c), state.2 ++ [c])

/-- One literal chronological update. -/
public def extendedPrefixStep (t : Fin p.T) (za : Source p × AuxiliaryArray p) (state : Option (SlowSet p) ×
      List (Cell rate)) :
    Option (SlowSet p) × List (Cell rate) :=
  prefixStep (fun c : Cell rate => c.nextSlowSet) (liveTagAt t) (fun v => cellAt t v.1 v.2) za state

/-- Chronological recursion through the first physical collection. -/
public def extendedPrefixStateAux (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) :
    (n : ℕ) → n ≤ p.T → Source p × AuxiliaryArray p → Option (SlowSet p) × List (Cell rate)
  | 0, _, _ => (none, [])
  | n + 1, hn, za =>
      let state := extendedPrefixStateAux rate rewards C_star C_h n (Nat.le_of_succ_le hn) za
      extendedPrefixStep rate rewards C_star C_h ⟨n, Nat.lt_of_succ_le hn⟩ za state

local notation "prefixState" => extendedPrefixStateAux rate rewards C_star C_h

private theorem measurable_option_cases {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun v => match o v with | none => f v | some a => g (v, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have hsplit := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp hsplit using 1
  funext v
  cases h : o v <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

private theorem measurable_prefixStep {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (next : B → A) (hnext : Measurable next)
    (tag : X → Unit ⊕ B) (htag : Measurable tag)
    (cell : A × X → Option B) (hcell : Measurable cell)
    (happend : Measurable (fun v : List B × B => v.1 ++ [v.2])) :
    Measurable (fun v : X × (Option A × List B) =>
      prefixStep next tag cell v.1 v.2) := by
  let D := X × (Option A × List B)
  let candidateAt : D → Option B := fun v => match v.2.1 with
    | none => none | some U => cell (U, v.1)
  have hl : Measurable candidateAt := measurable_option_cases _ (measurable_fst.comp measurable_snd)
    _ measurable_const _ (hcell.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hc : Measurable (Sum.elim (fun v : D × Unit => candidateAt v.1)
      (fun v : D × B => some v.2)) := (hl.comp measurable_fst).sumElim
        (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_snd)
  have hf : Measurable (fun v : D => match tag v.1 with
      | .inl _ => candidateAt v | .inr c => some c) := by
    convert hc.comp ((MeasurableEquiv.prodSumDistrib D Unit B).measurable.comp
      (measurable_id.prodMk (htag.comp measurable_fst))) using 1
    funext v
    simp only [Function.comp_apply, id_eq]
    cases tag v.1 <;> rfl
  have hp : Measurable (fun v : D × B => (some (next v.2), v.1.2.2 ++ [v.2])) :=
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ (hnext.comp measurable_snd)).prodMk
        (happend.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  convert measurable_option_cases _ hf _ measurable_snd _ hp using 1
  funext v
  unfold prefixStep prefixCandidate
  cases tag v.1 <;> rfl

public theorem measurable_extendedPrefixStep (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (fun v : (Source p × AuxiliaryArray p) × (Option (SlowSet p) × List (Cell rate)) =>
      extendedPrefixStep rate rewards C_star C_h t v.1 v.2) := by
  have hn : Measurable (fun c : Cell rate => c.nextSlowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.mono le_rfl le_top
  have ha : Measurable (fun v : List (Cell rate) × Cell rate => v.1 ++ [v.2]) :=
    (measurable_appendCurrentTag rate).comp (measurable_fst.prodMk (measurable_inr.comp measurable_snd))
  exact measurable_prefixStep _ hn _ (measurable_currentCellTag rate rewards C_star C_h t)
    _ (measurable_collectionCellAt rate rewards C_star C_h control0 t) ha

public theorem measurable_extendedPrefixStateAux (control0 : TimeControl p) : ∀ n (hn : n ≤ p.T),
      Measurable (prefixState n hn) := by
  intro n
  induction n with
  | zero => intro hn; exact measurable_const
  | succ n ih =>
      intro hn
      change Measurable (fun za => extendedPrefixStep rate rewards C_star C_h
        ⟨n, Nat.lt_of_succ_le hn⟩ za (prefixState n (Nat.le_of_succ_le hn) za))
      have hi : Measurable (prefixState n (Nat.le_of_succ_le hn)) := ih (Nat.le_of_succ_le hn)
      have hp : Measurable (fun za : Source p × AuxiliaryArray p =>
          (za, prefixState n (Nat.le_of_succ_le hn) za)) := measurable_id.prodMk hi
      convert (measurable_extendedPrefixStep rate rewards C_star C_h control0 ⟨n, Nat.lt_of_succ_le hn⟩).comp hp using 1
      rfl

public theorem extendedPrefixStep_auxiliary_ext (t : Fin p.T) (z : Source p) (a b : AuxiliaryArray p)
    (state : Option (SlowSet p) × List (Cell rate))
    (h0 : a (t, 0) = b (t, 0)) (h1 : a (t, 1) = b (t, 1)) :
    extendedPrefixStep rate rewards C_star C_h t (z, a) state =
      extendedPrefixStep rate rewards C_star C_h t (z, b) state := by
  unfold extendedPrefixStep prefixStep prefixCandidate
  rw [currentCellTag_auxiliary_ext rate rewards C_star C_h t z a b h1]
  cases liveTagAt t (z, b) with
  | inr cell => rfl
  | inl u =>
      cases state.1 with
      | none => rfl
      | some U =>
          dsimp only
          rw [collectionCellAt_auxiliary_ext rate rewards C_star C_h t U z a b h0 h1]

private theorem prefixState_ext : ∀ n (hn : n ≤ p.T) (za zb : Source p × AuxiliaryArray p),
    (∀ t : Fin p.T, t.val < n → ∀ S, extendedPrefixStep rate rewards C_star C_h t za S =
      extendedPrefixStep rate rewards C_star C_h t zb S) → prefixState n hn za = prefixState n hn zb := by
  intro n
  induction n with
  | zero => intro hn za zb h; rfl
  | succ n ih =>
      intro hn za zb h
      change extendedPrefixStep rate rewards C_star C_h ⟨n, Nat.lt_of_succ_le hn⟩ za _ =
        extendedPrefixStep rate rewards C_star C_h ⟨n, Nat.lt_of_succ_le hn⟩ zb _
      rw [ih (Nat.le_of_succ_le hn) za zb (fun t ht => h t (by omega))]
      exact h ⟨n, Nat.lt_of_succ_le hn⟩ (Nat.lt_succ_self n) _

public theorem extendedPrefixStateAux_auxiliary_ext : ∀ n (hn : n ≤ p.T) (z : Source p) (a b : AuxiliaryArray p),
      (∀ t : Fin p.T, t.val < n → ∀ l : Fin 2, a (t, l) = b (t, l)) →
      prefixState n hn (z, a) = prefixState n hn (z, b) := by
  intro n hn z a b hab
  apply prefixState_ext rate rewards C_star C_h
  intro t ht S
  exact extendedPrefixStep_auxiliary_ext rate rewards C_star C_h t z a b S (hab t ht 0) (hab t ht 1)

public theorem extendedPrefixStep_sourcePrefix (control0 : TimeControl p) (t : Fin p.T) (n : ℕ) (ht : t.val < n)
    (z : Source p) (a : AuxiliaryArray p) (state : Option (SlowSet p) × List (Cell rate)) :
    extendedPrefixStep rate rewards C_star C_h t (z, a) state =
      extendedPrefixStep rate rewards C_star C_h t (sourcePrefix control0 n z, a) state := by
  have hc := currentCellTag_sourcePrefix rate rewards C_star C_h control0 t z a
  have hc' := currentCellTag_sourcePrefix rate rewards C_star C_h control0 t (sourcePrefix control0 n z) a
  rw [sourcePrefix_sourcePrefix control0 (t.val + 1) n (by omega)] at hc'
  have htag := hc.trans hc'.symm
  unfold extendedPrefixStep prefixStep prefixCandidate
  rw [htag]
  cases liveTagAt t (sourcePrefix control0 n z, a) with
  | inr cell => rfl
  | inl u =>
      cases state.1 with
      | none => rfl
      | some U =>
          dsimp only
          rw [collectionCellAt_sourcePrefix rate rewards C_star C_h control0 t n ht U z a]

public theorem extendedPrefixStateAux_sourcePrefix (control0 : TimeControl p) :
    ∀ n (hn : n ≤ p.T) (z : Source p) (a : AuxiliaryArray p),
      prefixState n hn (z, a) = prefixState n hn (sourcePrefix control0 n z, a) := by
  intro n hn z a
  apply prefixState_ext rate rewards C_star C_h
  intro t ht S
  exact extendedPrefixStep_sourcePrefix rate rewards C_star C_h control0 t n ht z a S

public theorem extendedPrefixStateAux_replace_current (control0 : TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (hnt : n ≤ t.val)
    (z : Source p) (a : AuxiliaryArray p) (u : TimeControl p) :
    prefixState n hn (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u, a) =
      prefixState n hn (z, a) := by
  rw [extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h control0 n hn
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) a,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 t n hnt z u]
  exact (extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h control0 n hn z a).symm

public theorem extendedPrefixStateAux_replace_residual (t : Fin p.T)
    (z : Source p) (a : AuxiliaryArray p) (x : Scalar) :
    prefixState t.val (Nat.le_of_lt t.isLt) (z, Function.update a (t, 1) x) =
      prefixState t.val (Nat.le_of_lt t.isLt) (z, a) := by
  classical
  apply extendedPrefixStateAux_auxiliary_ext
  intro v hv l
  exact Function.update_of_ne (by intro h; have he : v = t := congrArg Prod.fst h; subst v; omega) _ _

/-- The actual first collection starts immediately after the whole first LIVE window. -/
public def collectionStart (z : Source p) : ℕ := launchAt z +
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z

public theorem collectionStart_le_of_actualDomain (t : Fin p.T) (z : Source p)
    (hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t) :
    collectionStart rate rewards C_star C_h z ≤ t.val := by
  obtain ⟨r, hr, hm⟩ := hz
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val z := by
    by_contra hn
    rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hn] at hr
    cases hr
  obtain ⟨_, _, hread, _⟩ := actual_data rewards C_star C_h z t r hr hm
  exact ReferenceFirstCollectionPrecallCalendarSupport.old_readout_after_firstLiveWindow
    rate rewards C_star C_h t z hlaunch r hr (by rw [hread]; rfl)

public theorem collectionCellAt_none_before_collectionStart (t : Fin p.T) (U : SlowSet p)
    (z : Source p) (a : AuxiliaryArray p)
    (ht : t.val < collectionStart rate rewards C_star C_h z) :
    cellAt t U (z, a) = none := by
  classical
  have hn : z ∉ actualDomain (rate := rate) rewards C_star C_h t := by
    intro hz
    have h := collectionStart_le_of_actualDomain rate rewards C_star C_h t z hz
    omega
  simp only [collectionCellAt, ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?, dite_eq_right hn]

public theorem firstLiveLength_pos_of_actualDomain (t : Fin p.T) (z : Source p)
    (hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t) :
    0 < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z := by
  obtain ⟨r, hr, _⟩ := hz
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val z := by
    by_contra hn
    rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hn] at hr
    cases hr
  have hc := hlaunch.1
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate z rewards C_star C_h hc
  have hcoord := (ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc).2.2.2.1
  have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch rate z rewards C_star C_h _ hl
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hs := hlaunch.2
  cases hR : suffixAt z with
  | nil => rw [hR] at hlen; simp only [List.length_nil] at hlen; omega
  | cons first rest =>
      rw [hR] at hconnected
      have hfirst : first.input.state.coordinator = .first := by
        rw [hconnected.1]
        exact hcoord
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen first.input = false := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch, hfirst,
          CoordinatorRoundDispatch.dispatch]
        rfl
      simp only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow,
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hR, List.takeWhile_cons,
        hcut, Bool.not_false, ite_true, List.length_cons]
      omega

public theorem extendedPrefixStateAux_seed : ∀ n (hn : n ≤ p.T) (za : Source p × AuxiliaryArray p),
    (prefixState n hn za).1 = (prefixState n hn za).2.getLast?.map (fun c => c.nextSlowSet) := by
  intro n
  induction n with
  | zero => intro hn za; rfl
  | succ n ih =>
      intro hn za
      let t : Fin p.T := ⟨n, Nat.lt_of_succ_le hn⟩
      let state := prefixState n (Nat.le_of_succ_le hn) za
      have hseed : state.1 = state.2.getLast?.map (fun c => c.nextSlowSet) := ih (Nat.le_of_succ_le hn) za
      change (extendedPrefixStep rate rewards C_star C_h t za state).1 =
        (extendedPrefixStep rate rewards C_star C_h t za state).2.getLast?.map _
      unfold extendedPrefixStep prefixStep
      split
      · exact hseed
      · simp only [List.getLast?_append_cons]; rfl

public theorem extendedPrefixStateAux_before_collectionStart : ∀ n (hn : n ≤ p.T) (z : Source p) (a : AuxiliaryArray p),
      n ≤ collectionStart rate rewards C_star C_h z →
      (prefixState n hn (z, a)).2 = calendarPast rate rewards C_star C_h (z, a) n := by
  intro n
  induction n with
  | zero =>
      intro hn z a hbefore
      exact (calendarPast_zero rate rewards C_star C_h (z, a)).symm
  | succ n ih =>
      intro hn z a hbefore
      let t : Fin p.T := ⟨n, Nat.lt_of_succ_le hn⟩
      let state := prefixState n (Nat.le_of_succ_le hn) (z, a)
      have hp : state.2 = calendarPast rate rewards C_star C_h (z, a) n := ih (Nat.le_of_succ_le hn) z a (by omega)
      have hc (U : SlowSet p) := collectionCellAt_none_before_collectionStart
        rate rewards C_star C_h t U z a (by dsimp [t]; omega)
      change (extendedPrefixStep rate rewards C_star C_h t (z, a) state).2 = _
      rw [calendarPast_successor rate rewards C_star C_h t (z, a)]
      cases htag : liveTagAt t (z, a) with
      | inr c => simpa only [extendedPrefixStep, prefixStep, prefixCandidate, htag, List.append_assoc] using
          congrArg (fun L => L ++ [c]) hp
      | inl u =>
          cases hu : state.1 with
          | none => simpa only [extendedPrefixStep, prefixStep, prefixCandidate, htag, hu, List.append_nil] using hp
          | some U => simpa only [extendedPrefixStep, prefixStep, prefixCandidate, htag, hu, hc U, List.append_nil] using hp

private theorem prefixStep_prefix {X A B : Type*} (next : B → A) (tag : X → Unit ⊕ B)
    (cell : A × X → Option B) (x : X) (state : Option A × List B) :
    state.2 <+: (prefixStep next tag cell x state).2 := by
  unfold prefixStep
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

public theorem extendedPrefixStateAux_prefix : ∀ n (hn : n ≤ p.T) (m : ℕ) (hmn : m ≤ n)
      (za : Source p × AuxiliaryArray p),
    (prefixState m (hmn.trans hn) za).2 <+: (prefixState n hn za).2 := by
  intro n hn m hmn za
  induction hmn with
  | refl => exact List.prefix_refl _
  | @step n hmn ih =>
      exact (ih (Nat.le_of_succ_le hn)).trans (prefixStep_prefix _ _ _ za (prefixState n (Nat.le_of_succ_le hn) za))

public theorem firstLive_prefix_of_actualDomain (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t) :
    livePast (z, a) <+: (prefixState t.val (Nat.le_of_lt t.isLt) (z, a)).2 := by
  let u := collectionStart rate rewards C_star C_h z
  have hut : u ≤ t.val := collectionStart_le_of_actualDomain rate rewards C_star C_h t z hz
  have huT : u ≤ p.T := hut.trans (Nat.le_of_lt t.isLt)
  have hu := extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h u huT z a le_rfl
  have hcalendar : calendarPast rate rewards C_star C_h (z, a) u = livePast (z, a) := by
    rw [calendarPast_eq_take_elapsed]
    have hs : u - launchAt z = (livePast (z, a)).length := by
      rw [firstLiveChronologicalPrefix_length]
      dsimp [u, collectionStart]
      omega
    rw [hs, List.take_length]
  rw [hcalendar] at hu
  rw [← hu]
  exact extendedPrefixStateAux_prefix rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) u hut (z, a)

public theorem generatedIncoming_present (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t) :
    ∃ U : SlowSet p, (prefixState t.val (Nat.le_of_lt t.isLt) (z, a)).1 = some U := by
  let state := prefixState t.val (Nat.le_of_lt t.isLt) (z, a)
  have hpos : 0 < state.2.length := by
    have hp := firstLive_prefix_of_actualDomain rate rewards C_star C_h t z a hz
    have hl := firstLiveLength_pos_of_actualDomain rate rewards C_star C_h t z hz
    have hlen := firstLiveChronologicalPrefix_length rate rewards C_star C_h (z, a)
    dsimp only at hlen
    have hle := hp.length_le
    change (livePast (z, a)).length ≤ state.2.length at hle
    omega
  have hs : state.1 = state.2.getLast?.map (fun c => c.nextSlowSet) :=
    extendedPrefixStateAux_seed rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) (z, a)
  cases hlast : state.2.getLast? with
  | none =>
      have he := List.getLast?_eq_none_iff.mp hlast
      rw [he] at hpos
      cases hpos
  | some c => exact ⟨c.nextSlowSet, by rw [hs, hlast]; rfl⟩

public theorem currentCellTag_absent_of_actualDomain (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t) :
    liveTagAt t (z, a) = Sum.inl () := by
  have hstart := collectionStart_le_of_actualDomain rate rewards C_star C_h t z hz
  have hlen := firstLiveChronologicalPrefix_length rate rewards C_star C_h (z, a)
  dsimp only [collectionStart] at hstart
  dsimp only at hlen
  have hi : (livePast (z, a)).length ≤ t.val - launchAt z := by omega
  rw [currentCellTag_eq_lookup]
  split
  · simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_none hi]
  · rfl

/-- The literal complete logical-cell list at every boundary. -/
@[simp] public def extendedPast (n : Fin (p.T + 1)) (za : Source p × AuxiliaryArray p) : List (Cell rate) :=
  (prefixState n.val (Nat.le_of_lt_succ n.isLt) za).2

local notation "pastAt" => extendedPast rate rewards C_star C_h

/-- The observer carried into the killed-law recursion. -/
public def extendedObservation (control0 : TimeControl p) (n : Fin (p.T + 1))
    (za : Source p × AuxiliaryArray p) : Observation rate :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val za.1, (labelZero za.2, pastAt n za))

local notation "observerAt" => extendedObservation rate rewards C_star C_h

public theorem measurable_extendedPast (control0 : TimeControl p) (n : Fin (p.T + 1)) : Measurable (pastAt n) :=
  measurable_snd.comp (measurable_extendedPrefixStateAux rate rewards C_star C_h control0
    n.val (Nat.le_of_lt_succ n.isLt))

public theorem measurable_extendedObservation (control0 : TimeControl p) (n : Fin (p.T + 1)) :
    Measurable (observerAt control0 n) :=
  ((measurable_sourcePrefix control0 n.val).comp measurable_fst).prodMk
    (((measurable_labelZero p).comp measurable_snd).prodMk (measurable_extendedPast rate rewards C_star C_h control0 n))

public theorem extendedPrefixStateAux_zero (za : Source p × AuxiliaryArray p) :
    prefixState 0 (Nat.zero_le _) za = (none, []) := rfl

public theorem extendedPast_zero (za : Source p × AuxiliaryArray p) : pastAt 0 za = [] := rfl

public theorem extendedPast_succ_live (t : Fin p.T) (za : Source p × AuxiliaryArray p) (cell : Cell rate)
    (hcell : liveTagAt t za = Sum.inr cell) :
    pastAt t.succ za = pastAt t.castSucc za ++ [cell] := by
  change (extendedPrefixStep rate rewards C_star C_h t za (prefixState t.val (Nat.le_of_lt t.isLt) za)).2 = _
  simp [extendedPrefixStep, prefixStep, prefixCandidate, hcell, extendedPast]

/-- Read the incoming set only from the existing complete list. -/
public def incomingFromList (rate : RateInput p) (L : List (Cell rate)) : Option (SlowSet p) :=
  L.getLast?.map (fun c => c.nextSlowSet)

public theorem measurable_incomingFromList (rate : RateInput p) : Measurable (incomingFromList rate) := by
  let get : Unit ⊕ Cell rate → Option (SlowSet p) := Sum.elim (fun _ => none) (fun c => some c.nextSlowSet)
  have hn : Measurable (fun c : Cell rate => c.nextSlowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet.mono le_rfl le_top
  have hg : Measurable get := measurable_const.sumElim
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hn)
  have he : Measurable (fun v : ℕ × (ℕ → Unit ⊕ Cell rate) => v.2 (v.1 - 1)) :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply (n - 1)
  have h := hg.comp (he.comp ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates)
  convert h using 1
  funext L
  dsimp only [incomingFromList, Function.comp_apply, get,
    ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt]
  rw [List.getLast?_eq_getElem?]
  cases L[L.length - 1]? <;> rfl

/-- Supply the retained whole label-zero array and one current residual scalar to the local operation. -/
public def roundAuxiliary (t : Fin p.T) (v : LabelZeroArray p × Scalar) : AuxiliaryArray p :=
  fun q => if q.2 = 0 then v.1 q.1 else
    if q.1 = t then v.2 else ReferenceFirstLiveActualRefreshTestLaw.scalarZero

public theorem measurable_roundAuxiliary (t : Fin p.T) : Measurable (roundAuxiliary (p := p) t) := by
  classical
  unfold roundAuxiliary
  apply Measurable.of_eval
  intro q
  split_ifs <;> fun_prop

/-- The original current source control. -/
public def extensionInput (rate : RateInput p) (t : Fin p.T) (v : Observation rate × (TimeControl p × Scalar)) :
    (Source p × AuxiliaryArray p) × (Option (SlowSet p) × List (Cell rate)) :=
  ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1.1 v.2.1,
    roundAuxiliary t (v.1.2.1, v.2.2)), (incomingFromList rate v.1.2.2, v.1.2.2))

public theorem measurable_extensionInput (rate : RateInput p) (t : Fin p.T) : Measurable (extensionInput rate t) := by
  have hL : Measurable (fun v : Observation rate × (TimeControl p × Scalar) => v.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  exact (((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk
    ((measurable_roundAuxiliary t).comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)))).prodMk
      (((measurable_incomingFromList rate).comp hL).prodMk hL)

/-- A chronological physical-control/residual innovation. -/
public def extensionSample (t : Fin p.T) (v : Observation rate × (TimeControl p × Scalar)) : Observation rate :=
  let d := extensionInput rate t v
  (d.1.1, (v.1.2.1, (extendedPrefixStep rate rewards C_star C_h t d.1 d.2).2))

public theorem measurable_extensionSample (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (extensionSample rate rewards C_star C_h t) := by
  have hs := (measurable_extendedPrefixStep rate rewards C_star C_h control0 t).comp (measurable_extensionInput rate t)
  exact (measurable_fst.comp (measurable_fst.comp (measurable_extensionInput rate t))).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk (measurable_snd.comp hs))

local notation "sampleAt" => extensionSample rate rewards C_star C_h

public theorem extensionSample_actual (control0 : TimeControl p) (t : Fin p.T) (za : Source p × AuxiliaryArray p) :
    sampleAt t (observerAt control0 t.castSucc za, (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))) =
      observerAt control0 t.succ za := by
  classical
  let state := prefixState t.val (Nat.le_of_lt t.isLt) za
  have hseed : state.1 = incomingFromList rate state.2 :=
    extendedPrefixStateAux_seed rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) za
  have hsource := prefix_successor_restore control0 t za.1
  change sourcePrefix control0 (t.val + 1) za.1 = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (sourcePrefix control0 t.val za.1) (ReferenceSourceCurrentControlFreshness.u_t p t za.1) at hsource
  have hp := extendedPrefixStep_sourcePrefix rate rewards C_star C_h control0 t (t.val + 1)
    (Nat.lt_succ_self _) za.1 za.2 state
  have ha := extendedPrefixStep_auxiliary_ext rate rewards C_star C_h t (sourcePrefix control0 (t.val + 1) za.1) za.2
    (roundAuxiliary t (labelZero za.2, za.2 (t, 1))) state
    (by simp only [roundAuxiliary, labelZero, ite_true])
    (by simp only [roundAuxiliary, (show (1 : Fin 2) ≠ 0 by decide), ite_false, ite_true])
  unfold extensionSample extensionInput extendedObservation
  change (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (sourcePrefix control0 t.val za.1) (ReferenceSourceCurrentControlFreshness.u_t p t za.1),
      (labelZero za.2, (extendedPrefixStep rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (sourcePrefix control0 t.val za.1) (ReferenceSourceCurrentControlFreshness.u_t p t za.1),
          roundAuxiliary t (labelZero za.2, za.2 (t, 1)))
        (incomingFromList rate state.2, state.2)).2)) =
    (sourcePrefix control0 (t.val + 1) za.1,
      (labelZero za.2, (extendedPrefixStep rate rewards C_star C_h t za state).2))
  rw [← hsource, ← hseed, ← ha, ← hp]

public theorem noCallBefore_succ (t : Fin p.T) (z : Source p) :
    precall t.succ z ↔ precall t.castSucc z ∧ noCall t z := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (by simpa using Nat.lt_succ_of_lt hv), h t (Nat.lt_succ_self _)⟩
  · rintro ⟨h, ht⟩ v hv
    by_cases hvt : v.val < t.val
    · exact h v hvt
    · have he : v = t := Fin.ext (by simp only [Fin.val_succ] at hv; omega)
      subst v
      exact ht

public theorem noCallAt_sourcePrefix (control0 : TimeControl p) (t : Fin p.T) (n : ℕ) (ht : t.val ≤ n) (z : Source p) :
    noCall t z ↔ noCall t (sourcePrefix control0 n z) := by
  rw [noCallAt_iff_callAt_none, noCallAt_iff_callAt_none]
  rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 t z,
    ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 t
      (sourcePrefix control0 n z), sourcePrefix_sourcePrefix control0 t.val n ht]

public theorem noCallBefore_sourcePrefix (control0 : TimeControl p) (n : Fin (p.T + 1)) (z : Source p) :
    precall n z ↔ precall n (sourcePrefix control0 n.val z) := by
  unfold NoCallBefore
  apply forall_congr'
  intro t
  exact imp_congr_right (fun ht => noCallAt_sourcePrefix rate rewards C_star C_h control0 t n.val (Nat.le_of_lt ht) z)

/-- Reconstruct the complete generated observation with only the current label-one coordinate erased. -/
public def extendedFromErasure (t : Fin p.T) (v : Source p × ErasedAuxiliaryArray (p := p) t) : Observation rate :=
  let a := insertActualRefreshCoordinate t v.2 scalarZero
  (v.1, (labelZero a, pastAt t.castSucc (v.1, a)))

public theorem measurable_extendedFromErasure (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (extendedFromErasure rate rewards C_star C_h t) := by
  have ha : Measurable (fun v : Source p × ErasedAuxiliaryArray (p := p) t =>
      insertActualRefreshCoordinate t v.2 scalarZero) :=
    (measurable_insertActualRefreshCoordinate t).comp (measurable_snd.prodMk measurable_const)
  exact measurable_fst.prodMk (((measurable_labelZero p).comp ha).prodMk
    ((measurable_extendedPast rate rewards C_star C_h control0 t.castSucc).comp (measurable_fst.prodMk ha)))

private theorem split_insert_original (t : Fin p.T) (a : AuxiliaryArray p) :
    insertActualRefreshCoordinate t (actualRefreshScalarSplit t a).1 (actualRefreshScalarSplit t a).2 = a :=
  (actualRefreshScalarSplit_symm_apply t (actualRefreshScalarSplit t a)).symm.trans
    ((actualRefreshScalarSplit t).symm_apply_apply a)

private theorem split_scalar (t : Fin p.T) (a : AuxiliaryArray p) : (actualRefreshScalarSplit t a).2 = a (t, 1) := by
  have h := congrArg (fun b : AuxiliaryArray p => b (t, 1)) (split_insert_original t a)
  simpa only [insertActualRefreshCoordinate, dite_true] using h

public theorem extendedFromErasure_actual (control0 : TimeControl p) (t : Fin p.T) (za : Source p × AuxiliaryArray p) :
    extendedFromErasure rate rewards C_star C_h t
      (sourcePrefix control0 t.val za.1, (actualRefreshScalarSplit t za.2).1) = observerAt control0 t.castSucc za := by
  let a := insertActualRefreshCoordinate t (actualRefreshScalarSplit t za.2).1 scalarZero
  have hcoord (q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) (hq : q ≠ (t, 1)) : a q = za.2 q := by
    rw [← split_insert_original t za.2]
    simp only [a, insertActualRefreshCoordinate, hq, dite_false]
  have hlabel : labelZero a = labelZero za.2 := by
    funext u
    exact hcoord (u, 0) (by intro h; exact Fin.zero_ne_one (congrArg Prod.snd h))
  have hpast := congrArg Prod.snd (extendedPrefixStateAux_auxiliary_ext rate rewards C_star C_h
    t.val (Nat.le_of_lt t.isLt) (sourcePrefix control0 t.val za.1) a za.2 (by
      intro u hu l
      apply hcoord
      intro heq
      have hut : u = t := congrArg Prod.fst heq
      subst u
      omega))
  have hsource := congrArg Prod.snd (extendedPrefixStateAux_sourcePrefix rate rewards C_star C_h
    control0 t.val (Nat.le_of_lt t.isLt) za.1 za.2)
  change (sourcePrefix control0 t.val za.1, (labelZero a,
      (prefixState t.val (Nat.le_of_lt t.isLt) (sourcePrefix control0 t.val za.1, a)).2)) = _
  rw [hlabel, hpast, ← hsource]
  rfl

private theorem measurePreserving_reorder {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun v : (A × B) × (C × D) => ((v.1.1, v.2.1), (v.1.2, v.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc b c d).symm
  have h3 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := (measurePreserving_prodAssoc a c (b.prod d)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- The original current physical control and current residual are fresh jointly. -/
public theorem extendedObservation_current_innovation_product (control0 : TimeControl p) (t : Fin p.T) :
    (enlargedSourceLaw p).map (fun za =>
        (observerAt control0 t.castSucc za, (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1)))) =
      ((enlargedSourceLaw p).map (observerAt control0 t.castSucc)).prod (calendarInnovationLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let μc := μ.map (sourcePrefix control0 t.val)
  let μe := erasedAuxiliaryLaw (p := p) t
  let μu := ContinuousLearningRows.timeControlLaw p
  let μx := scalarLaw
  let f := fun z : Source p => (sourcePrefix control0 t.val z, ReferenceSourceCurrentControlFreshness.u_t p t z)
  have hf : Measurable f := (measurable_sourcePrefix control0 t.val).prodMk
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hsource : MeasurePreserving f μ (μc.prod μu) := ⟨hf, sourcePrefix_currentControl_product control0 t⟩
  have hsplit := hsource.prod (measurePreserving_actualRefreshScalarSplit (p := p) t)
  have hreorder := measurePreserving_reorder μc μu μe μx
  let g := extendedFromErasure rate rewards C_star C_h t
  have hg : Measurable g := measurable_extendedFromErasure rate rewards C_star C_h control0 t
  have hobs : MeasurePreserving g (μc.prod μe) ((μc.prod μe).map g) := ⟨hg, rfl⟩
  have hfull := (hobs.prod (MeasurePreserving.id (μu.prod μx))).comp (hreorder.comp hsplit)
  have hjoint : (enlargedSourceLaw p).map (fun za =>
      (observerAt control0 t.castSucc za, (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1)))) =
        ((μc.prod μe).map g).prod (calendarInnovationLaw p) := by
    convert hfull.map_eq using 1
    congr 1
    funext za
    apply Prod.ext
    · exact (extendedFromErasure_actual rate rewards C_star C_h control0 t za).symm
    · exact Prod.ext rfl (split_scalar t za.2).symm
    rfl
  have hu : Measurable (fun za : Source p × AuxiliaryArray p =>
      (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))) :=
    ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_fst).prodMk
      ((measurable_pi_apply (t, 1)).comp measurable_snd)
  have hmarg := congrArg Measure.fst hjoint
  rw [Measure.fst_map_prodMk (measurable_extendedObservation rate rewards C_star C_h control0 t.castSucc)
    hu, Measure.fst_prod] at hmarg
  rw [hmarg]
  exact hjoint

/-- Explicit chronological innovation kernel. -/
public def extensionKernel (control0 : TimeControl p) (t : Fin p.T) :
    ProbabilityTheory.Kernel (Observation rate) (Observation rate) :=
  ProbabilityTheory.Kernel.mapOfMeasurable (ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const (Observation rate) (calendarInnovationLaw p)))
    (sampleAt t)
    (measurable_extensionSample rate rewards C_star C_h control0 t)

public theorem extensionKernel_apply (control0 : TimeControl p) (t : Fin p.T) (w : Observation rate) :
    extensionKernel rate rewards C_star C_h control0 t w = (calendarInnovationLaw p).map
      (fun ux => sampleAt t (w, ux)) := by
  change (((ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
    (ProbabilityTheory.Kernel.const (Observation rate) (calendarInnovationLaw p))) w).map (sampleAt t)) = _
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_extensionSample rate rewards C_star C_h control0 t) measurable_prodMk_left]
  rfl

/-- Kill at the first actual collection invocation BEFORE its sampler. -/
public def preKernel (control0 : TimeControl p) (t : Fin p.T) :
    ProbabilityTheory.Kernel (Observation rate) (Observation rate) := by
  classical
  exact ProbabilityTheory.Kernel.piecewise
    ((measurableSet_noCallAt rate rewards C_star C_h control0 t).preimage measurable_fst)
    (extensionKernel rate rewards C_star C_h control0 t) 0

public theorem preKernel_lintegral (control0 : TimeControl p) (t : Fin p.T) (w : Observation rate)
    (Phi : Observation rate → ℝ≥0∞) (hPhi : Measurable Phi) :
    ∫⁻ y, Phi y ∂preKernel rate rewards C_star C_h control0 t w =
      if noCall t w.1 then ∫⁻ ux, Phi (sampleAt t (w, ux)) ∂calendarInnovationLaw p else 0 := by
  classical
  simp only [preKernel, ProbabilityTheory.Kernel.piecewise_apply, Set.mem_preimage, Set.mem_ofPred_eq]
  split
  · rw [extensionKernel_apply]
    exact lintegral_map (g := fun ux => sampleAt t (w, ux)) hPhi
      ((measurable_extensionSample rate rewards C_star C_h control0 t).comp measurable_prodMk_left)
  · simp only [zero_apply, lintegral_zero_measure]

public theorem killed_successor_lintegral (control0 : TimeControl p) (t : Fin p.T)
    (Phi : Observation rate → ℝ≥0∞) (hPhi : Measurable Phi) :
    ∫⁻ za, Phi (observerAt control0 t.succ za) ∂(enlargedSourceLaw p).restrict {za | precall t.succ za.1} =
    ∫⁻ za, ∫⁻ y, Phi y ∂preKernel rate rewards C_star C_h control0 t (observerAt control0 t.castSucc za)
      ∂(enlargedSourceLaw p).restrict {za | precall t.castSucc za.1} := by
  classical
  let O := observerAt control0 t.castSucc
  let fresh := fun za : Source p × AuxiliaryArray p =>
    (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))
  let F := fun v : Observation rate × (TimeControl p × Scalar) =>
    if precall t.castSucc v.1.1 ∧ noCall t v.1.1
    then Phi (sampleAt t v) else 0
  have hO : Measurable O := measurable_extendedObservation rate rewards C_star C_h control0 t.castSucc
  have hfresh : Measurable fresh :=
    ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_fst).prodMk
      ((measurable_pi_apply (t, 1)).comp measurable_snd)
  have hF : Measurable F := (hPhi.comp (measurable_extensionSample rate rewards C_star C_h control0 t)).ite
    (((measurableSet_noCallBefore rate rewards C_star C_h control0 t.castSucc).preimage
      (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_noCallAt rate rewards C_star C_h control0 t).preimage
        (measurable_fst.comp measurable_fst))) measurable_const
  have hS : MeasurableSet {za : Source p × AuxiliaryArray p | precall t.castSucc za.1} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 t.castSucc).preimage
    (measurable_fst : Measurable (Prod.fst : Source p × AuxiliaryArray p → Source p))
  have hS' : MeasurableSet {za : Source p × AuxiliaryArray p | precall t.succ za.1} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 t.succ).preimage
    (measurable_fst : Measurable (Prod.fst : Source p × AuxiliaryArray p → Source p))
  have hleft : (∫⁻ za, F (O za, fresh za) ∂enlargedSourceLaw p) = ∫⁻ za, Phi (observerAt control0 t.succ za)
        ∂(enlargedSourceLaw p).restrict {za | precall t.succ za.1} := by
    rw [← lintegral_indicator hS']
    apply lintegral_congr
    intro za
    change (if precall t.castSucc (sourcePrefix control0 t.val za.1) ∧
        noCall t (sourcePrefix control0 t.val za.1) then Phi (sampleAt t (O za, fresh za)) else 0) =
      if precall t.succ za.1 then Phi (observerAt control0 t.succ za) else 0
    have hE : precall t.castSucc za.1 ↔ precall t.castSucc (sourcePrefix control0 t.val za.1) :=
      noCallBefore_sourcePrefix rate rewards C_star C_h control0 t.castSucc za.1
    have hactual : sampleAt t (O za, fresh za) = observerAt control0 t.succ za :=
      extensionSample_actual rate rewards C_star C_h control0 t za
    have hC := noCallAt_sourcePrefix rate rewards C_star C_h control0 t t.val le_rfl za.1
    simp only [← hE, ← hC, noCallBefore_succ, hactual]
  have hright : (∫⁻ w, ∫⁻ ux, F (w, ux) ∂calendarInnovationLaw p ∂(enlargedSourceLaw p).map O) =
      ∫⁻ za, ∫⁻ y, Phi y ∂preKernel rate rewards C_star C_h control0 t (O za)
        ∂(enlargedSourceLaw p).restrict {za | precall t.castSucc za.1} := by
    rw [lintegral_map hF.lintegral_prod_right' hO, ← lintegral_indicator hS]
    apply lintegral_congr
    intro za
    change (∫⁻ ux, F (O za, ux) ∂calendarInnovationLaw p) =
      if precall t.castSucc za.1 then ∫⁻ y, Phi y ∂preKernel rate rewards C_star C_h control0 t (O za) else 0
    rw [preKernel_lintegral rate rewards C_star C_h control0 t (O za) Phi hPhi]
    have hE := noCallBefore_sourcePrefix rate rewards C_star C_h control0 t.castSucc za.1
    change (∫⁻ ux, if precall t.castSucc (O za).1 ∧ noCall t (O za).1 then
      Phi (sampleAt t (O za, ux)) else 0 ∂calendarInnovationLaw p) = _
    change precall t.castSucc za.1 ↔ precall t.castSucc (O za).1 at hE
    simp only [← hE]
    by_cases hs : precall t.castSucc za.1
    · by_cases hc : noCall t (O za).1 <;> simp only [hs, hc, true_and, ite_true, ite_false, lintegral_zero]
    · simp only [hs, false_and, ite_false, lintegral_zero]

  rw [← hleft, ← hright]
  have hjoint : (enlargedSourceLaw p).map (fun za => (O za, fresh za)) =
      ((enlargedSourceLaw p).map O).prod (calendarInnovationLaw p) :=
    extendedObservation_current_innovation_product rate rewards C_star C_h control0 t
  calc _ = ∫⁻ v, F v ∂(enlargedSourceLaw p).map (fun za => (O za, fresh za)) :=
      (lintegral_map hF (hO.prodMk hfresh)).symm
    _ = _ := by rw [hjoint]; exact lintegral_prod _ hF.aemeasurable

/-- Explicit chronological subprobability recursion. -/
public def betaPreAux (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) : (n : ℕ) → n ≤ p.T → Measure (Observation rate)
  | 0, _ => initialCalendarLaw rate control0
  | n + 1, hn => (betaPreAux rate rewards C_star C_h control0 n (Nat.le_of_succ_le hn)).bind
      (preKernel rate rewards C_star C_h control0 ⟨n, Nat.lt_of_succ_le hn⟩)

/-- The killed chronological law at every boundary, including zero and T. -/
public def betaPre (control0 : TimeControl p) (n : Fin (p.T + 1)) : Measure (Observation rate) :=
  betaPreAux rate rewards C_star C_h control0 n.val (Nat.le_of_lt_succ n.isLt)

public theorem extendedObservation_zero_map (control0 : TimeControl p) :
    (enlargedSourceLaw p).map (observerAt control0 0) = initialCalendarLaw rate control0 := by
  have h : observerAt control0 0 = observationAt rate rewards C_star C_h control0 0 := by
    funext za
    change (sourcePrefix control0 0 za.1, (labelZero za.2, [])) =
      (sourcePrefix control0 0 za.1, (labelZero za.2, calendarPast rate rewards C_star C_h za 0))
    rw [calendarPast_zero]
  rw [h]
  exact observationAt_zero_map rate rewards C_star C_h control0

private theorem betaPreAux_lintegral (control0 : TimeControl p) :
    ∀ n (hn : n ≤ p.T) (Phi : Observation rate → ℝ≥0∞), Measurable Phi →
      (∫⁻ za, Phi (observerAt control0 ⟨n, Nat.lt_succ_of_le hn⟩ za)
        ∂(enlargedSourceLaw p).restrict {za | precall ⟨n, Nat.lt_succ_of_le hn⟩ za.1}) =
      ∫⁻ w, Phi w ∂betaPreAux rate rewards C_star C_h control0 n hn := by
  intro n
  induction n with
  | zero =>
      intro hn Phi hPhi
      have hE : {za : Source p × AuxiliaryArray p | precall 0 za.1} = Set.univ := by ext za; simp [NoCallBefore]
      change (∫⁻ za, Phi (observerAt control0 0 za) ∂(enlargedSourceLaw p).restrict {za | precall 0 za.1}) =
        ∫⁻ w, Phi w ∂initialCalendarLaw rate control0
      rw [hE, Measure.restrict_univ, ← extendedObservation_zero_map rate rewards C_star C_h control0]
      exact (lintegral_map hPhi (measurable_extendedObservation rate rewards C_star C_h control0 0)).symm
  | succ n ih =>
      intro hn Phi hPhi
      let t : Fin p.T := ⟨n, Nat.lt_of_succ_le hn⟩
      have hk : Measurable (fun w => ∫⁻ y, Phi y ∂preKernel rate rewards C_star C_h control0 t w) :=
        hPhi.lintegral_kernel
      have hstep := killed_successor_lintegral rate rewards C_star C_h control0 t Phi hPhi
      have hprev := ih (Nat.le_of_succ_le hn) _ hk
      change _ = ∫⁻ w, Phi w ∂(betaPreAux rate rewards C_star C_h control0 n
        (Nat.le_of_succ_le hn)).bind (preKernel rate rewards C_star C_h control0 t)
      rw [Measure.lintegral_bind (ProbabilityTheory.Kernel.aemeasurable _) hPhi.aemeasurable]
      exact hstep.trans hprev

local notation "betaAt" => betaPre rate rewards C_star C_h

/-- Unnormalized whole-source/whole-label-zero/whole-history killed law. -/
public theorem extendedObservation_map_restrict_eq_betaPre (control0 : TimeControl p) (n : Fin (p.T + 1)) :
    ((enlargedSourceLaw p).restrict {za | precall n za.1}).map (observerAt control0 n) = betaAt control0 n := by
  apply Measure.ext_of_lintegral
  intro Phi hPhi
  rw [lintegral_map hPhi (measurable_extendedObservation rate rewards C_star C_h control0 n)]
  exact betaPreAux_lintegral rate rewards C_star C_h control0 n.val (Nat.le_of_lt_succ n.isLt) Phi hPhi

public theorem betaPre_mass (control0 : TimeControl p) (n : Fin (p.T + 1)) :
    betaAt control0 n Set.univ = enlargedSourceLaw p {za | precall n za.1} := by
  rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 n,
    Measure.map_apply (measurable_extendedObservation rate rewards C_star C_h control0 n) MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply_univ]

public theorem betaPre_mass_le_one (control0 : TimeControl p) (n : Fin (p.T + 1)) : betaAt control0 n Set.univ ≤ 1 := by
  rw [betaPre_mass]
  simpa only [measure_univ] using (measure_mono (μ := enlargedSourceLaw p)
      (Set.subset_univ {za : Source p × AuxiliaryArray p | precall n za.1}))

/-- Arbitrary Borel real JOINT tests of the retained source. -/
public theorem joint_test (control0 : TimeControl p) (n : Fin (p.T + 1)) (Phi : Observation rate → ℝ)
    (hPhi : Measurable Phi) :
    (∫ za, Phi (observerAt control0 n za) ∂(enlargedSourceLaw p).restrict {za | precall n za.1}) =
      ∫ w, Phi w ∂betaAt control0 n := by
  rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 n]
  exact (integral_map (measurable_extendedObservation rate rewards C_star C_h control0 n).aemeasurable
    hPhi.aestronglyMeasurable).symm

section Characterization

open ReferenceActualCollectionHiddenRefreshPath
open ReferenceFirstLiveCollectionPathJoin

/-- Calendar interval coverage includes the cutoff head and excludes the invocation. -/
public theorem actualDomain_of_collection_interval (q : Fin p.T) (z : Source p)
    (hq : collectionStart rate rewards C_star C_h z ≤ q.val)
    (hqend : q.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z) :
    z ∈ actualDomain (rate := rate) rewards C_star C_h q := by
  let R := suffixAt z
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z
  let j := q.val - launchAt z - w
  have hend := ReferenceFirstCollectionOneRoundLogicalCell.firstCollection_endpoint (rate := rate) rewards C_star C_h z
  have hstart : launchAt z + w ≤ q.val := hq
  change _ = launchAt z + w + B.length at hend
  have hj : j < B.length := by dsimp [j]; omega
  have hp : B <+: R.drop w := by
    refine ⟨(R.drop (w + 1)).dropWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
    dsimp [B, ReferenceFirstCollectionOneRoundLogicalCell.firstCollection, ReferenceCollectionPhaseHistory.collectionWindow, w]
    rw [List.append_assoc, List.takeWhile_append_dropWhile]
    simp
    rfl
  have hget := hp.getElem hj
  rw [List.getElem_drop] at hget
  have hlen := hp.length_le
  simp only [List.length_drop] at hlen
  have hindex : w + j = q.val - launchAt z := by dsimp [j]; omega
  have hR : R[q.val - launchAt z]? = some B[j] := by
    rw [← hindex, List.getElem?_eq_getElem (by omega), ← hget]
  refine ⟨B[j], ?_, List.getElem_mem hj⟩
  simpa only [actualRecord, ite_eq_left (show launchAt z ≤ q.val by omega)] using hR

public theorem collectionCellAt_of_record (q : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (r : Record rate) (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z) (U : SlowSet p) :
    cellAt q U (z, a) = collectionLogicalCellAt rewards C_star C_h z q r hr hm U (labelZero a) (a (q, 1)) := by
  have hd : z ∈ actualDomain (rate := rate) rewards C_star C_h q := ⟨r, hr, hm⟩
  have he : domainRecord rewards C_star C_h q ⟨z, hd⟩ = r :=
    Option.some.inj ((domainRecord_spec rewards C_star C_h q ⟨z, hd⟩).symm.trans hr)
  simp only [collectionCellAt, ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?, dite_eq_left hd, he]
  rfl

/-- Generated incoming sets and the entire list follow the enabled/disabled branch of the actual input. -/
public theorem generated_collection_step (q : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (r : Record rate) (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z) :
    ∃ U, (prefixState q.val (Nat.le_of_lt q.isLt) (z, a)).1 = some U ∧
      let c := inputAt z q r hr hm
      let e := localCell z q r hr hm U (labelZero a) (fastAt q z) (a (q, 1))
      prefixState (q.val + 1) (Nat.succ_le_of_lt q.isLt) (z, a) =
        if c.enabled then (some e.nextSlowSet, (prefixState q.val (Nat.le_of_lt q.isLt) (z, a)).2 ++ [e])
        else prefixState q.val (Nat.le_of_lt q.isLt) (z, a) := by
  have hd : z ∈ actualDomain (rate := rate) rewards C_star C_h q := ⟨r, hr, hm⟩
  obtain ⟨U, hU⟩ := generatedIncoming_present rate rewards C_star C_h q z a hd
  refine ⟨U, hU, ?_⟩
  have ht := currentCellTag_absent_of_actualDomain rate rewards C_star C_h q z a hd
  change extendedPrefixStep rate rewards C_star C_h q (z, a) _ = _
  simp only [extendedPrefixStep, prefixStep, prefixCandidate, ht, hU,
    collectionCellAt_of_record rate rewards C_star C_h q z a r hr hm U,
    collectionLogicalCellAt, cellWithScalar?]
  cases (inputAt z q r hr hm).enabled <;> simp

private theorem collection_word_data (e b : ℕ) (z : Source p)
    (hc : z ∈ collectionPrefixCell rate rewards C_star C_h e b)
    (q : Fin p.T) (r : Record rate) (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z) :
    ∃ hk : q.val - launchAt z < (collectionWord rate rewards C_star C_h e b z hc).length, numericalPast z q r hr hm =
        (collectionWord rate rewards C_star C_h e b z hc).take (q.val - launchAt z) ∧
      inputAt z q r hr hm = (collectionWord rate rewards C_star C_h e b z hc)[q.val - launchAt z]'hk := by
  let R := suffixAt z
  let W := collectionWord rate rewards C_star C_h e b z hc
  have hlaunch := collectionPrefixCell_launch rate rewards C_star C_h e b z hc
  have hactive := Classical.choose_spec hlaunch
  have hcells := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  rw [hactive] at hcells
  obtain ⟨L, hlen, hmap, hprefix, _⟩ := hcells
  have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hfull := hprefix R.length le_rfl
  have hdate : launchAt z + R.length = p.T := by dsimp [R]; omega
  rw [hdate, ← hlen, List.take_length] at hfull
  have hLW : L = W := Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch))
  subst L
  have hstart := collectionStart_le_of_actualDomain rate rewards C_star C_h q z ⟨r, hr, hm⟩
  have hsq : launchAt z ≤ q.val := by dsimp [collectionStart] at hstart; omega
  have hlookup : R[q.val - launchAt z]? = some r := by
    simpa only [actualRecord, ite_eq_left hsq] using hr
  obtain ⟨hkR, hrec⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hkW : q.val - launchAt z < W.length := by rw [hlen]; exact hkR
  refine ⟨hkW, ?_, ?_⟩
  · have hp := hprefix (q.val - launchAt z) hkR.le
    rw [Nat.add_sub_of_le hsq, ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells,
      actualPast_spec rewards C_star C_h z q r hr hm] at hp
    exact Option.some.inj hp
  · have he := congrArg (fun xs => xs[q.val - launchAt z]?) hmap
    rw [List.getElem?_map, hlookup, Option.map_some,
      ReferenceFirstCollectionOneRoundLogicalCell.actualInput_spec rewards C_star C_h z q r hr hm,
      List.getElem?_map, List.getElem?_eq_getElem hkW, Option.map_some] at he
    exact Option.some.inj (Option.some.inj he)


section Event
variable (u t : Fin p.T) (z : EventSource rate rewards C_star C_h u t) (a : AuxiliaryArray p)
local notation "D" => collectionPath rate rewards C_star C_h u t z a
local notation "H" => joinedPast rate rewards C_star C_h u t z D

private theorem event_anchor_one : (oldPayload rate rewards C_star C_h (u.val - launchAt z.val)
      (t.val - launchAt z.val) z.val
      (firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property)).anchor =
        fun _ => 1 := by
  let s := launchAt z.val
  let e := u.val - s
  let b := t.val - s
  let hc := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property
  obtain ⟨he, r, owned, base, hcoord, _, _, hpayload⟩ := collectionPrefixCell_live rate rewards C_star C_h e b z.val hc
  have hlaunch := collectionPrefixCell_launch rate rewards C_star C_h e b z.val hc
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z.val rewards C_star C_h).mp (by rw [Classical.choose_spec hlaunch]; rfl)
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h hcross
  let span := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h z.val
  have hR := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z.val hcross
  change suffixAt z.val = (ReferenceActivePhysicalHorizon.run initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s (p.T - s) span seed.activeAtStart).records at hR
  have hcount : e < p.T - s := by
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z.val rewards C_star C_h
    omega
  have hat := ReferenceLocalReleaseGateChronology.run_record_at initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s seed.activeAtStart
    (p.T - s) span ⟨e, hcount⟩
  have hactual : (suffixAt z.val)[e] = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s e (by omega) seed.activeAtStart := by
    simpa only [hR] using hat
  have hstate : (ReferenceActivePhysicalHorizon.run initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s e
      (by omega) seed.activeAtStart).finalState.coordinator = .live r owned base := by
    rw [hactual] at hcoord
    exact hcoord
  have hwindow : e ≤ (ReferenceFirstComplementMassBudget.firstWindow initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s (p.T - s) span seed.activeAtStart).length := by
    have heq := (firstLiveCollectionEvent_canonicalPrefixCell rate rewards C_star C_h u t z.val z.property).1
    change e = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (suffixAt z.val)).length at heq
    simpa only [hR] using heq.le
  have henv := ReferenceFirstLiveWeightEnvelope.run_first_live_weight_envelope initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s (p.T - s) span
    seed.activeAtStart seed.coordinatorFirst e hcount.le hwindow
  rw [hstate] at henv
  rw [oldPayload_eq rate rewards C_star C_h e b z.val hc r.payload hpayload]
  exact funext henv.1

/-- The first incoming set is the SAME trigger already retained in the final LIVE cell. -/
public theorem generated_seed_eq_collectionPath : (prefixState u.val (Nat.le_of_lt u.isLt) (z.val, a)).1 = some (D 0) ∧
    (prefixState u.val (Nat.le_of_lt u.isLt) (z.val, a)).2 = H := by
  have hdates := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  have hp := firstLiveCollectionEvent_calendarPast rate rewards C_star C_h u t z.val a z.property
  have hpU := extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h
    u.val (Nat.le_of_lt u.isLt) z.val a (by simpa only [collectionStart] using hdates.2.2.le)
  have hcal : calendarPast rate rewards C_star C_h (z.val, a) u.val = livePast (z.val, a) := by
    rw [calendarPast_eq_take_elapsed]
    have hlen := firstLiveChronologicalPrefix_length rate rewards C_star C_h (z.val, a)
    apply List.take_of_length_le
    dsimp only at hlen
    omega
  rw [hcal] at hpU
  refine ⟨?_, hpU.trans (hp.1.symm.trans (joinedPast_actual rate rewards C_star C_h u t z a).symm)⟩
  rw [extendedPrefixStateAux_seed, hpU, List.getLast?_eq_getElem?]
  obtain ⟨hk, hnext⟩ := firstLiveCollectionEvent_last_next rate rewards C_star C_h u t z.val a z.property
  have hlen := hp.2
  simp only [hp.1] at hlen hnext hk
  rw [hlen, List.getElem?_eq_getElem hk, Option.map_some]
  exact congrArg some (by
    simpa only [collectionPath, sampledArrayPath, sampledPath_zero, actualPrefixCoordinates,
      actualCoordinateIndex, DeferredRefreshUniformEvaluator.coordinateIndex] using hnext)

private theorem collectionPath_successor (i : Fin (t.val - u.val)) :
    let s := launchAt z.val
    let e := u.val - s
    let b := t.val - s
    let hc := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property
    let q : Fin p.T := ⟨u.val + i.val, by have hi := i.isLt; have ht := t.isLt; omega⟩
    D i.succ = DeferredRefreshUniformKernels.sampleRecordedRefresh p (Q)
        (collectionState rate rewards C_star C_h e b z.val hc (e + i.val))
        (windowInput rate rewards C_star C_h e b z.val hc ⟨i.val, by
          have h := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
          have hi := i.isLt; dsimp [b, e]; omega⟩)
        (fun _ => 1) (fun _ => zero_lt_one)
        (D i.castSucc) (a (q, 0), a (q, 1)) := by
  dsimp only
  rw [collectionPath_explicit]
  dsimp only [explicitPath]
  rw [sampledPath_succ]
  dsimp only [transitionSampler, innovations, labelZero]
  simp only [event_anchor_one rate rewards C_star C_h u t z]


private theorem cell_next_sample (q : Fin p.T) (z : Source p) (r : Record rate) (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z)
    (U : SlowSet p) (a0 : LabelZeroArray p) (f x : Scalar)
    (he : (inputAt z q r hr hm).enabled = true)
    (hs : (RecordedQueueRun.run (Q) (numericalPast z q r hr hm)).overflow = false) :
    (localCell z q r hr hm U a0 f x).nextSlowSet = DeferredRefreshUniformKernels.sampleRecordedRefresh p (Q)
        (RecordedQueueRun.run (Q) (numericalPast z q r hr hm))
        (inputAt z q r hr hm) (fun _ => 1) (fun _ => zero_lt_one) U (a0 q, x) := by
  simp only [cellWithScalar, cellWithNext, nextSet, hs, he, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ite_false, DeferredRefreshUniformKernels.sampleRecordedRefresh,
    RecordedSlowRefresh.proposalProbability_active p _ _ _ hs he, RecordedSlowRefresh.hazard,
    FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq, residualDraw_eq_sampleResidual]
  rfl

private theorem collectionState_clear (e b : ℕ) (z : Source p)
    (hc : z ∈ collectionPrefixCell rate rewards C_star C_h e b) (k : ℕ) (hk : k ≤ b) :
    (collectionState rate rewards C_star C_h e b z hc k).overflow = false := by
  have hb := collectionWord_bound rate rewards C_star C_h e b z hc
  have hclear := collectionWord_retained rate rewards C_star C_h e b z hc
  unfold collectionState at hclear ⊢
  cases ho : (RecordedQueueRun.run (Q) ((collectionWord rate rewards C_star C_h e b z hc).take k)).overflow with
  | false => rfl
  | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        _ _ k (hk.trans hb)).mp ho
      have hlast := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        _ _ b hb).mpr (hfirst.trans hk)
      rw [hclear] at hlast
      cases hlast

/-- At every offset the actual appended list projects to the SAME deferred path. -/
public theorem generated_collectionPath_prefix : ∀ n (hn : n ≤ t.val - u.val), ∃ K : List (Cell rate),
      (prefixState (u.val + n) (by have ht := t.isLt; omega) (z.val, a)).1 = some (D ⟨n, by omega⟩) ∧
      (prefixState (u.val + n) (by have ht := t.isLt; omega) (z.val, a)).2 = H ++ K ∧
      K.length = n ∧ K.map (fun c => (c.slowSet, c.nextSlowSet)) = List.ofFn (fun j : Fin n =>
          (D ⟨j.val, by have hj := j.isLt; omega⟩, D ⟨j.val + 1, by have hj := j.isLt; omega⟩)) := by
  have hdates := firstLiveCollectionEvent_dates rate rewards C_star C_h u t z.val z.property
  obtain ⟨theta, _, _, hfirst, _⟩ := firstLiveCollectionEvent_firstCall rate rewards C_star C_h u t z.val z.property
  have hend : ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z.val = t.val := by
    simp only [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hfirst]
  let s := launchAt z.val
  let e := u.val - s
  let b := t.val - s
  let hc := firstLiveCollectionEvent_prefixMembership rate rewards C_star C_h u t z.val z.property
  intro n
  induction n with
  | zero =>
      intro hn
      have hseed := generated_seed_eq_collectionPath rate rewards C_star C_h u t z a
      exact ⟨[], hseed.1, by simpa only [Nat.add_zero, List.append_nil] using hseed.2, rfl, rfl⟩
  | succ n ih =>
      intro hn
      obtain ⟨K, hU, hL, hlen, hmap⟩ := ih (by omega)
      let q : Fin p.T := ⟨u.val + n, by have ht := t.isLt; omega⟩
      have hd := actualDomain_of_collection_interval rate rewards C_star C_h q z.val
        (by dsimp [q, collectionStart]; omega) (by rw [hend]; dsimp [q]; omega)
      obtain ⟨r, hr, hm⟩ := hd
      obtain ⟨hk, hpast, hinput⟩ := collection_word_data rate rewards C_star C_h e b z.val hc q r hr hm
      have hindex : q.val - launchAt z.val = e + n := by
        dsimp [q, e, s]; omega
      have hin : inputAt z.val q r hr hm =
          windowInput rate rewards C_star C_h e b z.val hc ⟨n, by dsimp [b, e]; omega⟩ := by
        simpa only [windowInput, hindex] using hinput
      have hpre : RecordedQueueRun.run (Q) (numericalPast z.val q r hr hm) =
          collectionState rate rewards C_star C_h e b z.val hc (e + n) := by
        simp only [collectionState, hpast, hindex]
      have he : (inputAt z.val q r hr hm).enabled = true := by
        rw [hinput]
        simpa only [hindex] using (ReferenceActualCollectionEnabledPrefixEndpoint.actual_collection_enabled_prefix
            rate rewards C_star C_h e b z.val hc).2 n (by dsimp [b, e]; omega)
      have hs : (RecordedQueueRun.run (Q) (numericalPast z.val q r hr hm)).overflow = false := by
        rw [hpre]
        exact collectionState_clear rate rewards C_star C_h e b z.val hc (e + n) (by dsimp [b, e]; omega)
      obtain ⟨U, hU', hstep⟩ := generated_collection_step rate rewards C_star C_h q z.val a r hr hm
      have hUeq : U = D ⟨n, by omega⟩ := Option.some.inj (hU'.symm.trans hU)
      subst U
      let c := localCell z.val q r hr hm (D ⟨n, by omega⟩) (labelZero a) (fastAt q z.val) (a (q, 1))
      have hslow : c.slowSet = D ⟨n, by omega⟩ :=
        (ReferenceFirstCollectionOneRoundLogicalCell.cell_pre_nonoverflow rewards C_star C_h z.val q r hr hm
          _ _ _ _ he hs).1
      have hnext : c.nextSlowSet = D ⟨n + 1, by omega⟩ := by
        rw [cell_next_sample rate rewards C_star C_h q z.val r hr hm _ _ _ _ he hs, hpre, hin]
        exact (collectionPath_successor rate rewards C_star C_h u t z a ⟨n, by omega⟩).symm
      dsimp only at hstep
      simp only [he, ite_true] at hstep
      refine ⟨K ++ [c], ?_, ?_, by simp only [List.length_append, List.length_singleton, hlen], ?_⟩
      · change (prefixState (q.val + 1) _ (z.val, a)).1 = _
        rw [hstep]
        exact congrArg some hnext
      · change (prefixState (q.val + 1) _ (z.val, a)).2 = _
        rw [hstep, hL, List.append_assoc]
      · rw [List.map_append, hmap, List.map_cons, List.map_nil, hslow, hnext, List.ofFn_succ']
        simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

end Event

/-- Every generated collection entry comes from its actual date and generated incoming set. -/
public theorem extendedPast_collection_origin : ∀ n (hn : n ≤ p.T) (za : Source p × AuxiliaryArray p) (c : Cell rate),
      c ∈ (prefixState n hn za).2 → c ∈ livePast za ∨ ∃ (q : Fin p.T) (U : SlowSet p), q.val < n ∧
        (prefixState q.val (Nat.le_of_lt q.isLt) za).1 = some U ∧ cellAt q U za = some c := by
  intro n
  induction n with
  | zero => intro hn za c hc; cases hc
  | succ n ih =>
      intro hn za c hc
      let q : Fin p.T := ⟨n, Nat.lt_of_succ_le hn⟩
      let S := prefixState n (Nat.le_of_succ_le hn) za
      have hprev (hc : c ∈ S.2) : c ∈ livePast za ∨ ∃ (r : Fin p.T) (U : SlowSet p), r.val < n + 1 ∧
            (prefixState r.val (Nat.le_of_lt r.isLt) za).1 = some U ∧ cellAt r U za = some c := by
        rcases ih (Nat.le_of_succ_le hn) za c hc with h | ⟨r, U, hr, hU, hcell⟩
        · exact Or.inl h
        · exact Or.inr ⟨r, U, by omega, hU, hcell⟩
      change c ∈ (extendedPrefixStep rate rewards C_star C_h q za S).2 at hc
      cases htag : liveTagAt q za with
      | inr d =>
          simp only [extendedPrefixStep, prefixStep, prefixCandidate, htag, List.mem_append, List.mem_singleton] at hc
          rcases hc with h | rfl
          · exact hprev h
          · left
            have hmem : c ∈ calendarPast rate rewards C_star C_h za (q.val + 1) := by
              rw [calendarPast_successor rate rewards C_star C_h q za, htag]
              exact List.mem_append_right _ (List.mem_singleton_self c)
            rw [calendarPast_eq_take_elapsed] at hmem
            exact List.mem_of_mem_take hmem

      | inl u =>
          cases hU : S.1 with
          | none => exact hprev (by simpa only [extendedPrefixStep, prefixStep, prefixCandidate, htag, hU] using hc)
          | some U =>
              cases hcell : cellAt q U za with
              | none => exact hprev (by simpa only [extendedPrefixStep, prefixStep, prefixCandidate, htag, hU, hcell] using hc)
              | some d =>
                  simp only [extendedPrefixStep, prefixStep, prefixCandidate, htag, hU, hcell,
                    List.mem_append, List.mem_singleton] at hc
                  rcases hc with h | rfl
                  · exact hprev h
                  · exact Or.inr ⟨q, U, by dsimp [q]; omega, hU, hcell⟩

/-- Full actual numerical and branch characterization of every appended collection cell. -/
public theorem generated_collection_cell_fields (n : Fin (p.T + 1))
    (z : Source p) (a : AuxiliaryArray p) (c : Cell rate)
    (hc : c ∈ pastAt n (z, a))
    (hnotlive : c ∉ livePast (z, a)) :
    ∃ (q : Fin p.T) (r : Record rate) (hr : recordAt q z = some r)
      (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z)
      (U : SlowSet p),
      q.val < n.val ∧
      (prefixState q.val (Nat.le_of_lt q.isLt) (z, a)).1 = some U ∧
      let I := inputAt z q r hr hm
      let S := RecordedQueueRun.run (Q) (numericalPast z q r hr hm)
      I.enabled = true ∧ c.time = q ∧ c.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      c.numerical = numericalCoordinates I ∧ c.before = S ∧
      c.after = RecordedQueueRun.step (Q) S I ∧ c.arrivals = RecordedQueueRun.acceptedRecord (Q) S I ∧
      c.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n)
        (S.registers j) (RecordedQueueRun.acceptedRecord (Q) S I j)) ∧
      c.slowSet = (if S.overflow then frozenSlowSet p else U) ∧
      c.fastArm = (if S.overflow then frozenFastArm p else (actualFast rewards C_star C_h z q r hr hm U
          (fastAt q z)).val) ∧
      c.proposal = (I.enabled && !S.overflow && decide ((a (q, 0)).val < 4 * p.m * rate.eta.val)) ∧
      c.nextSlowSet = (if S.overflow then frozenSlowSet p else
        if c.proposal then residualDraw rate S I (fun _ => 1) (fun _ => zero_lt_one) (a (q, 1)) else U) ∧
      ∀ j, c.service j ≤ 4 * (Q).n ∧
        c.after.registers j = QueueReplay.transition (4 * (Q).n) (c.before.registers j) (c.arrivals j) := by
  rcases extendedPast_collection_origin rate rewards C_star C_h n.val (Nat.le_of_lt_succ n.isLt)
      (z, a) c hc with h | ⟨q, U, hq, hU, he⟩
  · exact (hnotlive h).elim
  · classical
    unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell? at he
    split at he
    · rename_i hd
      let r := domainRecord rewards C_star C_h q ⟨z, hd⟩
      have hr := domainRecord_spec rewards C_star C_h q ⟨z, hd⟩
      have hm := domainRecord_mem rewards C_star C_h q ⟨z, hd⟩
      change collectionLogicalCellAt rewards C_star C_h z q r hr hm U (labelZero a) (a (q, 1)) = some c at he
      unfold collectionLogicalCellAt cellWithScalar? at he
      split at he
      · rename_i henabled
        have hceq := Option.some.inj he
        refine ⟨q, r, hr, hm, U, hq, hU, henabled, ?_⟩
        rw [← hceq]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
        exact ⟨RecordedQueueRun.recordService_le_capacity _ _ _, rfl⟩
      · cases he
    · cases he

/-- Disabled collection dates append nothing and preserve all numerical registers. -/
public theorem generated_collection_disabled (q : Fin p.T) (z : Source p) (a : AuxiliaryArray p)
    (r : Record rate) (hr : recordAt q z = some r)
    (hm : r ∈ ReferenceFirstCollectionOneRoundLogicalCell.firstCollection (rate := rate) rewards C_star C_h z)
    (he : (inputAt z q r hr hm).enabled = false) :
    prefixState (q.val + 1) (Nat.succ_le_of_lt q.isLt) (z, a) = prefixState q.val (Nat.le_of_lt q.isLt) (z, a) ∧
    ∀ j, (RecordedQueueRun.step (Q) (RecordedQueueRun.run (Q) (numericalPast z q r hr hm))
      (inputAt z q r hr hm)).registers j =
      (RecordedQueueRun.run (Q) (numericalPast z q r hr hm)).registers j := by
  obtain ⟨_, _, hstep⟩ := generated_collection_step rate rewards C_star C_h q z a r hr hm
  exact ⟨by simpa only [he, Bool.false_eq_true, ite_false] using hstep,
    ReferenceFirstCollectionOneRoundLogicalCell.disabled_registers rewards C_star C_h z q r hr hm he⟩

end Characterization

end Bandits.Support.ReferenceFirstCollectionLogicalPrefixExtension

end
